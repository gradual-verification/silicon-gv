// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.state

import viper.silver.ast
import viper.silver.cfg.silver.SilverCfg
import viper.silicon.common.Mergeable
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.state.State.OldHeaps
import viper.silicon.state.terms.{Term, Var}
import viper.silicon.supporters.functions.{FunctionRecorder, NoopFunctionRecorder}
import viper.silicon.{Map, Stack}

final case class State(g: Store = Store(),
                       oldStore: Option[Store] = None,
                       h: Heap = Heap(),
                       oldHeaps: OldHeaps = Map.empty,

                       isImprecise: Boolean = false,
                       optimisticHeap: Heap = Heap(),
                       gatherFrame: Boolean = false,
                       frameArgHeap: Heap = Heap(),

                       parallelizeBranches: Boolean = false,

                       recordVisited: Boolean = false,
                       visited: List[ast.Predicate] = Nil, /* TODO: Use a multiset instead of a list */

                       methodCfg: SilverCfg = null,
                       invariantContexts: Stack[(Boolean,Boolean,Heap,Heap)] = Stack.empty,

                       constrainableARPs: InsertionOrderedSet[Var] = InsertionOrderedSet.empty,
                       quantifiedVariables: Stack[Var] = Nil,
                       retrying: Boolean = false,
                       underJoin: Boolean = false,
                       functionRecorder: FunctionRecorder = NoopFunctionRecorder,
                       conservingSnapshotGeneration: Boolean = false,
                       recordPossibleTriggers: Boolean = false,
                       possibleTriggers: Map[ast.Exp, Term] = Map(),

                       triggerExp: Boolean = false,

                       partiallyConsumedHeap: Option[Heap] = None,
                       permissionScalingFactor: Term = terms.FullPerm(),

                       reserveHeaps: Stack[Heap] = Nil,
                       reserveCfgs: Stack[SilverCfg] = Stack(),
                       conservedPcs: Stack[Vector[RecordedPathConditions]] = Stack(),
                       recordPcs: Boolean = false,
                       exhaleExt: Boolean = false,

                       applyHeuristics: Boolean = false,
                       heuristicsDepth: Int = 0,
                       triggerAction: AnyRef = null,

                       ssCache: SsCache = Map.empty,
                       hackIssue387DisablePermissionConsumption: Boolean = false,

                       qpFields: InsertionOrderedSet[ast.Field] = InsertionOrderedSet.empty,
                       qpPredicates: InsertionOrderedSet[ast.Predicate] = InsertionOrderedSet.empty,
                       qpMagicWands: InsertionOrderedSet[MagicWandIdentifier] = InsertionOrderedSet.empty,
                       smCache: SnapshotMapCache = SnapshotMapCache.empty,
                       pmCache: PmCache = Map.empty,
                       smDomainNeeded: Boolean = false,
                       /* TODO: Isn't this data stable, i.e. fully known after a preprocessing step? If so, move it to the appropriate supporter. */
                       predicateSnapMap: Map[ast.Predicate, terms.Sort] = Map.empty,
                       predicateFormalVarMap: Map[ast.Predicate, Seq[terms.Var]] = Map.empty,
                       isMethodVerification: Boolean = false,
                       methodCallAstNode: Option[ast.MethodCall] = None,
                       foldOrUnfoldAstNode: Option[ast.Node] = None,
                       loopPosition: Option[CheckPosition.Loop] = None,
                       unfoldingAstNode: Option[ast.Node] = None,
                       forFraming: Boolean = false,
                       generateChecks: Boolean = true,
                       needConditionFramingUnfold: Boolean = false,
                       needConditionFramingProduce: Boolean = false,
                       madeOptimisticAssumptions: Boolean = false,
                       evalHeapsSet: Boolean = false)
    extends Mergeable[State] {

  def incCycleCounter(m: ast.Predicate) =
    if (recordVisited) copy(visited = m :: visited)
    else this

  def decCycleCounter(m: ast.Member) =
    if (recordVisited) {
      require(visited.contains(m))

      val (ms, others) = visited.partition(_ == m)
      copy(visited = ms.tail ::: others)
    }
  else
    this

  def cycles(m: ast.Member) = visited.count(_ == m)

  def setConstrainable(arps: Iterable[Var], constrainable: Boolean) = {
    val newConstrainableARPs =
      if (constrainable) constrainableARPs ++ arps
      else constrainableARPs -- arps

    copy(constrainableARPs = newConstrainableARPs)
  }

  def scalePermissionFactor(p: Term) =
    copy(permissionScalingFactor = terms.PermTimes(p, permissionScalingFactor))

  def merge(other: State): State =
    State.merge(this, other)

  def preserveAfterLocalEvaluation(post: State): State =
    State.preserveAfterLocalEvaluation(this, post)

  def functionRecorderQuantifiedVariables(): Seq[Var] =
    functionRecorder.data.fold(Seq.empty[Var])(_.arguments)

  def relevantQuantifiedVariables(filterPredicate: Var => Boolean): Seq[Var] = (
       functionRecorderQuantifiedVariables()
    ++ quantifiedVariables.filter(filterPredicate)
  )

  def relevantQuantifiedVariables(occurringIn: Seq[Term]): Seq[Var] =
    relevantQuantifiedVariables(x => occurringIn.exists(_.contains(x)))

  lazy val relevantQuantifiedVariables: Seq[Var] =
    relevantQuantifiedVariables(_ => true)

  override val toString = s"${this.getClass.getSimpleName}(...)"
}

object State {
  type OldHeaps = Map[String, Heap]
  val OldHeaps = Map

  def merge(s1: State, s2: State): State = {
    /* TODO: Instead of aborting with a pattern mismatch, all mismatches
     *       should be detected first (and accumulated), and afterwards a meaningful
     *       exception should be thrown. This would improve debugging significantly.
     */
    // completed above todo -> Priyam

    val mismatches = scala.collection.mutable.ListBuffer[String]()

    s1 match {
      case State(g1, oldStore1, h1, oldHeaps1,
                 isImprecise1, optimisticHeap1,
                 gatherFrame1, frameArgHeap1,
                 parallelizeBranches1,
                 recordVisited1, visited1,
                 methodCfg1, invariantContexts1,
                 constrainableARPs1,
                 quantifiedVariables1,
                 retrying1,
                 underJoin1,
                 functionRecorder1,
                 conservingSnapshotGeneration1,
                 recordPossibleTriggers1, possibleTriggers1,
                 triggerExp1,
                 partiallyConsumedHeap1,
                 permissionScalingFactor1,
                 reserveHeaps1, reserveCfgs1, conservedPcs1, recordPcs1, exhaleExt1,
                 applyHeuristics1, heuristicsDepth1, triggerAction1,
                 ssCache1, hackIssue387DisablePermissionConsumption1,
                 qpFields1, qpPredicates1, qpMagicWands1, smCache1, pmCache1, smDomainNeeded1,
                 predicateSnapMap1, predicateFormalVarMap1, hack1,
                 methodCallAstNode1, foldOrUnfoldAstNode1, loopPosition1, unfoldingAstNode1, forFraming1, generateChecks1,
                 needConditionFramingUnfold1, needConditionFramingProduce1,
                 madeOptimisticAssumptions1, evalHeapsSet1) =>
        //sys.error("testing")

        s2 match {
          case State(g2, oldStore2, h2, oldHeaps2, // oldStore and oldHeaps shouldn't be checked
                     isImprecise2, optimisticHeap2, // optimisticHeap not checked
                     gatherFrame2, frameArgHeap2,
                     parallelizeBranches2,
                     recordVisited2, visited2,
                     methodCfg2, invariantContexts2,
                     constrainableARPs2, // not checked
                     quantifiedVariables2,
                     retrying2,
                     underJoin2,
                     functionRecorder2, // not checked
                     conservingSnapshotGeneration2,
                     recordPossibleTriggers2, possibleTriggers2, // triggers not checked
                     triggerExp2, // not checked
                     partiallyConsumedHeap2,
                     permissionScalingFactor2,
                     reserveHeaps2, reserveCfgs2, conservedPcs2, recordPcs2, exhaleExt2,
                     applyHeuristics2, heuristicsDepth2, triggerAction2,
                     ssCache2, hackIssue387DisablePermissionConsumption2, // sscache not checked
                     qpFields2, qpPredicates2, qpMagicWands2, smCache2, pmCache2, smDomainNeeded2, // pmCache not checked
                     predicateSnapMap2, predicateFormalVarMap2, hack2,
                     methodCallAstNode2, foldOrUnfoldAstNode2, loopPosition2, unfoldingAstNode2, forFraming2,
                     generateChecks2, needConditionFramingUnfold2, // needConditionFramingUnfold not checked
                     needConditionFramingProduce2, madeOptimisticAssumptions2, evalHeapsSet2) => // needConditionFramingProduce not checked
            // only check relevant constructs
            if (g1 != g2) mismatches += s"g mismatch: ${g1} != ${g2}"
            if (h1 != h2) mismatches += s"heap mismatch: ${h1} != ${h2}"
            if (isImprecise1 != isImprecise2) mismatches += s"isImprecise mismatch: ${isImprecise1} != ${isImprecise2}"
            if (gatherFrame1 != gatherFrame2) mismatches += s"gatherFrame mismatch: ${gatherFrame1} != ${gatherFrame2}"
            if (frameArgHeap1 != frameArgHeap2) mismatches += s"frameArgHeap mismatch: ${frameArgHeap1} != ${frameArgHeap2}"
            if (parallelizeBranches1 != parallelizeBranches2) mismatches += s"parallelizeBranches mismatch: ${parallelizeBranches1} != ${parallelizeBranches2}"
            if (recordVisited1 != recordVisited2) mismatches += s"recordVisited mismatch: ${recordVisited1} != ${recordVisited2}"
            if (visited1 != visited2) mismatches += s"visited mismatch: ${visited1} != ${visited2}"
            if (methodCfg1 != methodCfg2) mismatches += s"methodCfg mismatch: ${methodCfg1} != ${methodCfg2}"
            if (invariantContexts1 != invariantContexts2) mismatches += s"invariantContexts mismatch: ${invariantContexts1} != ${invariantContexts2}"
            if (quantifiedVariables1 != quantifiedVariables2) mismatches += s"quantifiedVariables mismatch: ${quantifiedVariables1} != ${quantifiedVariables2}"
            if (retrying1 != retrying2) mismatches += s"retrying mismatch: ${retrying1} != ${retrying2}"
            if (underJoin1 != underJoin2) mismatches += s"underJoin mismatch: ${underJoin1} != ${underJoin2}"
            if (conservingSnapshotGeneration1 != conservingSnapshotGeneration2) mismatches += s"conservingSnapshotGeneration mismatch: ${conservingSnapshotGeneration1} != ${conservingSnapshotGeneration2}"
            if (recordPossibleTriggers1 != recordPossibleTriggers2) mismatches += s"recordPossibleTriggers mismatch: ${recordPossibleTriggers1} != ${recordPossibleTriggers2}"
            if (partiallyConsumedHeap1 != partiallyConsumedHeap2) mismatches += s"partiallyConsumedHeap mismatch: ${partiallyConsumedHeap1} != ${partiallyConsumedHeap2}"
            if (permissionScalingFactor1 != permissionScalingFactor2) mismatches += s"permissionScalingFactor mismatch: ${permissionScalingFactor1} != ${permissionScalingFactor2}"
            if (reserveHeaps1 != reserveHeaps2) mismatches += s"reserveHeaps mismatch: ${reserveHeaps1} != ${reserveHeaps2}"
            if (reserveCfgs1 != reserveCfgs2) mismatches += s"reserveCfgs mismatch: ${reserveCfgs1} != ${reserveCfgs2}"
            if (conservedPcs1 != conservedPcs2) mismatches += s"conservedPcs mismatch: ${conservedPcs1} != ${conservedPcs2}"
            if (recordPcs1 != recordPcs2) mismatches += s"recordPcs mismatch: ${recordPcs1} != ${recordPcs2}"
            if (exhaleExt1 != exhaleExt2) mismatches += s"exhaleExt mismatch: ${exhaleExt1} != ${exhaleExt2}"
            if (applyHeuristics1 != applyHeuristics2) mismatches += s"applyHeuristics mismatch: ${applyHeuristics1} != ${applyHeuristics2}"
            if (heuristicsDepth1 != heuristicsDepth2) mismatches += s"heuristicsDepth mismatch: ${heuristicsDepth1} != ${heuristicsDepth2}"
            if (triggerAction1 != triggerAction2) mismatches += s"triggerAction mismatch: ${triggerAction1} != ${triggerAction2}"
            if (hackIssue387DisablePermissionConsumption1 != hackIssue387DisablePermissionConsumption2) mismatches += s"hackIssue387DisablePermissionConsumption mismatch: ${hackIssue387DisablePermissionConsumption1} != ${hackIssue387DisablePermissionConsumption2}"
            if (qpFields1 != qpFields2) mismatches += s"qpFields mismatch: ${qpFields1} != ${qpFields2}"
            if (qpPredicates1 != qpPredicates2) mismatches += s"qpPredicates mismatch: ${qpPredicates1} != ${qpPredicates2}"
            if (qpMagicWands1 != qpMagicWands2) mismatches += s"qpMagicWands mismatch: ${qpMagicWands1} != ${qpMagicWands2}"
            if (smDomainNeeded1 != smDomainNeeded2) mismatches += s"smDomainNeeded mismatch: ${smDomainNeeded1} != ${smDomainNeeded2}"
            if (predicateSnapMap1 != predicateSnapMap2) mismatches += s"predicateSnapMap mismatch: ${predicateSnapMap1} != ${predicateSnapMap2}"
            if (predicateFormalVarMap1 != predicateFormalVarMap2) mismatches += s"predicateFormalVarMap mismatch: ${predicateFormalVarMap1} != ${predicateFormalVarMap2}"
            if (hack1 != hack2) mismatches += s"hack mismatch: ${hack1} != ${hack2}"
            if (methodCallAstNode1 != methodCallAstNode2) mismatches += s"methodCallAstNode mismatch: ${methodCallAstNode1} != ${methodCallAstNode2}"
            if (foldOrUnfoldAstNode1 != foldOrUnfoldAstNode2) mismatches += s"foldOrUnfoldAstNode mismatch: ${foldOrUnfoldAstNode1} != ${foldOrUnfoldAstNode2}"
            if (loopPosition1 != loopPosition2) mismatches += s"loopPosition mismatch: ${loopPosition1} != ${loopPosition2}"
            if (unfoldingAstNode1 != unfoldingAstNode2) mismatches += s"unfoldingAstNode mismatch: ${unfoldingAstNode1} != ${unfoldingAstNode2}"
            if (forFraming1 != forFraming2) mismatches += s"forFraming mismatch: ${forFraming1} != ${forFraming2}"
            if (generateChecks1 != generateChecks2) mismatches += s"generateChecks mismatch: ${generateChecks1} != ${generateChecks2}"

            if (mismatches.nonEmpty) {
                throw new IllegalArgumentException("State merging failed due to mismatches: " + mismatches.mkString(", "))
            }

            val functionRecorder3 = functionRecorder1.merge(functionRecorder2)
            val triggerExp3 = triggerExp1 && triggerExp2
            val possibleTriggers3 = possibleTriggers1 ++ possibleTriggers2
            val constrainableARPs3 = constrainableARPs1 ++ constrainableARPs2

            val smCache3 = smCache1.union(smCache2)
            val pmCache3 = pmCache1 ++ pmCache2
            val ssCache3 = ssCache1 ++ ssCache2

            val madeOptimisticAssumptions3 = madeOptimisticAssumptions1 || madeOptimisticAssumptions2
            val evalHeapsSet3 = evalHeapsSet1 || evalHeapsSet2
            val oldHeaps3 = oldHeaps1 ++ oldHeaps2
            val optimisticHeap3 = Heap(optimisticHeap1.values.filter(ch => optimisticHeap2.values.exists(_ == ch))) // Intersection of Heaps
            // println(s"optimisticHeap1: ${optimisticHeap1.values.mkString("[", ", ", "]")}")
            // println(s"optimisticHeap2: ${optimisticHeap2.values.mkString("[", ", ", "]")}")
            // println(s"optimisticHeap3: ${optimisticHeap3.values.mkString("[", ", ", "]")}")

            s1.copy(functionRecorder = functionRecorder3,
                    possibleTriggers = possibleTriggers3,
                    triggerExp = triggerExp3,
                    constrainableARPs = constrainableARPs3,
                    ssCache = ssCache3,
                    smCache = smCache3,
                    pmCache = pmCache3,
                    madeOptimisticAssumptions = madeOptimisticAssumptions3,
                    evalHeapsSet = evalHeapsSet3,
                    oldHeaps = oldHeaps3,
                    optimisticHeap = optimisticHeap3)
            // TODO: Should oldStore be updated here? what is oldStore for?

          case _ =>
            throw new IllegalArgumentException("State merging failed: unexpected mismatch between symbolic states")
    }}
  }

  def preserveAfterLocalEvaluation(pre: State, post: State): State = {
    pre.copy(functionRecorder = post.functionRecorder,
             possibleTriggers = post.possibleTriggers,
             smCache = post.smCache,
             constrainableARPs = post.constrainableARPs)
  }

  def conflictFreeUnionOrAbort[K, V](m1: Map[K, V], m2: Map[K, V]): Map[K,V] =
    viper.silicon.utils.conflictFreeUnion(m1, m2) match {
      case (m3, conflicts) if conflicts.isEmpty => m3
      case _ => sys.error("Unexpected mismatch between contexts")
    }

  def merge[M <: Mergeable[M]](candidate1: Option[M], candidate2: Option[M]): Option[M] =
    (candidate1, candidate2) match {
      case (Some(m1), Some(m2)) => Some(m1.merge(m2))
      case (None, None) => None
      case _ => sys.error("Unexpected mismatch between contexts")
    }
}
