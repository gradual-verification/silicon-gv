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
                       madeOptimisticAssumptions: Boolean = false)
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
                 isImprecise, optimisticHeap1,
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
                 predicateSnapMap1, predicateFormalVarMap1, hack,
                 methodCallAstNode1, foldOrUnfoldAstNode1, loopPosition1, unfoldingAstNode1, forFraming, generateChecks,
                 needConditionFramingUnfold, needConditionFramingProduce,
                 madeOptimisticAssumptions) =>
        //sys.error("testing")

        s2 match {
          case State(g2, oldStore2, h2, oldHeaps2,
                     isImprecise2, optimisticHeap2,
                     gatherFrame2, frameArgHeap2,
                     parallelizeBranches2,
                     recordVisited2, visited2,
                     methodCfg2, invariantContexts2,
                     constrainableARPs2, // not relevant
                     quantifiedVariables2,
                     retrying2,
                     underJoin2,
                     functionRecorder2, // not relevant
                     conservingSnapshotGeneration2,
                     recordPossibleTriggers2, possibleTriggers2, // triggers not relevant
                     triggerExp2, // not relevant
                     partiallyConsumedHeap2,
                     permissionScalingFactor2,
                     reserveHeaps2, reserveCfgs2, conservedPcs2, recordPcs2, exhaleExt2,
                     applyHeuristics2, heuristicsDepth2, triggerAction2,
                     ssCache2, hackIssue387DisablePermissionConsumption2, // sscache not relevant
                     qpFields2, qpPredicates2, qpMagicWands2, smCache2, pmCache2, smDomainNeeded2,
                     predicateSnapMap2, predicateFormalVarMap2, hack2,
                     methodCallAstNode2, foldOrUnfoldAstNode2, loopPosition2, unfoldingAstNode2, forFraming2,
                     generateChecks2, needConditionFramingUnfold2,
                     needConditionFramingProduce2, madeOptimisticAssumptions2) =>
           // only check relevant constructs
            if (g1 != g2) mismatches += "g mismatch"
            if (oldStore1 != oldStore2) mismatches += s"oldStore mismatch ${oldStore1} != ${oldStore2}"
            if (h1 != h2) mismatches += "heap mismatch"
            if (oldHeaps1 != oldHeaps2) mismatches += "oldHeaps mismatch"
            if (isImprecise != isImprecise2) mismatches += "isImprecise mismatch"
            if (optimisticHeap1 != optimisticHeap2) mismatches += "optimisticHeap mismatch"
            if (gatherFrame1 != gatherFrame2) mismatches += "gatherFrame mismatch"
            if (frameArgHeap1 != frameArgHeap2) mismatches += "frameArgHeap mismatch"
            if (parallelizeBranches1 != parallelizeBranches2) mismatches += "parallelizeBranches mismatch"
            if (recordVisited1 != recordVisited2) mismatches += "recordVisited mismatch"
            if (visited1 != visited2) mismatches += "visited mismatch"
            if (methodCfg1 != methodCfg2) mismatches += "methodCfg mismatch"
            if (invariantContexts1 != invariantContexts2) mismatches += "invariantContexts mismatch"
            if (quantifiedVariables1 != quantifiedVariables2) mismatches += "quantifiedVariables mismatch"
            if (retrying1 != retrying2) mismatches += "retrying mismatch"
            if (underJoin1 != underJoin2) mismatches += "underJoin mismatch"
            if (conservingSnapshotGeneration1 != conservingSnapshotGeneration2) mismatches += "conservingSnapshotGeneration mismatch"
            if (recordPossibleTriggers1 != recordPossibleTriggers2) mismatches += "recordPossibleTriggers mismatch"
            if (partiallyConsumedHeap1 != partiallyConsumedHeap2) mismatches += "partiallyConsumedHeap mismatch"
            if (permissionScalingFactor1 != permissionScalingFactor2) mismatches += "permissionScalingFactor mismatch"
            if (reserveHeaps1 != reserveHeaps2) mismatches += "reserveHeaps mismatch"
            if (reserveCfgs1 != reserveCfgs2) mismatches += "reserveCfgs mismatch"
            if (conservedPcs1 != conservedPcs2) mismatches += "conservedPcs mismatch"
            if (recordPcs1 != recordPcs2) mismatches += "recordPcs mismatch"
            if (exhaleExt1 != exhaleExt2) mismatches += "exhaleExt mismatch"
            if (applyHeuristics1 != applyHeuristics2) mismatches += "applyHeuristics mismatch"
            if (heuristicsDepth1 != heuristicsDepth2) mismatches += "heuristicsDepth mismatch"
            if (triggerAction1 != triggerAction2) mismatches += "triggerAction mismatch"
            if (hackIssue387DisablePermissionConsumption1 != hackIssue387DisablePermissionConsumption2) mismatches += "hackIssue387DisablePermissionConsumption mismatch"
            if (qpFields1 != qpFields2) mismatches += "qpFields mismatch"
            if (qpPredicates1 != qpPredicates2) mismatches += "qpPredicates mismatch"
            if (qpMagicWands1 != qpMagicWands2) mismatches += "qpMagicWands mismatch"
            //if (smCache1 != smCache2) mismatches += "smCache mismatch" - not needed
            //if (pmCache1 != pmCache2) mismatches += "pmCache mismatch" - not needed
            if (smDomainNeeded1 != smDomainNeeded2) mismatches += "smDomainNeeded mismatch"
            if (predicateSnapMap1 != predicateSnapMap2) mismatches += "predicateSnapMap mismatch"
            if (predicateFormalVarMap1 != predicateFormalVarMap2) mismatches += "predicateFormalVarMap mismatch"
            if (hack != hack2) mismatches += "hack mismatch"
            if (methodCallAstNode1 != methodCallAstNode2) mismatches += "methodCallAstNode mismatch"
            if (foldOrUnfoldAstNode1 != foldOrUnfoldAstNode2) mismatches += "foldOrUnfoldAstNode mismatch"
            if (loopPosition1 != loopPosition2) mismatches += "loopPosition mismatch"
            if (unfoldingAstNode1 != unfoldingAstNode2) mismatches += "unfoldingAstNode mismatch"
            if (forFraming != forFraming2) mismatches += "forFraming mismatch"
            if (generateChecks != generateChecks2) mismatches += s"generateChecks mismatch ${generateChecks} != ${generateChecks2}"
            if (needConditionFramingUnfold != needConditionFramingUnfold2) mismatches += "needConditionFramingUnfold mismatch"
            if (needConditionFramingProduce != needConditionFramingProduce2) mismatches += "needConditionFramingProduce mismatch"
            if (madeOptimisticAssumptions != madeOptimisticAssumptions2) mismatches += "madeOptimisticAssumptions mismatch"

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

            s1.copy(functionRecorder = functionRecorder3,
                    possibleTriggers = possibleTriggers3,
                    triggerExp = triggerExp3,
                    constrainableARPs = constrainableARPs3,
                    ssCache = ssCache3,
                    smCache = smCache3,
                    pmCache = pmCache3)

          case _ =>
            throw new IllegalArgumentException("State merging failed: unexpected mismatch between symbolic states")
    }}

    // s1 match {
    //   /* Decompose state s1 */
    //   case State(g1, oldStore1, h1, oldHeaps1,
    //              isImprecise, optimisticHeap1,
    //              gatherFrame1, frameArgHeap1,
    //              parallelizeBranches1,
    //              recordVisited1, visited1,
    //              methodCfg1, invariantContexts1,
    //              constrainableARPs1,
    //              quantifiedVariables1,
    //              retrying1,
    //              underJoin1,
    //              functionRecorder1,
    //              conservingSnapshotGeneration1,
    //              recordPossibleTriggers1, possibleTriggers1,
    //              triggerExp1,
    //              partiallyConsumedHeap1,
    //              permissionScalingFactor1,
    //              reserveHeaps1, reserveCfgs1, conservedPcs1, recordPcs1, exhaleExt1,
    //              applyHeuristics1, heuristicsDepth1, triggerAction1,
    //              ssCache1, hackIssue387DisablePermissionConsumption1,
    //              qpFields1, qpPredicates1, qpMagicWands1, smCache1, pmCache1, smDomainNeeded1,
    //              predicateSnapMap1, predicateFormalVarMap1, hack,
    //              methodCallAstNode1, foldOrUnfoldAstNode1, loopPosition1, unfoldingAstNode1, forFraming, generateChecks,
    //              needConditionFramingUnfold, needConditionFramingProduce,
    //              madeOptimisticAssumptions) =>

    //     /* Decompose state s2: most values must match those of s1 */
    //     s2 match {
    //       // we do not care whether oldStore matches here; oldStore should not
    //       // stick around for that long?
    //       case State(`g1`, `oldStore1`, `h1`, `oldHeaps1`,
    //                  `isImprecise`, `optimisticHeap1`,
    //                  `gatherFrame1`, `frameArgHeap1`,
    //                  `parallelizeBranches1`,
    //                  `recordVisited1`, `visited1`,
    //                  `methodCfg1`, `invariantContexts1`,
    //                  constrainableARPs2,
    //                  `quantifiedVariables1`,
    //                  `retrying1`,
    //                  `underJoin1`,
    //                  functionRecorder2,
    //                  `conservingSnapshotGeneration1`,
    //                  `recordPossibleTriggers1`, possibleTriggers2,
    //                  triggerExp2,
    //                  `partiallyConsumedHeap1`,
    //                  `permissionScalingFactor1`,
    //                  `reserveHeaps1`, `reserveCfgs1`, `conservedPcs1`, `recordPcs1`, `exhaleExt1`,
    //                  `applyHeuristics1`, `heuristicsDepth1`, `triggerAction1`,
    //                  ssCache2, `hackIssue387DisablePermissionConsumption1`,
    //                  `qpFields1`, `qpPredicates1`, `qpMagicWands1`, smCache2, pmCache2, `smDomainNeeded1`,
    //                  `predicateSnapMap1`, `predicateFormalVarMap1`, `hack`,
    //                  `methodCallAstNode1`, `foldOrUnfoldAstNode1`, `loopPosition1`, `unfoldingAstNode1`,`forFraming`,
    //                  `generateChecks`, `needConditionFramingUnfold`,
    //                  `needConditionFramingProduce`, `madeOptimisticAssumptions`) =>

    //         val functionRecorder3 = functionRecorder1.merge(functionRecorder2)
    //         val triggerExp3 = triggerExp1 && triggerExp2
    //         val possibleTriggers3 = possibleTriggers1 ++ possibleTriggers2
    //         val constrainableARPs3 = constrainableARPs1 ++ constrainableARPs2

    //         val smCache3 = smCache1.union(smCache2)
    //         val pmCache3 = pmCache1 ++ pmCache2

    //         val ssCache3 = ssCache1 ++ ssCache2

    //         s1.copy(functionRecorder = functionRecorder3,
    //                 possibleTriggers = possibleTriggers3,
    //                 triggerExp = triggerExp3,
    //                 constrainableARPs = constrainableARPs3,
    //                 ssCache = ssCache3,
    //                 smCache = smCache3,
    //                 pmCache = pmCache3)

    //       case _ =>
    //         sys.error("State merging failed: unexpected mismatch between symbolic states")
    //   }
    // }
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
