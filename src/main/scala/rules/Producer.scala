// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.debugger.DebugExp
import viper.silicon.Config.JoinMode

import scala.collection.mutable
import viper.silver.ast
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silver.verifier.PartialVerificationError
//<<<<<<< HEAD
import viper.silicon.interfaces.{Unreachable, VerificationResult}
import viper.silicon.interfaces.state.{ChunkIdentifer, NonQuantifiedChunk}
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.records.data.{CondExpRecord, ImpliesRecord, ProduceRecord}
/*=======
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.interfaces.state.{ChunkIdentifer, NonQuantifiedChunk}
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.records.data.{CondExpRecord, ProduceRecord}
>>>>>>> upstream/master*/
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.supporters.functions.NoopFunctionRecorder
import viper.silicon.utils.toSf
import viper.silicon.verifier.Verifier
import viper.silver.verifier.reasons.{NegativePermission, QPAssertionNotInjective}

trait ProductionRules extends SymbolicExecutionRules {

  /** Produce assertion `a` into state `s`.
    *
    * @param s The state to produce the assertion into.
    * @param sf The heap snapshot determining the values of the produced partial heap.
    * @param a The assertion to produce.
    * @param pve The error to report in case the production fails.
    * @param v The verifier to use.
    * @param Q The continuation to invoke if the production succeeded, with the state and
    *          the verifier resulting from the production as arguments.
    * @return The result of the continuation.
    */
  def produce(s: State,
              sf: (Sort, Verifier) => Term,
              a: ast.Exp,
              pve: PartialVerificationError,
              v: Verifier)
             (Q: (State, Verifier) => VerificationResult)
             : VerificationResult



  /** Subsequently produces assertions `as` into state `s`.
    *
    * `produces(s, sf, as, _ => pve, v)` should (not yet tested ...) be equivalent to
    * `produce(s, sf, BigAnd(as), pve, v)`, expect that the former allows a more-fine-grained
    * error messages.
    *
    * @param s The state to produce the assertions into.
    * @param sf The heap snapshots determining the values of the produced partial heaps.
    * @param as The assertions to produce.
    * @param pvef The error to report in case the production fails. Given assertions `as`, an error
    *             `pvef(as_i)` will be reported if producing assertion `as_i` fails.
    * @param v @see [[produce]]
    * @param Q @see [[produce]]
    * @return @see [[produce]]
    */
  def produces(s: State,
               sf: (Sort, Verifier) => Term,
               as: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Verifier) => VerificationResult)
              : VerificationResult
}

object producer extends ProductionRules {
  import brancher._
  import evaluator._

  /* Overview of and interaction between the different available produce-methods:
   *   - `produce` and `produces` are the entry methods and intended to be called by *clients*
   *     (e.g. from the executor), but *not* by the implementation of the producer itself
   *     (e.g. recursively).
   *   - Produce methods suffixed with `tlc` (or `tlcs`) expect top-level conjuncts as assertions.
   *     The other produce methods therefore split the given assertion(s) into top-level
   *     conjuncts and forward these to `produceTlcs`.
   *   - `produceTlc` implements the actual symbolic execution rules for producing an assertion,
   *     and `produceTlcs` is basically `produceTlc` lifted to a sequence of assertions
   *     (a continuation-aware fold, if you will).
   *   - Certain operations such as logging need to be performed per produced top-level conjunct.
   *     This is implemented by `wrappedProduceTlc`: a wrapper around (or decorator for)
   *     `produceTlc` that performs additional operations before/after invoking `produceTlc`.
   *     `produceTlcs` therefore repeatedly invokes `wrappedProduceTlc` (and not `produceTlc`
   *     directly)
   *   - `produceR` is intended for recursive calls: it takes an assertion, splits it into
   *     top-level conjuncts and uses `produceTlcs` to produce each of them (hence, each assertion
   *     to produce passes `wrappedProduceTlc` before finally reaching `produceTlc`).
   *   - Note that the splitting into top-level conjuncts performed by `produceR` is not redundant,
   *     although the entry methods such as `produce` split assertions as well: if a client needs
   *     to produce `a1 && (b ==> a2 && a3) && a4`, then the entry method will split the assertion
   *     into the sequence `[a1, b ==> a2 && a3, a4]`, and the recursively produced assertion
   *     `a2 && a3` (after having branched over `b`) needs to be split again.
   */

  /** @inheritdoc */
  def produce(s: State,
              sf: (Sort, Verifier) => Term,
              a: ast.Exp,
              pve: PartialVerificationError,
              v: Verifier)
             (Q: (State, Verifier) => VerificationResult)
             : VerificationResult =

    produceR(s, sf, a.whenInhaling, pve, v)(Q)

  /** @inheritdoc */
  def produces(s: State,
               sf: (Sort, Verifier) => Term,
               as: Seq[ast.Exp],
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Verifier) => VerificationResult)
              : VerificationResult = {

    val allTlcs = mutable.ListBuffer[ast.Exp]()
    val allPves = mutable.ListBuffer[PartialVerificationError]()

    as.foreach(a => {
      val tlcs = a.whenInhaling.topLevelConjuncts
      val pves = Seq.fill(tlcs.length)(pvef(a))

      allTlcs ++= tlcs
      allPves ++= pves
    })

    produceTlcs(s, sf, allTlcs.result(), allPves.result(), v)(Q)
  }

  private def produceTlcs(s: State,
                          sf: (Sort, Verifier) => Term,
                          as: Seq[ast.Exp],
                          pves: Seq[PartialVerificationError],
                          v: Verifier)
                         (Q: (State, Verifier) => VerificationResult)
                         : VerificationResult = {

    // TODO: unset the method call ast node field here!
    // TODO: check the other places where we do something like this...
    
    if (as.isEmpty)
      Q(s, v)
    else {
      val a = as.head.whenInhaling
      val pve = pves.head

      if (as.tail.isEmpty)
        wrappedProduceTlc(s, sf, a, pve, v)(Q)
      else {
        try {
          val (sf0, sf1) =
            v.snapshotSupporter.createSnapshotPair(s, sf, a, viper.silicon.utils.ast.BigAnd(as.tail), v)
          /* TODO: Refactor createSnapshotPair s.t. it can be used with Seq[Exp],
           *       then remove use of BigAnd; for one it is not efficient since
           *       the tail of the (decreasing list parameter as) is BigAnd-ed
           *       over and over again.
           */

          wrappedProduceTlc(s, sf0, a, pve, v)((s1, v1) =>
            produceTlcs(s1, sf1, as.tail, pves.tail, v1)(Q))
        } catch {
          // We will get an IllegalArgumentException from createSnapshotPair if sf(...) returns Unit.
          // This should never happen if we're in a reachable state, so here we check for that
          // (without timeout, since there is no fallback) and stop verifying the current branch.
          case _: IllegalArgumentException if v.decider.check(False, Verifier.config.assertTimeout.getOrElse(0)) =>
            Unreachable()
        }

      }
    }
  }

  private def produceR(s: State,
                       sf: (Sort, Verifier) => Term,
                       a: ast.Exp,
                       pve: PartialVerificationError,
                       v: Verifier)
                      (Q: (State, Verifier) => VerificationResult)
                      : VerificationResult = {

    val tlcs = a.topLevelConjuncts
    val pves = Seq.fill(tlcs.length)(pve)
    
    produceTlcs(s, sf, tlcs, pves, v)(Q)
  }

  /** Wrapper/decorator for consume that injects the following operations:
    *   - Logging, see Executor.scala for an explanation
    */
  private def wrappedProduceTlc(s: State,
                                sf: (Sort, Verifier) => Term,
                                a: ast.Exp,
                                pve: PartialVerificationError,
                                v: Verifier)
                               (Q: (State, Verifier) => VerificationResult)
                               : VerificationResult = {

    val sepIdentifier = v.symbExLog.openScope(new ProduceRecord(a, s, v.decider.pcs))
    produceTlc(s, sf, a, pve, v)((s1, v1) => {
      v1.symbExLog.closeScope(sepIdentifier)
      Q(s1, v1)})
  }

  private def produceTlc(s: State,
                         sf: (Sort, Verifier) => Term,
                         a: ast.Exp,
                         pve: PartialVerificationError,
                         v: Verifier)
                        (continuation: (State, Verifier) => VerificationResult)
                        : VerificationResult = {

    v.logger.debug(s"\nPRODUCE ${viper.silicon.utils.ast.sourceLineColumn(a)}: $a")
    v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))

    val Q: (State, Verifier) => VerificationResult = (state, verifier) =>
      continuation(if (state.exhaleExt) state.copy(reserveHeaps = state.h +: state.reserveHeaps.drop(1)) else state, verifier)

    val produced = a match {

      // TODO: figure out how imprecise deals with snapshots - J
      case impr @ ast.ImpreciseExp(e) =>
      //  val (sf0, sf1) = v.snapshotSupporter.createSnapshotPair(s, sf, a, a, v)
        val second = toSf(Second(sf(sorts.Snap, v)))
        produce(s.copy(isImprecise = true), second, e, pve, v)(Q)

/*      case imp @ ast.Implies(e0, a0) if !a.isPure =>
        val impLog = new GlobalBranchRecord(imp, s, v.decider.pcs, "produce")
        val sepIdentifier = SymbExLogger.currentLog().insert(impLog)
        SymbExLogger.currentLog().initializeBranching()

        eval(s, e0, pve, v)((s1, t0, v1) => {
          impLog.finish_cond()
          val branch_res =
            branch(s1, t0, v1)(
              (s2, v2) => produceR(s2, sf, a0, pve, v2)((s3, v3) => {
                val res1 = Q(s3, v3)
                impLog.finish_thnSubs()
                SymbExLogger.currentLog().prepareOtherBranch(impLog)
                res1}),
              (s2, v2) => {
                v2.decider.assume(sf(sorts.Snap, v2) === Unit)
                  * TODO: Avoid creating a fresh var (by invoking) `sf` that is not used
                   * otherwise. In order words, only make this assumption if `sf` has
                   * already been used, e.g. in a snapshot equality such as `s == (s1, s2)`.
                   *
                val res2 = Q(s2, v2)
                impLog.finish_elsSubs()
                res2})
          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})
*/
      // this would be invoked on a postcondition? after the precondition is
      // consumed and evaluated maybe
      
      // use and unset the method call ast node attached to the state for
      // postconditions here
      //
      // IMPORTANT: that field must be unset before 
      case ite @ ast.CondExp(e0, a1, a2) =>
        val condExpRecord = new CondExpRecord(ite, s, v.decider.pcs, "produce")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)

        val s_1 = s.copy(generateChecks = false, needConditionFramingProduce = true)
//<<<<<<< HEAD
        evalpc(s_1, e0, pve, v, false)((s1, t0, e0New, v1) => {
          val s1_1 = s.copy(generateChecks = true, needConditionFramingProduce = false, evalHeapsSet = s1.evalHeapsSet, oldHeaps = s1.oldHeaps)
/*=======
        evalpc(s_1, e0, pve, v, false)((s1, t0, v1) => {
          val s1_1 = s.copy(generateChecks = true, needConditionFramingProduce = false, evalHeapsSet = s1.evalHeapsSet, oldHeaps = s1.oldHeaps) // updating evalHeapsSet and oldHeaps for getting heap information in unfolding case
          // updating evalHeapsSet, oldHeaps is necessary to translate the branch condition when e0 is an unfolding expression
>>>>>>> upstream/master*/

            // val branchPositionAstNode = s.methodCallAstNode match {
            //   case None => {
            //     println("We could not find a method call ast node! Why? Try to look into it...")
            //     ite
            //   }
            //   case Some(methodCallAstNode) => methodCallAstNode
            // }
            
            val branchPosition: Option[CheckPosition] =
              (s1_1.methodCallAstNode, s1_1.foldOrUnfoldAstNode, s1_1.loopPosition, s1_1.unfoldingAstNode) match {
                case (None, None, None, None) => None
                case (Some(methodCallAstNode), None, None, _) =>
                  Some(CheckPosition.GenericNode(methodCallAstNode))
                case (None, Some(foldOrUnfoldAstNode), None, _) =>
                  Some(CheckPosition.GenericNode(foldOrUnfoldAstNode))
                case (None, None, Some(loopPosition), _) =>
                  Some(loopPosition)
                case (None, None, None, Some(unfoldingAstNode)) =>
                  Some(CheckPosition.GenericNode(unfoldingAstNode))
                case _ =>
                  println((s1_1.methodCallAstNode, s1_1.foldOrUnfoldAstNode, s1_1.loopPosition, s1_1.unfoldingAstNode))
                  sys.error("Error: _ match case when setting a branch condition origin!")
              }

//<<<<<<< HEAD
            branch(s1_1, t0, (e0, e0New), branchPosition, v1)(
              (s2, v2) => {
                val s2a = s2.copy(evalHeapsSet = s_1.evalHeapsSet, oldHeaps = s_1.oldHeaps) // reverting evalHeapsSet and oldHeaps that was updated for getting Heap information in unfolding case
                produceR(s2a, sf, a1, pve, v2)((s3, v3) => {
                v3.symbExLog.closeScope(uidCondExp)
                Q(s3, v3)
              })},
              (s2, v2) => {
                val s2a = s2.copy(evalHeapsSet = s_1.evalHeapsSet, oldHeaps = s_1.oldHeaps) // reverting evalHeapsSet and oldHeaps that was updated for getting Heap information in unfolding case
                produceR(s2, sf, a2, pve, v2)((s3, v3) => {
                v3.symbExLog.closeScope(uidCondExp)
/*=======
            branch(s1_1, t0, e0, branchPosition, v1)((s2, v2) => {
                val s2a = s2.copy(evalHeapsSet = s_1.evalHeapsSet, oldHeaps = s_1.oldHeaps) // reverting evalHeapsSet and oldHeaps that was updated for getting Heap information in unfolding case
                produceR(s2a, sf, a1, pve, v2)((s3, v3) => {
                SymbExLogger.currentLog().closeScope(uidCondExp)
                Q(s3, v3)
              })},
              (s2, v2) => {
                val s2a = s2.copy(evalHeapsSet = s_1.evalHeapsSet, oldHeaps = s_1.oldHeaps) // reverting evalHeapsSet and oldHeaps that was updated for getting Heap information in unfolding case
                produceR(s2a, sf, a2, pve, v2)((s3, v3) => {
                SymbExLogger.currentLog().closeScope(uidCondExp)
>>>>>>> upstream/master*/
                Q(s3, v3)
              })})
        })

/*      case let: ast.Let if !let.isPure =>
 *      letSupporter.handle[ast.Exp](s, let, pve, v)((s1, g1, body, v1) =>
 *        produceR(s1.copy(g = s1.g + g1), sf, body, pve, v1)(Q))
 */
//<<<<<<< HEAD
      case accPred@ast.FieldAccessPredicate(ast.FieldAccess(eRcvr, field), _) =>
/*=======
      case loc @ ast.FieldAccessPredicate(locacc @ ast.FieldAccess(eRcvr, field), perm) =>
>>>>>>> upstream/master*/
        val s0 = s.copy(generateChecks = false)
        val perm = accPred.perm
        evalpc(s0, eRcvr, pve, v, false)((s1, tRcvr, eRcvrNew, v1) =>
          evalpc(s1, perm, pve, v1, false)((s2, tPerm, ePermNew, v2) => {
            val s2_0 = s2.copy(generateChecks = true)
//<<<<<<< HEAD
            if(chunkSupporter.inHeap(s2_0, s2_0.h, s2_0.h.values, field, Seq(tRcvr), v2)) {
              // NEED: Actually because it's in the heap, but don't know how to do that yet
              createFailure(pve dueTo NegativePermission(perm), v2, s2_0, "") }
/*=======
            if(chunkSupporter.inHeap(s2_0.h, s2_0.h.values, field, Seq(tRcvr), v2) && !v2.decider.checkSmoke()) {
              createFailure(pve dueTo LocInHeap(locacc), v2, s2_0) 
            }
>>>>>>> upstream/master*/
            else {
              val snap = sf(v2.symbolConverter.toSort(field.typ), v2)
              val gain = PermTimes(tPerm, s2_0.permissionScalingFactor)
              val (debugHeapName, debugLabel) = v2.getDebugOldLabel(s2_0, accPred.pos)
              val snapExp = Option.when(withExp)(ast.DebugLabelledOld(ast.FieldAccess(eRcvrNew.get, field)(), debugLabel)(accPred.pos, accPred.info, accPred.errT))
              val gainExp = ePermNew.map(p => ast.PermMul(p, s2_0.permissionScalingFactorExp.get)(p.pos, p.info, p.errT))
/*            if (s2.qpFields.contains(field)) {
 *            val trigger = (sm: Term) => FieldTrigger(field.name, sm, tRcvr)
 *            quantifiedChunkSupporter.produceSingleLocation(s2, field, Seq(`?r`), Seq(tRcvr), snap, gain, trigger, v2)(Q)
 *          } else {
 */
              val ch = BasicChunk(FieldID, BasicChunkIdentifier(field.name), Seq(tRcvr), Option.when(withExp)(Seq(eRcvrNew.get)), snap, snapExp, gain, gainExp)
              chunkSupporter.produce(s2_0, s2_0.h, ch, v2)((s3, h3, v3) => {
                v3.decider.assume(tRcvr !== Null, None)
                Q(s3.copy(h = h3), v3)})
            }
        }))

      case accPred @ ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), perm) =>
        val predicate = s.program.findPredicate(predicateName)
        val s0 = s.copy(generateChecks = false)
        val perm = accPred.perm
        evalspc(s0, eArgs, _ => pve, v, false)((s1, tArgs, eArgsNew, v1) =>
          evalpc(s1, perm, pve, v1, false)((s2, tPerm, ePermNew, v2) => {
            val s2_0 = s2.copy(generateChecks = true)
//<<<<<<< HEAD
            if (chunkSupporter.inHeap(s2_0, s2_0.h, s2_0.h.values, predicate, tArgs, v2)) {
              // Actually because it's in the heap, but don't know how to do that yet
              createFailure(pve dueTo NegativePermission(perm), v2, s2_0, "") }
            else {
              val snap = sf(
                predicate.body.map(v2.snapshotSupporter.optimalSnapshotSort(_, s2_0.program)._1)
                            .getOrElse(sorts.Snap), v2)
              val gain = PermTimes(tPerm, s2_0.permissionScalingFactor)
              val gainExp = ePermNew.map(p => ast.PermMul(p, s2_0.permissionScalingFactorExp.get)(p.pos, p.info, p.errT))
/*=======
            val snap = sf(
              predicate.body.map(v2.snapshotSupporter.optimalSnapshotSort(_, Verifier.program)._1)
                          .getOrElse(sorts.Snap), v2)
            val gain = PermTimes(tPerm, s2_0.permissionScalingFactor)
>>>>>>> upstream/master*/
/*            if (s2.qpPredicates.contains(predicate)) {
            val formalArgs = s2.predicateFormalVarMap(predicate)
            val trigger = (sm: Term) => PredicateTrigger(predicate.name, sm, tArgs)
            quantifiedChunkSupporter.produceSingleLocation(
              s2, predicate, formalArgs, tArgs, snap, gain, trigger, v2)(Q)
          } else {
*/
//<<<<<<< HEAD
              val snap1 = snap.convert(sorts.Snap)
              val ch = BasicChunk(PredicateID, BasicChunkIdentifier(predicate.name), tArgs, eArgsNew, snap1, None, gain, gainExp)
              chunkSupporter.produce(s2_0, s2_0.h, ch, v2)((s3, h3, v3) => {
                /* if (Verifier.config.enablePredicateTriggersOnInhale() && s3.functionRecorder == NoopFunctionRecorder) {
                  v3.decider.assume(App(Verifier.predicateData(predicate).triggerFunction, snap1 +: tArgs))
                } */
                Q(s3.copy(h = h3), v3)})
            }}))
/*=======
            val snap1 = snap.convert(sorts.Snap)
            val ch = BasicChunk(PredicateID, BasicChunkIdentifier(predicate.name), tArgs, snap1, gain)
            chunkSupporter.produce(s2_0, s2_0.h, ch, v2)((s3, h3, v3) => {
              *//* if (Verifier.config.enablePredicateTriggersOnInhale() && s3.functionRecorder == NoopFunctionRecorder) {
                v3.decider.assume(App(Verifier.predicateData(predicate).triggerFunction, snap1 +: tArgs))
              } *//*
              Q(s3.copy(h = h3), v3)})
          }))
>>>>>>> upstream/master*/

/*
      case wand: ast.MagicWand if s.qpMagicWands.contains(MagicWandIdentifier(wand, Verifier.program)) =>
        val bodyVars = wand.subexpressionsToEvaluate(Verifier.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ)))
        evals(s, bodyVars, _ => pve, v)((s1, args, v1) => {
          val (sm, smValueDef) =
            quantifiedChunkSupporter.singletonSnapshotMap(s1, wand, args, sf(v1.snapshotSupporter.optimalSnapshotSort(wand, s1, v1), v1), v1)
          v1.decider.prover.comment("Definitional axioms for singleton-SM's value")
          val definitionalAxiomMark = v1.decider.setPathConditionMark()
          val debugExp = Option.when(withExp)(DebugExp.createInstance("Definitional axioms for singleton-SM's value", true))
          v1.decider.assumeDefinition(smValueDef, debugExp)
          val conservedPcs =
            if (s1.recordPcs) (s1.conservedPcs.head :+ v1.decider.pcs.after(definitionalAxiomMark)) +: s1.conservedPcs.tail
            else s1.conservedPcs
          val ch =
            quantifiedChunkSupporter.createSingletonQuantifiedChunk(formalVars, formalVarExps, wand, args, bodyVarsNew,
              FullPerm, Option.when(withExp)(ast.FullPerm()(wand.pos, wand.info, wand.errT)), sm, s.program)
          val h2 = s1.h + ch
          val smCache1 = if (s1.heapDependentTriggers.contains(MagicWandIdentifier(wand, s1.program))){
            val (relevantChunks, _) =
              quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](h2, ch.id)
            val (smDef1, smCache1) =
              quantifiedChunkSupporter.summarisingSnapshotMap(
                s1, wand, formalVars, relevantChunks, v1)
            val argsStr = bodyVarsNew.mkString(", ")
            val debugExp = Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${ch.id.toString}($argsStr))", isInternal_ = true))
            v1.decider.assume(PredicateTrigger(ch.id.toString, smDef1.sm, args), debugExp)
            smCache1
          } else {
            s1.smCache
          }
          val smDef = SnapshotMapDefinition(wand, sm, Seq(smValueDef), Seq())
          val s2 =
            s1.copy(h = h2,
                    functionRecorder = s1.functionRecorder.recordFvfAndDomain(smDef),
                    smCache = smCache1,
                    conservedPcs = conservedPcs)
          Q(s2, v1)})

      case wand: ast.MagicWand =>
        val snap = sf(v.snapshotSupporter.optimalSnapshotSort(wand, s, v), v)
        magicWandSupporter.createChunk(s, wand, MagicWandSnapshot(snap), pve, v)((s1, chWand, v1) =>
          chunkSupporter.produce(s1, s1.h, chWand, v1)((s2, h2, v2) =>
            Q(s2.copy(h = h2), v2)))

       * TODO: Initial handling of QPs is identical/very similar in consumer
       *       and producer. Try to unify the code.
       *
      case QuantifiedPermissionAssertion(forall, cond, acc: ast.FieldAccessPredicate) =>
        val qid = acc.loc.field.name
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), Seq(acc.loc.rcv, acc.perm), optTrigger, qid, pve, v) {
          case (s1, qvars, qvarExps, Seq(tCond), eCondNew, Some((Seq(tRcvr, tPerm), rcvrPerm, tTriggers, (auxGlobals, auxNonGlobals), auxExps)), v1) =>
            val tSnap = sf(sorts.FieldValueFunction(v1.snapshotSupporter.optimalSnapshotSort(acc.loc.field, s1, v1), acc.loc.field.name), v1)
            val s1a = s1.copy(constrainableARPs = s.constrainableARPs)
            quantifiedChunkSupporter.produce(
              s1a,
              forall,
              acc.loc.field,
              qvars, qvarExps, Seq(`?r`),
              Option.when(withExp)(Seq(ast.LocalVarDecl(`?r`.id.name, ast.Ref)())),
              qid, optTrigger,
              tTriggers,
              auxGlobals,
              auxNonGlobals,
              auxExps.map(_._1),
              auxExps.map(_._2),
              tCond,
              eCondNew.map(_.head),
              Seq(tRcvr),
              rcvrPerm.map(rp => Seq(rp.head)),
              tSnap,
              tPerm,
              rcvrPerm.map(_(1)),
              pve,
              NegativePermission(acc.perm),
              QPAssertionNotInjective(acc.loc),
              v1
            )(Q)
          case (s1, _, _, _, _, None, v1) => Q(s1.copy(constrainableARPs = s.constrainableARPs), v1)
        }

      case QuantifiedPermissionAssertion(forall, cond, acc: ast.PredicateAccessPredicate) =>
        val predicate = s.program.findPredicate(acc.loc.predicateName)
        val formalVars = s.predicateFormalVarMap(predicate)
        val formalVarExps = predicate.formalArgs
        val qid = acc.loc.predicateName
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), acc.perm +: acc.loc.args, optTrigger, qid, pve, v) {
          case (s1, qvars, qvarExps, Seq(tCond), eCondNew, Some((Seq(tPerm, tArgs @ _*), permArgs, tTriggers, (auxGlobals, auxNonGlobals), auxExps)), v1) =>
            val tSnap = sf(sorts.PredicateSnapFunction(s1.predicateSnapMap(predicate), predicate.name), v1)
            val s1a = s1.copy(constrainableARPs = s.constrainableARPs)
            quantifiedChunkSupporter.produce(
              s1a,
              forall,
              predicate,
              qvars,
              qvarExps,
              formalVars,
              Option.when(withExp)(formalVarExps),
              qid,
              optTrigger,
              tTriggers,
              auxGlobals,
              auxNonGlobals,
              auxExps.map(_._1),
              auxExps.map(_._2),
              tCond,
              eCondNew.map(_.head),
              tArgs,
              permArgs.map(_.tail),
              tSnap,
              tPerm,
              permArgs.map(_.head),
              pve,
              NegativePermission(acc.perm),
              QPAssertionNotInjective(acc.loc),
              v1
            )(Q)
          case (s1, _, _, _, _, None, v1) => Q(s1.copy(constrainableARPs = s.constrainableARPs), v1)
        }

      case QuantifiedPermissionAssertion(forall, cond, wand: ast.MagicWand) =>
        val bodyVars = wand.subexpressionsToEvaluate(s.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
        val formalVarExps = Option.when(withExp)(bodyVars.indices.toList.map(i => ast.LocalVarDecl(s"x$i", bodyVars(i).typ)()))
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        val qid = MagicWandIdentifier(wand, s.program).toString
        evalQuantified(s, Forall, forall.variables, Seq(cond), bodyVars, optTrigger, qid, pve, v) {
          case (s1, qvars, qvarExps, Seq(tCond), eCondNew, Some((tArgs, eArgsNew, tTriggers, (auxGlobals, auxNonGlobals), auxExps)), v1) =>
            val tSnap = sf(sorts.PredicateSnapFunction(sorts.Snap, qid), v1)
            quantifiedChunkSupporter.produce(
              s1,
              forall,
              wand,
              qvars,
              qvarExps,
              formalVars,
              formalVarExps,
              qid,
              optTrigger,
              tTriggers,
              auxGlobals,
              auxNonGlobals,
              auxExps.map(_._1),
              auxExps.map(_._2),
              tCond,
              eCondNew.map(_.head),
              tArgs,
              eArgsNew,
              tSnap,
              FullPerm,
              Option.when(withExp)(ast.FullPerm()()),
              pve,
              NegativePermission(ast.FullPerm()()),
              QPAssertionNotInjective(wand),
              v1
            )(Q)
          case (s1, _, _, _, _, None, v1) => Q(s1, v1)
        }
*/
/*      case _: ast.InhaleExhaleExp =>
 *      Failure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(a))
 */
      /* Any regular expressions, i.e. boolean and arithmetic. */
      case _ =>
        v.decider.assume(sf(sorts.Snap, v) === Unit,
          Option.when(withExp)(DebugExp.createInstance("Empty snapshot", true))) /* TODO: See comment for case ast.Implies above */
        val s0 = s.copy(generateChecks = false)
        evalpc(s0, a, pve, v, false)((s1, t, aNew, v1) => {
          val s2 = s1.copy(generateChecks = true)
          v1.decider.assume(t, Option.when(withExp)(a), aNew)
          Q(s2, v1)})
    }

    produced
  }
}
