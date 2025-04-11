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
import viper.silver.verifier.reasons._
//<<<<<<< HEAD
import viper.silicon.Stack
import viper.silicon.interfaces.{Failure, VerificationResult}
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.records.data.{CondExpRecord, ConsumeRecord, ImpliesRecord}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.supporters.Translator
import viper.silicon.utils.ast.BigAnd
/*=======
import viper.silicon.interfaces.VerificationResult
import viper.silicon.logger.records.data.{CondExpRecord, ConsumeRecord, ImpliesRecord}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.utils.ast.BigAnd
>>>>>>> upstream/master*/
import viper.silicon.verifier.Verifier
import viper.silicon.utils

trait ConsumptionRules extends SymbolicExecutionRules {

  /** Consume assertion `a` from state `s`.
    *
    * @param s The state to consume the assertion from.
    * @param a The assertion to consume.
    * @param returnSnap Whether a snapshot should be returned or not.
    * @param pve The error to report in case the consumption fails.
    * @param v The verifier to use.
    * @param Q The continuation to invoke if the consumption succeeded, with the following
    *          arguments: state (1st argument) and verifier (3rd argument) resulting from the
    *          consumption, and a heap snapshot (2bd argument )representing the values of the
    *          consumed partial heap.
    * @return The result of the continuation.
    */
  def consume(s: State, a: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
             (Q: (State, Option[Term], Verifier) => VerificationResult)
             : VerificationResult

  /** Subsequently consumes the assertions `as` (from head to tail), starting in state `s`.
    *
    * `consumes(s, as, _ => pve, v)` should (not yet tested ...) be equivalent to
    * `consume(s, BigAnd(as), pve, v)`, expect that the former allows a more-fine-grained
    * error messages.
    *
    * @param s The state to consume the assertions from.
    * @param as The assertions to consume.
    * @param returnSnap Whether a snapshot should be returned or not.
    * @param pvef The error to report in case a consumption fails. Given assertions `as`, an error
    *             `pvef(as_i)` will be reported if consuming assertion `as_i` fails.
    * @param v @see [[consume]]
    * @param Q @see [[consume]]
    * @return @see [[consume]]
    */
  def consumes(s: State,
               as: Seq[ast.Exp],
               returnSnap: Boolean,
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Option[Term], Verifier) => VerificationResult)
              : VerificationResult
}

object consumer extends ConsumptionRules {
  import brancher._
  import evaluator._

  /* See the comment in Producer.scala for an overview of the different produce methods: the
   * different consume methods provided by the consumer work and interact analogously.
   */

  /** @inheritdoc */
  def consume(s: State, a: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
             (Q: (State, Option[Term], Verifier) => VerificationResult)
             : VerificationResult = {

//<<<<<<< HEAD
    val consumed = a match {
      case impr @ ast.ImpreciseExp(e) =>
        consumeR(s, true, s.optimisticHeap, s.h, e.whenExhaling, returnSnap, pve, v)((s1, oh1, h1, snap, v1) => {
          val s2 = s1.copy(isImprecise = true, h = Heap(), optimisticHeap = Heap(),
                           partiallyConsumedHeap = s.partiallyConsumedHeap)
          Q(s2, Combine(Unit, snap), v1)})

      case _ =>
        consumeR(s, s.isImprecise, s.optimisticHeap, s.h, a.whenExhaling, returnSnap, pve, v)((s1, oh1, h1, snap, v1) => {
          val s2 = s1.copy(h = h1, optimisticHeap = oh1,
                           partiallyConsumedHeap = s.partiallyConsumedHeap)
          Q(s2, snap, v1)})
    }
    consumed
/*=======
    consumeR(s, s.h, a.whenExhaling, returnSnap, pve, v)((s1, h1, snap, v1) => {
      val s2 = s1.copy(h = h1,
                       partiallyConsumedHeap = s.partiallyConsumedHeap)
      Q(s2, snap, v1)})
>>>>>>> upstream/master*/
  }


  /** @inheritdoc */
  def consumes(s: State,
               as: Seq[ast.Exp],
               returnSnap: Boolean,
               pvef: ast.Exp => PartialVerificationError,
               v: Verifier)
              (Q: (State, Option[Term], Verifier) => VerificationResult)
              : VerificationResult = {

    val allTlcs = mutable.ListBuffer[ast.Exp]()
    val allPves = mutable.ListBuffer[PartialVerificationError]()

    var imprecise = false

  //  println("as: " + as)
    as.foreach(a => {
    //  println("a: " + a.whenExhaling.topLevelConjuncts)
      a match {
        // if a is an imprecise expression we add all the expressions
        // within it to our list ltcs's
        case impr @ ast.ImpreciseExp(e) =>
          imprecise = true
          val exps = e.whenExhaling.topLevelConjuncts
          exps.foreach(exp => {
      //      println("exp: " + exp)
            val tlcs = exp.whenExhaling.topLevelConjuncts
            val pves = Seq.fill(tlcs.length)(pvef(exp))

            allTlcs ++= tlcs
            allPves ++= pves

          })
        case _ =>
          val tlcs = a.whenExhaling.topLevelConjuncts
          val pves = Seq.fill(tlcs.length)(pvef(a))

          allTlcs ++= tlcs
          allPves ++= pves
      }
    })

//<<<<<<< HEAD
//    println("tlcs: " + allTlcs)
//    println("tlcs result: " + allTlcs.result())


    if(imprecise) {
      consumeTlcs(s, true, s.optimisticHeap, s.h, allTlcs.result(), allPves.result(), v)((s1, oh1, h1, snap1, v1) => {
        val s2 = s1.copy(h = Heap(),
                        optimisticHeap = Heap(),
                        partiallyConsumedHeap = s.partiallyConsumedHeap,
                        isImprecise = true)
        Q(s2, Combine(Unit, snap1), v1)
      })
    } else {
      consumeTlcs(s, s.isImprecise, s.optimisticHeap, s.h, allTlcs.result(), allPves.result(), v)((s1, oh1, h1, snap1, v1) => {
        val s2 = s1.copy(h = h1,
                        optimisticHeap = oh1,
                        partiallyConsumedHeap = s.partiallyConsumedHeap)
        Q(s2, snap1, v1)
      })
    }
  }
//=======
/*
    consumeTlcs(s, s.h, allTlcs.result(), returnSnap, allPves.result(), v)((s1, h1, snap1, v1) => {
>>>>>>> upstream/master
      val s2 = s1.copy(h = h1,
                       partiallyConsumedHeap = s.partiallyConsumedHeap)
      Q(s2, snap1, v1)
    })
  }
*/
  private def consumeTlcs(s: State,
                          impr: Boolean,
                          oh: Heap,
                          h: Heap,
                          tlcs: Seq[ast.Exp],
                          returnSnap: Boolean,
                          pves: Seq[PartialVerificationError],
                          v: Verifier)
//<<<<<<< HEAD
                         (Q: (State, Heap, Heap, Option[Term], Verifier) => VerificationResult)
                         : VerificationResult = {

    if (tlcs.isEmpty)
      Q(s, oh, h, if (returnSnap) Some(Unit) else None, v)
/*=======
                         (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                         : VerificationResult = {

    if (tlcs.isEmpty)
      Q(s, h, if (returnSnap) Some(Unit) else None, v)
>>>>>>> upstream/master*/
    else {
      val a = tlcs.head
      val pve = pves.head


      if (tlcs.tail.isEmpty)
//<<<<<<< HEAD
        wrappedConsumeTlc(s, impr, oh, h, a, returnSnap, pve, v)(Q)
      else
        wrappedConsumeTlc(s, impr, oh, h, a, returnSnap, pve, v)((s1, oh1, h1, snap1, v1) => {
          consumeTlcs(s1, impr, oh1, h1, tlcs.tail, returnSnap, pves.tail, v1)((s2, oh2, h2, snap2, v2) =>
            (snap1, snap2) match {
              case (Some(sn1), Some(sn2)) if returnSnap => Q(s2, oh2, h2, Some(Combine(sn1, sn2)), v2)
              case (None, None) if !returnSnap => Q(s2, oh2, h2, None, v2)
              case (_, _) =>  sys.error(s"Consume returned unexpected snapshot: ${(returnSnap, (snap1, snap2))}")
            })
        })
    }
  }

  private def consumeR(s: State, impr: Boolean, oh: Heap, h: Heap, a: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
                      (Q: (State, Heap, Heap, Term, Verifier) => VerificationResult)
/*=======
        wrappedConsumeTlc(s, h, a, returnSnap, pve, v)(Q)
      else
        wrappedConsumeTlc(s, h, a, returnSnap, pve, v)((s1, h1, snap1, v1) => {
          consumeTlcs(s1, h1, tlcs.tail, returnSnap, pves.tail, v1)((s2, h2, snap2, v2) =>

            (snap1, snap2) match {
              case (Some(sn1), Some(sn2)) if returnSnap => Q(s2, h2, Some(Combine(sn1, sn2)), v2)
              case (None, None) if !returnSnap => Q(s2, h2, None, v2)
              case (_, _) =>  sys.error(s"Consume returned unexpected snapshot: ${(returnSnap, (snap1, snap2))}")
            })
        })
    }
  }

  private def consumeR(s: State, h: Heap, a: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
                      (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
>>>>>>> upstream/master*/
                      : VerificationResult = {

    val tlcs = a.topLevelConjuncts
    val pves = Seq.fill(tlcs.length)(pve)

//<<<<<<< HEAD
    consumeTlcs(s, impr, oh, h, tlcs, returnSnap, pves, v)(Q)
/*=======
    consumeTlcs(s, h, tlcs, returnSnap, pves, v)(Q)
>>>>>>> upstream/master*/
  }

  /** Wrapper/decorator for consume that injects the following operations:
    *   - Logging, see Executor.scala for an explanation
    *   - Failure-driven state consolidation
    */
  protected def wrappedConsumeTlc(s: State,
                                  impr: Boolean,
                                  oh: Heap,
                                  h: Heap,
                                  a: ast.Exp,
                                  returnSnap: Boolean,
                                  pve: PartialVerificationError,
                                  v: Verifier)
//<<<<<<< HEAD
                                 (Q: (State, Heap, Heap, Option[Term], Verifier) => VerificationResult)
/*=======
                                 (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
>>>>>>> upstream/master*/
                                 : VerificationResult = {
// Do we need to do this stuff on oh? - Jacob
    /* tryOrFail effects the "main" heap s.h, so we temporarily set the consume-heap h to be the
     * main heap. Note that the main heap is used for evaluating expressions during an ongoing
     * consume.
     */
    val sInit = s.copy(h = h)
//<<<<<<< HEAD
    val s0 = stateConsolidator.consolidate(sInit, v)
    val h0 = s0.h /* h0 is h, but consolidated */
    val s1 = s0.copy(h = s.h)

    /* TODO: To remove this cast: Add a type argument to the ConsumeRecord.
     *       Globally the types match, but locally the type system does not know.
     */
    val sepIdentifier = v1.symbExLog.openScope(new ConsumeRecord(a, s1, v.decider.pcs))
    consumeTlc(s1, impr, oh, h0, a, returnSnap, pve, v)((s2, oh2, h2, snap2, v1) => {
      v2.symbExLog.closeScope(sepIdentifier)
      Q(s2, oh2, h2, snap2, v1)})
  }

  private def consumeTlc(s: State, impr: Boolean, oh: Heap, h: Heap, a: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
                        (Q: (State, Heap, Heap, Term, Verifier) => VerificationResult)
/*=======
    executionFlowController.tryOrFail2[Heap, Option[Term]](sInit, v)((s0, v1, QS) => {
      val h0 = s0.h *//* h0 is h, but potentially consolidated */
      //val s1 = s0.copy(h = s.h) /* s1 is s, but the retrying flag might be set */

      /*val sepIdentifier = v1.symbExLog.openScope(new ConsumeRecord(a, s1, v.decider.pcs))

      consumeTlc(s1, h0, a, returnSnap, pve, v1)((s2, h2, snap2, v2) => {
        v2.symbExLog.closeScope(sepIdentifier)
        QS(s2, h2, snap2, v2)})
    })(Q)
  }

  private def consumeTlc(s: State, h: Heap, a: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
                        (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
>>>>>>> upstream/master*/
                        : VerificationResult = {
    
    /* ATTENTION: Expressions such as `perm(...)` must be evaluated in-place,
     * i.e. in the partially consumed heap which is denoted by `h` here. The
     * evaluator evaluates such expressions in the heap
     * `context.partiallyConsumedHeap`. Hence, this field must be updated every
     * time permissions have been consumed.
     */

    v.logger.debug(s"\nCONSUME ${viper.silicon.utils.ast.sourceLineColumn(a)}: $a")
    v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
    v.logger.debug("h = " + v.stateFormatter.format(h))
    if (s.reserveHeaps.nonEmpty)
      v.logger.debug("hR = " + s.reserveHeaps.map(v.stateFormatter.format).mkString("", ",\n     ", ""))

    val consumed = a match {
//<<<<<<< HEAD

/*
      case imp @ ast.Implies(e0, a0) if !a.isPure =>
        val impLog = new GlobalBranchRecord(imp, s, v.decider.pcs, "consume")
        val sepIdentifier = SymbExLogger.currentLog().insert(impLog)
        SymbExLogger.currentLog().initializeBranching()

        evaluator.eval(s, e0, pve, v)((s1, t0, v1) => {
          impLog.finish_cond()
          val branch_res =
            branch(s1, t0, v1)(
              (s2, v2) => consumeR(s2, h, a0, pve, v2)((s3, h3, snap3, v3) => {
                val res1 = Q(s3, h3, snap3, v3)
                impLog.finish_thnSubs()
                SymbExLogger.currentLog().prepareOtherBranch(impLog)
                res1}),
              (s2, v2) => {
                val res2 = Q(s2, h, Unit, v2)
                impLog.finish_elsSubs()
                res2})
          SymbExLogger.currentLog().collapse(null, sepIdentifier)
          branch_res})
*/
      // this would be invoked on a precondition? after the method call site is
      // encountered i think
      
      // consume the method call ast node attached to the state for
      // preconditions here

      // IMPORTANT: entering this method should remove that ast node from the
      // state, that is, we should set it to None(?)
      //
      // set some local variable, sourceCall, so we can continue to access it?
      case ite @ ast.CondExp(e0, a1, a2) =>
/*=======
      case imp @ ast.Implies(e0, a0) if !a.isPure && s.moreJoins.id >= JoinMode.Impure.id =>
        val impliesRecord = new ImpliesRecord(imp, s, v.decider.pcs, "consume")
        val uidImplies = v.symbExLog.openScope(impliesRecord)
        consumeConditionalTlcMoreJoins(s, h, e0, a0, None, uidImplies, returnSnap, pve, v)(Q)

      case imp @ ast.Implies(e0, a0) if !a.isPure =>
        val impliesRecord = new ImpliesRecord(imp, s, v.decider.pcs, "consume")
        val uidImplies = v.symbExLog.openScope(impliesRecord)

        evaluator.eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          branch(s1, t0, (e0, e0New), v1)(
            (s2, v2) => consumeR(s2, h, a0, returnSnap, pve, v2)((s3, h1, t1, v3) => {
              v3.symbExLog.closeScope(uidImplies)
              Q(s3, h1, t1, v3)
            }),
            (s2, v2) => {
              v2.symbExLog.closeScope(uidImplies)
              Q(s2, h, if (returnSnap) Some(Unit) else None, v2)
            }))

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure && s.moreJoins.id >= JoinMode.Impure.id =>
        val condExpRecord = new CondExpRecord(ite, s, v.decider.pcs, "consume")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)
        consumeConditionalTlcMoreJoins(s, h, e0, a1, Some(a2), uidCondExp, returnSnap, pve, v)(Q)

      case ite @ ast.CondExp(e0, a1, a2) if !a.isPure =>
>>>>>>> upstream/master*/
        val condExpRecord = new CondExpRecord(ite, s, v.decider.pcs, "consume")
        val uidCondExp = v.symbExLog.openScope(condExpRecord)

//<<<<<<< HEAD
        evalpc(s.copy(isImprecise = impr), e0, pve, v)((s1, t0, v1) => {
          val s2 = s1.copy(isImprecise = s.isImprecise)
      
            // what was happening here...?
            // we were unsetting the position in the state at the beginning of
            // consumeTlc, but we were not able to attach it to the branching info
            //
            // we weren't seeing it at this point, where we were matching on it to see if
            // it was None
            //
            // this has been changed since that point, but we should figure out what the
            // issue was... it is commit with the message "Buggy changes to track branch positions
            // for method call sites"
            val branchPosition: Option[CheckPosition] =
              (s.methodCallAstNode, s.foldOrUnfoldAstNode, s.loopPosition) match {
                case (None, None, None) => None
                case (Some(methodCallAstNode), None, None) => Some(CheckPosition.GenericNode(methodCallAstNode))
                case (None, Some(foldOrUnfoldAstNode), None) => Some(CheckPosition.GenericNode(foldOrUnfoldAstNode))
                case (None, None, Some(_)) => s.loopPosition
                case _ => {
                  sys.error("This should not happen, at least until we support "
                    + "unfoldings, maybe! We don't deal with this case at the "
                    + "moment because we want to know if this happens!")
                }
              }

            branch(s2, t0, e0, branchPosition, v1)(
              // the things in the branch (the then and else contents) may reach
              // the final case of consumeTlc, where we unset the method
              // callsite ast node
              //
              // that's why it worked before...? the way we do it now is
              // better, maybe
              (s3, v2) => consumeR(s3, impr, oh, h, a1, pve, v2)((s4, oh3, h3, t1, v3) => {
                v3.symbExLog.closeScope(uidCondExp)
                Q(s4, oh3, h3, t1, v3)
              }),
              (s3, v2) => consumeR(s3, impr, oh, h, a2, pve, v2)((s4, oh3, h3, t1, v3) => {
                v3.symbExLog.closeScope(uidCondExp)
                Q(s4, oh3, h3, t1, v3)
              }))
        })
/*=======
        eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
          branch(s1, t0, (e0, e0New), v1)(
            (s2, v2) => consumeR(s2, h, a1, returnSnap, pve, v2)((s3, h1, t1, v3) => {
              v3.symbExLog.closeScope(uidCondExp)
              Q(s3, h1, t1, v3)
            }),
            (s2, v2) => consumeR(s2, h, a2, returnSnap, pve, v2)((s3, h1, t1, v3) => {
              v3.symbExLog.closeScope(uidCondExp)
              Q(s3, h1, t1, v3)
            })))
>>>>>>> upstream/master*/

      /* TODO: Initial handling of QPs is identical/very similar in consumer
       *       and producer. Try to unify the code.
       */

/*
      case QuantifiedPermissionAssertion(forall, cond, acc: ast.FieldAccessPredicate) =>
        val field = acc.loc.field
        val qid = BasicChunkIdentifier(acc.loc.field.name)
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)

        evalQuantified(s, Forall, forall.variables, Seq(cond), Seq(acc.perm, acc.loc.rcv), optTrigger, qid.name, pve, v) {
          case (s1, qvars, qvarExps, Seq(tCond), condNew, Some((Seq(tPerm, tRcvr), permRcvrOpt, tTriggers, (auxGlobals, auxNonGlobals), auxExps)), v1) =>
            quantifiedChunkSupporter.consume(
              s = s1,
              h = h,
              resource = field,
              qvars = qvars,
              qvarExps = qvarExps,
              formalQVars = Seq(`?r`),
              formalQVarsExp = Option.when(withExp)(Seq(ast.LocalVarDecl(`?r`.id.name, ast.Ref)())),
              qid = qid.name,
              optTrigger = optTrigger,
              tTriggers = tTriggers,
              auxGlobals = auxGlobals,
              auxNonGlobals = auxNonGlobals,
              auxGlobalsExp = auxExps.map(_._1),
              auxNonGlobalsExp = auxExps.map(_._2),
              tCond = tCond,
              eCond = condNew.map(_.head),
              tArgs = Seq(tRcvr),
              eArgs = permRcvrOpt.map(permRcvr => Seq(permRcvr(1))),
              tPerm = tPerm,
              ePerm = permRcvrOpt.map(_(0)),
              returnSnap = returnSnap,
              pve = pve,
              negativePermissionReason = NegativePermission(acc.perm),
              notInjectiveReason = QPAssertionNotInjective(acc.loc),
              insufficientPermissionReason = InsufficientPermission(acc.loc),
              v1)((s2, h2, snap, v2) => Q(s2.copy(constrainableARPs = s.constrainableARPs), h2, snap, v2))
          case (s1, _, _, _, _, None, v1) => Q(s1, h, if (returnSnap) Some(Unit) else None, v1)
        }

      case QuantifiedPermissionAssertion(forall, cond, acc: ast.PredicateAccessPredicate) =>
<<<<<<< HEAD
        val predicate = Verifier.program.findPredicate(acc.loc.predicateName)
         * TODO: Quantified codomain variables are used in axioms and chunks (analogous to `?r`)
=======
        val predicate = s.program.findPredicate(acc.loc.predicateName)
        /* TODO: Quantified codomain variables are used in axioms and chunks (analogous to `?r`)
>>>>>>> upstream/master
         *       and need to be instantiated in several places. Hence, they need to be known,
         *       which is more complicated if fresh identifiers are used.
         *       At least two options:
         *         1. Choose fresh identifiers each time; remember/restore, e.g. by storing these variables in chunks
         *         2. Choose fresh identifiers once; store in and take from state (or from object Verifier)
         *
        val formalVars = s.predicateFormalVarMap(predicate)
        val qid = BasicChunkIdentifier(acc.loc.predicateName)
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        evalQuantified(s, Forall, forall.variables, Seq(cond), acc.perm +: acc.loc.args, optTrigger, qid.name, pve, v) {
          case (s1, qvars, qvarExps, Seq(tCond), condNew, Some((Seq(tPerm, tArgs @ _*), permArgsNew, tTriggers, (auxGlobals, auxNonGlobals), auxExps)), v1) =>
            quantifiedChunkSupporter.consume(
              s = s1,
              h = h,
              resource = predicate,
              qvars = qvars,
              qvarExps = qvarExps,
              formalQVars = formalVars,
              formalQVarsExp = Option.when(withExp)(predicate.formalArgs),
              qid = qid.name,
              optTrigger = optTrigger,
              tTriggers = tTriggers,
              auxGlobals = auxGlobals,
              auxNonGlobals = auxNonGlobals,
              auxGlobalsExp = auxExps.map(_._1),
              auxNonGlobalsExp = auxExps.map(_._2),
              tCond = tCond,
              eCond = condNew.map(_.head),
              tArgs = tArgs,
              eArgs = permArgsNew.map(_.tail),
              tPerm = tPerm,
              ePerm = permArgsNew.map(_.head),
              returnSnap = returnSnap,
              pve = pve,
              negativePermissionReason = NegativePermission(acc.perm),
              notInjectiveReason = QPAssertionNotInjective(acc.loc),
              insufficientPermissionReason = InsufficientPermission(acc.loc),
              v1)((s2, h2, snap, v2) => Q(s2.copy(constrainableARPs = s.constrainableARPs), h2, snap, v2))
          case (s1, _, _, _, _, None, v1) => Q(s1, h, if (returnSnap) Some(Unit) else None, v1)
        }

      case QuantifiedPermissionAssertion(forall, cond, wand: ast.MagicWand) =>
        val bodyVars = wand.subexpressionsToEvaluate(s.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
        val formalVarExps = Option.when(withExp)(bodyVars.indices.toList.map(i => ast.LocalVarDecl(s"x$i", bodyVars(i).typ)()))
        val qid = MagicWandIdentifier(wand, s.program).toString
        val optTrigger =
          if (forall.triggers.isEmpty) None
          else Some(forall.triggers)
        val ePerm = ast.FullPerm()()
        val tPerm = FullPerm
        evalQuantified(s, Forall, forall.variables, Seq(cond), bodyVars, optTrigger, qid, pve, v) {
          case (s1, qvars, qvarExps, Seq(tCond), condNew, Some((tArgs, bodyVarsNew, tTriggers, (auxGlobals, auxNonGlobals), auxExps)), v1) =>
            quantifiedChunkSupporter.consume(
              s = s1,
              h = h,
              resource = wand,
              qvars = qvars,
              qvarExps = qvarExps,
              formalQVars = formalVars,
              formalQVarsExp = formalVarExps,
              qid = qid,
              optTrigger = optTrigger,
              tTriggers = tTriggers,
              auxGlobals = auxGlobals,
              auxNonGlobals = auxNonGlobals,
              auxGlobalsExp = auxExps.map(_._1),
              auxNonGlobalsExp = auxExps.map(_._2),
              tCond = tCond,
              eCond = condNew.map(_.head),
              tArgs = tArgs,
              eArgs = bodyVarsNew,
              tPerm = tPerm,
              ePerm = Option.when(withExp)(ePerm),
              returnSnap = returnSnap,
              pve = pve,
              negativePermissionReason = NegativePermission(ePerm),
              notInjectiveReason = sys.error("Quantified wand not injective"), /*ReceiverNotInjective(...)*/
              //insufficientPermissionReason = MagicWandChunkNotFound(wand), /*InsufficientPermission(...)*/
              /*v1)((s2, h2, snap, v2) => Q(s2.copy(constrainableARPs = s.constrainableARPs), h2, snap, v2))
          case (s1, _, _, _, _, None, v1) => Q(s1.copy(constrainableARPs = s.constrainableARPs), h, if (returnSnap) Some(Unit) else None, v1)
        }
<<<<<<< HEAD
*/
/*
      case ast.AccessPredicate(loc @ ast.FieldAccess(eRcvr, field), ePerm)
=======

      case accPred@ast.AccessPredicate(loc @ ast.FieldAccess(eRcvr, field), ePerm)
>>>>>>> upstream/master
              if s.qpFields.contains(field) =>

        eval(s, eRcvr, pve, v)((s1, tRcvr, eRcvrNew, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, ePermNew, v2) => {
            val s2p = if (s2.heapDependentTriggers.contains(field)){
              val (relevantChunks, _) =
                quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s2.h, BasicChunkIdentifier(field.name))
              val (smDef1, smCache1) =
                quantifiedChunkSupporter.summarisingSnapshotMap(
                  s2, field, Seq(`?r`), relevantChunks, v2)
              val debugExp = Option.when(withExp)(DebugExp.createInstance(s"Field Trigger: ${eRcvrNew.get.toString}.${field.name}"))
              v2.decider.assume(FieldTrigger(field.name, smDef1.sm, tRcvr), debugExp)
              //            v2.decider.assume(PermAtMost(tPerm, FullPerm()))
              s2.copy(smCache = smCache1)
            } else {
              s2
            }
            val loss = if (!Verifier.config.unsafeWildcardOptimization() || s2.permLocations.contains(field))
              PermTimes(tPerm, s2.permissionScalingFactor)
            else
              WildcardSimplifyingPermTimes(tPerm, s2.permissionScalingFactor)
            val lossExp = ePermNew.map(p => ast.PermMul(p, s2.permissionScalingFactorExp.get)(ePerm.pos, ePerm.info, ePerm.errT))
            quantifiedChunkSupporter.consumeSingleLocation(
              s2p,
              h,
              Seq(`?r`),
              Option.when(withExp)(Seq(ast.LocalVarDecl("r", ast.Ref)(accPred.pos, accPred.info, accPred.errT))),
              Seq(tRcvr),
              eRcvrNew.map(Seq(_)),
              loc,
              loss,
              lossExp,
              returnSnap,
              None,
              pve,
              v2
            )((s3, h3, snap, v3) => {
              val s4 = s3.copy(constrainableARPs = s1.constrainableARPs,
                               partiallyConsumedHeap = Some(h3))
              Q(s4, oh, h3, snap, v3)})}))

      case ast.AccessPredicate(loc @ ast.PredicateAccess(eArgs, predname), ePerm)
              if s.qpPredicates.contains(s.program.findPredicate(predname)) =>

        val predicate = s.program.findPredicate(predname)
        val formalVars = s.predicateFormalVarMap(predicate)

        evals(s, eArgs, _ => pve, v)((s1, tArgs, eArgsNew, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, ePermNew, v2) => {
            val s2p = if (s2.heapDependentTriggers.contains(predicate)){
              val (relevantChunks, _) =
                quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](s.h, BasicChunkIdentifier(predname))
              val (smDef1, smCache1) =
                quantifiedChunkSupporter.summarisingSnapshotMap(
                  s2, predicate, s2.predicateFormalVarMap(predicate), relevantChunks, v2)
              val debugExp = Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger(${predicate.name}(${eArgsNew.mkString(", ")}))", isInternal_ = true))
              v2.decider.assume(PredicateTrigger(predicate.name, smDef1.sm, tArgs), debugExp)
              s2.copy(smCache = smCache1)
            } else {
              s2
            }

            val loss = if (!Verifier.config.unsafeWildcardOptimization() || s2.permLocations.contains(loc.loc(s2.program)))
              PermTimes(tPerm, s2.permissionScalingFactor)
            else
              WildcardSimplifyingPermTimes(tPerm, s2.permissionScalingFactor)
            val lossExp = ePermNew.map(p => ast.PermMul(p, s2.permissionScalingFactorExp.get)(ePerm.pos, ePerm.info, ePerm.errT))
            quantifiedChunkSupporter.consumeSingleLocation(
              s2p,
              h,
              formalVars,
              Option.when(withExp)(predicate.formalArgs),
              tArgs,
              eArgsNew,
              loc,
              loss,
              lossExp,
              returnSnap,
              None,
              pve,
              v2
            )((s3, h3, snap, v3) => {
              val s4 = s3.copy(constrainableARPs = s1.constrainableARPs,
                               partiallyConsumedHeap = Some(h3))
              Q(s4, oh, h3, snap, v3)})}))
*/

/*
      case let: ast.Let if !let.isPure =>
        letSupporter.handle[ast.Exp](s, let, pve, v)((s1, g1, body, v1) => {
          val s2 = s1.copy(g = s1.g + g1)
<<<<<<< HEAD
          consumeR(s2, impr, oh, h, body, pve, v1)(Q)})
*/
/*
      case ast.AccessPredicate(locacc: ast.LocationAccess, perm) =>
        eval(s, perm, pve, v)((s1, tPerm, v1) =>
          evalLocationAccesspc(s1.copy(isImprecise = impr), locacc, pve, v1)((s2, _, tArgs, v2) =>
            v2.decider.assert(perms.IsNonNegative(tPerm)){
              case true =>
                val resource = locacc.res(Verifier.program)
                val loss = PermTimes(tPerm, s2.permissionScalingFactor)
                val ve = pve dueTo InsufficientPermission(locacc)
                val description = s"consume ${a.pos}: $a"
                chunkSupporter.consume(s2, h, resource, tArgs, loss, ve, v2, description)((s3, h1, snap1, v3) => {
                  val s4 = s3.copy(partiallyConsumedHeap = Some(h1),
                                   constrainableARPs = s.constrainableARPs,
                                   isImprecise = s3.isImprecise)
                  *
                  if (s4.isImprecise) {
                    //heaprem a.k.a. .consume
                    //Q()
                  } else if () {

                  } else {
                    //create failure
                  }

                  *
                  Q(s4, h1, snap1, v3)})
              case false =>
                createFailure(pve dueTo NegativePermission(perm), v2, s2)}))
*/
/*=======
          consumeR(s2, h, body, returnSnap, pve, v1)(Q)})

      case ast.AccessPredicate(locacc: ast.LocationAccess, perm) =>
        eval(s, perm, pve, v)((s1, tPerm, permNew, v1) =>
          evalLocationAccess(s1, locacc, pve, v1)((s2, _, tArgs, eArgs, v2) =>
            permissionSupporter.assertNotNegative(s2, tPerm, perm, permNew, pve, v2)((s3, v3) => {
              val resource = locacc.res(s.program)
              val loss = if (!Verifier.config.unsafeWildcardOptimization() || s2.permLocations.contains(locacc.loc(s2.program)))
                PermTimes(tPerm, s2.permissionScalingFactor)
              else
                WildcardSimplifyingPermTimes(tPerm, s2.permissionScalingFactor)
              val lossExp = permNew.map(p => ast.PermMul(p, s3.permissionScalingFactorExp.get)(p.pos, p.info, p.errT))
              val ve = pve dueTo InsufficientPermission(locacc)
              val description = s"consume ${a.pos}: $a"
              chunkSupporter.consume(s3, h, resource, tArgs, eArgs, loss, lossExp, returnSnap, ve, v3, description)((s4, h1, snap1, v4) => {
                val s5 = s4.copy(partiallyConsumedHeap = Some(h1),
                                 constrainableARPs = s.constrainableARPs)
                Q(s5, h1, snap1, v4)})})))
>>>>>>> upstream/master*/

      case ast.PredicateAccessPredicate(locacc: ast.LocationAccess, perm) =>
       //eval for expression and perm (perm should always be 1)
        evalpc(s.copy(isImprecise = impr), perm, pve, v)((s1, tPerm, v1) =>
          evalLocationAccesspc(s1.copy(isImprecise = impr), locacc, pve, v1)((s2, predName, tArgs, v2) => {
            v2.decider.assertgv(s.isImprecise, perms.IsPositive(tPerm)) {
              case true =>
                val resource = locacc.res(Verifier.program)
                val loss = PermTimes(tPerm, s2.permissionScalingFactor)
                val ve = pve dueTo InsufficientPermission(locacc)
                val description = s"consume ${a.pos}: $a"
                var s3 = s2.copy(isImprecise = s.isImprecise)

                chunkSupporter.consume(s3, h, true, resource, tArgs, loss, ve, v2, description)((s4, h1, snap1, v3, chunkExisted) => {

                  profilingInfo.incrementTotalConjuncts

                  if (s4.isImprecise) {
                    chunkSupporter.consume(s4, oh, false, resource, tArgs, loss, ve, v3, description)((s5, oh1, snap2, v4, chunkExisted1) => {
                      
                      if (!chunkExisted && !chunkExisted1) {
                        
                        val runtimeCheckAstNode: CheckPosition =
                          (s5.methodCallAstNode, s5.foldOrUnfoldAstNode, s5.loopPosition) match {
                            case (None, None, None) => CheckPosition.GenericNode(a)
                            case (Some(methodCallAstNode), None, None) => CheckPosition.GenericNode(methodCallAstNode)
                            case (None, Some(foldOrUnfoldAstNode), None) => CheckPosition.GenericNode(foldOrUnfoldAstNode)
                            case (None, None, Some(loopPosition)) => loopPosition
                            case _ => sys.error("Conflicting positions found while producing runtime check!")
                          }

                        val g = s5.oldStore match {
                          case Some(g) => g
                          case None => s5.g
                        }
                        val translatedArgs: Seq[ast.Exp] =
                          tArgs.map(tArg => new Translator(s5.copy(g = g), v4.decider.pcs).translate(tArg) match {
                            case None => sys.error("Error translating! Exiting safely.")
                            case Some(expr) => expr
                          })

                        if (s5.generateChecks) {
                          runtimeChecks.addChecks(runtimeCheckAstNode,
                            ast.PredicateAccessPredicate(ast.PredicateAccess(translatedArgs, predName)(), perm)(),
                            viper.silicon.utils.zip3(v4.decider.pcs.branchConditionsSemanticAstNodes,
                              v4.decider.pcs.branchConditionsAstNodes,
                              v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                            a,
                            s5.forFraming)
                        }
                      }

                      if (chunkExisted) {
                        
                        profilingInfo.incrementEliminatedConjuncts

                        Q(s5, oh1, h1, snap1, v4)}

                      else {

                        if (chunkExisted1) {
                          profilingInfo.incrementEliminatedConjuncts
                        }

                        Q(s5, oh1, h1, snap2, v4)}})}

                  else if (chunkExisted) {

                    profilingInfo.incrementEliminatedConjuncts

                    Q(s4, oh, h1, snap1, v3)}

                  else {

                    createFailure(pve dueTo InsufficientPermission(locacc), v3, s4)}})

              case false =>

                createFailure(pve dueTo InsufficientPermission(locacc), v2, s2)

            } match {

              case (verificationResult, _) => verificationResult

            }}))


      case ast.FieldAccessPredicate(locacc: ast.LocationAccess, perm) =>

       //eval for expression and perm (perm should always be 1)
        evalpc(s.copy(isImprecise = impr), perm, pve, v)((s1, tPerm, v1) =>
          evalLocationAccesspc(s1.copy(isImprecise = impr), locacc, pve, v1)((s2, field, tArgs, v2) => {
            // is this why we produce a runtime check for != Null? does the
            // path condition not imply this (no, apparently it does not, at least for the
            // extra_check_issue.vpr example)
            v2.decider.assertgv(s.isImprecise, And(perms.IsPositive(tPerm), tArgs.head !== Null())){
              case true =>
                val resource = locacc.res(Verifier.program)
                val loss = PermTimes(tPerm, s2.permissionScalingFactor)
                val ve = pve dueTo InsufficientPermission(locacc)
                val description = s"consume ${a.pos}: $a"
                var s3 = s2.copy(isImprecise = s.isImprecise)

                chunkSupporter.consume(s3, h, true, resource, tArgs, loss, ve, v2, description)((s4, h1, snap1, v3, chunkExisted) => {

                  profilingInfo.incrementTotalConjuncts

                  // don't know if this should be s3 or s4 - J
                  if (s4.isImprecise) {
                    chunkSupporter.consume(s4, oh, false, resource, tArgs, loss, ve, v3, description)((s5, oh1, snap2, v4, chunkExisted1) => {
                      
                      if (!chunkExisted && !chunkExisted1) {

                        val runtimeCheckAstNode: CheckPosition =
                          (s5.methodCallAstNode, s5.foldOrUnfoldAstNode, s5.loopPosition) match {
                            case (None, None, None) => CheckPosition.GenericNode(locacc)
                            case (Some(methodCallAstNode), None, None) =>
                              CheckPosition.GenericNode(methodCallAstNode)
                            case (None, Some(foldOrUnfoldAstNode), None) =>
                              CheckPosition.GenericNode(foldOrUnfoldAstNode)
                            case (None, None, Some(loopPosition)) => loopPosition
                            case _ => sys.error("Conflicting positions!")
                          }

                        val g = s5.oldStore match {
                          case Some(g) => g
                          case None => s5.g
                        }
                        val translatedArgs: Seq[ast.Exp] =
                          tArgs.map(tArg => new Translator(s5.copy(g = g), v4.decider.pcs).translate(tArg) match {
                            case None => sys.error("Error translating! Exiting safely.")
                            case Some(expr) => expr
                          })

                        if (s5.generateChecks) {
                          runtimeChecks.addChecks(runtimeCheckAstNode,
                            ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, resource.asInstanceOf[ast.Field])(), perm)(),
                            viper.silicon.utils.zip3(v4.decider.pcs.branchConditionsSemanticAstNodes,
                              v4.decider.pcs.branchConditionsAstNodes,
                              v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                            a,
                            s5.forFraming)
                        }
                      }

                      if (chunkExisted) {

                        profilingInfo.incrementEliminatedConjuncts
                        Q(s5, oh1, h1, snap1, v4)}

                      else {

                        // we don't want to count it if the runtime check
                        // path happened, i think
                        if (chunkExisted1) {
                          profilingInfo.incrementEliminatedConjuncts
                        }

                        Q(s5, oh1, h1, snap2, v4)}})}
                  else if (chunkExisted) {
                    profilingInfo.incrementEliminatedConjuncts
                    Q(s4, oh, h1, snap1, v3)}
                  else {
                    createFailure(pve dueTo InsufficientPermission(locacc), v3, s4)}})

              case false =>
                createFailure(pve dueTo InsufficientPermission(locacc), v2, s2)

            // this is the assertgv case for field access
            } match {
                case (verificationResult, potentialReturnedChecks) => {
                  potentialReturnedChecks match {
                    case None => ()
                    case Some(returnedChecks) => {
                      // should use v2.decider.pcs here? yes

                      val runtimeCheckAstNode: CheckPosition =
                        (s2.methodCallAstNode, s2.foldOrUnfoldAstNode, s2.loopPosition) match {
                          case (None, None, None) => CheckPosition.GenericNode(a)
                          case (Some(methodCallAstNode), None, None) =>
                            CheckPosition.GenericNode(methodCallAstNode)
                          case (None, Some(foldOrUnfoldAstNode), None) => CheckPosition.GenericNode(foldOrUnfoldAstNode)
                          case (None, None, Some(loopPosition)) => loopPosition
                          case _ =>
                            sys.error("Conflicting positions while looking for position!")
                        }

                      val g = s2.oldStore match {
                        case Some(g) => g
                        case None => s2.g
                      }

                      if (s2.generateChecks) {
                        runtimeChecks.addChecks(runtimeCheckAstNode,
                          (new Translator(s2.copy(g = g), v2.decider.pcs).translate(returnedChecks) match {
                            case None => sys.error("Error translating! Exiting safely.")
                            case Some(expr) => expr
                          }),
                        viper.silicon.utils.zip3(v2.decider.pcs.branchConditionsSemanticAstNodes,
                          v2.decider.pcs.branchConditionsAstNodes,
                          v2.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                        a,
                        s2.forFraming)
                      }
                    }
                  }
                  verificationResult
                }
            }}))

/*
      case ast.AccessPredicate(locacc: ast.LocationAccess, perm/*,need an overloaded copy with impreciseHeap as a parameter*/) => //add h_?; perm = 1

       //eval for expression and perm (perm should always be 1)
        evalpc(s.copy(isImprecise = impr), perm, pve, v)((s1, tPerm, v1) =>
          evalLocationAccesspc(s1.copy(isImprecise = impr), locacc, pve, v1)((s2, _, tArgs, v2) => {

            v2.decider.assertgv(s.isImprecise, perms.IsPositive(tPerm)){
              case true =>
                val resource = locacc.res(Verifier.program)
                val loss = PermTimes(tPerm, s2.permissionScalingFactor)
                val ve = pve dueTo InsufficientPermission(locacc)
                val description = s"consume ${a.pos}: $a"
                var s3 = s2.copy(isImprecise = s.isImprecise)



                chunkSupporter.consume(s3, h, resource, tArgs, loss, ve, v2, description)((s4, h1, snap1, v3, chunkExisted) => {
/*                  val s4 = s3.copy(partiallyConsumedHeap = Some(h1),
                                   constrainableARPs = s.constrainableARPs,
                                   isImprecise = s3.isImprecise)
  */
/*                  if (s4.isImprecise) {
                    //do we want to use s3 or s4 here?
                    //heaprem a.k.a. .consume
                    //Q()
                  } else if () {

                  } else {
                    //create failure
                  }

*/
                  Q(s4, oh, h1, snap1, v3)})
              case false =>
                createFailure(pve dueTo InsufficientPermission(locacc), v2, s2)}}))
*/
/*
      case _: ast.InhaleExhaleExp =>
        createFailure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(a), v, s, "valid AST")
*/
      /* Handle wands */
/*      case wand: ast.MagicWand if s.qpMagicWands.contains(MagicWandIdentifier(wand, s.program)) =>
        val bodyVars = wand.subexpressionsToEvaluate(s.program)
        val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(bodyVars(i).typ), false))
        val formalVarExps = Option.when(withExp)(bodyVars.indices.toList.map(i => ast.LocalVarDecl(s"x$i", bodyVars(i).typ)()))
        evals(s, bodyVars, _ => pve, v)((s1, tArgs, bodyVarsNew, v1) => {
          val s1p = if (s1.heapDependentTriggers.contains(MagicWandIdentifier(wand, s.program))){
            val (relevantChunks, _) =
              quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](s1.h, MagicWandIdentifier(wand, s.program))
            val (smDef1, smCache1) =
              quantifiedChunkSupporter.summarisingSnapshotMap(
                s1, wand, formalVars, relevantChunks, v1)
            val argsString = bodyVarsNew.mkString(", ")
            val predName = MagicWandIdentifier(wand, s.program).toString
            val debugExp = Option.when(withExp)(DebugExp.createInstance(s"PredicateTrigger($predName($argsString))", isInternal_ = true))
            v1.decider.assume(PredicateTrigger(predName, smDef1.sm, tArgs), debugExp)
            s1.copy(smCache = smCache1)
          } else {
            s1
          }
          val loss = s1.permissionScalingFactor
          val lossExp = s1.permissionScalingFactorExp
          quantifiedChunkSupporter.consumeSingleLocation(
            s1p,
            h,
            formalVars,
            formalVarExps,
            tArgs,
            Option.when(withExp)(bodyVars),
            wand,
            loss,
            lossExp,
            returnSnap,
            None,
            pve,
            v1
          )((s3, h3, snap, v3) => {
            val s4 = s3.copy(constrainableARPs = s1.constrainableARPs,
                             partiallyConsumedHeap = Some(h3))
            Q(s4, h3, snap, v3)})})

      case wand: ast.MagicWand =>
        magicWandSupporter.evaluateWandArguments(s, wand, pve, v)((s1, tArgs, eArgs, v1) => {
          val ve = pve dueTo MagicWandChunkNotFound(wand)
          val description = s"consume wand $wand"
          chunkSupporter.consume(s1, h, wand, tArgs, eArgs, FullPerm, Option.when(withExp)(ast.FullPerm()(wand.pos, wand.info, wand.errT)), returnSnap, ve, v1, description)(Q)
        })
*/
      case _ => {

//<<<<<<< HEAD
        var returnedState: Option[(State, viper.silicon.decider.RecordedPathConditions)] = None

        // make sure we map the runtime check from the method call site, if
        // we're currently looking at a precondition... otherwise, just use
        // the ast node passed into consumeTlc
        //
        // should we check for a fold or unfold statement here, too?
        //
        // we want to map the runtime check from the fold or unfold statement,
        // not something in the body of a predicate
        var runtimeCheckAstNode: CheckPosition = (s.methodCallAstNode, s.foldOrUnfoldAstNode, s.loopPosition) match {
          case (None, None, None) => CheckPosition.GenericNode(a)
          case (Some(methodCallAstNode), None, None) =>
            CheckPosition.GenericNode(methodCallAstNode)
          case (None, Some(foldOrUnfoldAstNode), None) => CheckPosition.GenericNode(foldOrUnfoldAstNode)
          case (None, None, Some(loopPosition)) => loopPosition

          // TODO: This should not occur, but it did at one point. Figure out why?
          case _ =>
            sys.error("Conflicting positions while looking for position! "
              + s"Position: ${(s.methodCallAstNode, s.foldOrUnfoldAstNode, s.loopPosition)}")
        }

        evalAndAssert(s, impr, a, returnSnap, pve, v)((s1, t, v1) => {

          returnedState = Some((s1, v1.decider.pcs.duplicate()))

          // the methodCallAstNode field should only stick around until we
          // consume the precondition of the method, right? we unset it here if
          // it exists, and after encountering a method call ast node, we must
          // go here (and nowhere else?)? we also only use this field here
          //
          // this is (partially?) wrong; we should really unset the field in
          // the state at the beginning of the method... though everything in a
          // precondition must(?) go through this case eventually, so that may
          // be why the previous version appeared to work fine

          Q(s1, oh, h, t, v1)
        }) match {
          case (verificationResult, Some(returnedChecks)) =>
            returnedState match {
              case Some((s1, pcs)) => {
                val g = s1.oldStore match {
                  case Some(g) => g
                  case None => s1.g
                }

                if (s1.generateChecks) {
                  runtimeChecks.addChecks(runtimeCheckAstNode,
                    (new Translator(s1.copy(g = g), pcs).translate(returnedChecks) match {
                      case None => sys.error("Error translating! Exiting safely.")
                      case Some(expr) => expr
                    }),
                  viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                    v.decider.pcs.branchConditionsAstNodes,
                    v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                  a,
                  s1.forFraming)
                }

                verificationResult
              }
              case _ => sys.error("This should not occur!")
            }
          case (verificationResult, None) => verificationResult
        }
      }
/*=======
      case _ =>
        evalAndAssert(s, a, returnSnap, pve, v)((s1, t, v1) => {
          Q(s1, h, t, v1)
        })
>>>>>>> upstream/master*/
    }

    consumed
  }

/*<<<<<<< HEAD
  private def evalAndAssert(s: State, impr: Boolean, e: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
                           (Q: (State, Option[Term], Verifier) => VerificationResult)
                           : (VerificationResult, Option[Term]) = {
=======*/
  private def consumeConditionalTlcMoreJoins(s: State, h: Heap, e0: ast.Exp, a1: ast.Exp, a2: Option[ast.Exp], scopeUid: Int,
                                             returnSnap: Boolean,
                                             pve: PartialVerificationError, v: Verifier)
                                            (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                                            : VerificationResult = {
    eval(s, e0, pve, v)((s1, t0, e0New, v1) =>
      joiner.join[(Heap, Option[Term]), (Heap, Option[Term])](s1, v1, resetState = false)((s1, v1, QB) => {
        branch(s1.copy(parallelizeBranches = false), t0, (e0, e0New), v1)(
          (s2, v2) =>
            consumeR(s2.copy(parallelizeBranches = s1.parallelizeBranches), h, a1, returnSnap, pve, v2)((s3, h1, t1, v3) => {
            v3.symbExLog.closeScope(scopeUid)
            QB(s3, (h1, t1), v3)
          }),
          (s2, v2) =>
            a2 match {
              case Some(a2) => consumeR(s2.copy(parallelizeBranches = s1.parallelizeBranches), h, a2, returnSnap, pve, v2)((s3, h1, t1, v3) => {
                v3.symbExLog.closeScope(scopeUid)
                QB(s3, (h1, t1), v3)
              })
              case None =>
                v2.symbExLog.closeScope(scopeUid)
                QB(s2.copy(parallelizeBranches = s1.parallelizeBranches), (h, if (returnSnap) Some(Unit) else None), v2)
            })
      })(entries => {
        val s2 = entries match {
          case Seq(entry) => // One branch is dead
            (entry.s, entry.data)
          case Seq(entry1, entry2) => // Both branches are alive
            val mergedData = (
              State.mergeHeap(
                entry1.data._1, And(entry1.pathConditions.branchConditions), Option.when(withExp)(BigAnd(entry1.pathConditions.branchConditionExps.map(_._2.get))),
                entry2.data._1, And(entry2.pathConditions.branchConditions), Option.when(withExp)(BigAnd(entry2.pathConditions.branchConditionExps.map(_._2.get))),
              ),
              // Assume that entry1.pcs is inverse of entry2.pcs
              (entry1.data._2, entry2.data._2) match {
                case (Some(t1), Some(t2)) if returnSnap => Some(Ite(And(entry1.pathConditions.branchConditions), t1, t2))
                case (None, None) if !returnSnap => None
                case (_, _) => sys.error(s"Unexpected join data entries: $entries")
              }
            )
            (entry1.pathConditionAwareMergeWithoutConsolidation(entry2, v1), mergedData)
          case _ =>
            sys.error(s"Unexpected join data entries: $entries")
        }
        s2
      })((s4, data, v4) => {
        Q(s4, data._1, data._2, v4)
      })
    )
  }


  private def evalAndAssert(s: State, impr: Boolean, e: ast.Exp, returnSnap: Boolean, pve: PartialVerificationError, v: Verifier)
                           (Q: (State, Option[Term], Verifier) => VerificationResult)
                           : (VerificationResult, Option[Term]) = {
//>>>>>>> upstream/master

    /* It is expected that the partially consumed heap (h in the above implementation of
     * `consume`) has already been assigned to `c.partiallyConsumedHeap`.
     *
     * Switch to the eval heap (σUsed) of magic wand's exhale-ext, if necessary.
     * This is done here already (the evaluator would do it as well) to ensure that the eval
     * heap is consolidated by tryOrFail if the assertion fails.
     * The latter is also the reason for wrapping the assertion check in a tryOrFail block:
     * the tryOrFail that wraps the consumption of each top-level conjunct would not consolidate
     * the right heap.
     */

    val s1 = s.copy(h = magicWandSupporter.getEvalHeap(s),
                    reserveHeaps = Nil,
                    exhaleExt = false)

//<<<<<<< HEAD
    val s2 = stateConsolidator.consolidate(s1, v)

    var returnValue: Option[(VerificationResult, Option[Term])] = None

    val result = evalpc(s2.copy(isImprecise = impr), e, pve, v)((s3, t, v1) => {
      val s4 = s3.copy(isImprecise = s2.isImprecise)
      v1.decider.assertgv(s4.isImprecise, t) {
        case true =>
          v1.decider.assume(t)
          val s5 = s4.copy(h = s.h,
                           reserveHeaps = s.reserveHeaps,
                           exhaleExt = s.exhaleExt)
          Q(s5, Some(Unit), v1)
        case false =>
        //  println("pve " + pve + "\ne " + e + "\nv1 " + v1 + "\ns3 " + s3)
          //println("heap: " + s.h + "\noh: " + s.optimisticHeap)
          //val s4 = s3.copy(isImprecise = false)
          createFailure(pve dueTo AssertionFalse(e), v1, s3)
          // matching on the return value of assertgv
    } match {
      case (verificationResult, returnedCheck) => {
        returnValue = Some((verificationResult, returnedCheck))
        verificationResult
      }
    }})

    returnValue match {
      case Some((verificationResult, returnedCheck)) =>
        (verificationResult, returnedCheck)
      case None =>
        (result, None)
    }
/*=======
    executionFlowController.tryOrFail0(s1, v)((s2, v1, QS) => {
      eval(s2, e, pve, v1)((s3, t, eNew, v2) => {
        val termToAssert = t match {
          case Quantification(q, vars, body, trgs, name, isGlob, weight) =>
            val transformed = FunctionPreconditionTransformer.transform(body, s3.program)
            v2.decider.assume(Quantification(q, vars, transformed, trgs, name+"_precondition", isGlob, weight), Option.when(withExp)(e), eNew)
            Quantification(q, vars, Implies(transformed, body), trgs, name, isGlob, weight)
          case _ => t
        }
        v2.decider.assert(termToAssert) {
          case true =>
            v2.decider.assume(t, Option.when(withExp)(e), eNew)
            QS(s3, v2)
          case false =>
            val failure = createFailure(pve dueTo AssertionFalse(e), v2, s3, termToAssert, eNew)
            if (s3.retryLevel == 0 && v2.reportFurtherErrors()){
              v2.decider.assume(t, Option.when(withExp)(e), eNew)
              failure combine QS(s3, v2)
            } else failure}})
    })((s4, v4) => {
      val s5 = s4.copy(h = s.h,
                       reserveHeaps = s.reserveHeaps,
                       exhaleExt = s.exhaleExt)
      Q(s5, if (returnSnap) Some(Unit) else None, v4)
    })
>>>>>>> upstream/master*/
  }
}
