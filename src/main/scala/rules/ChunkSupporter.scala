// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silicon.Stack
import viper.silicon.debugger.DebugExp
import scala.reflect.ClassTag
import viper.silver.ast
import viper.silver.verifier.{PartialVerificationError, VerificationError}
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Failure, Success, VerificationResult}
import viper.silicon.logger.SymbExLogger
import viper.silicon.resources.{FieldID, NonQuantifiedPropertyInterpreter, PredicateID, Resources}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.supporters.Translator
import viper.silicon.utils
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.parser.PUnknown
import viper.silver.verifier.{VerificationError, PartialVerificationError}

import scala.reflect.ClassTag

trait ChunkSupportRules extends SymbolicExecutionRules {
  def consume(s: State,
              h: Heap,
              consolidate: Boolean,
              resource: ast.Resource,
              args: Seq[Term],
              argsExp: Option[Seq[ast.Exp]],
              perms: Term,
              permsExp: Option[ast.Exp],
              returnSnap: Boolean,
              ve: VerificationError,
              v: Verifier,
              description: String) 
              (Q: (State, Heap, Option[Term], Verifier, Boolean) => VerificationResult)
             : VerificationResult

  def produce(s: State, h: Heap, ch: NonQuantifiedChunk, v: Verifier)
             (Q: (State, Heap, Verifier) => VerificationResult)
             : VerificationResult

  def lookup(s: State,
             h: Heap,
             oh: Heap,
             addToOh: Boolean,
             resource: ast.Resource,
             runtimeCheckFieldTarget: ast.FieldAccess, 
             args: Seq[Term],
             argsExp: Option[Seq[ast.Exp]],
             pve: PartialVerificationError,
             ve: VerificationError,
             v: Verifier,
             generateChecks: Boolean = true)
            (Q: (State, Heap, Heap, Term, Verifier) => VerificationResult)
            : VerificationResult

  def inHeap[CH <: NonQuantifiedChunk: ClassTag]
            (s: State,
             h: Heap,
             chunk: Iterable[Chunk],
             resource: ast.Resource,
             args: Seq[Term],
             v: Verifier)
            : Boolean


  def findChunk[CH <: NonQuantifiedChunk: ClassTag]
               (chunks: Iterable[Chunk],
                id: ChunkIdentifer,
                args: Iterable[Term],
                v: Verifier)
               : Option[CH]

  def findChunksWithID[CH <: NonQuantifiedChunk: ClassTag]
                      (chunks: Iterable[Chunk],
                       id: ChunkIdentifer)
                      : Iterable[CH]
}

object chunkSupporter extends ChunkSupportRules {

  def consume(s: State,
              h: Heap,
              consolidate: Boolean,
              resource: ast.Resource,
              args: Seq[Term],
              argsExp: Option[Seq[ast.Exp]],
              perms: Term,
              permsExp: Option[ast.Exp],
              returnSnap: Boolean,
              ve: VerificationError,
              v: Verifier,
              description: String)
             (Q: (State, Heap, Option[Term], Verifier, Boolean) => VerificationResult)
             : VerificationResult = {
    consume2(s, h, consolidate, resource, args, argsExp, perms, permsExp, returnSnap, ve, v)((s2, h2, optSnap, v2) =>
      optSnap match {
        case Some(snap) =>
          Q(s2, h2, Some(snap.convert(sorts.Snap)), v2, true)
        case None if returnSnap =>
          /* Not having consumed anything could mean that we are in an infeasible
           * branch, or that the permission amount to consume was zero.
           *
           * [MS 2022-01-28] Previously, a a fresh snapshot was retured, which also had to be
           * registered with the function recorder. However, since nothing was consumed,
           * returning the unit snapshot seems more appropriate.
           */
          val fresh = v2.decider.fresh(sorts.Snap, Option.when(withExp)(PUnknown()))
          val s3 = s2.copy(functionRecorder = s2.functionRecorder.recordFreshSnapshot(fresh.applicable))
          Q(s3, h2, Some(fresh), v2, false)
        case None =>
          Q(s2, h2, None, v2, false)
      })
  }
//<<<<<<< HEAD
  
  private def consume2(s: State,
                       h: Heap,
                       consolidate: Boolean,
                       resource: ast.Resource,
                       args: Seq[Term],
                       argsExp: Option[Seq[ast.Exp]],
                       perms: Term,
                       permsExp: Option[ast.Exp],
                       returnSnap: Boolean,
                       ve: VerificationError,
                       v: Verifier)
                      (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                      : VerificationResult = {
    
    val id = ChunkIdentifier(resource, s.program)
    if (s.exhaleExt) {
      val failure = createFailure(ve, v, s, "chunk consume in package")
      magicWandSupporter.transfer(s, perms, permsExp, failure, Seq(), v)(consumeGreedy(_, _, id, true, resource, args, _, _, _))((s1, optCh, v1) =>
        if (returnSnap){
          Q(s1, h, optCh.flatMap(ch => Some(ch.snap)), v1)
        } else {
          Q(s1, h, None, v1)
        })
    } else {
        val s1 = s.copy(h = h)
        val v1 = v
      //executionFlowController.tryOrFail2[Heap, Option[Term]](s.copy(h = h), v)((s1, v1, QS) =>
        if (s1.moreCompleteExhale) {
          moreCompleteExhaleSupporter.consumeComplete(s1, s1.h, resource, args, argsExp, perms, permsExp, returnSnap, ve, v1)((s2, h2, snap2, v2) => {
            Q(s2.copy(h = s.h), h2, snap2, v2)
          })
        } else {
          var s1 = s.copy(h = h)
          if (consolidate) {
            s1 = v.stateConsolidator(s).consolidate(s.copy(h = h), v)
          }
          consumeGreedy(s1, s1.h, id, consolidate, resource, args, perms, permsExp, v1) match {
            case (Complete(), s2, h2, optCh2) =>
              val snap = optCh2 match {
                case Some(ch) if returnSnap =>
                  if (v1.decider.check(IsPositive(perms), Verifier.config.checkTimeout())) {
                    Some(ch.snap)
                  } else {
                    Some(Ite(IsPositive(perms), ch.snap.convert(sorts.Snap), Unit))
                  }
                case _ => None
              }
              Q(s2.copy(h = s.h), h2, snap, v1)
            case _ if v1.decider.checkSmoke(true) =>
              Success() // TODO: Mark branch as dead?
            case (Incomplete(p, _), s2, h2, None) =>
              Q(s2.copy(h = s.h), h2, None, v)
          }
        }
      //)(Q)
/*=======

  private def consume(s: State,
                      h: Heap,
                      consolidate: Boolean, // True when regular heap
                      resource: ast.Resource,
                      args: Seq[Term],
                      perms: Term,
                      ve: VerificationError,
                      v: Verifier)
                     (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                     : VerificationResult = {
    var s1 = s.copy(h = h)
    if (consolidate) {
      s1 = stateConsolidator.consolidate(s.copy(h = h), v)
    }
    consumeGreedy(s1, s1.h, consolidate, resource, args, perms, v) match {
      case (Complete(), s2, h2, optCh2) =>
        Q(s2.copy(h = s.h), h2, optCh2.map(_.snap), v)

      case _ if v.decider.checkSmoke() =>
        Success()

      case (Incomplete(p), s2, h2, None) =>
        Q(s2.copy(h = s.h), h2, None, v)

>>>>>>> upstream/master*/
    }
  }

  private def consumeGreedy(s: State,
                            h: Heap,
//<<<<<<< HEAD
                            id: ChunkIdentifer,
//=======
                            isRegularHeap: Boolean,
//>>>>>>> upstream/master
                            resource: ast.Resource,
                            args: Seq[Term],
                            perms: Term,
                            permsExp: Option[ast.Exp],
                            v: Verifier)
                            : (ConsumptionResult, State, Heap, Option[NonQuantifiedChunk])= {

    resource match {
      case f: ast.Field => {
        /* heap-rem-acc */
        /* the foldl portion of heap-rem-acc
         * builds a new heap of chunks that definitely do not
         * contain the acc pred to remove
        */
        var newH: Heap = h.values.foldLeft(Heap()) { (currHeap, chunk) =>
          chunk match {
            case c: NonQuantifiedChunk =>

              // The term in checkgv uses infix notation I got from a different check to see if the args are equal
              var statusCheckgv = true

              if (id == c.id) {
                // TODO;staticprofiling: this is responsible for the static profiling issue, maybe
                statusCheckgv = v.decider.checkgv(s.isImprecise, And(c.args zip args map (x => x._1 === x._2)), Some(Verifier.config.checkTimeout())) match {
                  case (status, runtimeCheck) => status
                }
              }

              if ((id != c.id) || (!statusCheckgv)){
                currHeap + c
              }
              else {
                currHeap
              }
            case _ =>
              currHeap
          }
        }

        // tries to find the chunk in h
        findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
          // I'm not sure if I need these checks but I included them to be safe - J
/*<<<<<<< HEAD
          case Some(ch) if v.decider.check(ch.perm === perms, Verifier.config.checkTimeout()) && v.decider.check(perms === FullPerm, Verifier.config.checkTimeout()) =>
            (Complete(), s, newH, Some(ch))
=======*/
          case Some(ch) if v.decider.check(ch.perm === perms, Verifier.config.checkTimeout()) && v.decider.check(perms === FullPerm, Verifier.config.checkTimeout()) =>
            // handles removing all predicates from OH when field chunk is in optimistic heap (Note: field chunk in regular heap handled by next case) - Priyam
            if (!isRegularHeap){
              var newH2: Heap = newH.values.foldLeft(Heap()) { (currHeap, chunk) =>
                chunk match {
                  case c: NonQuantifiedChunk =>
                    c.resourceID match {
                      case FieldID =>
                        currHeap + c
                      case _ =>
                        currHeap
                    }
                  case _ =>
                    currHeap
                }
              }
              (Complete(), s, newH2, Some(ch))
            }
            else {
              (Complete(), s, newH, Some(ch))
            }

//>>>>>>> upstream/master

          case _ => {
            var newH2: Heap = newH.values.foldLeft(Heap()) { (currHeap, chunk) =>
              chunk match {
                case c: NonQuantifiedChunk =>
                  c.resourceID match {
                    case FieldID =>
                      currHeap + c
                    case _ =>
                      currHeap
                  }
                case _ =>
                  currHeap
              }
            }
            (Incomplete(perms, permsExp), s, newH2, None)
          }
        }
      }

      case p: ast.Predicate => {
        /* heap-rem-pred */
        findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
/*<<<<<<< HEAD
          case Some(ch) if v.decider.check(ch.perm === perms, Verifier.config.checkTimeout()) && v.decider.check(perms === FullPerm, Verifier.config.checkTimeout()) =>
            var newH = h - ch
            (Complete(), s, newH, Some(ch))
=======*/
          case Some(ch) if v.decider.check(perms === FullPerm, Verifier.config.checkTimeout()) =>
            val toTake = PermMin(ch.perm, perms)
            val newChunk = ch.withPerm(PermMinus(ch.perm, toTake), None)
            val takenChunk = Some(ch.withPerm(toTake, None))
            var newHeap = h - ch
            if (!v.decider.check(newChunk.perm === NoPerm, Verifier.config.checkTimeout())) {
              newHeap = newHeap + newChunk
            }
            (ConsumptionResult(PermMinus(perms, toTake), None, Seq(), v, 0), s, newHeap, takenChunk)
//>>>>>>> upstream/master
          case _ =>
            (Incomplete(perms, permsExp), s, Heap(), None)
        }
      }
    }
  }

  def produce(s: State, h: Heap, ch: NonQuantifiedChunk, v: Verifier)
             (Q: (State, Heap, Verifier) => VerificationResult)
             : VerificationResult = {

    // Try to merge the chunk into the heap by finding an alias.
    // In any case, property assumptions are added after the merge step.
    val (fr1, h1) = v.stateConsolidator(s).merge(s.functionRecorder, s, h, ch, v)
    Q(s.copy(functionRecorder = fr1), h1, v)
  }

  def lookup(s: State,
             h: Heap,
             oh: Heap,
             addToOh: Boolean,
             resource: ast.Resource,
             runtimeCheckFieldTarget: ast.FieldAccess,
             args: Seq[Term],
             argsExp: Option[Seq[ast.Exp]],
             pve: PartialVerificationError,
             ve: VerificationError,
             v: Verifier,
             generateChecks: Boolean = true)
            (Q: (State, Heap, Heap, Term, Verifier) => VerificationResult)
            : VerificationResult = {
      val s1 = v.stateConsolidator(s).consolidate(s.copy(h = h, optimisticHeap = oh), v)
      val lookupFunction =
        if (s1.moreCompleteExhale) moreCompleteExhaleSupporter.lookupComplete _
        else lookupGreedy _
      lookupFunction(s1, s1.h, s1.optimisticHeap, addToOh, resource,
        runtimeCheckFieldTarget, args, argsExp, pve, ve, v, generateChecks)((s2, tSnap, v1) =>
        Q(s2.copy(h = s.h, optimisticHeap = s.optimisticHeap), s2.h, s2.optimisticHeap, tSnap, v1))
    }

  private def lookupGreedy(s: State,
                           h: Heap,
                           oh: Heap,
                           addToOh: Boolean,
                           resource: ast.Resource,
                           runtimeCheckFieldTarget: ast.FieldAccess,
                           args: Seq[Term],
                           argsExp: Option[Seq[ast.Exp]],
                           pve: PartialVerificationError,
                           ve: VerificationError,
                           v: Verifier,
                           generateChecks: Boolean)
                          (Q: (State, Term, Verifier) => VerificationResult)
                          : VerificationResult = {

    val id = ChunkIdentifier(resource, s.program)

    profilingInfo.incrementTotalConjuncts

    findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
      case Some(ch) if v.decider.check(IsPositive(ch.perm), Verifier.config.checkTimeout()) =>

        profilingInfo.incrementEliminatedConjuncts

        if (s.gatherFrame) {
          findChunk[NonQuantifiedChunk](s.frameArgHeap.values, id, args, v) match {
            case Some(c) if v.decider.check(IsPositive(c.perm), Verifier.config.checkTimeout()) =>
              Q(s, ch.snap, v)
            case _ => Q(s.copy(frameArgHeap = s.frameArgHeap + ch), ch.snap, v)
          }
        } else {
          Q(s, ch.snap, v)
        }

      // TODO: should this case be moved to when the chunk cannot be found in the oh?
      case _ if v.decider.checkSmoke(true) =>
        profilingInfo.incrementEliminatedConjuncts
        if (s.isInPackage) {
          val snap = v.decider.fresh(v.snapshotSupporter.optimalSnapshotSort(resource, s, v), Option.when(withExp)(PUnknown()))
          Q(s, snap, v)
        } else {
          Success() // TODO: Mark branch as dead?
        }

      case _ => {
        findChunk[NonQuantifiedChunk](oh.values, id, args, v) match {
          case Some(ch) if v.decider.check(IsPositive(ch.perm), Verifier.config.checkTimeout()) =>

            profilingInfo.incrementEliminatedConjuncts

            if (s.gatherFrame) {
              findChunk[NonQuantifiedChunk](s.frameArgHeap.values, id, args, v) match {
                case Some(c) if v.decider.check(IsPositive(c.perm), Verifier.config.checkTimeout()) =>
                  Q(s, ch.snap, v)
                case _ => Q(s.copy(frameArgHeap = s.frameArgHeap + ch), ch.snap, v)
              }
            } else {
              Q(s, ch.snap, v)
            }

          // this is the eval case for adding run-time checks
          case _ if s.isImprecise && addToOh =>
            resource match {
              case f: ast.Field => {
                v.decider.assertgv(s.isImprecise, args.head !== Null) {
                  case true =>
/*<<<<<<< HEAD
                    val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ), Option.when(withExp)(PUnknown()))
                    val ch = BasicChunk(FieldID, BasicChunkIdentifier(f.name), args, argsExp, snap, None, FullPerm, None)
=======*/
                    val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ), Option.when(withExp)(PUnknown()))
                    val ch = BasicChunk(FieldID, BasicChunkIdentifier(f.name), args, argsExp, snap, None, FullPerm, None)
                    if (SymbExLogger.enabled) {
                      // add chunk created by trying to find nonexistent chunk in imprecise state to snaps
                      SymbExLogger.populateSnaps(Vector(ch), s)
                    }
//>>>>>>> upstream/master
                    val s2 = s.copy(optimisticHeap = oh)

                    val runtimeCheckAstNode: CheckPosition =
                      (s2.methodCallAstNode, s2.foldOrUnfoldAstNode, s2.loopPosition, s2.unfoldingAstNode) match {
                        case (None, None, None, None) => CheckPosition.GenericNode(runtimeCheckFieldTarget)
                        case (Some(methodCallAstNode), None, None, _) => CheckPosition.GenericNode(methodCallAstNode)
                        case (None, Some(foldOrUnfoldAstNode), None, _) => CheckPosition.GenericNode(foldOrUnfoldAstNode)
                        case (None, None, Some(loopPosition), _) => loopPosition
                        case (None, None, None, Some(unfoldingAstNode)) => CheckPosition.GenericNode(unfoldingAstNode)
                        case _ => sys.error("Conflicting positions found while adding runtime check!")
                      }

                    val (g, tH, tOH) = s2.oldStore match {
                      /* this match sequence shouldn't be necessary based on currently functionality, but here for safety - JW */
                      case Some(g) => (g, s2.h + s2.oldHeaps(Verifier.PRE_HEAP_LABEL), s2.optimisticHeap + s2.oldHeaps(Verifier.PRE_OPTHEAP_LABEL))
                      case None => (s2.g, s2.h, s2.optimisticHeap)
                    }
                    val translatedArgs: Seq[ast.Exp] =
                      args.map(tArg => new Translator(s2.copy(g = g, h = tH, optimisticHeap = tOH), v.decider.pcs).translate(tArg) match {
                        case None => sys.error("Error translating! Exiting safely.")
                        case Some(expr) => expr
                      })

                    if (s2.generateChecks) {
                      runtimeChecks.addChecks(runtimeCheckAstNode,
                        ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), Some(ast.FullPerm()()))(),
                        viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                          v.decider.pcs.branchConditionsAstNodes,
                          v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                        runtimeCheckFieldTarget,
                        s2.forFraming)
                      runtimeCheckFieldTarget.addCheck(ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), Some(ast.FullPerm()()))())
                    }

                    v.decider.assume(args.head !== Null, None)

                    if (s2.gatherFrame) {
                      findChunk[NonQuantifiedChunk](s2.frameArgHeap.values, id, args, v) match {
                        case Some(c) if v.decider.check(IsPositive(c.perm), Verifier.config.checkTimeout()) =>
                          /* Shouldn't make it to this case based on functionality, but here for safety */
                          Q(s.copy(optimisticHeap = s2.optimisticHeap + ch), snap, v)
                        case _ => Q(s.copy(optimisticHeap = s2.optimisticHeap + ch, frameArgHeap = s2.frameArgHeap + ch), snap, v)
                      }
                    } else {
                      Q(s.copy(optimisticHeap = s2.optimisticHeap + ch), snap, v)
                    }

                  case false =>
                    createFailure(ve, v, s, "looking up chunk", true)

                } match {
                  case (verificationResult, _) => verificationResult
                }
              }

              /*case p : ast.Predicate => {
                // TODO: this case will need updated when "unfolding in" is added; not applicable now but maybe in future
                val snap = v.decider.fresh(s"$id(${args.mkString(",")})", sorts.Snap)
                val ch = BasicChunk(PredicateID, BasicChunkIdentifier(p.name), args, snap, FullPerm())
                val s2 = s.copy(optimisticHeap = oh)
                chunkSupporter.produce(s2, s2.optimisticHeap, ch, v)((s3, oh2, v2) =>
                  Q(s.copy(optimisticHeap = oh2), snap, v2))
              }*/

              case _ => /* should never reach this case */
                createFailure(ve, v, s, "looking up chunk", true)
            }

          // this is the evalpc case for consume
          case _ if s.isImprecise && !addToOh && s.generateChecks =>
            resource match {
              case f: ast.Field => {
                v.decider.assertgv(s.isImprecise, args.head !== Null) {
                  case true => {
/*<<<<<<< HEAD
                    val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ), Option.when(withExp)(PUnknown()))
=======*/
                    val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ), Option.when(withExp)(PUnknown()))
                    if (SymbExLogger.enabled) {
                      // add chunk created by trying to find nonexistent chunk in imprecise state to snaps
                      val chonk = BasicChunk(FieldID, BasicChunkIdentifier(f.name), args, argsExp, snap, None, FullPerm, None)
                      SymbExLogger.populateSnaps(Vector(chonk), s)
                    }
//>>>>>>> upstream/master

                    val runtimeCheckAstNode: CheckPosition =
                      (s.methodCallAstNode, s.foldOrUnfoldAstNode, s.loopPosition, s.unfoldingAstNode) match {
                        case (None, None, None, None) => CheckPosition.GenericNode(runtimeCheckFieldTarget)
                        case (Some(methodCallAstNode), None, None, _) => CheckPosition.GenericNode(methodCallAstNode)
                        case (None, Some(foldOrUnfoldAstNode), None, _) => CheckPosition.GenericNode(foldOrUnfoldAstNode)
                        case (None, None, Some(loopPosition), _) => loopPosition
                        case (None, None, None, Some(unfoldingAstNode)) => CheckPosition.GenericNode(unfoldingAstNode)
                        case _ => sys.error("Conflicting positions found while adding runtime check!")
                      }

                    val (g, tH, tOH) = s.oldStore match {
                      /* Heap/OH part shouldn't be necessary based on currently functionality, but here for safety - JW */
                      case Some(g) => (g, s.h + s.oldHeaps(Verifier.PRE_HEAP_LABEL), s.optimisticHeap + s.oldHeaps(Verifier.PRE_OPTHEAP_LABEL))
                      case None => (s.g, s.h, s.optimisticHeap)
                    }
                    val translatedArgs: Seq[ast.Exp] =
                      args.map(tArg => new Translator(s.copy(g = g, h = tH, optimisticHeap = tOH), v.decider.pcs).translate(tArg) match {
                        case None => sys.error("Error translating! Exiting safely.")
                        case Some(expr) => expr
                      })

                    runtimeChecks.addChecks(runtimeCheckAstNode,
                      ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), Some(ast.FullPerm()()))(),
                      viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                        v.decider.pcs.branchConditionsAstNodes,
                        v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                      runtimeCheckFieldTarget,
                      s.forFraming)
                    runtimeCheckFieldTarget.addCheck(ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), Some(ast.FullPerm()()))())

                    Q(s.copy(madeOptimisticAssumptions = true), snap, v)
                  }

                  case false => createFailure(ve, v, s, "looking up chunk", true)

                } match {
                  case (verificationResult, _) => verificationResult
                }
              }

              /*case p: ast.Predicate => {
                // TODO: this case will need updated when "unfolding in" is added; not applicable now but maybe in future
                val snap = v.decider.fresh(s"$id(${args.mkString(",")})", sorts.Snap)
                Q(s, snap, v)
              }*/

              case _ => /* should never reach this case */
                createFailure(ve, v, s, "looking up chunk", true)
            }

          // this is the evalpc case for produce
          case _ if s.isImprecise && !addToOh && !s.generateChecks =>
            resource match {
              case f: ast.Field => {
/*<<<<<<< HEAD
                val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ), Option.when(withExp)(PUnknown()))
                val ch = BasicChunk(FieldID, BasicChunkIdentifier(f.name), args, argsExp, snap, None, FullPerm, None)
=======*/
                val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ), Option.when(withExp)(PUnknown()))
                val ch = BasicChunk(FieldID, BasicChunkIdentifier(f.name), args, argsExp, snap, None, FullPerm, None)
                if (SymbExLogger.enabled) {
                  // add chunk created by trying to find nonexistent chunk in imprecise state to snaps
                  SymbExLogger.populateSnaps(Vector(ch), s)
                }
//>>>>>>> upstream/master
                val s2 = s.copy(optimisticHeap = oh)

                if (!(s.needConditionFramingProduce &&
                      s.needConditionFramingUnfold)) {
                  profilingInfo.incrementEliminatedConjuncts
                }

                v.decider.assume(args.head !== Null, None)
                Q(s.copy(optimisticHeap = s2.optimisticHeap + ch, madeOptimisticAssumptions = true), snap, v)
              }

              /*case p: ast.Predicate => {
                // TODO: this case will need updated when "unfolding in" is added; not applicable now but maybe in future
                val snap = v.decider.fresh(s"$id(${args.mkString(",")})", sorts.Snap)
                Q(s, snap, v)
              }*/

              case _ => /* should never reach this case */
                createFailure(ve, v, s, "looking up chunk", true)
            }

          case _ =>
              createFailure(ve, v, s, "looking up chunk", true)
        }
      }
    }
  }


  def inHeap[CH <: NonQuantifiedChunk: ClassTag]
            (s: State,
             h: Heap,
             chunk: Iterable[Chunk],
             resource: ast.Resource,
             args: Seq[Term],
             v: Verifier)
            : Boolean = {

    val id = ChunkIdentifier(resource, s.program)

    //val tri: Iterable[Chunk] = h.values
  //  val relevantChunks = findChunksWithID[NonQuantifiedChunk](chunk, id)
  //  println(findChunkWithProver(relevantChunks, args, v))

    findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
        case Some(ch) if v.decider.check(IsPositive(ch.perm), Verifier.config.checkTimeout()) =>
        //  val relevantChunks = findChunksWithID[CH](h.values, id)
        //  println(relevantChunks)
          true
        case _ =>
          false
    }
  }


  def findChunk[CH <: NonQuantifiedChunk: ClassTag]
               (chunks: Iterable[Chunk],
                id: ChunkIdentifer,
                args: Iterable[Term],
                v: Verifier)
               : Option[CH] = {

    val relevantChunks = findChunksWithID[CH](chunks, id)
    findChunkLiterally(relevantChunks, args) orElse findChunkWithProver(relevantChunks, args, v)
  }

  def findChunksWithID[CH <: NonQuantifiedChunk: ClassTag](chunks: Iterable[Chunk], id: ChunkIdentifer): Iterable[CH] = {
    chunks.flatMap {
      case c: CH if id == c.id =>
          Some(c)
      case _ =>

          None
    }
  }

/** Extract the chunks with resource matching id.
 * Return two sequences of chunks -- one with resource id, and the
 * other with the remaining resources.
 */
  def splitHeap[CH <: NonQuantifiedChunk : ClassTag](h: Heap, id: ChunkIdentifer)
                                                   : (Seq[CH], Seq[Chunk]) = {

    var relevantChunks = Seq[CH]()
    var otherChunks = Seq[Chunk]()

    h.values foreach {
      case ch: CH if ch.id == id =>
        relevantChunks +:= ch
      case ch: QuantifiedChunk if ch.id == id =>
        sys.error(
          s"I did not expect quantified chunks on the heap for resource $id, "
            + s"but found $ch")
      case ch =>
        otherChunks +:= ch
    }

    (relevantChunks, otherChunks)
  }
  private def findChunkLiterally[CH <: NonQuantifiedChunk](chunks: Iterable[CH], args: Iterable[Term]) = {
    chunks find (ch => ch.args == args)
  }

  private def findChunkWithProver[CH <: NonQuantifiedChunk](chunks: Iterable[CH], args: Iterable[Term], v: Verifier) = {
    chunks find (ch =>
      args.size == ch.args.size &&
      v.decider.check(And(ch.args zip args map (x => x._1 === x._2)), Verifier.config.checkTimeout()))
  }
}
