// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import scala.reflect.ClassTag
import viper.silver.ast
import viper.silver.verifier.{VerificationError, PartialVerificationError}
import viper.silicon.Stack
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Failure, Success, VerificationResult}
import viper.silicon.resources.{NonQuantifiedPropertyInterpreter, Resources, FieldID, PredicateID}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{IsPositive, IsNonPositive, IsEpsilon}
import viper.silicon.supporters.Translator
import viper.silicon.utils
import viper.silicon.verifier.Verifier

trait ChunkSupportRules extends SymbolicExecutionRules {
  def consume(s: State,
              h: Heap,
              consolidate: Boolean,
              resource: ast.Resource,
              args: Seq[Term],
              perms: Term,
              ve: VerificationError,
              v: Verifier,
              description: String,
              isOpt: Boolean)
             (Q: (State, Heap, Term, Verifier, Boolean) => VerificationResult)
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
             pve: PartialVerificationError,
             ve: VerificationError,
             v: Verifier,
             generateChecks: Boolean = true)
            (Q: (State, Heap, Heap, Term, Verifier) => VerificationResult)
            : VerificationResult

  def inHeap[CH <: NonQuantifiedChunk: ClassTag]
            (h: Heap,
             chunk: Iterable[Chunk],
             resource: ast.Resource,
             args: Seq[Term],
             v: Verifier)
            : Boolean

  def permExceedsOne[CH <: NonQuantifiedChunk: ClassTag]
            (h: Heap,
             resource: ast.Resource,
             args: Seq[Term],
             v: Verifier,
             perm: Term)
            : Boolean


  def findChunk[CH <: NonQuantifiedChunk: ClassTag]
               (chunks: Iterable[Chunk],
                id: ChunkIdentifer,
                args: Iterable[Term],
                v: Verifier)
               : Option[CH]

  def findMatchingChunk[CH <: NonQuantifiedChunk: ClassTag]
                       (chunks: Iterable[Chunk],
                        chunk: CH,
                        v: Verifier)
                       : Option[CH]

  def findChunksWithID[CH <: NonQuantifiedChunk: ClassTag]
                      (chunks: Iterable[Chunk],
                       id: ChunkIdentifer)
                      : Iterable[CH]
}

object chunkSupporter extends ChunkSupportRules with Immutable {
  def consume(s: State,
              h: Heap,
              consolidate: Boolean,
              resource: ast.Resource,
              args: Seq[Term],
              perms: Term,
              ve: VerificationError,
              v: Verifier,
              description: String,
              isPre: Boolean) // Additional parameter is flag signaling whether we are consuming from precise heap or optimistic heap, maybe make field in Heap trait?
             (Q: (State, Heap, Term, Verifier, Boolean) => VerificationResult)
             : VerificationResult = {

      consume(s, h, consolidate, resource, args, perms, ve, v, isPre)((s1, h1, optSnap, v1) =>
        optSnap match {
          case Some(snap) =>
            Q(s1, h1, snap.convert(sorts.Snap), v1, true)

          case None =>
            /* Not having consumed anything could mean that we are in an infeasible
             * branch, or that the permission amount to consume was zero.
             * Returning a fresh snapshot in these cases should not lose any information.
             */

            val fresh = v1.decider.fresh(sorts.Snap)
            val s2 = s1.copy(functionRecorder = s1.functionRecorder.recordFreshSnapshot(fresh.applicable))
            Q(s2, h1, fresh, v1, false) // this being false
        })
  }

  private def consume(s: State,
                      h: Heap,
                      consolidate: Boolean,
                      resource: ast.Resource,
                      args: Seq[Term],
                      perms: Term,
                      ve: VerificationError,
                      v: Verifier,
                      isPre: Boolean) 
                     (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                     : VerificationResult = {
    var s1 = s.copy(h = h)
    if (consolidate) {
      s1 = stateConsolidator.consolidate(s.copy(h = h), v)
    }
    consumeGreedy(s1, s1.h, resource, args, perms, v, isPre) match {
      case (Complete(), s2, h2, optCh2) =>
        Q(s2.copy(h = s.h), h2, optCh2.map(_.snap), v)

      // should never reach this case
      case _ if v.decider.checkSmoke() =>
        Success()

      case (Incomplete(p), s2, h2, _) =>
        Q(s2.copy(h = s.h), h2, None, v)

    }
  }

  private def consumeGreedy(s: State,
                            h: Heap,
                            resource: ast.Resource,
                            args: Seq[Term],
                            perms: Term,
                            v: Verifier,
                            isPre: Boolean) = {

    val id = ChunkIdentifier(resource, Verifier.program)

    resource match {
      case f: ast.Field => {
      
        /* heap-rem-acc */
        val (newHeap, takenChunk, permDiff) = findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
          case Some(ch) if v.decider.check(IsEpsilon(ch.perm), Verifier.config.checkTimeout()) => {
            (h, None, perms)
          } 
          case Some(ch) => { 
            val toTake = PermMin(ch.perm, perms) // I don't know why Viper uses such a convoluted way to determine the necessary chunk.
            val newChunk = ch.withPerm(PermMinus(ch.perm, toTake))
            val takenChunk = Some(ch.withPerm(toTake))
            var newHeap = h - ch
            if (!v.decider.check(newChunk.perm === NoPerm(), Verifier.config.checkTimeout())) { 
              newHeap = newHeap + newChunk
            }
            
            if (v.decider.check(IsNonPositive(PermMinus(perms, toTake)), 0)) { // essentially what ConsumptionResult does
              (newHeap, takenChunk, NoPerm())
            }
            else {
              (h, None, PermMinus(perms, ch.perm))
            }
          }
          case _ => {
            (h, None, perms)
          }
        }

        var newH: Heap = newHeap.values.foldLeft(Heap()) { (currHeap, chunk) =>
          chunk match {
            case c: NonQuantifiedChunk => 

              // The term in checkgv uses infix notation I got from a different check to see if the args are equal - not CL
              var statusCheckgv = true

              if (id == c.id) {
                // TODO;staticprofiling: this is responsible for the static profiling issue, maybe - not CL
                statusCheckgv = v.decider.checkgv(s.isImprecise, And(c.args zip args map (x => x._1 === x._2)), Some(Verifier.config.checkTimeout())) match {
                  case (status, runtimeCheck) => status
                }
              }

              if ((id != c.id) || (!statusCheckgv)){ // if proven not equal, then continue to add to heap 
                currHeap + c
              }
              else if (v.decider.check(PermLess(permDiff, c.perm), Verifier.config.checkTimeout())) { // if perm < c.perm, then add to heap with diff
                /*
                As long as there are only chunks with permission epsilon inside the heap, we do not need an isPre flag 
                The isPre boolean flag is needed since when consuming from the optimistic heap, even if diff < ch.perm, we still want to remove full chunk
                from the optimistic heap as it doesn't preserve perm <= 1 invariant.
                */
                currHeap + c.withPerm(PermMinus(c.perm, permDiff)) 
              } else { // If perm >= c.perm, then remove it from the heap!
                currHeap
              }
            case _ => 
              currHeap
          }
        }

        takenChunk match {
          case Some(_) => (Complete(), s, newH, takenChunk)

          // case None if (v.decider.check(perms === NoPerm(), Verifier.config.checkTimeout())) => // for special case consume acc(x.f, 0/1)
          //   (Complete(), s, newH, None)

          case None => {
            var newH2: Heap = newH.values.foldLeft(Heap()) { (currHeap, chunk) =>
              chunk match {
                case c: NonQuantifiedChunk => // Potential small refactor? Change case to c: NonQuantifiedChunk if c.resourceID != FieldID
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
            (Incomplete(perms), s, newH2, None)
          }
        }
      }
    
      case p: ast.Predicate => {
        /* heap-rem-pred */
        findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
          case Some(ch) =>
            val toTake = PermMin(ch.perm, perms)
            val newChunk = ch.withPerm(PermMinus(ch.perm, toTake))
            val takenChunk = Some(ch.withPerm(toTake))
            var newHeap = h - ch
            if (!v.decider.check(newChunk.perm === NoPerm(), Verifier.config.checkTimeout())) {
              newHeap = newHeap + newChunk
            }
            (ConsumptionResult(PermMinus(perms, toTake), v, 0), s, newHeap, takenChunk)
          case None =>
            (Incomplete(perms), s, Heap(), None)
        }
      }
    }
  }

  def produce(s: State, h: Heap, ch: NonQuantifiedChunk, v: Verifier)
             (Q: (State, Heap, Verifier) => VerificationResult) = {
    // Try to merge the chunk into the heap by finding an alias.
    // In any case, property assumptions are added after the merge step.
    val (fr1, h1) = stateConsolidator.merge(s.functionRecorder, h, ch, v) 
    Q(s.copy(functionRecorder = fr1), h1, v)
  }

  def lookup(s: State,
             h: Heap,
             oh: Heap,
             addToOh: Boolean,
             resource: ast.Resource,
             runtimeCheckFieldTarget: ast.FieldAccess,
             args: Seq[Term],
             pve: PartialVerificationError,
             ve: VerificationError,
             v: Verifier,
             generateChecks: Boolean = true)
            (Q: (State, Heap, Heap, Term, Verifier) => VerificationResult)
            : VerificationResult = {
//    executionFlowController.tryOrFail2[Heap, Term](s.copy(h = h), v)((s1, v1, QS) => {
      val s1 = stateConsolidator.consolidate(s.copy(h = h, optimisticHeap = oh), v)
      val lookupFunction =
        if (s.isMethodVerification && Verifier.config.enableMoreCompleteExhale()) moreCompleteExhaleSupporter.lookupComplete _
        else lookupGreedy _
      lookupFunction(s1, s1.h, s1.optimisticHeap, addToOh, resource,
        runtimeCheckFieldTarget, args, pve, ve, v, generateChecks)((s2, tSnap, v1) =>
        Q(s2.copy(h = s.h, optimisticHeap = s.optimisticHeap), s2.h, s2.optimisticHeap, tSnap, v1))
//    })(Q)
  }

  private def lookupGreedy(s: State,
                           h: Heap,
                           oh: Heap,
                           addToOh: Boolean,
                           resource: ast.Resource,
                           runtimeCheckFieldTarget: ast.FieldAccess,
                           args: Seq[Term],
                           pve: PartialVerificationError,
                           ve: VerificationError,
                           v: Verifier,
                           generateChecks: Boolean)
                          (Q: (State, Term, Verifier) => VerificationResult)
                          : VerificationResult = {

    val id = ChunkIdentifier(resource, Verifier.program)

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
      case _ if v.decider.checkSmoke() =>

        profilingInfo.incrementEliminatedConjuncts

        Success()

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
                v.decider.assertgv(s.isImprecise, args.head !== Null()) {
                  case true =>
                    val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ))
                    val ch = BasicChunk(FieldID, BasicChunkIdentifier(f.name), args, snap, EpsilonPerm())
                    val s2 = s.copy(optimisticHeap = oh)

                    val runtimeCheckAstNode: CheckPosition =
                      (s2.methodCallAstNode, s2.foldOrUnfoldAstNode, s2.loopPosition) match {
                        case (None, None, None) => CheckPosition.GenericNode(runtimeCheckFieldTarget)
                        case (Some(methodCallAstNode), None, None) => CheckPosition.GenericNode(methodCallAstNode)
                        case (None, Some(foldOrUnfoldAstNode), None) => CheckPosition.GenericNode(foldOrUnfoldAstNode)
                        case (None, None, Some(loopPosition)) => loopPosition
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
                        ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), ast.EpsilonPerm()())(), // change this to check for epsilon perm ?
                        viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                          v.decider.pcs.branchConditionsAstNodes,
                          v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                        runtimeCheckFieldTarget,
                        s2.forFraming)
                      runtimeCheckFieldTarget.addCheck(ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), ast.EpsilonPerm()())())
                    }

                    v.decider.assume(args.head !== Null())

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
                    createFailure(ve, v, s, true).withLoad(args)

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
                createFailure(ve, v, s, true).withLoad(args)
            }

          // this is the evalpc case for consume
          case _ if s.isImprecise && !addToOh && s.generateChecks =>
            resource match {
              case f: ast.Field => {
                v.decider.assertgv(s.isImprecise, args.head !== Null()) {
                  case true => {
                    val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ))

                    val runtimeCheckAstNode: CheckPosition =
                      (s.methodCallAstNode, s.foldOrUnfoldAstNode, s.loopPosition) match {
                        case (None, None, None) => CheckPosition.GenericNode(runtimeCheckFieldTarget)
                        case (Some(methodCallAstNode), None, None) => CheckPosition.GenericNode(methodCallAstNode)
                        case (None, Some(foldOrUnfoldAstNode), None) => CheckPosition.GenericNode(foldOrUnfoldAstNode)
                        case (None, None, Some(loopPosition)) => loopPosition
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
                      ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), ast.EpsilonPerm()())(),
                      viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                        v.decider.pcs.branchConditionsAstNodes,
                        v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                      runtimeCheckFieldTarget,
                      s.forFraming)
                    runtimeCheckFieldTarget.addCheck(ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), ast.EpsilonPerm()())())

                    Q(s.copy(madeOptimisticAssumptions = true), snap, v)
                  }

                  case false => createFailure(ve, v, s, true).withLoad(args)

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
                createFailure(ve, v, s, true).withLoad(args)
            }

          // this is the evalpc case for produce
          case _ if s.isImprecise && !addToOh && !s.generateChecks =>
            resource match {
              case f: ast.Field => {
                val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ))
                val ch = BasicChunk(FieldID, BasicChunkIdentifier(f.name), args, snap, EpsilonPerm())
                val s2 = s.copy(optimisticHeap = oh)

                if (!(s.needConditionFramingProduce &&
                      s.needConditionFramingUnfold)) {
                  profilingInfo.incrementEliminatedConjuncts
                }

                v.decider.assume(args.head !== Null())
                Q(s.copy(optimisticHeap = s2.optimisticHeap + ch, madeOptimisticAssumptions = true), snap, v)
              }

              /*case p: ast.Predicate => {
                // TODO: this case will need updated when "unfolding in" is added; not applicable now but maybe in future
                val snap = v.decider.fresh(s"$id(${args.mkString(",")})", sorts.Snap)
                Q(s, snap, v)
              }*/

              case _ => /* should never reach this case */
                createFailure(ve, v, s, true).withLoad(args)
            }

          case _ =>
              createFailure(ve, v, s, true).withLoad(args)
        }
      }
    }
  }


  def inHeap[CH <: NonQuantifiedChunk: ClassTag]
            (h: Heap,
             chunk: Iterable[Chunk],
             resource: ast.Resource,
             args: Seq[Term],
             v: Verifier)
            : Boolean = {

    val id = ChunkIdentifier(resource, Verifier.program)

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

  def permExceedsOne[CH <: NonQuantifiedChunk: ClassTag]
            (h: Heap,
             resource: ast.Resource,
             args: Seq[Term],
             v: Verifier,
             perm: Term)
            : Boolean = {
    val id = ChunkIdentifier(resource, Verifier.program)
    
    val permSum = findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
      case Some(ch) =>
        PermPlus(ch.perm, perm)
      case None =>
        perm
    }

    if (v.decider.checkSmoke()) {
      false
    }
    else if (v.decider.check(PermLess(FullPerm(), permSum), Verifier.config.checkTimeout())) {
      // println(v.decider.pcs)
      // println(s"PermLess(FullPerm(), permSum) =  ${PermLess(FullPerm(), permSum)}")
      true
    }
    else {
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

  def findMatchingChunk[CH <: NonQuantifiedChunk: ClassTag]
                       (chunks: Iterable[Chunk], chunk: CH, v: Verifier): Option[CH] = {
    findChunk[CH](chunks, chunk.id, chunk.args, v)
  }

  def findChunksWithID[CH <: NonQuantifiedChunk: ClassTag](chunks: Iterable[Chunk], id: ChunkIdentifer): Iterable[CH] = {
    chunks.flatMap {
      case c: CH if id == c.id =>
          Some(c)
      case _ =>

          None
    }
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
