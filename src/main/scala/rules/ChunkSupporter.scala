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
import viper.silicon.state.terms.perms.IsPositive
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
              description: String)
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
              description: String)
             (Q: (State, Heap, Term, Verifier, Boolean) => VerificationResult)
             : VerificationResult = {

      consume(s, h, consolidate, resource, args, perms, ve, v)((s1, h1, optSnap, v1) =>
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
            Q(s2, h1, fresh, v1, false)
        })
  }

  private def consume(s: State,
                      h: Heap,
                      consolidate: Boolean,
                      resource: ast.Resource,
                      args: Seq[Term],
                      perms: Term,
                      ve: VerificationError,
                      v: Verifier)
                     (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                     : VerificationResult = {
    var s1 = s.copy(h = h)
    if (consolidate)
      s1 = stateConsolidator.consolidate(s.copy(h = h), v)
    consumeGreedy(s1, s1.h, resource, args, perms, v) match {
      case (Complete(), s2, h2, optCh2) =>
        Q(s2.copy(h = s.h), h2, optCh2.map(_.snap), v)

      // should never reach this case
      case _ if v.decider.checkSmoke() =>
        Success()

      case (Incomplete(p), s2, h2, None) =>
        Q(s2.copy(h = s.h), h2, None, v)

    }
  }

  private def consumeGreedy(s: State,
                            h: Heap,
                            resource: ast.Resource,
                            args: Seq[Term],
                            perms: Term,
                            v: Verifier) = {

    val id = ChunkIdentifier(resource, Verifier.program)

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
          case Some(ch) if v.decider.check(ch.perm === perms, Verifier.config.checkTimeout()) && v.decider.check(perms === FullPerm(), Verifier.config.checkTimeout()) =>
            (Complete(), s, newH, Some(ch))

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
            (Incomplete(perms), s, newH2, None)
          }
        }
      }

      case p: ast.Predicate => {
        /* heap-rem-pred */
        findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
          case Some(ch) if v.decider.check(ch.perm === perms, Verifier.config.checkTimeout()) && v.decider.check(perms === FullPerm(), Verifier.config.checkTimeout()) =>
            var newH = h - ch
            (Complete(), s, newH, Some(ch))
          case _ =>
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

        Q(s, ch.snap, v)

      // should never reach this case
      // TODO: ASK JENNA; err, we ARE reaching this case... is this a problem?
      case _ if v.decider.checkSmoke() =>

        profilingInfo.incrementEliminatedConjuncts

        Success()

      case _ => {
        findChunk[NonQuantifiedChunk](oh.values, id, args, v) match {
          case Some(ch) if v.decider.check(IsPositive(ch.perm), Verifier.config.checkTimeout()) =>

            profilingInfo.incrementEliminatedConjuncts

            Q(s, ch.snap, v)

          // this is the eval case for adding runtime checks
          case _ if s.isImprecise && addToOh =>
            resource match {
              case f: ast.Field => {
                val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ))
                val ch = BasicChunk(FieldID, BasicChunkIdentifier(f.name), args, snap, FullPerm())
                val s2 = s.copy(optimisticHeap = oh)

                val runtimeCheckAstNode: CheckPosition =
                  (s2.methodCallAstNode, s2.foldOrUnfoldAstNode, s2.loopPosition) match {
                    case (None, None, None) => CheckPosition.GenericNode(runtimeCheckFieldTarget)
                    case (Some(methodCallAstNode), None, None) => CheckPosition.GenericNode(methodCallAstNode)
                    case (None, Some(foldOrUnfoldAstNode), None) => CheckPosition.GenericNode(foldOrUnfoldAstNode)
                    case (None, None, Some(loopPosition)) => loopPosition
                    case _ => sys.error("Conflicting positions found while adding runtime check!")
                  }

                val (g, tH, tOH) = s2.oldStore match { /* this match sequence shouldn't be necessary based on currently functionality, but here for safety - JW */
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
                    ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), ast.FullPerm()())(),
                    viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                      v.decider.pcs.branchConditionsAstNodes,
                      v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                    runtimeCheckFieldTarget,
                    s2.forFraming)
                  runtimeCheckFieldTarget.addCheck(ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), ast.FullPerm()())())
                }

                chunkSupporter.produce(s2, s2.optimisticHeap, ch, v)((s3, oh2, v2) =>
                  Q(s.copy(optimisticHeap = oh2), snap, v2))
              }

              // TODO: ASK JENNA; should we be counting conjuncts here?
              case p : ast.Predicate => {
                val snap = v.decider.fresh(s"$id(${args.mkString(",")})", sorts.Snap)
                val ch = BasicChunk(PredicateID, BasicChunkIdentifier(p.name), args, snap, FullPerm())
                val s2 = s.copy(optimisticHeap = oh)
                chunkSupporter.produce(s2, s2.optimisticHeap, ch, v)((s3, oh2, v2) =>
                  Q(s.copy(optimisticHeap = oh2), snap, v2))
              }

              case _ => /* should never reach this case */
                createFailure(ve, v, s, true).withLoad(args)
            }
          // this is the evalpc (consume) case for adding runtime checks
          case _ if s.isImprecise && !addToOh && s.generateChecks =>
            resource match {
              case f: ast.Field => {
                val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ))

                if (generateChecks) {
                // This resolves positional information for the run-time check, and saves it to a 
                // variable to later be attached to the run-time check. It is enumerating all the 
                // possible sources and cases that could be involved in determining the right position 
                // for the check.
                  val runtimeCheckAstNode: CheckPosition =
                    (s.methodCallAstNode, s.foldOrUnfoldAstNode, s.loopPosition) match {
                      case (None, None, None) => CheckPosition.GenericNode(runtimeCheckFieldTarget)
                      case (Some(methodCallAstNode), None, None) => CheckPosition.GenericNode(methodCallAstNode)
                      case (None, Some(foldOrUnfoldAstNode), None) => CheckPosition.GenericNode(foldOrUnfoldAstNode)
                      case (None, None, Some(loopPosition)) => loopPosition
                      case _ => sys.error("Conflicting positions found while adding runtime check!")
                    }

                  val (g, tH, tOH) = s.oldStore match { /* Heap/OH part shouldn't be necessary based on currently functionality, but here for safety - JW */
                    case Some(g) => (g, s.h + s.oldHeaps(Verifier.PRE_HEAP_LABEL), s.optimisticHeap + s.oldHeaps(Verifier.PRE_OPTHEAP_LABEL))
                    case None => (s.g, s.h, s.optimisticHeap)
                  }
                // the `Seq[ast.Exp]` should be thought of as a conjunction of a bunch of formula terms
                  val translatedArgs: Seq[ast.Exp] =
                    args.map(tArg => new Translator(s.copy(g = g, h = tH, optimisticHeap = tOH), v.decider.pcs).translate(tArg) match {
                      case None => sys.error("Error translating! Exiting safely.")
                      case Some(expr) => expr
                    })
                    // This generates the check. The first argument is the position we found, the second 
                    // is the run-time check we need at that program point. The third is branching 
                    // information needed by the frontend to correctly determine, at run-time, when the 
                    // check should be done (it should only be done down the specific branch on which it 
                    // was generated). The fourth argument provides additional positioning information 
                    // to the frontend, and the last argument provides information to the frontend on 
                    // whether this check was a framing check: this allows for more efficient run-time 
                    // checks to be inserted into the generated C0 program by the frontend.
                  runtimeChecks.addChecks(runtimeCheckAstNode,
                    ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), ast.FullPerm()())(),
                    viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                      v.decider.pcs.branchConditionsAstNodes,
                      v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                    runtimeCheckFieldTarget,
                    s.forFraming)
                  runtimeCheckFieldTarget.addCheck(ast.FieldAccessPredicate(ast.FieldAccess(translatedArgs.head, f)(), ast.FullPerm()())())
              }
                Q(s.copy(madeOptimisticAssumptions = true), snap, v)
              }
              case p: ast.Predicate => {
                val snap = v.decider.fresh(s"$id(${args.mkString(",")})", sorts.Snap)
                Q(s, snap, v)
              }
              case _ => /* should never reach this case */
                createFailure(ve, v, s, true).withLoad(args)
            }

          // this is the evalpc case (produce) for NOT adding runtime checks
          /* addtoOh         : determines whether or not to add a fresh heap chunk to the optimistic heap 
                               and also says whether lookup is called from eval-pc or eval
             s.generateChecks: flag that tells us whether or not we are in produce or consume from eval-pc
                               — the flag is false if coming from a produce and true if coming from anything else
          */
          case _ if s.isImprecise && addToOh && !s.generateChecks =>
            resource match {
              case f : ast.Field => {
                val snap = v.decider.fresh(s"${args.head}.$id", v.symbolConverter.toSort(f.typ))
                val ch = BasicChunk(FieldID, BasicChunkIdentifier(f.name), args, snap, FullPerm())
                val s1 = s.copy(madeOptimisticAssumptions = false)
                val s2 = s1.copy(optimisticHeap = oh)

                // ? Probably not needed here
                val (g, tH, tOH) = s.oldStore match {
                    case Some(g) => (g, s.h + s.oldHeaps(Verifier.PRE_HEAP_LABEL), s.optimisticHeap + s.oldHeaps(Verifier.PRE_OPTHEAP_LABEL))
                    case None => (s.g, s.h, s.optimisticHeap)
                  }

                if(!(s.madeOptimisticAssumptions && 
                     s.needConditionFramingProduce && 
                     s.needConditionFramingUnfold)) {
                  profilingInfo.incrementEliminatedConjuncts
                }

                chunkSupporter.produce(s2, s2.optimisticHeap, ch, v)((s3, oh2, v2) =>
                  Q(s2.copy(optimisticHeap = oh2), snap, v2))
              }
              case p : ast.Predicate => {
                val snap = v.decider.fresh(s"$id(${args.mkString(",")})", sorts.Snap)
                val ch = BasicChunk(PredicateID, BasicChunkIdentifier(p.name), args, snap, FullPerm())
                val s2 = s.copy(optimisticHeap = oh)
                // TODO: Probably not necessary (reevaluate when `unfolding in` is added)
                chunkSupporter.produce(s2, s2.optimisticHeap, ch, v)((s3, oh2, v2) =>
                  Q(s.copy(optimisticHeap = oh2), snap, v2))
              }
            }
          }
          case _ => /* should never reach this case */
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
