// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import scala.reflect.ClassTag
import viper.silver.ast
import viper.silver.verifier.VerificationError
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Failure, Success, VerificationResult}
import viper.silicon.resources.{NonQuantifiedPropertyInterpreter, Resources}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.perms.IsOne
import viper.silicon.verifier.Verifier

trait ChunkSupportRules extends SymbolicExecutionRules {
  def consume(s: State,
              h: Heap,
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
             resource: ast.Resource,
             args: Seq[Term],
             ve: VerificationError,
             v: Verifier)
            (Q: (State, Heap, Term, Verifier) => VerificationResult)
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
              resource: ast.Resource,
              args: Seq[Term],
              perms: Term,
              ve: VerificationError,
              v: Verifier,
              description: String)
             (Q: (State, Heap, Term, Verifier, Boolean) => VerificationResult)
             : VerificationResult = {

  //  heuristicsSupporter.tryOperation[Heap, Term](description)(s, h, v)((s1, h1, v1, QS) => {


      consume(s, h, resource, args, perms, ve, v)((s1, h1, optSnap, v1) =>
        optSnap match {
          case Some(snap) =>
            Q(s1, h1, snap.convert(sorts.Snap), v1, true)

          case None =>
            /* Not having consumed anything could mean that we are in an infeasible
             * branch, or that the permission amount to consume was zero.
             * Returning a fresh snapshot in these cases should not lose any information.
             */

            print("got here \n")
            val fresh = v1.decider.fresh(sorts.Snap)
            val s2 = s1.copy(functionRecorder = s1.functionRecorder.recordFreshSnapshot(fresh.applicable))
            Q(s2, h1, fresh, v1, false)
        })
//    })(Q)
  }

  private def consume(s: State,
                      h: Heap,
                      resource: ast.Resource,
                      args: Seq[Term],
                      perms: Term,
                      ve: VerificationError,
                      v: Verifier)
                     (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                     : VerificationResult = {

    val id = ChunkIdentifier(resource, Verifier.program)
/*    if (s.exhaleExt) {
      val failure = Failure(ve).withLoad(args)
      magicWandSupporter.transfer(s, perms, failure, v)(consumeGreedy(_, _, id, args, _, _))((s1, optCh, v1) =>
        Q(s1, h, optCh.flatMap(ch => Some(ch.snap)), v1))
    } else {
*/
//      executionFlowController.tryOrFail2[Heap, Option[Term]](s.copy(h = h), v)((s1, v1, QS) =>
/*        if (s.isMethodVerification && Verifier.config.enableMoreCompleteExhale()) {
          moreCompleteExhaleSupporter.consumeComplete(s1, s1.h, resource, args, perms, ve, v1)((s2, h2, snap2, v2) => {
            QS(s2.copy(h = s.h), h2, snap2, v2)
          })
        } else {
*/
    val s1 = stateConsolidator.consolidate(s.copy(h = h), v)
    consumeGreedy(s1, s1.h, id, args, perms, v) match {
      case (Complete(), s2, h2, optCh2) =>
        Q(s2.copy(h = s.h), h2, optCh2.map(_.snap), v)

      // they indicate this branch may be dead, what should we do with it? - J
      case _ if v.decider.checkSmoke() =>
        Success() // TODO: Mark branch as dead?

      case (Incomplete(p), s2, h2, None) =>
        Q(s2.copy(h = s.h), h2, None, v)

/*
      case _ =>
        createFailure(ve, v, s1, true).withLoad(args)
*/
    }
//        }
//      )(Q)
//    }
  }

  private def consumeGreedy(s: State,
                            h: Heap,
                            id: ChunkIdentifer,
                            args: Seq[Term],
                            perms: Term,
                            v: Verifier) = {
    // no longer used
    val consumeExact = terms.utils.consumeExactRead(perms, s.constrainableARPs)


    // no longer used
    def assumeProperties(chunk: NonQuantifiedChunk, heap: Heap) = {
      val interpreter = new NonQuantifiedPropertyInterpreter(heap.values, v)
      val resource = Resources.resourceDescriptions(chunk.resourceID)
      v.decider.assume(interpreter.buildPathConditionsForChunk(chunk, resource.instanceProperties))
    }

//    println("h")
//    h.values.foreach(chunk => print(chunk + "\n"))

/* the foldl portion of heap-rem
 * builds a new heap of chunks that definitely do not
 * contain the info to remove
 */
    var newH: Heap = h.values.foldLeft(Heap()) { (currHeap, chunk) =>
      chunk match {
        case c: NonQuantifiedChunk =>

            // The term in checkgv uses infix notation I got from a different check to see if the args are equal
          if ((id != c.id) || (!v.decider.checkgv(s.isImprecise, And(c.args zip args map (x => x._1 === x._2)), Verifier.config.checkTimeout()))){
                currHeap + c
          }
          else {
            currHeap
          }
      case _ =>
        currHeap
      }
    }

//    println("new chunk")
//    newH.values.foreach(chunk => print(chunk + "\n"))

    // tries to find the chunk in h
    findChunk[NonQuantifiedChunk](h.values, id, args, v) match {

      // I'm not sure if I need these checks but I included them to be safe - J
      case Some(ch) if v.decider.check(ch.perm === perms, Verifier.config.checkTimeout()) && v.decider.check(perms === FullPerm(), Verifier.config.checkTimeout()) =>
          (Complete(), s, newH, Some(ch))
/*
//          println("ch: " + ch.id)
//        if (consumeExact) {
          val toTake = PermMin(ch.perm, perms)
          val newChunk = ch.withPerm(PermMinus(ch.perm, toTake))
//          println("newchunk: " + newChunk.id)
          val takenChunk = Some(ch.withPerm(toTake))
          var newHeap = h - ch
          // I think this next line should only be for fractional perms
*          if (!v.decider.check(newChunk.perm === NoPerm(), Verifier.config.checkTimeout())) {
            newHeap = newHeap + newChunk
            assumeProperties(newChunk, newHeap)
          }
*
          (ConsumptionResult(PermMinus(perms, toTake), v, 0), s, newHeap, takenChunk)
*        } else {
          // we should never be in here
          if (v.decider.check(ch.perm !== NoPerm(), Verifier.config.checkTimeout())) {
            v.decider.assume(PermLess(perms, ch.perm))
            val newChunk = ch.withPerm(PermMinus(ch.perm, perms))
            val takenChunk = ch.withPerm(perms)
            val newHeap = h - ch + newChunk
            assumeProperties(newChunk, newHeap)
            (Complete(), s, newHeap, Some(takenChunk))
          } else {
            (Incomplete(perms), s, h, None)
          }
        }
*
*/
      case _ =>
        (Incomplete(perms), s, newH, None)



/*
      case None =>
        if (consumeExact && s.retrying && v.decider.check(perms === NoPerm(), Verifier.config.checkTimeout())) {
          (Complete(), s, h, None)
        } else {
          (Incomplete(perms), s, h, None)
        }
*/

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
             resource: ast.Resource,
             args: Seq[Term],
             ve: VerificationError,
             v: Verifier)
            (Q: (State, Heap, Term, Verifier) => VerificationResult)
            : VerificationResult = {
//    executionFlowController.tryOrFail2[Heap, Term](s.copy(h = h), v)((s1, v1, QS) => {
      val s1 = stateConsolidator.consolidate(s.copy(h = h), v)
      val lookupFunction =
        if (s.isMethodVerification && Verifier.config.enableMoreCompleteExhale()) moreCompleteExhaleSupporter.lookupComplete _
        else lookupGreedy _
      lookupFunction(s1, s1.h, resource, args, ve, v)((s2, tSnap, v1) =>
        Q(s2.copy(h = s.h), s2.h, tSnap, v1))
//    })(Q)
  }

  private def lookupGreedy(s: State,
                           h: Heap,
                           resource: ast.Resource,
                           args: Seq[Term],
                           ve: VerificationError,
                           v: Verifier)
                          (Q: (State, Term, Verifier) => VerificationResult)
                          : VerificationResult = {

    val id = ChunkIdentifier(resource, Verifier.program)

    findChunk[NonQuantifiedChunk](h.values, id, args, v) match {
      case Some(ch) if v.decider.check(IsPositive(ch.perm), Verifier.config.checkTimeout()) =>
        Q(s, ch.snap, v)
      case _ if v.decider.checkSmoke() =>
        Success() // TODO: Mark branch as dead?
      case _ =>
        createFailure(ve, v, s, true).withLoad(args)
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
        case Some(ch) if v.decider.check(IsOne(ch.perm), Verifier.config.checkTimeout()) =>
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
