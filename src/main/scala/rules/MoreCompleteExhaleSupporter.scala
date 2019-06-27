// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import scala.collection.mutable.ListBuffer
import viper.silicon.SymbExLogger
import viper.silicon.interfaces.state._
import viper.silicon.interfaces.{Failure, Success, VerificationResult}
import viper.silicon.resources.{NonQuantifiedPropertyInterpreter, Resources}
import viper.silicon.rules.chunkSupporter.findChunksWithID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.{IsNonPositive, IsPositive}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.VerificationError

object moreCompleteExhaleSupporter extends Immutable {
  private def summarise(s: State,
                        relevantChunks: Seq[NonQuantifiedChunk],
                        resource: ast.Resource,
                        args: Seq[Term],
                        v: Verifier)
                       : (Var, Seq[Term], Term) = {

    val sort: Sort =
      resource match {
        case f: ast.Field => v.symbolConverter.toSort(f.typ)
        case _: ast.Predicate => sorts.Snap
        case _: ast.MagicWand => sorts.Snap
      }

    val summarisingSnapshot = v.decider.fresh(sort)
    var summarisingSnapshotDefinition: Seq[Term] = Vector.empty
    var permissionSum: Term = NoPerm()

    relevantChunks.foreach(ch => {
      val argumentEqualities =
        And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })

      summarisingSnapshotDefinition :+=
        Implies(And(argumentEqualities, IsPositive(ch.perm)), summarisingSnapshot === ch.snap)

      permissionSum =
        PermPlus(permissionSum, Ite(argumentEqualities, ch.perm, NoPerm()))
    })

    (summarisingSnapshot, summarisingSnapshotDefinition, permissionSum)
  }

  def lookupComplete(s: State,
                     h: Heap,
                     resource: ast.Resource,
                     args: Seq[Term],
                     ve: VerificationError,
                     v: Verifier)
                    (Q: (State, Term, Verifier) => VerificationResult)
                    : VerificationResult = {

    val id = ChunkIdentifier(resource, Verifier.program)
    val relevantChunks = findChunksWithID[NonQuantifiedChunk](h.values, id).toSeq

    if (relevantChunks.isEmpty) {
      if (v.decider.checkSmoke()) {
        Success() // TODO: Mark branch as dead?
      } else {
        Failure(ve).withLoad(args)
      }
    } else {
      val (snap, snapDef, pSum) = summarise(s, relevantChunks, resource, args, v)

      v.decider.assert(IsPositive(pSum)) {
        case true =>
          v.decider.assume(And(snapDef))
          val fr1 = s.functionRecorder.recordFreshSnapshot(snap.applicable)
          val s1 = s.copy(functionRecorder = fr1)
          Q(s1, snap, v)
        case false =>
          Failure(ve).withLoad(args)
      }
    }
  }

  def consumeComplete(s: State,
                      h: Heap,
                      resource: ast.Resource,
                      args: Seq[Term],
                      perms: Term,
                      ve: VerificationError,
                      v: Verifier)
                     (Q: (State, Heap, Option[Term], Verifier) => VerificationResult)
                     : VerificationResult = {

    val id = ChunkIdentifier(resource, Verifier.program)
    val relevantChunks = ListBuffer[NonQuantifiedChunk]()
    val otherChunks = ListBuffer[Chunk]()
    h.values foreach {
      case c: NonQuantifiedChunk if id == c.id => relevantChunks.append(c)
      case ch => otherChunks.append(ch)
    }

    if (relevantChunks.isEmpty) {
      // if no permission is exhaled, return none
      if (v.decider.check(perms === NoPerm(), Verifier.config.checkTimeout())) {
        Q(s, h, None, v)
      } else {
        Failure(ve).withLoad(args)
      }
    } else {
      val consumeExact = terms.utils.consumeExactRead(perms, s.constrainableARPs)

      var pNeeded = perms
      var pSum: Term = NoPerm()
      val newChunks = ListBuffer[NonQuantifiedChunk]()
      var moreNeeded = true

      val definiteAlias = chunkSupporter.findChunk[NonQuantifiedChunk](relevantChunks, id, args, v)

      val sortFunction: (NonQuantifiedChunk, NonQuantifiedChunk) => Boolean = (ch1, ch2) => {
        // The definitive alias and syntactic aliases should get priority, since it is always
        // possible to consume from them
        definiteAlias.contains(ch1) || !definiteAlias.contains(ch2) && ch1.args == args
      }

      relevantChunks.sortWith(sortFunction) foreach { ch =>
        if (moreNeeded) {
          val eq = And(ch.args.zip(args).map { case (t1, t2) => t1 === t2 })
          pSum = PermPlus(pSum, Ite(eq, ch.perm, NoPerm()))
          val pTakenBody = Ite(eq, PermMin(ch.perm, pNeeded), NoPerm())
          val pTakenMacro = v.decider.freshMacro("complete_pTaken", Seq(), pTakenBody)
          val pTaken = App(pTakenMacro, Seq())
          SymbExLogger.currentLog().addMacro(pTaken, pTakenBody)
          val newChunk = ch.withPerm(PermMinus(ch.perm, pTaken))
          pNeeded = PermMinus(pNeeded, pTaken)

          if (!v.decider.check(IsNonPositive(newChunk.perm), Verifier.config.splitTimeout())) {
            newChunks.append(newChunk)
          }

          val toCheck = if (consumeExact) pNeeded === NoPerm() else IsPositive(pSum)
          moreNeeded = !v.decider.check(toCheck, Verifier.config.splitTimeout())
        } else {
          newChunks.append(ch)
        }
      }

      val allChunks = otherChunks ++ newChunks
      val interpreter = new NonQuantifiedPropertyInterpreter(allChunks, v)
      newChunks foreach { ch =>
        val resource = Resources.resourceDescriptions(ch.resourceID)
        v.decider.assume(interpreter.buildPathConditionsForChunk(ch, resource.instanceProperties))
      }

      val newHeap = Heap(allChunks)
      val (snap, snapDefs, _) = summarise(s, relevantChunks, resource, args, v)

      if (!moreNeeded) {
        if (!consumeExact) {
          v.decider.assume(PermLess(perms, pSum))
        }
        v.decider.assume(And(snapDefs))
        Q(s, newHeap, Some(snap), v)
      } else {
        val toAssert = if (consumeExact) pNeeded === NoPerm() else IsPositive(pSum)
        v.decider.assert(toAssert) {
          case true =>
            if (!consumeExact) {
              v.decider.assume(PermLess(perms, pSum))
            }
            v.decider.assume(And(snapDefs))
            Q(s, newHeap, Some(snap), v)
          case false =>
            Failure(ve).withLoad(args)
        }
      }
    }
  }
}