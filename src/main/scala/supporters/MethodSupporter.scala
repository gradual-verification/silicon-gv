// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import com.typesafe.scalalogging.Logger
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silver.verifier.errors._
import viper.silicon.interfaces._
import viper.silicon.decider.Decider
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.records.data.EndRecord
import viper.silicon.logger.records.data.WellformednessCheckRecord
import viper.silicon.rules.{consumer, executionFlowController, executor, wellFormedness}
import viper.silicon.state.{Heap, State, Store}
import viper.silicon.state.State.OldHeaps
import viper.silicon.verifier.{Verifier, VerifierComponent}
import viper.silicon.utils.freshSnap

/* TODO: Consider changing the DefaultMethodVerificationUnitProvider into a SymbolicExecutionRule */

trait MethodVerificationUnit extends VerificationUnit[ast.Method]

trait DefaultMethodVerificationUnitProvider extends VerifierComponent { v: Verifier =>
  def logger: Logger
  def decider: Decider

  object methodSupporter extends MethodVerificationUnit with StatefulComponent {
    import executor._
    import consumer._
    import wellFormedness._

    private var _units: Seq[ast.Method] = _

    def analyze(program: ast.Program): Unit = {
      _units = program.methods
    }

    def units = _units

    def verify(sInit: State, method: ast.Method): Seq[VerificationResult] = {
      logger.debug("\n\n" + "-" * 10 + " METHOD " + method.name + "-" * 10 + "\n")
      decider.prover.comment("%s %s %s".format("-" * 10, method.name, "-" * 10))
      SymbExLogger.openMemberScope(method, null, v.decider.pcs)
      val pres = method.pres
      val posts = method.posts

      val body = method.bodyOrAssumeFalse.toCfg()
        /* TODO: Might be worth special-casing on methods with empty bodies */

      val postViolated = (offendingNode: ast.Exp) => PostconditionViolated(offendingNode, method)

      val ins = method.formalArgs.map(_.localVar)
      val outs = method.formalReturns.map(_.localVar)

      val g = Store(   ins.map(x => (x, decider.fresh(x)))
                    ++ outs.map(x => (x, decider.fresh(x)))
                    ++ method.scopedDecls.collect { case l: ast.LocalVarDecl => l }.map(_.localVar).map(x => (x, decider.fresh(x))))

      val s = sInit.copy(isImprecise = false,
                         optimisticHeap = Heap(),
                         g = g,
                         h = Heap(),
                         oldHeaps = OldHeaps(),
                         methodCfg = body)


      if (Verifier.config.printMethodCFGs()) {
        viper.silicon.common.io.toFile(
          body.toDot,
          new java.io.File(s"${Verifier.config.tempDirectory()}/${method.name}.dot"))
      }

      val result =
        /* Combined the well-formedness check and the execution of the body, which are two separate
         * rules in Smans paper.
         */
         
        executionFlowController.locally(s, v)((s1, v1) => {
          wellformed(s1, freshSnap, pres, ContractNotWellformed(viper.silicon.utils.ast.BigAnd(pres)), v1)((s2, v2) => {
            v2.decider.prover.saturate(Verifier.config.z3SaturationTimeouts.afterContract)
            val s2a = s2.copy(oldHeaps = s2.oldHeaps + (Verifier.PRE_STATE_LABEL -> s2.h))
            (  executionFlowController.locally(s2a, v2)((s3, v3) => {
                  val s4 = s3.copy(isImprecise = false,
                                   optimisticHeap = Heap(),
                                   h = Heap())
                  val impLog = new WellformednessCheckRecord(posts, s, v.decider.pcs)
                  val sepIdentifier = SymbExLogger.currentLog().openScope(impLog)
                  wellformed(s4, freshSnap, posts, ContractNotWellformed(viper.silicon.utils.ast.BigAnd(posts)), v3)((_, v4) => {
                    SymbExLogger.currentLog().closeScope(sepIdentifier)
                    Success()})})
            && {
               executionFlowController.locally(s2a, v2)((s3, v3) => {
                  exec(s3, body, v3)((s4, v4) => {
                    val sepIdentifier = SymbExLogger.currentLog().openScope(new EndRecord(s4, v4.decider.pcs))
                    consumes(s4, posts, postViolated, v4)((s5, _, v5) => {
                      SymbExLogger.currentLog().closeScope(sepIdentifier)
                      // print final state here
                      // put logger debug here
                      v4.logger.debug(s"\nFINAL STATE OF METHOD ${method.name}")
                      v4.logger.debug(v4.stateFormatter.format(s5, v5.decider.pcs))
                      Success()
                    })
                  }) }) }  )})})

      SymbExLogger.closeMemberScope()
      Seq(result)
    }

    /* Lifetime */

    def start() {}

    def reset(): Unit = {
      _units = Seq.empty
    }

    def stop() {}
  }
}
