// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.verifier

import java.util.concurrent._
import org.apache.commons.pool2.{BasePooledObjectFactory, ObjectPool, PoolUtils, PooledObject}
import org.apache.commons.pool2.impl.{DefaultPooledObject, GenericObjectPool, GenericObjectPoolConfig}
import viper.silicon.Config
import viper.silicon.interfaces.VerificationResult
import viper.silver.components.StatefulComponent
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.terms.{Decl, Term}

class VerificationPoolManager(primary: PrimaryVerifier) extends StatefulComponent {
  private val numberOfSecondaryVerifiers: Int = Verifier.config.numberOfParallelVerifiers()

  /*private*/ var secondaryVerifiers: Seq[SecondaryVerifier] = _
  /*private*/ var secondaryVerifierExecutor: ExecutorService = _
  /*private*/ var secondaryVerifierPool: ObjectPool[SecondaryVerifier] = _

  /* private */ var runningVerificationTasks: ConcurrentHashMap[AnyRef, Boolean] = _

  private[verifier] object pooledVerifiers extends ProverLike {
    def emit(content: String): Unit = secondaryVerifiers foreach (_.decider.prover.emit(content))
    def assume(term: Term): Unit = secondaryVerifiers foreach (_.decider.prover.assume(term))
    def declare(decl: Decl): Unit =  secondaryVerifiers foreach (_.decider.prover.declare(decl))
    def comment(content: String): Unit = secondaryVerifiers foreach (_.decider.prover.comment(content))

    def saturate(data: Option[Config.Z3StateSaturationTimeout]): Unit =
      secondaryVerifiers foreach (_.decider.prover.saturate(data))

    def saturate(timeout: Int, comment: String): Unit =
      secondaryVerifiers foreach (_.decider.prover.saturate(timeout, comment))
  }

  /* Verifier pool management */

  private def setupSecondaryVerifierPool(): Unit = {
    secondaryVerifiers = Vector.empty
    runningVerificationTasks = new ConcurrentHashMap()

    val poolConfig: GenericObjectPoolConfig[SecondaryVerifier] = new GenericObjectPoolConfig()
    poolConfig.setMaxTotal(numberOfSecondaryVerifiers)
    poolConfig.setMaxIdle(numberOfSecondaryVerifiers) /* Prevent pool from shutting down idle Z3 instances */
    poolConfig.setBlockWhenExhausted(true)

    val factory = PoolUtils.synchronizedPooledFactory(secondaryVerifierPoolableObjectFactory)

    secondaryVerifierPool =
    //    PoolUtils.synchronizedPool(
    new GenericObjectPool[SecondaryVerifier](factory, poolConfig)
    //    )

    PoolUtils.prefill(secondaryVerifierPool, poolConfig.getMaxTotal)
    //  Thread.sleep(2000)

    assert(secondaryVerifiers.length == poolConfig.getMaxTotal)
    secondaryVerifiers foreach (_.start())

    secondaryVerifierExecutor = Executors.newFixedThreadPool(poolConfig.getMaxTotal)
//    secondaryVerifierExecutor = Executors.newWorkStealingPool(poolConfig.getMaxTotal)
  }

  private def resetSecondaryVerifierPool(): Unit = {
    secondaryVerifiers foreach (_.reset())

    runningVerificationTasks.clear()
  }

  private def teardownSecondaryVerifierPool(): Unit = {
    if (secondaryVerifiers != null) {
      secondaryVerifiers foreach (_.stop())

      secondaryVerifierExecutor.shutdown()
      secondaryVerifierExecutor.awaitTermination(10, TimeUnit.SECONDS)
    }

    if (secondaryVerifierPool != null) {
      secondaryVerifierPool.close()
    }
  }

  private object secondaryVerifierPoolableObjectFactory extends BasePooledObjectFactory[SecondaryVerifier] {
    def create(): SecondaryVerifier = {
      val secondary = new SecondaryVerifier(primary, primary.nextUniqueVerifierId(), primary.reporter)
      secondaryVerifiers = secondary +: secondaryVerifiers

      secondary
    }

    def wrap(arg: SecondaryVerifier): PooledObject[SecondaryVerifier] = new DefaultPooledObject(arg)
  }

  /* Verification task management */

  private final class SecondaryBorrowingVerificationTask(task: SecondaryVerifier => Seq[VerificationResult])
      extends Callable[Seq[VerificationResult]] {

    def call(): Seq[VerificationResult] = {
      var secondary: SecondaryVerifier = null

      try {
        secondary = secondaryVerifierPool.borrowObject()

        task(secondary)
      } finally {
        if (secondary != null) {
          secondaryVerifierPool.returnObject(secondary)
        }
      }
    }
  }

  def queueVerificationTask(task: SecondaryVerifier => Seq[VerificationResult])
                           : Future[Seq[VerificationResult]] = {

    secondaryVerifierExecutor.submit(new SecondaryBorrowingVerificationTask(task))
  }

  /* Lifetime */

  def start(): Unit = {
    setupSecondaryVerifierPool()
  }

  def reset(): Unit = {
    resetSecondaryVerifierPool()
  }

  def stop(): Unit = {
    teardownSecondaryVerifierPool()
  }
}
