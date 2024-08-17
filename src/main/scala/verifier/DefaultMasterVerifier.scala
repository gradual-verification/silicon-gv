// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.verifier

import java.text.SimpleDateFormat
import java.util.concurrent._
import scala.util.Random
import viper.silver.ast
import viper.silver.components.StatefulComponent
import viper.silicon._
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.SMTLib2PreambleReader
import viper.silicon.interfaces._
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.reporting.{MultiRunRecorders, condenseToViperResult}
import viper.silicon.rules.executionFlowController
import viper.silicon.state._
import viper.silicon.state.terms.{Decl, Sort, Term, sorts}
import viper.silicon.supporters._
import viper.silicon.supporters.functions.DefaultFunctionVerificationUnitProvider
import viper.silicon.supporters.qps._
import viper.silicon.utils.Counter
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.cfg.silver.SilverCfg
import viper.silver.plugin.PluginAwareReporter
import viper.silver.reporter.{ConfigurationConfirmation, VerificationResultMessage}

/* TODO: Extract a suitable MasterVerifier interface, probably including
 *         - def verificationPoolManager: VerificationPoolManager)
 *         - def uniqueIdCounter: String)
 */

trait MasterVerifier extends Verifier {
  def nextUniqueVerifierId(): String
  def verificationPoolManager: VerificationPoolManager
}

class DefaultMasterVerifier(config: Config, override val reporter: PluginAwareReporter)
    extends BaseVerifier(config, "00")
       with MasterVerifier
       with DefaultFunctionVerificationUnitProvider
       with DefaultPredicateVerificationUnitProvider {

  Verifier.config = config

  private val uniqueIdCounter = new Counter(1)
  def nextUniqueVerifierId(): String = f"${uniqueIdCounter.next()}%02d"

  protected val preambleReader = new SMTLib2PreambleReader

//  protected val sequencesContributor = new DefaultSequencesContributor(domainTranslator, config)
//  protected val setsContributor = new DefaultSetsContributor(domainTranslator, config)
//  protected val multisetsContributor = new DefaultMultisetsContributor(domainTranslator, config)
//  protected val domainsContributor = new DefaultDomainsContributor(symbolConverter, domainTranslator)
  protected val fieldValueFunctionsContributor = new DefaultFieldValueFunctionsContributor(preambleReader, symbolConverter, termConverter, config)
  protected val predSnapGenerator = new PredicateSnapGenerator(symbolConverter, snapshotSupporter)
  protected val predicateAndWandSnapFunctionsContributor = new DefaultPredicateAndWandSnapFunctionsContributor(preambleReader, termConverter, predSnapGenerator, config)

  // coworker verifiers in _coworkerVerificationPoolManager execute branches in parallel,
  // while worker verifiers in _workerVerificationPoolManager execute methods or cfg in parallel
  private val _coworkerVerificationPoolManager: VerificationPoolManager = new VerificationPoolManager(this)
  private val _workerVerificationPoolManager: VerificationPoolManager = new VerificationPoolManager(this)

  def verificationPoolManager: VerificationPoolManager = _coworkerVerificationPoolManager

  private val statefulSubcomponents = List[StatefulComponent](
    uniqueIdCounter,
  //  sequencesContributor, setsContributor, domainsContributor,
    fieldValueFunctionsContributor,
    predSnapGenerator, predicateAndWandSnapFunctionsContributor,
    functionsSupporter, predicateSupporter,
    _coworkerVerificationPoolManager,
    _workerVerificationPoolManager,
    MultiRunRecorders /* In lieu of a better place, include MultiRunRecorders singleton here */
  )

  /* Lifetime */

  override def start() {
    super.start()
    statefulSubcomponents foreach (_.start())
  }

  override def reset() {
    super.reset()
    statefulSubcomponents foreach (_.reset())
  }

  override def stop() {
    super.stop()
    statefulSubcomponents foreach (_.stop())
  }

  /* Verifier orchestration */

  private object allProvers extends ProverLike {
    def emit(content: String): Unit = {
      decider.prover.emit(content)
      _coworkerVerificationPoolManager.pooledVerifiers.emit(content)
      _workerVerificationPoolManager.pooledVerifiers.emit(content)
    }

    def assume(term: Term): Unit = {
      decider.prover.assume(term)
      _coworkerVerificationPoolManager.pooledVerifiers.assume(term)
      _workerVerificationPoolManager.pooledVerifiers.assume(term)
    }

    def declare(decl: Decl): Unit = {
      decider.prover.declare(decl)
      _coworkerVerificationPoolManager.pooledVerifiers.declare(decl)
      _workerVerificationPoolManager.pooledVerifiers.declare(decl)
    }

    def comment(content: String): Unit = {
      decider.prover.comment(content)
      _coworkerVerificationPoolManager.pooledVerifiers.comment(content)
      _workerVerificationPoolManager.pooledVerifiers.comment(content)
    }

    def saturate(timeout: Int, comment: String): Unit = {
      decider.prover.saturate(timeout, comment)
      _coworkerVerificationPoolManager.pooledVerifiers.saturate(timeout, comment)
      _workerVerificationPoolManager.pooledVerifiers.saturate(timeout, comment)
    }

    def saturate(data: Option[Config.Z3StateSaturationTimeout]): Unit = {
      decider.prover.saturate(data)
      _coworkerVerificationPoolManager.pooledVerifiers.saturate(data)
      _workerVerificationPoolManager.pooledVerifiers.saturate(data)
    }
  }

  /* Program verification */

  def verify(_program: ast.Program, cfgs: Seq[SilverCfg]): List[VerificationResult] = {
    /** Trigger computation is currently not thread-safe; hence, all triggers are computed
      * up-front, before the program is verified in parallel.
      * This is done bottom-up to ensure that nested quantifiers are transformed as well
      * (top-down should also work, but the default of 'innermost' won't).
      * See also [[viper.silicon.utils.ast.autoTrigger]].
      */
    val program =
      _program.transform({
        case forall: ast.Forall if forall.isPure =>
          viper.silicon.utils.ast.autoTrigger(forall, forall.autoTrigger)
        case exists: ast.Exists =>
          viper.silicon.utils.ast.autoTrigger(exists, exists.autoTrigger)
      }, Traverse.BottomUp)

    // TODO: Autotrigger for cfgs.

    if (config.printTranslatedProgram()) {
      println(program)
    }

    Verifier.program = program

    predSnapGenerator.setup(program) // TODO: Why did Nadja put this here?


    allProvers.comment("Started: " + new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(System.currentTimeMillis()) /*bookkeeper.formattedStartTime*/)
    allProvers.comment("Silicon.version: " + Silicon.version)
    allProvers.comment(s"Input file: ${Verifier.inputFile.getOrElse("<unknown>")}")
    allProvers.comment(s"Verifier id: $uniqueId")
    allProvers.comment("-" * 60)
    allProvers.comment("Begin preamble")

    allProvers.comment("/" * 10 + " Static preamble")
    emitStaticPreamble(allProvers)

    analyzeProgramAndEmitPreambleContributions(program, allProvers) // TODO: Add support for cfgs.

    allProvers.comment("End preamble")
    allProvers.comment("-" * 60)

    allProvers.saturate(config.z3SaturationTimeouts.afterPrelude)


    SymbExLogger.resetMemberList()
    SymbExLogger.setConfig(config)

    /* TODO: A workaround for Silver issue #94. toList must be before flatMap.
     *       Otherwise Set will be used internally and some error messages will be lost.
     */
    val functionVerificationResults = functionsSupporter.units.toList flatMap (function => {
      val s = createInitialState(function, program)
      val startTime = System.currentTimeMillis()
      // making declarations of local variable pushed and popped,
      // so that they won't be kept in the bottom of Z3
      val results = Seq(executionFlowController.locally(s, this)((_, _) => {
        val verificationResults = this.functionsSupporter.verify(s, function)
        verificationResults.head
      }))
      val elapsed = System.currentTimeMillis() - startTime
      reporter report VerificationResultMessage(s"silicon", function, elapsed, condenseToViperResult(results))
      logger debug s"Silicon finished verification of function `${function.name}` in ${viper.silver.reporter.format.formatMillisReadably(elapsed)} seconds with the following result: ${condenseToViperResult(results).toString}"
      results
    })

    val predicateVerificationResults = predicateSupporter.units.toList flatMap (predicate => {
      val s = createInitialState(predicate, program)
      val startTime = System.currentTimeMillis()
      // making declarations of local variable pushed and popped
      // so that they won't be kept in the bottom of Z3
      val results = Seq(executionFlowController.locally(s, this)((_, _) => {
        val verificationResults = this.predicateSupporter.verify(s, predicate)
        verificationResults.head
      }))
      val elapsed = System.currentTimeMillis() - startTime
      reporter report VerificationResultMessage(s"silicon", predicate, elapsed, condenseToViperResult(results))
      logger debug s"Silicon finished verification of predicate `${predicate.name}` in ${viper.silver.reporter.format.formatMillisReadably(elapsed)} seconds with the following result: ${condenseToViperResult(results).toString}"
      results
    })
    decider.prover.stop()

    _workerVerificationPoolManager.pooledVerifiers.comment("-" * 60)
    _workerVerificationPoolManager.pooledVerifiers.comment("Begin function- and predicate-related preamble")
    predicateSupporter.declareSortsAfterVerification(_workerVerificationPoolManager.pooledVerifiers)
    functionsSupporter.declareSortsAfterVerification(_workerVerificationPoolManager.pooledVerifiers)
    predicateSupporter.declareSymbolsAfterVerification(_workerVerificationPoolManager.pooledVerifiers)
    functionsSupporter.declareSymbolsAfterVerification(_workerVerificationPoolManager.pooledVerifiers)
    predicateSupporter.emitAxiomsAfterVerification(_workerVerificationPoolManager.pooledVerifiers)
    functionsSupporter.emitAxiomsAfterVerification(_workerVerificationPoolManager.pooledVerifiers)
    _workerVerificationPoolManager.pooledVerifiers.comment("End function- and predicate-related preamble")
    _workerVerificationPoolManager.pooledVerifiers.comment("-" * 60)

    val verificationTaskFutures: Seq[Future[Seq[VerificationResult]]] =
      program.methods.filterNot(excludeMethod).map(method => {
        val s = createInitialState(method, program).copy(parallelizeBranches = true) /* [BRANCH-PARALLELISATION] */
        _workerVerificationPoolManager.queueVerificationTask(v => {
          val startTime = System.currentTimeMillis()
          // making declarations of local variable pushed and popped
          // so that they won't be kept in the bottom of Z3
          val results = Seq(executionFlowController.locally(s, v)((_, _) => {
            val verificationResults = v.methodSupporter.verify(s, method)
            verificationResults.head
          }))
          val elapsed = System.currentTimeMillis() - startTime
          reporter report VerificationResultMessage(s"silicon", method, elapsed, condenseToViperResult(results))
          logger debug s"Silicon finished verification of method `${method.name}` in ${viper.silver.reporter.format.formatMillisReadably(elapsed)} seconds with the following result: ${condenseToViperResult(results).toString}"

          results
        })
      }) ++ cfgs.map(cfg => {
        val s = createInitialState(cfg, program).copy(parallelizeBranches = true) /* [BRANCH-PARALLELISATION] */


        _workerVerificationPoolManager.queueVerificationTask(v => {
          val startTime = System.currentTimeMillis()
          val results = v.cfgSupporter.verify(s, cfg)
          val elapsed = System.currentTimeMillis() - startTime

          reporter report VerificationResultMessage(s"silicon"/*, cfg*/, elapsed, condenseToViperResult(results))
          logger debug s"Silicon finished verification of method `CFG` in ${viper.silver.reporter.format.formatMillisReadably(elapsed)} seconds with the following result: ${condenseToViperResult(results).toString}"

          results
        })
      })

    val methodVerificationResults = verificationTaskFutures.flatMap(_.get())

    logger.debug(s"Final runtime checks: ${runtimeChecks.getChecks}")

    /** Write JavaScript-Representation of the log if the SymbExLogger is enabled */
    SymbExLogger.writeJSFile()
    /** Write DOT-Representation of the log if the SymbExLogger is enabled */
    SymbExLogger.writeDotFile()
    SymbExLogger.writeTextFile()

    // _program.foreach((astNode) => {
    //   println(s"ast node: ${astNode}")
    //   println(s"runtime checks for ast node: ${astNode.getChecks()}")
    // })

    (   functionVerificationResults
     ++ predicateVerificationResults
     ++ methodVerificationResults)
  }

  private def createInitialState(member: ast.Member, program: ast.Program): State = {
    val quantifiedFields = InsertionOrderedSet(ast.utility.QuantifiedPermissions.quantifiedFields(member, program))
    val quantifiedPredicates = InsertionOrderedSet(ast.utility.QuantifiedPermissions.quantifiedPredicates(member, program))
    val quantifiedMagicWands = InsertionOrderedSet(ast.utility.QuantifiedPermissions.quantifiedMagicWands(member, program)).map(MagicWandIdentifier(_, program))
    val applyHeuristics = program.fields.exists(_.name.equalsIgnoreCase("__CONFIG_HEURISTICS"))

    State(qpFields = quantifiedFields,
          qpPredicates = quantifiedPredicates,
          qpMagicWands = quantifiedMagicWands,
          applyHeuristics = applyHeuristics,
          predicateSnapMap = predSnapGenerator.snapMap,
          predicateFormalVarMap = predSnapGenerator.formalVarMap,
          isMethodVerification = member.isInstanceOf[ast.Member],
          depth = 0)
  }

  private def createInitialState(cfg: SilverCfg, program: ast.Program): State = {
    val quantifiedFields = InsertionOrderedSet(program.fields)
    val quantifiedPredicates = InsertionOrderedSet(program.predicates)
    val quantifiedMagicWands = InsertionOrderedSet[MagicWandIdentifier]() // TODO: Implement support for quantified magic wands.
    val applyHeuristics = program.fields.exists(_.name.equalsIgnoreCase("__CONFIG_HEURISTICS"))

    State(qpFields = quantifiedFields,
      qpPredicates = quantifiedPredicates,
      qpMagicWands = quantifiedMagicWands,
      applyHeuristics = applyHeuristics,
      predicateSnapMap = predSnapGenerator.snapMap,
      predicateFormalVarMap = predSnapGenerator.formalVarMap,
      depth = 0)
  }

  private def excludeMethod(method: ast.Method) = (
       !method.name.matches(config.includeMethods())
    || method.name.matches(config.excludeMethods()))

  /* Prover preamble: Static preamble */

  private def emitStaticPreamble(sink: ProverLike) {
    sink.comment("\n; /z3config.smt2")
    preambleReader.emitPreamble("/z3config.smt2", sink)

    if (config.z3RandomizeSeeds()) {
      sink.comment(s"\n; Randomise seeds [--${config.z3RandomizeSeeds.name}]")
      val options =
        Seq("sat.random_seed", "nlsat.seed", "fp.spacer.random_seed", "smt.random_seed", "sls.random_seed")
          .map (key => s"(set-option :$key ${Random.nextInt(10000)})")

      preambleReader.emitPreamble(options, sink)
    }

    val smt2ConfigOptions =
      config.z3ConfigArgs().map { case (k, v) => s"(set-option :$k $v)" }

    if (smt2ConfigOptions.nonEmpty) {
      // One can pass options to Z3. This allows to check whether they have been received.
      val msg = s"Additional Z3 configuration options are '${config.z3ConfigArgs()}'"
      reporter report ConfigurationConfirmation(msg)
      logger info msg
      preambleReader.emitPreamble(smt2ConfigOptions, sink)
    }

    sink.comment("\n; /preamble.smt2")
    preambleReader.emitPreamble("/preamble.smt2", sink)
  }

  /* Prover preamble: After program analysis */

  private val analysisOrder: Seq[PreambleContributor[_, _, _]] = Seq(
/*  sequencesContributor,
    setsContributor,
    multisetsContributor,
    domainsContributor, */
    fieldValueFunctionsContributor,
    predicateAndWandSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val sortDeclarationOrder: Seq[PreambleContributor[_, _, _]] = Seq(
/*  sequencesContributor,
    setsContributor,
    multisetsContributor,
    domainsContributor, */
    fieldValueFunctionsContributor,
    predicateAndWandSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val sortWrapperDeclarationOrder: Seq[PreambleContributor[Sort, _, _]] = Seq(
/*  sequencesContributor,
    setsContributor,
    multisetsContributor,
    domainsContributor, */
    fieldValueFunctionsContributor,
    predicateAndWandSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val symbolDeclarationOrder: Seq[PreambleContributor[_, _, _]] = Seq(
    /* Sequences depend on multisets ($Multiset.fromSeq, which is
     * additionally axiomatised in the sequences axioms).
     * Multisets depend on sets ($Multiset.fromSet).
     */
/*  sequencesContributor,
    setsContributor,
    multisetsContributor,
    domainsContributor, */
    fieldValueFunctionsContributor,
    predicateAndWandSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private val axiomDeclarationOrder: Seq[PreambleContributor[Sort, _, _]] = Seq(
/*  sequencesContributor,
    setsContributor,
    multisetsContributor,
    domainsContributor, */
    fieldValueFunctionsContributor,
    predicateAndWandSnapFunctionsContributor,
    functionsSupporter,
    predicateSupporter
  )

  private def analyzeProgramAndEmitPreambleContributions(program: ast.Program, sink: ProverLike) {
    analysisOrder foreach (component => {
      component.analyze(program)
      component.updateGlobalStateAfterAnalysis()
    })

    sink.comment("/" * 10 + " Sorts")
    sortDeclarationOrder foreach (component =>
      component.declareSortsAfterAnalysis(sink))

    sink.comment("/" * 10 + " Sort wrappers")
    emitSortWrappers(Seq(sorts.Int, sorts.Bool, sorts.Ref, sorts.Perm), sink)

    sortWrapperDeclarationOrder foreach (component =>
      emitSortWrappers(component.sortsAfterAnalysis, sink))

    sink.comment("/" * 10 + " Symbols")
    symbolDeclarationOrder foreach (component =>
      component.declareSymbolsAfterAnalysis(sink))

  //  sink.comment("/" * 10 + " Uniqueness assumptions from domains")
  //  domainsContributor.emitUniquenessAssumptionsAfterAnalysis(sink)

    /* Note: The triggers of the axioms of snapshot functions (FVFs and PSFs) mention the
     * corresponding sort wrappers. These axioms therefore need to be emitted after the sort
     * wrappers have been declared.
     */

    sink.comment("/" * 10 + " Axioms")
    axiomDeclarationOrder foreach (component =>
      component.emitAxiomsAfterAnalysis(sink))
  }

  private def emitSortWrappers(ss: Iterable[Sort], sink: ProverLike) {
    if (ss.nonEmpty) {
      sink.comment("Declaring additional sort wrappers")

      ss.foreach(sort => {
        val toSnapWrapper = terms.SortWrapperDecl(sort, sorts.Snap)
        val fromSnapWrapper = terms.SortWrapperDecl(sorts.Snap, sort)

        sink.declare(toSnapWrapper)
        sink.declare(fromSnapWrapper)

        preambleReader.emitParametricPreamble("/sortwrappers.smt2",
                                              Map("$S$" -> termConverter.convert(sort)),
                                              sink)
      })
    }
  }
}
