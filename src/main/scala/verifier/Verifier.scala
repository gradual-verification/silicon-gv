//<<<<<<< HEAD
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.verifier

import com.typesafe.scalalogging.Logger
import viper.silicon.decider.Decider
import viper.silicon.reporting.StateFormatter
import viper.silicon.state.terms.{AxiomRewriter, TriggerGenerator}
import viper.silicon.rules.StateConsolidationRules
import viper.silicon.state.{Heap, IdentifierFactory, State, SymbolConverter}
import viper.silicon.supporters.{QuantifierSupporter, SnapshotSupporter}
import viper.silicon.utils.Counter
import viper.silicon.Config
import viper.silicon.logger.MemberSymbExLogger
import viper.silver.ast
import viper.silver.reporter.Reporter

import java.util.concurrent.atomic.AtomicInteger

trait Verifier {
  def uniqueId: String

  def symbExLog: MemberSymbExLogger
  def openSymbExLogger(member: ast.Member): Unit
  def logger: Logger
  def reporter: Reporter
  def counter(id: AnyRef): Counter

  def decider: Decider
  def symbolConverter: SymbolConverter
  def stateFormatter: StateFormatter
  def identifierFactory: IdentifierFactory
  def triggerGenerator: TriggerGenerator
  def axiomRewriter: AxiomRewriter
  def quantifierSupporter: QuantifierSupporter
  def snapshotSupporter: SnapshotSupporter
  def stateConsolidator(s: State): StateConsolidationRules

  def verificationPoolManager: VerificationPoolManager

  val errorsReportedSoFar = new AtomicInteger(0);

  var debugHeapCounter = new AtomicInteger(0);

  def reportFurtherErrors(): Boolean = (Verifier.config.numberOfErrorsToReport() > errorsReportedSoFar.get()
    || Verifier.config.numberOfErrorsToReport() == 0);

  /**
    * Returns debug labels for 1) the given heap (will reuse an existing one if one already exists), independently of
    * the position of the current expression, and 2) the current expression in the given heap.
    * @param s the current state
    * @param pos the position of the current expression
    * @param h the heap to consider, if not the heap from state s
    * @return a pair containing the label of the given heap, and the label of the current expression in the given heap
    */
  def getDebugOldLabel(s: State, pos: ast.Position, h: Option[Heap] = None): (String, String) = {
    val posString = pos match {
      case column: ast.HasLineColumn => s"l:${column.line}.${column.column}"
      case _ => s"l:unknown"
    }
    val heap = h match {
      case Some(heap) => heap
      case None => s.h
    }
    val equalHeaps = s.oldHeaps.filter(h => h._1.startsWith("debug@") && h._2.equals(heap)).keys
    if (equalHeaps.nonEmpty){
      (equalHeaps.head, s"${equalHeaps.head}#$posString")
    } else {
      val counter = debugHeapCounter.getAndIncrement()
      (s"debug@$counter", s"debug@$counter#$posString")
    }
  }
}

object Verifier {
  val PRE_STATE_LABEL = "old"
  val PRE_HEAP_LABEL = "oldH"
  val PRE_OPTHEAP_LABEL = "oldOH"
  val EVAL_HEAP_LABEL = "oldeH"
  val EVAL_OPTHEAP_LABEL = "oldeOH"
  val MAGIC_WAND_LHS_STATE_LABEL = ast.LabelledOld.LhsOldLabel

  private var _config: Config = _
  def config: Config = _config
  /*private*/ def config_=(config: Config): Unit = { _config = config }
}

trait VerifierComponent { this: Verifier => }
/*=======
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.verifier

import java.nio.file.Path

import com.typesafe.scalalogging.Logger
import viper.silver.ast
import viper.silicon.{Config, Map}
import viper.silicon.decider.Decider
import viper.silicon.reporting.StateFormatter
import viper.silicon.state.{IdentifierFactory, SymbolConverter}
import viper.silicon.state.terms.{AxiomRewriter, TriggerGenerator}
import viper.silicon.supporters.{PredicateData, QuantifierSupporter, SnapshotSupporter}
import viper.silicon.supporters.functions.FunctionData
import viper.silicon.utils.Counter
import viper.silver.plugin.PluginAwareReporter
import viper.silver.ast.LabelledOld

trait Verifier {
  def uniqueId: String

  def logger: Logger
  def reporter: PluginAwareReporter
  def counter(id: AnyRef): Counter

  def decider: Decider
  def symbolConverter: SymbolConverter
  def stateFormatter: StateFormatter
  def identifierFactory: IdentifierFactory
  def triggerGenerator: TriggerGenerator
  def axiomRewriter: AxiomRewriter
  def quantifierSupporter: QuantifierSupporter
  def snapshotSupporter: SnapshotSupporter

  def verificationPoolManager: VerificationPoolManager
}
*/
/* TODO: Replace getters and setters by public vars
   TODO: Add a description to each var that explain when it is expected to be set */
/*object Verifier {
  val PRE_STATE_LABEL = "old"
  val PRE_HEAP_LABEL = "oldH"
  val PRE_OPTHEAP_LABEL = "oldOH"
  val EVAL_HEAP_LABEL = "oldeH"
  val EVAL_OPTHEAP_LABEL = "oldeOH"
  val MAGIC_WAND_LHS_STATE_LABEL = LabelledOld.LhsOldLabel

  private var _config: Config = _
  def config: Config = _config*/
  ///*private*/ def config_=(config: Config): Unit = { _config = config }

  //private var _program: ast.Program = _
  //def program: ast.Program = _program
  ///*private*/ def program_=(program: ast.Program): Unit = { _program = program }

  //private var _inputFile: Option[Path] = None
  //def inputFile: Option[Path] = _inputFile
  ///*private*/ def inputFile_=(file: Option[Path]): Unit = { _inputFile = file }

  //private var _predicateData: Map[ast.Predicate, PredicateData] = _
  //def predicateData: Map[ast.Predicate, PredicateData] = _predicateData
  ///*private*/ def predicateData_=(predicateData: Map[ast.Predicate, PredicateData]): Unit =
  //  { _predicateData = predicateData }

  //private var _functionData: Map[ast.Function, FunctionData] = _
  //def functionData: Map[ast.Function, FunctionData] = _functionData
  ///*private*/ def functionData_=(functionData: Map[ast.Function, FunctionData]): Unit =
  //{ _functionData = functionData }
//}

//trait VerifierComponent { this: Verifier => }
//>>>>>>> upstream/master
