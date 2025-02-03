// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger

import java.nio.file.{Files, Path, Paths}

import spray.json._
import LogConfigProtocol._
import com.typesafe.scalalogging.Logger
import org.slf4j.LoggerFactory
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.interfaces.state.Chunk
import viper.silicon.logger.SymbExLogger.getRecordConfig
import viper.silicon.logger.records.SymbolicRecord
import viper.silicon.logger.records.data.{DataRecord, FunctionRecord, MemberRecord, MethodRecord, PredicateRecord}
import viper.silicon.logger.records.scoping.{CloseScopeRecord, OpenScopeRecord, ScopingRecord}
import viper.silicon.logger.records.structural.BranchingRecord
import viper.silicon.logger.renderer.SimpleTreeRenderer
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.{Config, Map}
import viper.silver.ast
import viper.silver.verifier.AbstractError

import scala.annotation.elidable
import scala.annotation.elidable._
import scala.collection.mutable
import scala.util.{Failure, Success, Try}

/* TODO: InsertionOrderedSet is used by the logger, but the insertion order is
 *       probably irrelevant for logging. I.e. it might be ok if these sets were
 *       traversed in non-deterministic order.
 */

/**
  * ================================
  * SymbExLogger Usage
  * ================================
  * The SymbExLogger has to be enabled by passing `--ideModeAdvanced` to Silicon (which in turn
  * requires numberOfParallelVerifiers to be 1).
  * Unless otherwise specified, the default logConfig will be used (viper.silicon.logger.LogConfig.default()):
  * All logged records will be included in the report, but store, heap, and path conditions will be omitted.
  *
  * A custom logConfig can be used by passing `--logConfig <pathToLogConfig>` to Silicon. The logConfig has to be valid
  * JSON in the following format:
  * {
  *   "isBlackList": false,
  *   "includeStore": false,
  *   "includeHeap": false,
  *   "includeOldHeap": false,
  *   "includePcs": false,
  *   "recordConfigs": [
  *     {
  *       "kind": "method"
  *     },
  *     {
  *       "kind": "execute",
  *       "value": "a := 1"
  *     }
  *   ]
  * }
  *
  * isBlackList: specifies whether recordConfigs should be interpreted as a black- or whitelist
  * includeStore: specifies whether store information for each record (that offers it) should be included
  * includeHeap: specifies whether heap information for each record (that offers it) should be included
  * includeOldHeap: specifies whether old heap information for each record (that offers it) should be included
  * includePcs: specifies whether path condition information for each record (that offers it) should be included
  * recordConfigs: array of recordConfig
  * recordConfig.kind: string with which each SymbolicRecord.toTypeString() is matched against
  * recordConfig.value: optional string with which each SymbolicRecord.toSimpleString() is matched against
  *
  * Therefore, the above example leads to the following logger behavior:
  * - No store, heap, old heap, and path condition information will be present in the report
  * - By interpreting recordConfigs as whitelist, all records of type MethodRecord will be included in the report as
  *   well as any ExecuteRecord with statement "a := 1" (all other ExecuteRecords will be omitted)
  */

/*
 * ================================
 * SymbExLogger Architecture
 * ================================
 * Overall concept:
 * 1) SymbExLogger Object:
 *    Is used as interface to access the logs. Code from this file that is used in Silicon
 *    should only be used via SymbExLogger. Contains a list of SymbLog, one SymbLog
 *    per method/function/predicate (member). The method 'currentLog()' gives access to the log
 *    of the currently executed member.
 * 2) SymbLog:
 *    Contains the log for a member. Most important methods: openScope/closeScope/insertBranchPoint. To 'start'
 *    a record use openScope, to finish the recording use closeScope. For each execution path, there should be a
 *    closeScope for each openScope. Due to branching this means that there might be multiple closeScopes for a
 *    openScope, because the scope has to be closed on each branch. However to support verification failures, the log
 *    does not have to be complete. In case of a missing close scope record, the scope will be closed immediately
 *    before an outer close scope record.
 * 3) Records:
 *    There are scoping records representing open and close scope in the log. These records will be automatically
 *    inserted in the log by SymbExLogger depending on other records.
 *    Structural records represent branching and joining in the resulting log. JoiningRecords are inserted as regular
 *    data records, BranchingRecords are inserted using the special interface (insertBranchPoint, markReachable,
 *    switchToNextBranch, and endBranchPoint).
 *    Data records represent symbolic primitives (execute, evalute, consume, produce) as well as executions of some
 *    algorithms of the symbolic execution engine. Inserting a data record automatically creates a scope for it. Each
 *    subsequent log entry is assumped to be in the scope until scopeClose is invoked.
 *
 *    Example to illustrate the way a silver program is logged:
 *    Assume the following silver code:
 *
 *    method m() {
 *      var a: Int
 *      a := 1
 *      a := a+2
 *    }
 *
 *    This results in a log that can be visualized as a
 *    simple tree (see: SimpleTreeRenderer) as follows:
 *
 *    method m
 *      WellformednessCheck null
 *      execute var a: Int
 *      execute a := 1
 *        evaluate 1
 *      execute a := a + 2
 *        evaluate a + 2
 *          evaluate a
 *          evaluate 2
 *
 *    The order of insert/collapse is as follows:
 *    openScope(method m),
 *    openScope(WellformednessCheck null), closeScope(WellformednessCheck null),
 *    openScope(execute var a), closeScope(execute var a), openScope(execute a := 1), openScope(evaluate 1),
 *    closeScope(evaluate 1), closeScope(execute a := 1),
 *    openScope(execute a := a + 2), openScope(evaluate a + 2), openScope(evaluate a) closeScope(evaluate a),
 *    openScope(evaluate 2), closeScope(evaluate 2), closeScope(evaluate a + 2), closeScope(execute a := a + 2),
 *    closeScope(method m)
 *
 *    CloseScope basically 'removes one indentation', i.e., brings you one level higher in the tree.
 */

/**
  * ================================
  * GUIDE FOR ADDING RECORDS TO SymbExLogger
  * ================================
  *
  * SymbExLogger records calls to several symbolic primitives (execute, evalute, produce, consume) as well as algorithms
  * of Silicon. By default, only the current state, context and parameters of the primitives are stored (if configured
  * in logConfig).
  * If you want to get more information from certain structures, there are several ways to store additional
  * info:
  *
  * 1) Store the information as a CommentRecord.
  * 2) Implement a customized record.
  *
  * Use of CommentRecord (1):
  * At the point in the code where you want to add the comment, call
  * //val id = SymbExLogger.currentLog().openScope(new CommentRecord(my_info, σ, c)
  * //SymbExLogger.currentLog().closeScope(id)
  * σ is the current state (AnyRef, but should be of type State[_,_,_] usually), my_info
  * is a string that contains the information you want to store, c is the current
  * context. If you want to store more information than just a string, consider (2).
  *
  * Use of custom Records (2):
  * For already existing examples of data records, have look at records/data. In particular ProverAssertRecord might be
  * of interested, because it shows how additional info can be stored and inserted into RecordData during report
  * creation.
  * Inserting new structure records might be a bit more involved, depending on the use case.
  * As an example, the joining (e.g. occurring in pure conditional expressions) is discussed next:
  * Silicon uses Joiner to join execution after an execution block. A JoiningRecord is created at the beginning of the
  * Joiner and added to the log by calling:
  * // val uidJoin = SymbExLogger.currentLog().openScope(joiningRecord)
  * After executing the block and joining the execution, the following call to the SymbExLogger is made to close the
  * join scope:
  * // SymbExLogger.currentLog().closeScope(uidJoin)
  * Although JoiningRecord is a structural record and joining in symbolic execution has significant impact on the
  * execution structure, JoiningRecord behalves almost as a data record in SymbExLogger:
  * Due to the design that each data record (and joining record) causes a scope and the scope contains all
  * subexpressions, it naturally follows that branching records and their branches inside a join scope will be joined
  * because they are part of join's scope and the scope eventually ends.
  * Hence, of more interest is branching (which most likely occurs in every join scope):
  * If the execution is branched (occurs in Brancher as well as in Executor when following more than one branch) the
  * logger has to be informed about it in order that records on the individual branches are correctly logged.
  * To do so, the following call creates a new branch point with a number of branches that result out of it (but aren't
  * necessarily all reachable):
  * // val uidBranchPoint = SymbExLogger.currentLog().insertBranchPoint(2, Some(condition))
  * All records that will subsequently be inserted will be assigned to the first branch.
  * As soon as the execution of the first branch is complete, the logger needs to switch to the next branch:
  * // SymbExLogger.currentLog().switchToNextBranch(uidBranchPoint)
  * When the execution of all branches is done, the branch point is concluded:
  * // SymbExLogger.currentLog().endBranchPoint(uidBranchPoint)
  * Because the existence as well as non-existence of records on a branch does not imply reachability, the logger
  * needs to be explicitly informed for each branch that is reachable:
  * // SymbExLogger.currentLog().markReachable(uidBranchPoint)
  */

object SymbExLogger {
  /** Collection of logged Method/Predicates/Functions. **/
  var memberList: Seq[SymbLog] = Seq[SymbLog]()
  private var uidCounter = 0

  var enabled = false
  var logConfig: LogConfig = LogConfig.default()

  def freshUid(): Int = {
    val uid = uidCounter
    uidCounter = uidCounter + 1
    uid
  }

  def getRecordConfig(d: DataRecord): Option[RecordConfig] = {
    for (rc <- logConfig.recordConfigs) {
      if (rc.kind.equals(d.toTypeString)) {
        rc.value match {
          case Some(value) => if (value.equals(d.toSimpleString)) return Some(rc)
          case _ => return Some(rc)
        }
      }
    }
    None
  }

  /**
    * stores the last SMT solver statistics to calculate the diff
    */
  private var prevSmtStatistics: Map[String, String] = new Map()

  /** Add a new log for a method, function or predicate (member).
    *
    * @param member Either a MethodRecord, PredicateRecord or a FunctionRecord.
    * @param s      Current state. Since the body of the method (predicate/function) is not yet
    *               executed/logged, this is usually the empty state (use Σ(Ø, Ø, Ø) for empty
    *               state).
    * @param pcs    Current path conditions.
    */
  @elidable(INFO)
  def openMemberScope(member: ast.Member, s: State, pcs: PathConditionStack): Unit = {
    memberList = memberList ++ Seq(new SymbLog(member, s, pcs))
  }

  /** Use this method to access the current log, e.g., to access the log of the method
    * that gets currently symbolically executed.
    *
    * @return Returns the current method, predicate or function that is being logged.
    */
  def currentLog(): SymbLog = {
    if (enabled)
      memberList.last
    else NoopSymbLog
  }

  @elidable(INFO)
  def closeMemberScope(): Unit = {
    if (enabled) {
      currentLog().closeMemberScope()
    }
  }

  /**
    * Passes config from Silicon to SymbExLogger.
    *
    * @param c Config of Silicon.
    */
  def setConfig(c: Config): Unit = {
    setEnabled(c.ideModeAdvanced())
    logConfig = parseLogConfig(c)
  }

  @elidable(INFO)
  private def setEnabled(b: Boolean): Unit = {
    enabled = b
  }

  private def parseLogConfig(c: Config): LogConfig = {
    var logConfigPath = Try(c.logConfig())
    logConfigPath = logConfigPath.filter(path => Files.exists(Paths.get(path)))
    val source = logConfigPath.map(path => scala.io.Source.fromFile(path))
    val fileContent = source.map(s => s.getLines().mkString)
    val jsonAst = fileContent.flatMap(content => Try(content.parseJson))
    val logConfig = jsonAst.flatMap(ast => Try(ast.convertTo[LogConfig]))
    logConfig match {
      case Success(convertedConfig) => convertedConfig
      case Failure(_) => LogConfig.default()
    }
  }

  /**
    * Simple string representation of the logs.
    */
  def toSimpleTreeString: String = {
    if (enabled) {
      val simpleTreeRenderer = new SimpleTreeRenderer()
      simpleTreeRenderer.render(memberList)
    } else ""
  }

  // This method exists because IntelliJ cannot find SymbLog.main
  def m(symbLog: SymbLog): MemberRecord = symbLog.main

  var errors: Seq[AbstractError] = Seq.empty

  // we can have a single global snaps because fresh Vars starting with $t are globally unique
  val snaps = mutable.Map[Term, BasicChunk]()
  val freshPositions = mutable.Map[Term, ast.Position]()
  // while loops are uniquely identified by their invariants, this is needed
  // to find the position of the while loops for displaying the state when
  // entering and leaving the loop
  val whileLoops = mutable.Map[ast.Exp, ast.Stmt]()

  def formatTerm(term: Term): String =
    term match {
      case Var(SuffixedIdentifier(prefix, _, _), _) if prefix == "$t" =>
        formatBasicChunk(snaps(term), true)
      case Var(SuffixedIdentifier(prefix, _, _), _) if !prefix.contains("$result") && prefix.contains("$") =>
        if (freshPositions.contains(term) && freshPositions(term).isInstanceOf[ast.TranslatedPosition]) {
          val pos = freshPositions(term).asInstanceOf[ast.TranslatedPosition].pos
          formatBasicChunk(snaps(term), true) + "@" + pos.line.toString
        } else {
          formatBasicChunk(snaps(term), true)
        }
      case Var(SuffixedIdentifier(prefix, _, suffix), _) =>
        if (freshPositions.contains(term) && freshPositions(term).isInstanceOf[ast.TranslatedPosition]) {
          val pos = freshPositions(term).asInstanceOf[ast.TranslatedPosition].pos
          prefix + "@" + pos.line.toString
        } else {
          prefix
        }
      case SortWrapper(_, _) => formatBasicChunk(snaps(term), true)
      case Null() => "null"
      case True() => "true"
      case False() => "false"
      case IntLiteral(n) => n.toString
      case Plus(p0, p1) => "(" + formatTerm(p0) + " + " + formatTerm(p1) + ")"
      case Minus(p0, p1) => "(" + formatTerm(p0) + " - " + formatTerm(p1) + ")"
      case Times(p0, p1) => "(" + formatTerm(p0) + " * " + formatTerm(p1) + ")"
      case Div(p0, p1) => "(" + formatTerm(p0) + " / " + formatTerm(p1) + ")"
      case Mod(p0, p1) => "(" + formatTerm(p0) + " % " + formatTerm(p1) + ")"
      case BuiltinEquals(p0, p1) => "(" + formatTerm(p0) + " == " + formatTerm(p1) + ")"
      case Less(p0, p1) => "(" + formatTerm(p0) + " < " + formatTerm(p1) + ")"
      case AtMost(p0, p1) => "(" + formatTerm(p0) + " <= " + formatTerm(p1) + ")"
      case Greater(p0, p1) => "(" + formatTerm(p0) + " > " + formatTerm(p1) + ")"
      case AtLeast(p0, p1) => "(" + formatTerm(p0) + " >= " + formatTerm(p1) + ")"
      case Not(p) => "(" + "!" + formatTerm(p) + ")"
      case Or(ts) => "(" + ts.map(formatTerm).mkString(" || ") + ")"
      case And(ts) => "(" + ts.map(formatTerm).mkString(" && ") + ")"
      case Implies(p0, p1) => "(" + formatTerm(p0) + " ==> " + formatTerm(p1) + ")"
      case _ => "'" + term.toString + "'"
    }

  def formatBasicChunk(basicChunk: BasicChunk, insideTerm: Boolean): String = {
    val s = basicChunk.snap match {
      case Unit => " == " + basicChunk.snap.toString
      case Null() => " == null"
      case IntLiteral(n) => " == " + n.toString
      case True() => " == true"
      case False() => " == false"
      case Var(SuffixedIdentifier(prefix, _, _), _) if prefix == "$t" => ""
      case Var(SuffixedIdentifier(prefix, _, _), _) if !prefix.contains("$result") && prefix.contains("$") => ""
      case Var(SuffixedIdentifier(prefix, _, _), _) => " == " + prefix
      case _ => ""
    }
    basicChunk.resourceID match {
      case FieldID =>
        val typeAndFieldName = basicChunk.id.name.split("\\$")
        val fieldName = if (typeAndFieldName.length == 2) {
          typeAndFieldName.last
        } else {
          "?"
        }
        val fieldAcc = formatTerm(basicChunk.args.head) + "->" + fieldName
        if (insideTerm) {
          fieldAcc + s
        } else {
          "acc(" + fieldAcc + ")" + s
        }
      case PredicateID =>
        val argsAsString = basicChunk.args.map(formatTerm).mkString(", ")
        basicChunk.id.name + "(" + argsAsString + ")" + s
      case _ => ""
    }
  }

  def populateSnaps(chunks: Seq[Chunk]): Unit =
    for (chunk <- chunks) {
      chunk match {
        case basicChunk: BasicChunk =>
          basicChunk.snap match {
            case Var(SuffixedIdentifier(prefix, _, _), _) if prefix == "$t" =>
              snaps += basicChunk.snap -> basicChunk
            case Var(SuffixedIdentifier(prefix, _, _), _) if !prefix.contains("$result") && prefix.contains("$")  =>
              snaps += basicChunk.snap -> basicChunk
            case SortWrapper(wrappedTerm, sort) =>
              snaps += basicChunk.snap -> basicChunk
            case _ => {}
          }
        case _ => {}
      }
    }

  def diffChunks(oldChunks: Seq[Chunk], newChunks: Seq[Chunk]): (Seq[Chunk], Seq[Chunk]) = {
    val consumed = for (chunk <- oldChunks if !newChunks.exists(_ == chunk)) yield chunk
    val produced = for (chunk <- newChunks if !oldChunks.exists(_ == chunk)) yield chunk
    (consumed, produced)
  }

  def formatChunks(chunks: Seq[Chunk]): String = {
    var result = ""
    for (chunk <- chunks) {
      chunk match {
        case basicChunk: BasicChunk =>
          result += formatBasicChunk(basicChunk, false) + "; "
        case _ => { }
      }
    }
    result
  }

  def formatDiff(oldChunks: Seq[Chunk], newChunks: Seq[Chunk]): (String, String) = {
    val (consumed, produced) = diffChunks(oldChunks, newChunks)
    (formatChunks(consumed), formatChunks(produced))
  }

  def pcVisible(term: Term): Boolean =
    term match {
      case App(_, _) => false
      case Combine(_, _) => false
      case First(_) => false
      case Second(_) => false
      case Var(SuffixedIdentifier(prefix, _, _), _) if prefix == "$t" => snaps.isDefinedAt(term)
      case Var(SuffixedIdentifier(prefix, _, _), _) => true
      case SortWrapper(_, _) => snaps.isDefinedAt(term)
      case Null() => true
      case True() => true
      case False() => true
      case IntLiteral(n) => true
      case Plus(p0, p1) => pcVisible(p0) && pcVisible(p1)
      case Minus(p0, p1) => pcVisible(p0) && pcVisible(p1)
      case Times(p0, p1) => pcVisible(p0) && pcVisible(p1)
      case Div(p0, p1) => pcVisible(p0) && pcVisible(p1)
      case Mod(p0, p1) => pcVisible(p0) && pcVisible(p1)
      case BuiltinEquals(p0, p1) => pcVisible(p0) && pcVisible(p1)
      case Less(p0, p1) => pcVisible(p0) && pcVisible(p1)
      case AtMost(p0, p1) => pcVisible(p0) && pcVisible(p1)
      case Greater(p0, p1) => pcVisible(p0) && pcVisible(p1)
      case AtLeast(p0, p1) => pcVisible(p0) && pcVisible(p1)
      case Not(p) => pcVisible(p)
      case Or(ts) => ts.map(pcVisible).reduce((x, y) => x && y)
      case And(ts) => ts.map(pcVisible).reduce((x, y) => x && y)
      case Implies(p0, p1) => pcVisible(p0) && pcVisible(p1)
      case _ => true
    }

  def isNotEquals(term: Term): Boolean =
    term match {
      case Not(BuiltinEquals(_, _)) => false
      case _ => true
    }

  def formatPcs(oldPcs: InsertionOrderedSet[Term], newPcs: InsertionOrderedSet[Term]): String = {
    val added = for (pc <- newPcs if !oldPcs.exists(_ == pc)) yield pc
    added.filter(pcVisible).map(formatTerm).mkString(", ")
  }

  def formatStore(g: Store): Seq[(String, String)] =
    g.values.map({ case (v, term) => (v.name, formatTerm(term)) }).toList

  def populateWhileLoops(stmts: Seq[ast.Stmt]): Unit = {
    for (stmt <- stmts) {
      stmt match {
        case ast.NewStmt(lhs, fields) =>
        case _: ast.AbstractAssign =>
        case ast.MethodCall(methodName, args, targets) =>
        case ast.Exhale(exp) =>
        case ast.Inhale(exp) =>
        case ast.Assert(exp) =>
        case ast.Assume(exp) =>
        case ast.Fold(acc) =>
        case ast.Unfold(acc) =>
        case ast.Package(wand, proofScript) =>
        case ast.Apply(exp) =>
        case ast.Seqn(ss, scopedDecls) =>
          populateWhileLoops(ss)
        case ast.If(cond, thn, els) =>
          populateWhileLoops(thn.ss)
          populateWhileLoops(els.ss)
        case ast.While(cond, invs, body) =>
          assert(invs.length == 1)
          whileLoops += invs.head -> stmt
        case ast.Label(name, invs) =>
        case ast.Goto(target) =>
        case ast.LocalVarDeclStmt(decl) =>
        case _: ast.ExtensionStmt =>
      }
    }
  }

  def resetMaps(): Unit = {
    snaps.clear()
    freshPositions.clear()
    whileLoops.clear()
  }

  /** Path to the file that is being executed. Is used for UnitTesting. **/
  var filePath: Path = _

  /**
    * Resets the SymbExLogger-object, to make it ready for a new file.
    * Only needed when several files are verified together (e.g., sbt test).
    */
  def reset(): Unit = {
    memberList = Seq[SymbLog]()
    uidCounter = 0
    filePath = null
    logConfig = LogConfig.default()
    prevSmtStatistics = new Map()
  }

  def resetMemberList(): Unit = {
    memberList = Seq[SymbLog]()
    // or reset by calling it from Decider.reset
    prevSmtStatistics = new Map()
  }

  /**
    * Calculates diff between `currentStatistics` and the statistics from a previous call.
    * The difference is calculated if value can be converted to an int or double
    * @param currentStatistics most recent statistics from the SMT solver
    * @return map with differences (only containing values that could be converted) and keys with appended "-delta"
    */
  def getDeltaSmtStatistics(currentStatistics: Map[String, String]) : Map[String, String] = {
    val deltaStatistics = currentStatistics map getDelta filter { case (_, value) => value.nonEmpty } map {
      case (key, Some(value)) => (key + "-delta", value)
      case other => sys.error(s"Unexpected result pair $other")
    }
    // set prevStatistics (i.e. override values with same key or add):
    prevSmtStatistics = prevSmtStatistics ++ currentStatistics
    deltaStatistics
  }

  private def getDelta(pair: (String, String)): (String, Option[String]) = {
    val curValInt = try Some(pair._2.toInt) catch { case _: NumberFormatException => None }
    val prevValInt = prevSmtStatistics.get(pair._1) match {
      case Some(value) => try Some(value.toInt) catch { case _: NumberFormatException => None }
      case _ => Some(0) // value not found
    }
    val curValDouble = try Some(pair._2.toDouble) catch { case _: NumberFormatException => None }
    val prevValDouble = prevSmtStatistics.get(pair._1) match {
      case Some(value) => try Some(value.toDouble) catch { case _: NumberFormatException => None }
      case _ => Some(0.0) // value not found
    }
    (curValInt, prevValInt, curValDouble, prevValDouble) match {
      case (Some(curInt), Some(prevInt), _, _) => (pair._1, Some((curInt - prevInt).toString))
      case (_, _, Some(curDouble), Some(prevDouble)) => (pair._1, Some((curDouble - prevDouble).toString))
      case _ => (pair._1, None)
    }
  }
}

//========================= SymbLog ========================

/**
  * Concept: One object of SymbLog per Method/Predicate/Function. SymbLog
  * is used in the SymbExLogger-object.
  */
class SymbLog(v: ast.Member, s: State, pcs: PathConditionStack) {

  val logger: Logger =
    Logger(LoggerFactory.getLogger(s"${this.getClass.getName}"))

  /** top level log entries for this member; these log entries were recorded consecutively without branching;
    * in case branching occured, one of these records is a BranchingRecord with all branches as field attached to it */
  var log: Vector[SymbolicRecord] = Vector[SymbolicRecord]()
  /** this stack keeps track of BranchingRecords while adding records to the log; as soon as all branches of a
    * BranchingRecord are done, logging has to switch back to the previous BranchingRecord */
  var branchingStack: List[BranchingRecord] = List[BranchingRecord]()
  /** if a record was ignored due to the logConfig, its ID is tracked here and corresponding open and close scope
    * records will be ignored too */
  var ignoredDataRecords: Set[Int] = Set()

  /**
    * indicates whether this member's close was already closed
    */
  private var isClosed: Boolean = false

  // Maps macros to their body
  private var _macros = Map[App, Term]()

  val main: MemberRecord = v match {
    case m: ast.Method => new MethodRecord(m, s, pcs)
    case p: ast.Predicate => new PredicateRecord(p, s, pcs)
    case f: ast.Function => new FunctionRecord(f, s, pcs)
    case _ => null
  }
  openScope(main)

  private def appendLog(r: SymbolicRecord, ignoreBranchingStack: Boolean = false): Unit = {
    if (isClosed) {
      logger warn "ignoring record insertion to an already closed SymbLog instance"
      return
    }
    if (branchingStack.isEmpty || ignoreBranchingStack) {
      log = log :+ r
    } else {
      branchingStack.head.appendLog(r)
    }
  }

  /**
    * Inserts the record as well as a corresponding open scope record into the log
    * @param s non-null record
    * @return id with which closeScope should be called
    */
  @elidable(INFO)
  def openScope(s: DataRecord): Int = {
    s.id = SymbExLogger.freshUid()
    // check whether this record should be ignored:
    val recordConfig = getRecordConfig(s)
    val ignore = recordConfig match {
      case Some(_) => SymbExLogger.logConfig.isBlackList
      case _ => !SymbExLogger.logConfig.isBlackList
    }
    if (ignore) {
      ignoredDataRecords = ignoredDataRecords + s.id
    } else {
      appendLog(s)
      val openRecord = new OpenScopeRecord(s)
      insert(openRecord)
    }
    s.id
  }

  /**
    * Appends a scoping record to the log unless it's referenced data record is ignored
    * @param s non-null scoping record
    * @param ignoreBranchingStack true if the record should always be inserted in the root level
    * @return id of the scoping record
    */
  @elidable(INFO)
  private def insert(s: ScopingRecord, ignoreBranchingStack: Boolean = false): Int = {
    s.id = SymbExLogger.freshUid()
    if (!ignoredDataRecords.contains(s.refId)) {
      // the corresponding data record is not ignored
      s.timeMs = System.currentTimeMillis()
      appendLog(s, ignoreBranchingStack)
    }
    s.id
  }

  /**
    * Creates and appends a branching record to the log. Branching records do not cause scopes.
    * Use `switchToNextBranch` to change from the current to the next branch and `endBranchPoint` to conclude the
    * branch point after all branches were visited.
    * @param possibleBranchesCount number of branches that this branch point has but are not necessarily all reachable
    * @param condition branch condition
    * @return id of the branching record
    */
  @elidable(INFO)
  def insertBranchPoint(possibleBranchesCount: Int, condition: Option[Term] = None): Int = {
    val branchingRecord = new BranchingRecord(possibleBranchesCount, condition)
    branchingRecord.id = SymbExLogger.freshUid()
    appendLog(branchingRecord)
    branchingStack = branchingRecord :: branchingStack
    branchingRecord.id
  }

  /**
    * Changes from the current to the next branch of a specific branch point
    * @param uidBranchPoint id of the branching record
    */
  @elidable(INFO)
  def switchToNextBranch(uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    // no close scope is inserted because branches are not considered scopes
    branchingRecord.switchToNextBranch()
  }

  /**
    * Marks the current branch of a specific branch point as being reachable
    * @param uidBranchPoint id of the branching record
    */
  @elidable(INFO)
  def markReachable(uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    branchingRecord.markReachable()
  }

  /**
    * Ends the scope of a specific data record by inserting a corresponding close scope record into the log
    * @param n id of the data record
    */
  @elidable(INFO)
  def closeScope(n: Int): Unit = {
    val closeRecord = new CloseScopeRecord(n)
    insert(closeRecord)
  }

  /**
    * Concludes a specific branch point (which normaly happens after visiting all branches belonging to the branch point)
    * @param uidBranchPoint id of the branch point
    */
  @elidable(INFO)
  def endBranchPoint(uidBranchPoint: Int): Unit = {
    assert(branchingStack.nonEmpty)
    val branchingRecord = branchingStack.head
    assert(branchingRecord.id == uidBranchPoint)
    // no close scope is inserted because branches are not considered scopes
    branchingStack = branchingStack.tail
  }

  /**
    * Ends the scope of the member (i.e. main) by inserting a corresponding close scope record into the log
    */
  def closeMemberScope(): Unit = {
    if (isClosed) {
      return
    }
    val closeRecord = new CloseScopeRecord(main.id)
    // always insert this close scope record on the root log instead of at the correct place depending on branching stack:
    insert(closeRecord, ignoreBranchingStack = true)
    isClosed = true
  }

  /** Record the last prover query that failed.
    *
    * This is used to record failed SMT queries, that ultimately led Silicon
    * to a verification failure. Whenever a new SMT query is successful, then
    * the currently recorded one is supposed to be discarded (via the
    * discardSMTQuery method), because it did not cause a failure.
    *
    * @param query The query to be recorded.
    */
  @elidable(INFO)
  def setSMTQuery(query: Term): Unit = {
    if (main != null) {
      main.lastFailedProverQuery = Some(query)
    }
  }

  /** Discard the currently recorded SMT query.
    *
    * This is supposed to be called when we know the recorded SMT query cannot
    * have been the reason for a verification failure (e.g. a new query has
    * been performed afterwards).
    */
  @elidable(INFO)
  def discardSMTQuery(): Unit = {
    if (main != null) {
      main.lastFailedProverQuery = None
    }
  }

  def macros(): Map[App, Term] = _macros

  @elidable(INFO)
  def addMacro(m: App, body: Term): Unit = {
    _macros = _macros + (m -> body)
  }

  override def toString: String = new SimpleTreeRenderer().renderMember(this)
}

object NoopSymbLog extends SymbLog(null, null, null) {
  override def openScope(s: DataRecord): Int = 0
  override def insertBranchPoint(possibleBranchesCount: Int, condition: Option[Term]): Int = 0
  override def switchToNextBranch(uidBranchPoint: Int): Unit = {}
  override def markReachable(uidBranchPoint: Int): Unit = {}
  override def closeScope(n: Int): Unit = {}
  override def endBranchPoint(uidBranchPoint: Int): Unit = {}
  override def closeMemberScope(): Unit = {}
}
