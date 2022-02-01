package viper.silicon.state

import viper.silicon.Stack
import viper.silicon.supporters.{NodeHash, NodeEquiv}
import viper.silver.ast
import scala.collection.concurrent.{Map, TrieMap}

sealed trait CheckPosition

case object CheckPosition {
  case class GenericNode(node: ast.Node) extends CheckPosition
  case class Loop(invariants: Seq[ast.Exp], position: LoopPosition) extends CheckPosition
}

case class CheckInfo(checks: ast.Exp,
  branchInfo: Stack[(ast.Exp, ast.Node, Option[CheckPosition])],
  context: ast.Exp,
  overlaps: Boolean)

object runtimeChecks {

  // Maps an ast node to the runtime checks that must be done prior to it.
  //
  // We may need to track branch information for the case where a program
  // statement or expression after a conditional is dependent on the result of
  // the conditional; we may need to check the branch taken in the runtime
  // checks
  //
  // a CheckList is a Seq[CheckInfo]
  
  val nodeHash = new NodeHash[CheckPosition]
  val nodeEquiv = new NodeEquiv[CheckPosition]
  
  private val checks: Map[CheckPosition, CheckList] = new TrieMap[CheckPosition, CheckList](nodeHash, nodeEquiv)

  def addChecks(programPoint: CheckPosition,
    newCheck: ast.Exp,
    branchInfo: Stack[(ast.Exp, ast.Node, Option[CheckPosition])],
    context: ast.Exp,
    overlaps: Boolean): Unit = {
    
    checks.get(programPoint) match {
      case None => (checks += (programPoint ->
        List(CheckInfo(newCheck,
          branchInfo,
          context,
          overlaps))))
      case Some(checkList) =>
        (checks += (programPoint ->
          (CheckInfo(newCheck,
            branchInfo,
            context,
            overlaps)
          +: checkList)))
    }
  }

  def getChecks: Map[CheckPosition, CheckList] = {
    checks
  }
}
