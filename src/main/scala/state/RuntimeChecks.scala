package viper.silicon.state

import viper.silicon.Stack
import viper.silicon.supporters.{NodeHash, NodeEquiv}
import viper.silver.ast.{Exp, Node}
import scala.collection.concurrent.{Map, TrieMap}

case class CheckInfo(checks: Exp, branchInfo: Stack[(Exp, Node, Option[Node])], context: Exp, overlaps: Boolean)

object runtimeChecks {

  // Maps an ast node to the runtime checks that must be done prior to it.
  //
  // We may need to track branch information for the case where a program
  // statement or expression after a conditional is dependent on the result of
  // the conditional; we may need to check the branch taken in the runtime
  // checks
  //
  // a CheckList is a Seq[CheckInfo]
  
  val nodeHash = new NodeHash[Node]
  val nodeEquiv = new NodeEquiv[Node]
  
  private val checks: Map[Node, CheckList] = new TrieMap[Node, CheckList](nodeHash, nodeEquiv)

  def addChecks(programPoint: Node,
    newCheck: Exp,
    branchInfo: Stack[(Exp, Node, Option[Node])],
    context: Exp,
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

  def getChecks: Map[Node, CheckList] = {
    checks
  }
}
