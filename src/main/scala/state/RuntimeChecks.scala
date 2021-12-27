package viper.silicon.state

import viper.silicon.Stack
import viper.silicon.supporters.{NodeHash, NodeEquiv}
import viper.silver.ast.{Exp, Node}
import scala.collection.concurrent.{Map, TrieMap}

case class BranchInfo(branch: Stack[Exp], branchPosition: Stack[Node], branchOrigin: Stack[Option[Node]])

case class CheckInfo(checks: Exp, branch: BranchInfo, context: Exp, overlaps: Boolean)

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
    branch: Stack[Exp], branchPosition: Stack[Node], branchOrigin: Stack[Option[Node]],
    context: Exp,
    overlaps: Boolean): Unit = {
    
    checks.get(programPoint) match {
      case None => (checks += (programPoint ->
        List(CheckInfo(newCheck,
          BranchInfo(branch, branchPosition, branchOrigin),
          context,
          overlaps))))
      case Some(checkList) =>
        (checks += (programPoint ->
          (CheckInfo(newCheck,
            BranchInfo(branch, branchPosition, branchOrigin),
            context,
            overlaps)
          +: checkList)))
    }
  }

  def getChecks: Map[Node, CheckList] = {
    checks
  }
}
