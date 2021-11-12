package viper.silicon.state

import viper.silicon.Stack
import viper.silver.ast.{Exp, Node}
import scala.collection.concurrent.{Map, TrieMap}
import scala.util.hashing.Hashing

case class CheckInfo(checks: Exp, branch: Stack[Exp])

object NodeHash extends AnyRef with Hashing[Node] {

  def hash(node: Node): Int = {
    node.hashCode()
  }
}

object NodeReference extends AnyRef with Equiv[Node] {

  def equiv(node1: Node, node2: Node): Boolean = {
    node1 eq node2
  }
}

object runtimeChecks {

  // Maps an ast node to the runtime checks that must be done prior to it.
  //
  // We may need to track branch information for the case where a program
  // statement or expression after a conditional is dependent on the result of
  // the conditional; we may need to check the branch taken in the runtime
  // checks
  private val checks: Map[Node, CheckList] = new TrieMap[Node, CheckList](NodeHash, NodeReference)

  def addChecks(programPoint: Node, newCheck: Exp, branch: Stack[Exp]): Unit = {
    
    checks.get(programPoint) match {
      case None => (checks += (programPoint -> List(CheckInfo(newCheck, branch))))
      case Some(checkList) =>
        (checks += (programPoint -> (CheckInfo(newCheck, branch) +: checkList)))
    }
  }

  def getChecks: Map[Node, CheckList] = {
    checks
  }
}
