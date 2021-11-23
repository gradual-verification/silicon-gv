package viper.silicon.state

import viper.silicon.supporters.{NodeHash, NodeEquiv}
import viper.silver.ast
import scala.collection.concurrent.TrieMap

object reconstructedPermissions {

  val nodeHash = new NodeHash[ast.MethodCall]
  val nodeEquiv = new NodeEquiv[ast.MethodCall]

  private val permissionsMap = new TrieMap[ast.MethodCall, Iterable[ast.Exp]](nodeHash, nodeEquiv)

  def addMethodCallStatement(call: ast.MethodCall, permissions: Iterable[ast.Exp]) = {

    permissionsMap.get(call) match {
      case None => permissionsMap += (call -> permissions)
      case Some(oldPermissions) => permissionsMap += (call -> (oldPermissions ++ permissions))
    }
  }

  def getPermissionsFor(call: ast.MethodCall): Iterable[ast.Exp] = {
    permissionsMap(call)
  }

  def getPermissions = permissionsMap
}
