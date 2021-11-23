
package viper.silicon.supporters

import viper.silver.ast.Node

import scala.util.hashing.Hashing

class NodeHash[T <: Node] extends AnyRef with Hashing[T] {

  def hash(call: T): Int = {
    call.hashCode()
  }
}

class NodeEquiv[T <: Node] extends AnyRef with Equiv[T] {

  def equiv(call1: T, call2: T): Boolean = {
    call1.uniqueIdentifier == call2.uniqueIdentifier
  }
}

