
package viper.silicon.supporters

import scala.util.hashing.Hashing

class NodeHash[T <: Any] extends AnyRef with Hashing[T] {

  def hash(call: T): Int = {
    call.hashCode()
  }
}

class NodeEquiv[T <: AnyRef] extends AnyRef with Equiv[T] {

  def equiv(call1: T, call2: T): Boolean = {
    call1 eq call2
  }
}

