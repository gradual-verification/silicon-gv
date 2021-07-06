package viper.silicon.state

import viper.silver.ast.Exp
import scala.collection.concurrent.{Map, TrieMap}

object runtimeChecks {

  // Maps a pair of line and column numbers to the runtime checks that must be done there
  //
  // We may need to track branch information for the case where a program
  // statement or expression after a conditional is dependent on the result of
  // the conditional; we may need to check the branch taken in the runtime
  // checks
  private val checks: Map[(Int, Int), Seq[Exp]] = new TrieMap[(Int, Int), Seq[Exp]]

  def addChecks(programPoint: (Int, Int), newChecks: Seq[Exp]): Unit = {
    checks.get(programPoint) match {
      case None => (checks += (programPoint -> newChecks))
      case Some(oldChecks) => (checks += (programPoint -> (oldChecks ++ newChecks)))
    }
  }

  def getChecks: Map[(Int, Int), Seq[Exp]] = {
    checks
  }
}
