package viper.silicon.state

import viper.silicon.Stack
import viper.silver.ast.Exp
import scala.collection.concurrent.{Map, TrieMap}

case class ChecksInfo(checks: Seq[Exp], branch: Stack[Exp])

object runtimeChecks {

  // Maps a pair of line and column numbers to the runtime checks that must be done there
  //
  // We may need to track branch information for the case where a program
  // statement or expression after a conditional is dependent on the result of
  // the conditional; we may need to check the branch taken in the runtime
  // checks
  private val checks: Map[Exp, ChecksInfo] = new TrieMap[Exp, ChecksInfo]

  def addChecks(programPoint: Exp, newChecks: Seq[Exp], branch: Stack[Exp]): Unit = {
    checks.get(programPoint) match {
      case None => (checks += (programPoint -> ChecksInfo(newChecks, branch)))
      case Some(ChecksInfo(oldChecks, branch)) => (checks += (programPoint ->
        ChecksInfo((oldChecks ++ newChecks), branch)))
    }
  }

  def getChecks: Map[Exp, ChecksInfo] = {
    checks
  }
}
