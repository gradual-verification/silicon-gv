package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier


trait WellFormednessRules extends SymbolicExecutionRules {
  def wellformed(s: State,
                 sf: (Sort, Verifier) => Term,
                 e: ast.Exp,
                 pve: PartialVerificationError,
                 v: Verifier)
                (Q: (State, Verifier) => VerificationResult)
                : VerificationResult
}

object wellFormedness extends WellFormednessRules with Immutable {
  import producer._

  def wellformed(s: State,
                 sf: (Sort, Verifier) => Term,
                 e: ast.Exp,
                 pve: PartialVerificationError,
                 v: Verifier)
                (Q: (State, Verifier) => VerificationResult)
                : VerificationResult = {

    produce(s, sf, e, pve, v)((s1, v1) =>
      produce(s, sf, e, pve, v1)((s2, v2) =>
        Q(s2, v2)))
  }
}
