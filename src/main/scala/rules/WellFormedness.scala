package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silicon.state.terms._
import viper.silicon.verifier.Verifier


trait WellFormednessRules extends SymbolicExecutionRules {
  def wellFormed(s: State,
                 sf: (Sort, Verifier) => Term,
                 e: ast.Exp,
                 pve: PartialVerificationError,
                 v: Verifier)
                (Q: (State, Verifier) => VerificationResult)
                : VerificationResult
}

object wellFormedness extends WellFormednessRules with Immutable {
  import producer._

  def wellFormed(s: State,
                 sf: (Sort, Verifier) => Term,
                 e: ast.Exp,
                 pve: PartialVerificationError,
                 v: Verifier)
                (Q: (State, Verifier) => VerificationResult)
                : VerificationResult = {

    produces(s, sf, e, pve, v)((s1, v1) =>
      produces(s, sf, e, pve, v1)((s2, v2) =>
        Q(s2, v2)))
  }
}
