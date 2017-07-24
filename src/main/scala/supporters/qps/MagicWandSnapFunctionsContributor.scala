/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/* TODO: Large parts of this code are identical or at least very similar to the code that
 *       implements the support for quantified permissions to fields - merge it
 */

package  viper.silicon.supporters.qps

import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.Map
import viper.silicon.interfaces.{PreambleContributor, PreambleReader}
import viper.silicon.interfaces.decider.{ProverLike, TermConverter}
import viper.silicon.state.MagicWandIdentifier
import viper.silicon.state.terms.{Sort, SortDecl, sorts}

trait MagicWandSnapFunctionsContributor[SO, SY, AX] extends PreambleContributor[SO, SY, AX]

class DefaultMagicWandSnapFunctionsContributor(preambleReader: PreambleReader[String, String],
                                               termConverter: TermConverter[String, String, String])
  extends MagicWandSnapFunctionsContributor[Sort, String, String] {

  /* PreambleBlock = Comment x Lines */
  private type PreambleBlock = (String, Iterable[String])

  var collectedWands: InsertionOrderedSet[MagicWandIdentifier] = InsertionOrderedSet.empty
  private var collectedFunctionDecls: Iterable[PreambleBlock] = Seq.empty


  /* Lifetime */

  def reset() {
    collectedWands = InsertionOrderedSet.empty
    collectedFunctionDecls = Seq.empty
  }

  def stop() {}

  def start() {}

  /* Functionality */

  def analyze(program: ast.Program) {
    program visit {
      case ast.Forall(_, _, ast.Implies(_, wand: ast.MagicWand)) =>
        collectedWands += MagicWandIdentifier(wand)
    }

    collectedFunctionDecls = generateFunctionDecls
  }

  private def extractPreambleLines(from: Iterable[PreambleBlock]*): Iterable[String] =
    from.flatten.flatMap(_._2)

  private def emitPreambleLines(sink: ProverLike, from: Iterable[PreambleBlock]*): Unit = {
    from.flatten foreach { case (comment, declarations) =>
      sink.comment(comment)
      sink.emit(declarations)
    }
  }

  def generateFunctionDecls: Iterable[PreambleBlock] = {
    /* TODO: The predicate snap function axioms (see method generateAxioms) use set-contains
     *       and set equality (for sort Snap only), but Nadja only emits the necessary set function
     *       declarations, but no corresponding axioms. Looks like an oversight.
     */
    val setsTemplateFile = "/dafny_axioms/qpp_sets_declarations_dafny.smt2"
    val setsSort = sorts.Snap
    val substitutions = Map("$S$" -> termConverter.convert(setsSort))
    val setsDeclarations = preambleReader.readParametricPreamble(setsTemplateFile, substitutions)

    val snapsTemplateFile = "/predicate_snap_functions_declarations.smt2"
    collectedWands map (p => {
        val snapSort = sorts.Snap
        val id = p.toString
        val substitutions = Map("$PRD$" -> id, "$S$" -> termConverter.convert(snapSort))
        val declarations = preambleReader.readParametricPreamble(snapsTemplateFile, substitutions)

        (s"$snapsTemplateFile [${p.ghostFreeWand}: $snapSort]", declarations)
      })
  }

  def sortsAfterAnalysis: InsertionOrderedSet[Sort] = InsertionOrderedSet.empty

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
  }

  val symbolsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedFunctionDecls)

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedFunctionDecls)

  val axiomsAfterAnalysis: Iterable[String] =
    Seq.empty

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = {}

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}
