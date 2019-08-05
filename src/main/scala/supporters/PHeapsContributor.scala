// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.{Config, Map}
import viper.silicon.interfaces.{PreambleContributor, PreambleReader}
import viper.silicon.interfaces.decider.{ProverLike, TermConverter}
import viper.silicon.state.SymbolConverter
import viper.silicon.state.terms.{SortDecl, sorts}

trait PHeapsContributor[SO, SY, AX] extends PreambleContributor[SO, SY, AX]

class DefaultPHeapsContributor(preambleReader: PreambleReader[String, String],
                                            symbolConverter: SymbolConverter,
                                            termConverter: TermConverter[String, String, String],
                                            config: Config)
    extends PHeapsContributor[sorts.FieldValueFunction, String, String] {

  /* PreambleBlock = Comment x Lines */
  private type PreambleBlock = (String, Iterable[String])

  private var collectedAbstractFunctions: Seq[ast.Function] = Seq.empty
  private var collectedPredicates: Seq[ast.Predicate] = Seq.empty
  private var collectedFields: Seq[ast.Field] = Seq.empty
  private var collectedFunctionDecls: Iterable[PreambleBlock] = Seq.empty
  private var collectedAxioms: Iterable[PreambleBlock] = Seq.empty

  /* Lifetime */

  def reset() {
    collectedFunctionDecls = Seq.empty
    collectedAxioms = Seq.empty
  }

  def stop() {}
  def start() {}

  /* Functionality */

  def analyze(program: ast.Program) {

	// collectedAbstractFunctions = program.functions
	// collectedPredicates = program.predicates
	// collectedFields = program.fields

    collectedFunctionDecls = generatePHeapFunctions ++ generateFieldFunctionDecls(program.fields) ++ generatePredicateFunctionDecls(program.predicates) /*++ generateFunctionFunctionDecls(program.functions)*/
    collectedAxioms = axiomIII(program.fields) ++ axiomV(program.fields) ++ axiomVI(program.predicates)++ axiomVII() ++ axiomII(program.functions.filter(_.isAbstract)) ++ axiomIV(program.predicates) /*++ axiomI(program.fields, program.predicates)*/ ++ axiomVIII() ++ predicateSingletonFieldDomains(program.predicates, program.fields) ++ predicateSingletonPredicateDomains(program.predicates) ++ fieldSingletonPredicateDomains(program.predicates, program. fields) ++ fieldSingletonFieldDomains(program.fields)
  }

  private def extractPreambleLines(from: Iterable[PreambleBlock]*): Iterable[String] =
    from.flatten.flatMap(_._2)

  private def emitPreambleLines(sink: ProverLike, from: Iterable[PreambleBlock]*): Unit = {
    from.flatten foreach { case (comment, declarations) =>
      sink.comment(comment)
      sink.emit(declarations)
    }
  }

  def generatePHeapFunctions(): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/pheap_functions.smt2"
  	Seq(("basic pheap functions", preambleReader.readPreamble(templateFile)))	
  }

  def generateFieldFunctionDecls(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/field_functions.smt2"

    fields map (f => {
      val sort = symbolConverter.toSort(f.typ)
      val id = f.name
      val substitutions = Map("$FLD$" -> id, "$S$" -> termConverter.convert(sort))
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"$templateFile [$id: $sort]", declarations)
    })
  }

  def generateFunctionFunctionDecls(functions: Seq[ast.Function]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/function_functions.smt2"

    functions map (f => {
      val id = f.name
      val substitutions = Map("$FUN$" -> id)
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)
      (s"$templateFile [$id]", declarations)
    })
  }

  def generatePredicateFunctionDecls(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/predicate_functions.smt2"

    predicates map (p => {
      val pArgs_q = (p.formalArgs map (a => 
	  	"(" + a.name + " " + termConverter.convert(symbolConverter.toSort(a.typ)) + ")"
	  )).mkString(" ")
      val pArgs = (p.formalArgs map (a => a.name)).mkString(" ")
      val argSorts = (p.formalArgs map (a => termConverter.convert(symbolConverter.toSort(a.typ)))).mkString(" ")
      val id = p.name
      val substitutions = Map(
	  	"$PRD$" -> id,
		"$PRD_ARGS_S$" -> argSorts,
		"$PRD_ARGS_Q$" -> pArgs_q,
		"$PRD_ARGS$" -> pArgs,
	  )
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"$templateFile [$id: $argSorts]", declarations)
    })
  }

  def ext_eq_field(field: ast.Field, h1: String, h2: String): Iterable[String] = {
    val templateFile = "/pheap/partials/ext_eq_field.smt2"

    val id = field.name
    val substitutions = Map(
 	  "$FLD$" -> id,
	  "$H1$" -> h1,
	  "$H2$" -> h2,
	)

    preambleReader.readParametricPreamble(templateFile, substitutions)
  }

  def ext_eq_predicate(predicate: ast.Predicate, h1: String, h2: String): Iterable[String] = {
    val templateFile = "/pheap/partials/ext_eq_predicate.smt2"

    val id = predicate.name
    val substitutions = Map(
 	  "$PRD$" -> id,
	  "$H1$" -> h1,
	  "$H2$" -> h2,
	)

    preambleReader.readParametricPreamble(templateFile, substitutions)
  }

  def axiomI(fields: Seq[ast.Field], predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/axiomI.smt2"

	val h1 = "h1"
	val h2 = "h2"

    val substitutions = Map(
 	  "$ALL_EXT_EQ_FIELD$" -> (if (fields.isEmpty) "true" else (fields flatMap (f => this.ext_eq_field(f, h1, h2))).mkString("\n")),
 	  "$ALL_EXT_EQ_PREDICATE$" -> (if (predicates.isEmpty) "true" else (predicates flatMap (p => this.ext_eq_predicate(p, h1, h2))).mkString("\n")),
	  "$H1$" -> h1,
	  "$H2$" -> h2,
	)

	Seq(("pheap I", (preambleReader.readParametricPreamble(templateFile, substitutions))))
  }

  def axiomIV(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
    val templateFile = "/pheap/axiomIV.smt2"

    predicates map (p => {
      val pArgs_q = (p.formalArgs map (a => 
	  	"(" + a.name + " " + termConverter.convert(symbolConverter.toSort(a.typ)) + ")"
	  )).mkString(" ")
      val pArgs = (p.formalArgs map (a => a.name)).mkString(" ")
      val id = p.name
      val substitutions = Map(
	  	"$PRD$" -> id,
		"$PRD_ARGS$" -> pArgs,
		"$PRD_ARGS_Q$" -> pArgs_q,
	  )
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"$templateFile [$id]", declarations)
    })
  }

  def axiomII(abstractFuncs: Seq[ast.Function]): Iterable[PreambleBlock] = {
	val templateFile = "/pheap/axiomII.smt2"
	abstractFuncs map (f => {
      val id = f.name
	  val substitutions = Map(
	    "$FUN_ARGS_Q$" -> (f.formalArgs map (a =>
	      "(" + a.name + " " + termConverter.convert(symbolConverter.toSort(a.typ)) + ")"
	      )).mkString(" "),
	    "$FUN_ARGS$" -> (f.formalArgs map (_.name)).mkString(" "),
	    "$FUN$" -> id,
	  )
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"pheap II($id)", declarations)
	})
  }

  def axiomIII(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
	val templateFile = "/pheap/axiomIII.smt2"

    fields map (f => {
      val sort = symbolConverter.toSort(f.typ)
      val id = f.name
      val substitutions = Map("$FLD$" -> id, "$S$" -> termConverter.convert(sort))
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"pheap III($id)", declarations)
    })
  }

  def axiomV(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
	val templateFile = "/pheap/axiomV.smt2"

    fields map (f => {
      val sort = symbolConverter.toSort(f.typ)
      val id = f.name
      val substitutions = Map("$FLD$" -> id, "$S$" -> termConverter.convert(sort))
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"pheap V($id)", declarations)
    })
  }

  def axiomVI(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
	val templateFile = "/pheap/axiomVI.smt2"

    predicates map (p => {
      val id = p.name
      val substitutions = Map("$PRD$" -> id)
      val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

      (s"pheap VI($id)", declarations)
    })
  }

  def axiomVII(): Iterable[PreambleBlock] = {
	val templateFile = "/pheap/axiomVII.smt2"
    Seq((s"pheap VII", preambleReader.readPreamble(templateFile)))
  }
  
  def axiomVIII(): Iterable[PreambleBlock] = {
	val templateFile = "/pheap/axiomVIII.smt2"
    Seq((s"pheap VIII", preambleReader.readPreamble(templateFile)))
  }

  def predicateSingletonFieldDomains(predicates: Seq[ast.Predicate], fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
	val templateFile = "/pheap/predicate_singleton_field_domain.smt2"

    predicates flatMap (p => {
      val pred_id = p.name
      val pArgs = (p.formalArgs map (a => a.name)).mkString(" ")
      val pArgs_q = (p.formalArgs map (a => 
	  	"(" + a.name + " " + termConverter.convert(symbolConverter.toSort(a.typ)) + ")"
	  )).mkString(" ")
	  fields map (f => {
	    val field_id = f.name
	    val substitutions = Map(
		  "$PRD$" -> pred_id,
		  "$PRD_ARGS$" -> pArgs,
		  "$PRD_ARGS_Q$" -> pArgs_q,
		  "$FLD$" -> field_id
		)
		val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

		(s"predicate_singleton_field_domain ($pred_id, $field_id)", declarations)
	  })
    })
  }

  def fieldSingletonFieldDomains(fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
	val templateFile = "/pheap/field_singleton_field_domain.smt2"

    fields flatMap (f2 => {
      val field_id2 = f2.name
	  fields map (f => {
	      val field_id = f.name
	    if (field_id2 == field_id) {
          ("", Seq())
		} else {
          val sort = symbolConverter.toSort(f.typ)
    	  val substitutions = Map(
		    "$FLD2$" -> field_id2,
		    "$FLD$" -> field_id,
		    "$S$"   -> termConverter.convert(sort),
	      )
		  val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

		  (s"field_singleton_field_domain ($field_id, $field_id2)", declarations)
		}
	  })
    })
  }

  def fieldSingletonPredicateDomains(predicates: Seq[ast.Predicate], fields: Seq[ast.Field]): Iterable[PreambleBlock] = {
	val templateFile = "/pheap/field_singleton_predicate_domain.smt2"

    predicates flatMap (p => {
      val pred_id = p.name
	  fields map (f => {
	    val field_id = f.name
        val sort = symbolConverter.toSort(f.typ)
	    val substitutions = Map(
		  "$PRD$" -> pred_id,
		  "$FLD$" -> field_id,
		  "$S$"   -> termConverter.convert(sort),
		)
		val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

		(s"field_singleton_predicate_domain ($pred_id, $field_id)", declarations)
	  })
    })
  }

  def predicateSingletonPredicateDomains(predicates: Seq[ast.Predicate]): Iterable[PreambleBlock] = {
	val templateFile = "/pheap/predicate_singleton_predicate_domain.smt2"

    predicates flatMap (p => {
      val pred_id = p.name
      val pArgs = (p.formalArgs map (a => a.name)).mkString(" ")
      val pArgs_q = (p.formalArgs map (a => 
	  	"(" + a.name + " " + termConverter.convert(symbolConverter.toSort(a.typ)) + ")"
	  )).mkString(" ")
	  predicates map (p2 => {
	    val pred_id2 = p2.name
	    if (pred_id2 == pred_id) {
          ("", Seq())
		} else {
	      val substitutions = Map(
		    "$PRD$" -> pred_id,
		    "$PRD_ARGS$" -> pArgs,
		    "$PRD_ARGS_Q$" -> pArgs_q,
		    "$PRD2$" -> pred_id2
		  )
		  val declarations = preambleReader.readParametricPreamble(templateFile, substitutions)

		  (s"predicate_singleton_predicate_domain ($pred_id, $pred_id2)", declarations)
		}
	  })
    })
  }

  def sortsAfterAnalysis: InsertionOrderedSet[sorts.FieldValueFunction] = InsertionOrderedSet.empty

  def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
  	Seq(sorts.PHeap, sorts.Loc) foreach (s => sink.declare(SortDecl(s)))
  }

  val symbolsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedFunctionDecls)

  def declareSymbolsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedFunctionDecls)

  val axiomsAfterAnalysis: Iterable[String] =
    extractPreambleLines(collectedAxioms)

  def emitAxiomsAfterAnalysis(sink: ProverLike): Unit =
    emitPreambleLines(sink, collectedAxioms)

  def updateGlobalStateAfterAnalysis(): Unit = { /* Nothing to contribute*/ }
}