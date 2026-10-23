package viper.silicon.supporters

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.{PreambleContributor}
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.terms
import viper.silicon.state.terms._
import viper.silicon.state.{Identifier, IdentifierFactory}
import viper.silicon.state.terms.{Sort, SortDecl, sorts}
import viper.silicon.state.SymbolConverter
import viper.silver.ast
import viper.silver.ast.Program


class ArrayContributor(symbolConverter: SymbolConverter, identifierFactory: IdentifierFactory) extends PreambleContributor[Sort, terms.Function, terms.Term] {
  private var collectedTypeInstances: InsertionOrderedSet[ast.Type] = InsertionOrderedSet.empty
  private var collectedSorts: InsertionOrderedSet[sorts.Array] = InsertionOrderedSet.empty
  private var collectedFunctions: InsertionOrderedSet[terms.Function] = InsertionOrderedSet.empty
  private var collectedAxioms: InsertionOrderedSet[terms.Term] = InsertionOrderedSet.empty
  
  override def analyze(program: Program): Unit = {
    if (!program.existsDefined { case _ : ast.ArrayExp => true }) return

    program visit {
      case e @ ast.ArrayIndex(s, _)  => { collectedTypeInstances += e.typ }
      case ast.ArrayUpdate(_, _, elem) => { collectedTypeInstances += elem.typ }
    }

    
    collectedSorts = InsertionOrderedSet(collectedTypeInstances.map(typ => sorts.Array(symbolConverter.toSort(typ))))
    

    /* Array_length */
    collectedSorts.foreach 
      { sort => 
        collectedFunctions += terms.SMTFun(Identifier("Array_length"), sort, sorts.Int) 
        collectedFunctions += terms.SMTFun(Identifier("Array_index"), Seq(sort, sorts.Int), sort.elementsSort) }

    collectedSorts.foreach
      { sort =>
        val qvar = Var(identifierFactory.fresh("a"), sort, false)
        collectedAxioms += Forall(qvar, Less((predef.Zero, ArrayLength(qvar))), Trigger(ArrayLength(qvar))) }

    //Axiom of injectivity for Array[Ref]
    val qvar1 = Var(identifierFactory.fresh("a"), sorts.Array(sorts.Ref), false)
    val qvar2 = Var(identifierFactory.fresh("i1"), sorts.Int, false)
    val qvar3 = Var(identifierFactory.fresh("i2"), sorts.Int, false)
    collectedAxioms += Forall(Seq(qvar1, qvar2, qvar3), Implies(
      (And(Seq(
        AtMost(predef.Zero, qvar2),
        Less(qvar2, ArrayLength(qvar1)),
        AtMost(predef.Zero, qvar3),
        Less(qvar3, ArrayLength(qvar1)),
        Not(BuiltinEquals((qvar2, qvar3)))
      )),
      Not(BuiltinEquals(ArrayAt(qvar1, qvar2), ArrayAt(qvar1, qvar3))))
    ), Trigger(Seq())) 
  }

  override def sortsAfterAnalysis: Iterable[Sort] = collectedSorts

  override def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
  }

  override def symbolsAfterAnalysis: Iterable[terms.Function] = collectedFunctions

  override def declareSymbolsAfterAnalysis(sink: ProverLike): Unit = {
    symbolsAfterAnalysis foreach (f => sink.declare(terms.FunctionDecl(f)))
  }

  override def axiomsAfterAnalysis: Iterable[terms.Term] = collectedAxioms

  override def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = {
    sink.assumeAxioms(collectedAxioms, "Array axioms")
  }

  def reset(): Unit = {
    collectedTypeInstances = InsertionOrderedSet.empty
    collectedSorts = InsertionOrderedSet.empty
  }

  def stop(): Unit = {}
  def start(): Unit = {}
}
