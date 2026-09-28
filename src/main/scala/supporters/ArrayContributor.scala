package viper.silicon.supporters

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces.{PreambleContributor}
import viper.silicon.interfaces.decider.ProverLike
import viper.silicon.state.terms.{Sort, SortDecl, sorts}
import viper.silicon.state.SymbolConverter
import viper.silver.ast
import viper.silver.ast.Program

class ArrayContributor(symbolConverter: SymbolConverter) extends PreambleContributor[Sort, String, String] {
  private var collectedTypeInstances: InsertionOrderedSet[ast.Type] = InsertionOrderedSet.empty
  private var collectedSorts: InsertionOrderedSet[sorts.Array] = InsertionOrderedSet.empty
  
  override def analyze(program: Program): Unit = {
    if (!program.existsDefined { case _ : ast.ArrayExp => true }) return

    program visit {
     case e @ ast.ArrayIndex(s, _)  => { collectedTypeInstances += e.typ }
    }

    println(collectedTypeInstances)
    
    collectedSorts = InsertionOrderedSet(collectedTypeInstances.map(typ => sorts.Array(symbolConverter.toSort(typ))))
    println(collectedSorts)
  }

  override def sortsAfterAnalysis: Iterable[Sort] = collectedSorts

  override def declareSortsAfterAnalysis(sink: ProverLike): Unit = {
    sortsAfterAnalysis foreach (s => sink.declare(SortDecl(s)))
  }

  override def symbolsAfterAnalysis: Iterable[String] = Seq.empty

  override def declareSymbolsAfterAnalysis(sink: ProverLike): Unit = {}

  override def axiomsAfterAnalysis: Iterable[String] = Seq.empty

  override def emitAxiomsAfterAnalysis(sink: ProverLike): Unit = {}

  def reset(): Unit = {
    collectedTypeInstances = InsertionOrderedSet.empty
    collectedSorts = InsertionOrderedSet.empty
  }

  def stop(): Unit = {}
  def start(): Unit = {}
}
