package viper.silicon.supporters

import viper.silicon.state.terms


object TermDifference {

  def visitor(expansionPhase: terms.Term => terms.Term, excludedTerms: Seq[String], term: terms.Term): terms.Term = term match {
    case terms.Null() if excludedTerms.contains("Null") => expansionPhase(terms.Null())
    case terms.Null() => terms.Null()
    case terms.False() if excludedTerms.contains("False") => expansionPhase(terms.False())
    case terms.False() => terms.False()
    case terms.True() if excludedTerms.contains("True") => expansionPhase(terms.True())
    case terms.True() => terms.True()
    case terms.IntLiteral(i) if excludedTerms.contains("IntLiteral") => expansionPhase(terms.IntLiteral(i))
    case terms.IntLiteral(i) => terms.IntLiteral(i)
    case terms.Plus(t0, t1) if excludedTerms.contains("Plus") => expansionPhase(terms.Plus(t0, t1))
    case terms.Plus(t0, t1) => terms.Plus(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.Minus(t0, t1) if excludedTerms.contains("Minus") => expansionPhase(terms.Minus(t0, t1))
    case terms.Minus(t0, t1) => terms.Minus(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.Div(t0, t1) if excludedTerms.contains("Div") => expansionPhase(terms.Div(t0, t1))
    case terms.Div(t0, t1) => terms.Div(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.Times(t0, t1) if excludedTerms.contains("Times") => expansionPhase(terms.Times(t0, t1))
    case terms.Times(t0, t1) => terms.Times(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.Mod(t0, t1) if excludedTerms.contains("Mod") => expansionPhase(terms.Mod(t0, t1))
    case terms.Mod(t0, t1) => terms.Mod(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.Not(t) if excludedTerms.contains("Not") => expansionPhase(terms.Not(t))
    case terms.Not(t) => terms.Not(visitor(expansionPhase, excludedTerms, t))
    case terms.Or(ts) if excludedTerms.contains("Or") => expansionPhase(terms.Or(ts))
    case terms.Or(ts) => terms.Or(ts.map(term => visitor(expansionPhase, excludedTerms, term)))
    case terms.And(ts) if excludedTerms.contains("And") => expansionPhase(terms.And(ts))
    case terms.And(ts) => terms.And(ts.map(term => visitor(expansionPhase, excludedTerms, term)))
    case terms.Implies(t0, t1) if excludedTerms.contains("Implies") => expansionPhase(terms.Implies(t0, t1))
    case terms.Implies(t0, t1) => terms.Implies(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.Iff(t0, t1) if excludedTerms.contains("Iff") => expansionPhase(terms.Iff(t0, t1))
    case terms.Iff(t0, t1) => terms.Iff(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.Equals(t0, t1) if excludedTerms.contains("Equals") => expansionPhase(terms.Equals(t0, t1))
    case terms.Equals(t0, t1) => terms.Equals(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.Less(t0, t1) if excludedTerms.contains("Less") => expansionPhase(terms.Less(t0, t1))
    case terms.Less(t0, t1) => terms.Less(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.AtMost(t0, t1) if excludedTerms.contains("AtMost") => expansionPhase(terms.AtMost(t0, t1))
    case terms.AtMost(t0, t1) => terms.AtMost(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.AtLeast(t0, t1) if excludedTerms.contains("AtLeast") => expansionPhase(terms.AtLeast(t0, t1))
    case terms.AtLeast(t0, t1) => terms.AtLeast(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.Greater(t0, t1) if excludedTerms.contains("Greater") => expansionPhase(terms.Greater(t0, t1))
    case terms.Greater(t0, t1) => terms.Greater(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1))
    case terms.Ite(t0, t1, t2) if excludedTerms.contains("Ite") => expansionPhase(terms.Ite(t0, t1, t2))
    case terms.Ite(t0, t1, t2) => terms.Ite(visitor(expansionPhase, excludedTerms, t0), visitor(expansionPhase, excludedTerms, t1), visitor(expansionPhase, excludedTerms, t2))
    case terms.Var(name, sort) if excludedTerms.contains("Var") => expansionPhase(terms.Var(name, sort))
    case terms.Var(name, sort) => terms.Var(name, sort)
  }

  def eliminateImplications(symbolicValue: terms.Term): terms.Term = symbolicValue match {
    case terms.Implies(t0, t1) =>
      terms.Or(Seq(
        visitor(eliminateImplications, Seq("Implies", "Iff"), terms.Not(t0)),
        visitor(eliminateImplications, Seq("Implies", "Iff"), t1)))
    case terms.Iff(t0, t1) =>
      terms.And(Seq(
        terms.Or(Seq(
          visitor(eliminateImplications, Seq("Implies", "Iff"), terms.Not(t0)),
          visitor(eliminateImplications, Seq("Implies", "Iff"), t1))),
        terms.Or(Seq(
          visitor(eliminateImplications, Seq("Implies", "Iff"), t0),
          visitor(eliminateImplications, Seq("Implies", "Iff"), terms.Not(t1))))))
    case t => visitor(eliminateImplications, Seq("Implies", "Iff"), t)
  }

  def pushNegations(symbolicValue: terms.Term): terms.Term = symbolicValue match {
    case terms.Not(terms.And(ts)) => terms.Or(ts.map(term => pushNegations(terms.Not(term))))
    case terms.Not(terms.Or(ts)) => terms.And(ts.map(term => pushNegations(terms.Not(term))))
    case terms.Not(t) => terms.Not(visitor(pushNegations, Seq("Not"), t))
    case t => visitor(pushNegations, Seq("Not"), t)
  }

  def eliminateNestedOrs(symbolicValue: terms.Term): terms.Term = symbolicValue match {
    case terms.Or(ts) => terms.Or(returnOrBodies(symbolicValue))
    case t => visitor(eliminateNestedOrs, Seq("Or"), t)
  }

  def returnOrBodies(symbolicValue: terms.Term): Seq[terms.Term] = symbolicValue match {
    case terms.Or(ts) => ts.foldRight(Seq[terms.Term]())((term, restTerms) =>
        term match {
          case terms.Or(vs) => returnOrBodies(terms.Or(vs)) ++: restTerms
          case t => visitor(eliminateNestedOrs, Seq("Or"), t) +: restTerms
        })
  }

  // this must get called when an or is encountered, possibly or probably
  def pullAnds(symbolicValue: terms.Term): terms.Term = eliminateNestedOrs(symbolicValue) match {
    case terms.Or(ts) => 
      ts.find(term => term match {
        case terms.And(_) => true
        case _ => false
      }) match {
        case None => terms.Or(ts.map(term => visitor(pullAnds, Seq("Or"), term)))
        // this branch must be taken when that or term contains an and term, maybe
        case Some(t) => expandAnds(t, ts.filterNot(term => term == t))
      }
    case t => visitor(pullAnds, Seq("Or"), t)
  }

  def expandAnds(andTerm: terms.Term, orContents: Seq[terms.Term]): terms.Term = andTerm match {
    case terms.And(ts) => terms.And(ts.map(term => pullAnds(terms.Or(term +: ts))))
  }

  def eliminateNestedAnds(symbolicValue: terms.Term): terms.Term = symbolicValue match {
    case terms.And(ts) => terms.And(returnAndBodies(terms.And(ts)))
    case t => visitor(eliminateNestedAnds, Seq("And"), t)
  }

  def returnAndBodies(symbolicValue: terms.Term): Seq[terms.Term] = symbolicValue match {
    case terms.And(ts) => ts.foldRight(Seq[terms.Term]())((term, restTerms) =>
        term match {
          case terms.And(_) => returnAndBodies(term) ++: restTerms
          case t => visitor(eliminateNestedAnds, Seq("And"), t) +: restTerms
        })
  }

  val makeVar: String => terms.Var = (varName: String) => terms.Var(viper.silicon.state.Identifier(varName), terms.sorts.Int)

  val simpleImplicationTerm = terms.Implies(makeVar("x"), makeVar("y"))

  val simpleNegationTerm = terms.Not(makeVar("x"))

  val moreComplexNegationTerm = terms.Not(simpleImplicationTerm)

  // 3
  val moreComplexImplicationTerm = terms.Iff(terms.Implies(makeVar("a"), makeVar("e")), moreComplexNegationTerm)

  val evenMoreComplexNegationTerm = terms.Not(moreComplexNegationTerm)

  val evenMoreComplexNegationTermForRealThisTime = terms.Not(moreComplexImplicationTerm)

  // 10
  val termWithIgnoredTerms =
    terms.Iff(
      terms.Plus(terms.Var(viper.silicon.state.Identifier("k"), terms.sorts.Int), makeVar("w")),
      terms.Not(terms.Implies(
        terms.Plus(
          terms.Not(moreComplexImplicationTerm),
          terms.Not(evenMoreComplexNegationTermForRealThisTime)),
        terms.Not(evenMoreComplexNegationTerm))))

  // 24
  val moreComplexTermWithIgnoredTerms = terms.Implies(terms.Plus(termWithIgnoredTerms, evenMoreComplexNegationTermForRealThisTime), termWithIgnoredTerms)

  def testCNFTransform(): Unit = {

    println(pushNegations(eliminateImplications(simpleImplicationTerm)))

    println(pushNegations(eliminateImplications(simpleNegationTerm)))

    println(pushNegations(eliminateImplications(moreComplexNegationTerm)))

    println(pushNegations(eliminateImplications(moreComplexImplicationTerm)))

    println(pushNegations(eliminateImplications(evenMoreComplexNegationTerm)))

    println(pushNegations(eliminateImplications(evenMoreComplexNegationTermForRealThisTime)))

    println(pushNegations(eliminateImplications(termWithIgnoredTerms)))

    println(pullAnds(pushNegations(eliminateImplications(evenMoreComplexNegationTermForRealThisTime))))

    println(pullAnds(pushNegations(eliminateImplications(termWithIgnoredTerms))))

    println(eliminateNestedAnds(pullAnds(pushNegations(eliminateImplications(termWithIgnoredTerms)))))

    println(moreComplexTermWithIgnoredTerms)

    println(pushNegations(eliminateImplications(moreComplexTermWithIgnoredTerms)))

    println(eliminateNestedAnds(pullAnds(pushNegations(eliminateImplications(moreComplexTermWithIgnoredTerms)))))

    println(eliminateNestedAnds(eliminateNestedAnds(pullAnds(pushNegations(eliminateImplications(moreComplexTermWithIgnoredTerms))))))
  }
}
