package viper.silicon.supporters

import viper.silver.ast
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.state.{terms, State, Store, BasicChunk}
import viper.silicon.resources.{FieldID, PredicateID}

// should we use the path conditions from the state?
final class Translator(s: State, pcs: RecordedPathConditions) {
  
  // this is, to some extent, a stub method currently
  def translate(t: terms.Term): ast.Exp = {
    t match {
      case terms.Null() => ast.NullLit()()
      case terms.False() => ast.FalseLit()()
      case terms.True() => ast.TrueLit()()
      case terms.IntLiteral(i) => ast.IntLit(i)()
      case terms.Plus(t0, t1) => ast.Add(translate(t0), translate(t1))()
      case terms.Minus(t0, t1) => ast.Sub(translate(t0), translate(t1))()
      case terms.Div(t0, t1) => ast.Div(translate(t0), translate(t1))()
      case terms.Times(t0, t1) => ast.Mul(translate(t0), translate(t1))()
      case terms.Mod(t0, t1) => ast.Mod(translate(t0), translate(t1))()
      case terms.Not(t) => ast.Not(translate(t))()
      // exhaustiveness warnings are suppressed by the following four cases; do
      // these employ match guards via the seq matching?
      case terms.Or(ts) =>
        ts match {
          case t +: Seq() => ast.Or(translate(t), ast.FalseLit()())()
          case t +: vs => ast.Or(translate(t), translate(terms.Or(vs)))()
        }
      case terms.And(ts) =>
        ts match {
          case t +: Seq() => ast.And(translate(t), ast.TrueLit()())()
          case t +: vs => ast.And(translate(t), translate(terms.And(vs)))()
        }
      case terms.Implies(t0, t1) => ast.Implies(translate(t0), translate(t1))()
      case terms.Iff(t0, t1) => ast.And(ast.Implies(translate(t1), translate(t0))(),
        ast.Implies(translate(t0), translate(t1))())()
      case terms.Equals(t0, t1) => ast.EqCmp(translate(t0), translate(t1))()
      case terms.Less(t0, t1) => ast.LtCmp(translate(t0), translate(t1))()
      case terms.AtMost(t0, t1) => ast.LeCmp(translate(t0), translate(t1))()
      case terms.AtLeast(t0, t1) => ast.GeCmp(translate(t0), translate(t1))()
      case terms.Greater(t0, t1) => ast.GtCmp(translate(t0), translate(t1))()
      case terms.Ite(t0, t1, t2) => ast.CondExp(translate(t0), translate(t1), translate(t2))()
      case terms.Var(name, sort) =>
        sort match {
          case terms.sorts.Snap => ast.LocalVar("snapvar", ast.Int)()
          case _ => variableResolver(terms.Var(name, sort))
        }
      case terms.SortWrapper(t, sort) => variableResolver(terms.SortWrapper(t, sort))
      // how do we deal with snapshots? we need not {
      //
      // snapshots only exist in the path condition because the latter is
      // already passed around everywhere; translated snapshot terms should
      // never be returned from diff as part of a necessary runtime check, so
      // we need not translate them
      //
      // these cases only exist to prevent the translator from crashing during
      // testing; the translator is tested on the path condition, which
      // includes snapshot terms
      case terms.Unit => ast.LocalVar("snapvar", ast.Int)()
      case terms.First(_) => ast.LocalVar("snapvar", ast.Int)()
      case terms.Second(_) => ast.LocalVar("snapvar", ast.Int)()
      case terms.Combine(t0, t1) => ast.LocalVar("snapvar", ast.Int)()
      // }
      case _ => sys.error("match error in translate!")
    }
  }

  private def resolveType(variable: terms.Term): ast.Type = {
    variable match {
      case terms.Var(_, terms.sorts.Int) | terms.SortWrapper(_, terms.sorts.Int) => ast.Int
      case terms.Var(_, terms.sorts.Bool) | terms.SortWrapper(_, terms.sorts.Bool) => ast.Bool
      case terms.Var(_, terms.sorts.Ref) | terms.SortWrapper(_, terms.sorts.Ref) => ast.Ref
      case terms.Var(_, terms.sorts.Perm) | terms.SortWrapper(_, terms.sorts.Perm) => ast.Perm
      case _ => sys.error("Match error in resolveType!")
    }
  }

  private def variableResolver(variable: terms.Term): ast.Exp = {

    variableResolverHelper(variable) match {

      case Some(astVariable) => astVariable

      case None => {
        
        val pcsEquivalentVariables: Seq[terms.Term] = pcs.getEquivalentVariables(variable) match {
          case Seq() => sys.error("Could not find an equivalent variable in the "
            + s"path condition for the variable ${variable}!");
          case equivalentVariables => equivalentVariables
        }

        pcsEquivalentVariables.foldRight[Option[ast.Exp]](None)((term, resolvedVariable) =>
            resolvedVariable match {
              case Some(_) => resolvedVariable
              case None => variableResolverHelper(term)
            }) match {
              case Some(resolvedVariable) => resolvedVariable
              case None => sys.error(s"Could not resolve variable ${variable}")
            }
      }
    }
  }

  private def variableResolverHelper(variable: terms.Term): Option[ast.Exp] = {
    
    // TODO: this is not as efficient as it might be; we search both heaps when
    // this may not be necessary
    //
    // a successful variable lookup in one heap obviates the need for a
    // variable lookup in the other

    // TODO: Make this handle predicates

    // TODO: ASK JENNA: What is the old store for? It gets set before method
    // calls
    //
    // Oh, is it for resolving variables in the precondition (and post) using
    // the store from the context of the method call? maybe
    val store: Store = s.oldStore match {
      case None => s.g
      case Some(oldStore) => oldStore
    }

    val varType = resolveType(variable)

    // TODO: The case where both the regular heap and optimistic heap have the
    // variable should never happen, maybe
    (s.h.getChunkForValue(variable), s.optimisticHeap.getChunkForValue(variable)) match {
      case (Some(_), Some(_)) => sys.error("match error in variableResolverHelper!")

      case (Some((symVar, id)), None) =>
        store.getKeyForValue(symVar) match {
          case None => None
          case Some(astVar) => Some(ast.FieldAccess(astVar, ast.Field(id, varType)())())
        }

      case (None, Some((symVar, id))) =>
        store.getKeyForValue(symVar) match {
          case None => None
          case Some(astVar) => Some(ast.FieldAccess(astVar, ast.Field(id, varType)())())
        }

      case (None, None) => store.getKeyForValue(variable)
    }
  }

  def getAccessibilityPredicates: Iterable[ast.Exp] = {

    (s.h.values ++ s.optimisticHeap.values).map(chunk => chunk match {
      case BasicChunk(resourceId, id, args, snap, perm) => resourceId match {
        // TODO: Can we use translate for this case (or at least variableResolver?)
        // TODO: Does this need to access the old store?
        // TODO: Does this need to look in the path condition for equivalent
        //       variables? probably not, since it doesn't look in the heap
        case FieldID => {

          println(s"getAccessibilityPredicates argument head value: ${args.head}") 
          println(s"getAccessibilityPredicates argument value: ${args}")

          val varType = resolveType(args.head)

          val astVar = s.g.getKeyForValue(args.head) match {
            case None => sys.error(s"Could not resolve symbolic variable ${args.head}!")
            case Some(astVar) => astVar
          }

          ast.FieldAccess(astVar, ast.Field(id.toString, varType)())()
        }

        case PredicateID => {
          
          ast.PredicateAccess(args.map(predicateArg => translate(predicateArg)), id.toString)()
        }
      }
    })
  }
}
