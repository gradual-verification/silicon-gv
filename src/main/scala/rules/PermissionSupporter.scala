// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

// Copied from 
// https://github.com/viperproject/silicon/blob/4d756c797d31cb37f03a6e759c7b128bd0e306b5/src/main/scala/rules/PermissionSupporter.scala
// - CL

package viper.silicon.rules

import viper.silver.ast
import viper.silver.verifier.PartialVerificationError
import viper.silicon.interfaces.VerificationResult
import viper.silicon.state.State
import viper.silicon.state.terms.{Term, Var, perms}
import viper.silicon.verifier.Verifier
import viper.silver.verifier.reasons.{NegativePermission, NonPositivePermission}
import viper.silicon.state.{runtimeChecks, CheckPosition, BranchCond}
import viper.silicon.supporters.Translator

object permissionSupporter extends SymbolicExecutionRules {
  def assertNotNegative(s: State, tPerm: Term, ePerm: ast.Exp, pve: PartialVerificationError, v: Verifier)
                       (Q: (State, Verifier) => VerificationResult) 
                       : VerificationResult = { // maybe need to add profiling information?

    tPerm match {
      case k: Var if s.constrainableARPs.contains(k) => // dead case since we don't support wildcard
        Q(s, v)
      case _ =>
        v.decider.assertgv(s.isImprecise, perms.IsNonNegative(tPerm)) {
          case true => Q(s, v)
          case false => 
            createFailure(pve dueTo NegativePermission(ePerm), v, s)
        }
        match { 
          case (verificationResult, Some(_)) =>
            // small optimization - since IsNonNegative returns p == 0 || 0 < p, instead just hardcode 0 <= p
            if (s.generateChecks) {
              val g = s.oldStore match {
                case Some(g) => g
                case None => s.g
              }

              val runtimeCheckAstNode: CheckPosition =
                (s.methodCallAstNode, s.foldOrUnfoldAstNode, s.loopPosition) match {
                  case (None, None, None) => CheckPosition.GenericNode(ePerm)
                  case (Some(methodCallAstNode), None, None) =>
                    CheckPosition.GenericNode(methodCallAstNode)
                  case (None, Some(foldOrUnfoldAstNode), None) =>
                    CheckPosition.GenericNode(foldOrUnfoldAstNode)
                  case (None, None, Some(loopPosition)) => loopPosition
                  case _ => sys.error("Conflicting positions!")
                }

              val translatedPerm = new Translator(s.copy(g = g), v.decider.pcs).translate(tPerm) 
                match {
                  case None => sys.error("Error translating! Exiting safely.")
                  case Some(expr) => expr
                }
            
              runtimeChecks.addChecks(runtimeCheckAstNode, 
              ast.PermLeCmp(ast.NoPerm()(), translatedPerm)() // should I use translatedPerm or just ePerm here?
              , viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
              v.decider.pcs.branchConditionsAstNodes,
              v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
              ePerm, 
              s.forFraming) // should this just be true
            }
            verificationResult

          case (verificationResult, None) => verificationResult
        } 
      }
    }

  def assertPositive(s: State, tPerm: Term, ePerm: ast.Exp, pve: PartialVerificationError, v: Verifier)
                    (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    tPerm match {
      case k: Var if s.constrainableARPs.contains(k) => // dead case since we don't support wildcard
        Q(s, v)
      case _ =>
        v.decider.assertgv(s.isImprecise, perms.IsPositive(tPerm)) {
          case true => Q(s, v)
          case false => createFailure(pve dueTo NonPositivePermission(ePerm), v, s)
        } match {
          case (verificationResult, Some(_)) => 
            verificationResult

              val g = s.oldStore match {
                case Some(g) => g
                case None => s.g
              }

              val runtimeCheckAstNode: CheckPosition =
                (s.methodCallAstNode, s.foldOrUnfoldAstNode, s.loopPosition) match {
                  case (None, None, None) => CheckPosition.GenericNode(ePerm)
                  case (Some(methodCallAstNode), None, None) =>
                    CheckPosition.GenericNode(methodCallAstNode)
                  case (None, Some(foldOrUnfoldAstNode), None) =>
                    CheckPosition.GenericNode(foldOrUnfoldAstNode)
                  case (None, None, Some(loopPosition)) => loopPosition
                  case _ => sys.error("Conflicting positions!")
                }

              val translatedPerm = new Translator(s.copy(g = g), v.decider.pcs).translate(tPerm)
                match {
                  case None => sys.error("Error translating! Exiting safely.")
                  case Some(expr) => expr
                }

            runtimeChecks.addChecks(runtimeCheckAstNode, 
            ast.PermLtCmp(ast.NoPerm()(), translatedPerm)()
            , viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
            v.decider.pcs.branchConditionsAstNodes,
            v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
            ePerm, 
            s.forFraming) 

            verificationResult

          case (verificationResult, None) => verificationResult
        }
    }
  }
}