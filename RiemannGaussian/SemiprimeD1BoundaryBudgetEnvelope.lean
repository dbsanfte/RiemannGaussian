/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryLeafLoad

/-! # Uniform original-metadata polynomial factors -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryBudgetEnvelope
open SemiprimeD1JetAxes (Context)
open SemiprimeD1BoundaryRecordsGroupBounds
open SemiprimeD1BoundaryRecordsContractBounds
open SemiprimeD1BoundaryRecordsAttachBounds
open SemiprimeD1BoundaryRecordsLookupBounds

/-- Uniform projection factor for lists of length M and identifier inventory P. -/
def projection (M P : Nat) : Nat := 3*(P+1)*(P+1)+3*(M+1)*(M+2)

/-- Uniform two-sort full-jet join factor, independent of any table count. -/
def attachment (ctx : Context) (M P W : Nat) : Nat :=
  projection M P+3*recordBudget ctx M+8+
  200*(requestBudget ctx M M+1)*(W+3)+
  joinBudget ctx (requestBudget ctx M M+recordBudget ctx M)+
  200*(recordBudget ctx M+1)*(W+3)+7

/-- Uniform sort/group contraction factor, independent of any table count. -/
def contraction (ctx : Context) (M P W : Nat) : Nat :=
  projection M P+3*recordBudget ctx M+6+
    200*(recordBudget ctx M+1)*(W+3)+sumBudget ctx M+5

/-- Bound the actual port projection by original metadata inventories. -/
theorem project_le (source target : List Nat) (K M P : Nat)
    (hs : portMass source≤P) (ht : portMass target≤P) (hl : target.length≤M) (hk : K≤M) :
    projectBudget source target K≤projection M P := by
  unfold projectBudget projection
  gcongr

/-- Full record capacity grows monotonically with address width. -/
theorem record_le (ctx : Context) (K M : Nat) (h : K≤M) :
    recordBudget ctx K≤recordBudget ctx M := by unfold recordBudget; omega

/-- Actual whole-ring multiplication allowance is monotone in full record bytes. -/
theorem join_le (ctx : Context) (B C : Nat) (h : B≤C) :
    joinBudget ctx B≤joinBudget ctx C := by
  unfold joinBudget arithmeticBudget SemiprimeD1JetRingBounds.mulBudget
    SemiprimeD1JetRingBounds.mulAtBudget SemiprimeD1JetRingBounds.termBudget
  gcongr

/-- Both actual sorts and the monotone lookup admit one uniform metadata factor. -/
theorem attach_le (ctx : Context) (source target : List Nat) (K B M P W : Nat)
    (hs : portMass source≤P) (ht : portMass target≤P) (hl : target.length≤M)
    (hk : K≤M) (hb : B≤recordBudget ctx M) :
    attachBudget ctx source target K B W≤attachment ctx M P W := by
  have hp:=project_le source target K M P hs ht hl hk
  have hr:=record_le ctx K M hk
  have hreq : requestBudget ctx K target.length≤requestBudget ctx M M := by
    unfold requestBudget; omega
  have hj:=join_le ctx (requestBudget ctx K target.length+B)
    (requestBudget ctx M M+recordBudget ctx M) (by omega)
  unfold attachBudget attachment
  gcongr

/-- Rekey/sort/group work has a uniform metadata polynomial factor. -/
theorem contract_le (ctx : Context) (source target : List Nat) (K M P W : Nat)
    (hs : portMass source≤P) (ht : portMass target≤P) (hl : target.length≤M)
    (hk : K≤M) :
    contractBudget ctx source target K W≤contraction ctx M P W := by
  have hp:=project_le source target K M P hs ht hl hk
  have hr:=record_le ctx K M hk
  have ht':=record_le ctx target.length M hl
  have hsum : sumBudget ctx target.length≤ sumBudget ctx M := by unfold sumBudget; omega
  unfold contractBudget rekeyBudget contraction
  gcongr

end RiemannGaussian.SemiprimeD1BoundaryBudgetEnvelope
