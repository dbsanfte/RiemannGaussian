/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreCountBits

/-! # Finite physical branch-count circuit budgets
The recursive terminal guard is an internal proof interface for original metadata
bounds. It never supplies runtime terminal answers or count words.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceScoreCountBitsBudget
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceOffsetInputsCore SemiprimeSourceScoreCountBitsCore
open SemiprimeReportPolynomialGrowth

/-- Exact reachable-leaf resource obligation, with the same override recursion. -/
def TerminalCap {r Q : ℕ} (alphabet : List (Word r Q))
    (terminal : Environment r Q → Run Bool) (B : ℕ) : List ℕ → Environment r Q → Prop
  | [],env => (terminal env).work ≤ B
  | i::remaining,env => ∀ w∈alphabet,TerminalCap alphabet terminal B remaining (extend env i w)

/-- Literal finite-loop envelope for actual branch additions and child reports. -/
def countBudget (L Q B : ℕ) : ℕ → ℕ
  | 0 => B+2
  | m+1 => L*(countBudget L Q B m+Q+2+11*(1+m*L+L)+7)+1+L+3

/-- Every actual physical branch report is bounded from its reachable terminals. -/
theorem count_clock {r Q : ℕ} (alphabet : List (Word r Q))
    (terminal : Environment r Q → Run Bool) (B : ℕ) (remaining : List ℕ) (env : Environment r Q)
    (ht : TerminalCap alphabet terminal B remaining env) :
    (count alphabet terminal remaining env).clock ≤ countBudget alphabet.length Q B remaining.length := by
  induction remaining generalizing env with
  | nil =>
    change (terminal env).work+2 ≤ B+2
    exact Nat.add_le_add_right ht 2
  | cons i remaining ih =>
    have h := sumBits_clock (fun w =>
      let child := count alphabet terminal remaining (extend env i w)
      (⟨child.bits,child.clock+Q+2⟩:NatRun)) alphabet
      (1+remaining.length*alphabet.length) (countBudget alphabet.length Q B remaining.length+Q+2)
      (fun w _ => count_length alphabet terminal remaining (extend env i w))
      (fun w hw => Nat.add_le_add_right (Nat.add_le_add_right (ih _ (ht w hw)) Q) 2)
    simpa only [count,countBudget,List.length_cons,Nat.add_assoc] using
      Nat.add_le_add_right (Nat.add_le_add_right h alphabet.length) 3

/-- With a nonempty original alphabet, additional completion levels cannot lower the cap. -/
theorem countBudget_le_succ (L Q B m : ℕ) (hL : 0<L) :
    countBudget L Q B m ≤ countBudget L Q B (m+1) := by
  have h : countBudget L Q B m ≤ L*countBudget L Q B m := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (countBudget L Q B m) (show 1≤L from hL)
  have h' := Nat.mul_le_mul_left L
    (show countBudget L Q B m ≤ countBudget L Q B m+Q+2+11*(1+m*L+L)+7 from by omega)
  change countBudget L Q B m ≤ L*(countBudget L Q B m+Q+2+11*(1+m*L+L)+7)+1+L+3
  omega

/-- At-most-four active coordinates use a fixed-depth polynomial. -/
theorem countBudget_le_four (L Q B m : ℕ) (hL : 0<L) (hm : m≤4) :
    countBudget L Q B m ≤ countBudget L Q B 4 :=
  monotone_nat_of_le_succ (fun k => countBudget_le_succ L Q B k hL) hm

/-- Fixed monomial growth for the actual maximum local completion depth. -/
theorem countBudget_monomial : ∃ C k : ℕ,∀ S,countBudget S S S 4 ≤ C*(S+1)^k := by
  change SemiprimeReportPolynomialGrowth.Bound (fun S => countBudget S S S 4)
  simp only [countBudget]
  boundArithmetic

end RiemannGaussian.SemiprimeSourceScoreCountBitsBudget
