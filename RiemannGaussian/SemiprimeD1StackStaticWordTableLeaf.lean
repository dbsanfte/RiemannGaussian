/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticWordTableLeafCalls
/-! # Whole actual binary-coefficient leaf and complete physical cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackStaticWordTableLeaf
open SemiprimeD1StackStaticWordTable SemiprimeD1StackStaticWordTableSpec
open SemiprimeD1StackStaticWordTableLeafCalls SemiprimeD1StackStaticWordTableCleanup
open SemiprimeD1StackStaticWordTableEmit SemiprimeD1StackProcedureTrace SemiprimeD1StackProcedureReturns
variable {K L : Type} [DecidableEq K] [Fintype K] (s : Static K L)
/-- Own executed template/assignment/source/framing/cleanup allowance; the
source budget is a proved trace bound and never a physical operand. -/
def leafBound (original : K → List Bool) (budget : Nat → Nat) (width : Nat) : Nat :=
  s.roles.length*(6*inputBytes original+5)+7*width+budget width+
    s.roles.length*(Fintype.card K*(inputBytes original+width+budget width)+1)+
    50*(inputBytes original+width+budget width+1)+50
omit [DecidableEq K] [Fintype K] in
/-- Whole checker clearing preserves exactly the retained template/scanner/DFS words. -/
theorem clean_withChecker (original : K → List Bool) (bank : List Bool) (depth : Nat)
    (front hist : List Bool) (live : K → List Bool) :
    clean (withChecker (data original bank depth front hist) live)=data original bank depth front hist := by
  funext k;cases k <;> rfl
/-- The actual stopped source bank is bounded by its own executed pushes. -/
theorem checker_inventory_le (original : K → List Bool) (raw : List Bool) (budget : Nat → Nat)
    (t : Nat) (finish : C.State K L) (ht : t ≤ budget raw.length)
    (hr : C.run s.code t (checkerInitial s original raw)=some finish) (base : Stack K → List Bool) :
    inventory (withChecker base finish.data) ≤
      Fintype.card K*(inputBytes original+raw.length+budget raw.length) := by
  have hp (k : K) : (finish.data k).length ≤ inputBytes original+raw.length+budget raw.length := by
    have hh := output_cell_le s original raw t finish hr k
    omega
  change (∑ k : K, (finish.data k).length) ≤ _
  calc
    _ ≤ ∑ _k : K, (inputBytes original+raw.length+budget raw.length) := Finset.sum_le_sum (fun k _ => hp k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- COMPLETE actual leaf: physically load every template role, reverse the
actual assignment, call the fixed coefficient source, frame its actual word,
write all tags/reversal, physically drain ALL checker roles, then really return. -/
theorem leaf_returns (original : K → List Bool) (hraw : original s.raw=[])
    (answer : List Bool → List Bool) (budget : Nat → Nat) (hc : CheckerTrace s original answer budget)
    (bank front hist : List Bool) :
    ∃ t ≤ leafBound s original budget front.length, Returns (program s) t .leaf
      (data original bank 0 front hist)
      (data original bank 0 front ((leafBytes (answer front.reverse)).reverse++hist)) := by
  let nextHist := (leafBytes (answer front.reverse)).reverse++hist
  obtain ⟨a,ha,h0⟩ := load_call s original bank front hist
  have h1 := copy_prefix s original bank front hist
  have h2 := reverse_prefix s original hraw bank front hist
  obtain ⟨b,hb,finish,hr,hvalue,h3⟩ := checker_call s original answer budget hc bank front hist
  have h4 := emit_run s finish.data original bank front hist
  rw [hvalue] at h4
  let cleanupData := withChecker (data original bank 0 front nextHist) finish.data
  obtain ⟨c,hcTime,hclear⟩ := clear_returns s cleanupData
  have h5 := SemiprimeD1StackProcedureReturns.call (program s) c .leafCleanup (.clear 0) .leafReturn
    cleanupData (clean cleanupData) rfl hclear
  have he : clean cleanupData=data original bank 0 front nextHist := clean_withChecker original bank 0 front nextHist _
  rw [he] at h5
  have hh := runs_trans (program s) _ _ _ _ _ _ _ _ h0
    (runs_trans (program s) _ _ _ _ _ _ _ _ h1
      (runs_trans (program s) _ _ _ _ _ _ _ _ h2
        (runs_trans (program s) _ _ _ _ _ _ _ _ h3
          (runs_trans (program s) _ _ _ _ _ _ _ _ h4 h5))))
  refine ⟨_,?_,of_runs (program s) _ .leaf .leafReturn _ _ hh rfl⟩
  have hInv := checker_inventory_le s original front.reverse budget b finish
    (by simpa only [List.length_reverse] using hb) hr (data original bank 0 front nextHist)
  have hWord := output_cell_le s original front.reverse b finish hr s.output
  rw [hvalue,List.length_reverse] at hWord
  simp only [List.length_reverse] at hInv
  unfold leafBound
  change inventory cleanupData ≤ _ at hInv
  have hm := Nat.mul_le_mul_left s.roles.length (Nat.add_le_add_right hInv 1)
  omega
end RiemannGaussian.SemiprimeD1StackStaticWordTableLeaf

