/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeNumeric
open SemiprimeD1StackPortOwnerRecipe SemiprimeD1StackPortOwnerRecipeSpec
open SemiprimeD1StackPortOwnerRecipePrepare SemiprimeD1StackPortOwnerRecipeAcquisition
open SemiprimeD1StackPortOwnerRecipeEmit
/-- Actual acquired unary operand inventory, with fixed room for literal mode tags. -/
def volume (p:Counters) : ℕ := p.r+p.t+p.digits+p.tag+p.a+p.b+p.c+p.d+10
/-- A fixed quadratic cap for every operand of any real preparation primitive. -/
def cap (p:Counters) : ℕ := (volume p+1)^2
/-- Every primitive operand cap is derived from the original acquired counters. -/
theorem operand_caps (p:Counters) :
    9≤cap p ∧ p.r≤cap p ∧ p.t≤cap p ∧ p.digits≤cap p ∧ p.tag≤cap p ∧
    p.a≤cap p ∧ p.b≤cap p ∧ p.c≤cap p ∧ p.d≤cap p ∧
    p.r*p.t≤cap p ∧ p.r*p.t+1≤cap p ∧ p.a/p.r≤cap p ∧ p.b/p.r≤cap p ∧
    p.a%p.r≤cap p ∧ p.b%p.r≤cap p ∧ p.c+p.t≤cap p ∧ p.c+p.r≤cap p ∧
    p.a-1≤cap p ∧ p.b-1≤cap p ∧ p.digits-1≤cap p ∧ p.b+1≤cap p := by
  let s:=volume p
  have hs:10 ≤ s:=by dsimp [s,volume];omega
  have hr:p.r ≤ s:=by dsimp [s,volume];omega
  have ht:p.t ≤ s:=by dsimp [s,volume];omega
  have hd:p.digits ≤ s:=by dsimp [s,volume];omega
  have hg:p.tag ≤ s:=by dsimp [s,volume];omega
  have ha:p.a ≤ s:=by dsimp [s,volume];omega
  have hb:p.b ≤ s:=by dsimp [s,volume];omega
  have hc:p.c ≤ s:=by dsimp [s,volume];omega
  have he:p.d ≤ s:=by dsimp [s,volume];omega
  have hct:p.c+p.t ≤ s:=by dsimp [s,volume];omega
  have hcr:p.c+p.r ≤ s:=by dsimp [s,volume];omega
  have hbn:p.b+1 ≤ s:=by dsimp [s,volume];omega
  have hprod:p.r*p.t ≤ s^2:=by simpa only [pow_two] using Nat.mul_le_mul hr ht
  have hbase:s≤(s+1)^2:=by nlinarith
  have hdiva: p.a/p.r≤p.a:=Nat.div_le_self _ _
  have hdivb: p.b/p.r≤p.b:=Nat.div_le_self _ _
  have hmoda: p.a%p.r≤p.a:=Nat.mod_le _ _
  have hmodb: p.b%p.r≤p.b:=Nat.mod_le _ _
  have hsuba:p.a-1≤p.a:=Nat.sub_le _ _
  have hsubb:p.b-1≤p.b:=Nat.sub_le _ _
  have hsubd:p.digits-1≤p.digits:=Nat.sub_le _ _
  change 9≤(s+1)^2 ∧ _
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals change _ ≤ (s+1)^2
  all_goals first | omega | nlinarith
/-- Fresh scalar bound on the actual nested unary multiply-plus-offset trace. -/
theorem madd_clock (R a b c:ℕ) (ha:a≤R) (hb:b≤R) (hc:c≤R) :
    SemiprimeD1StackPortOwnerMaddBounds.budget a b c+1≤1000*(R+1)^2 := by
  have hab:a*b≤R^2:=by simpa only [pow_two] using Nat.mul_le_mul ha hb
  unfold SemiprimeD1StackPortOwnerMaddBounds.budget
  nlinarith
/-- Fresh scalar bound on the actual output counter of multiply-plus-offset. -/
theorem madd_value (R a b c:ℕ) (ha:a≤R) (hb:b≤R) (hc:c≤R) : a*b+c≤2*(R+1)^2 := by
  have hab:a*b≤R^2:=by simpa only [pow_two] using Nat.mul_le_mul ha hb
  nlinarith
/-- ALL real preparation call costs have one fixed operand-polynomial bound. -/
theorem stepTime_le (p:Counters) (pc:Fin 41) : stepTime p pc≤1000*(cap p+1)^2 := by
  obtain ⟨h9,hr,ht,hd,hg,ha,hb,hc,he,hprod,hwidth,hqa,hqb,hma,hmb,hct,hcr,ham,hbm,hdm,hbn⟩:=operand_caps p
  generalize hR:cap p=R at *
  clear hR
  fin_cases pc
  all_goals dsimp only [stepTime]
  all_goals first
    | (apply madd_clock <;> omega)
    | nlinarith
/-- Every literal computed register width is derived from the acquired operand inventory. -/
theorem cached_length_le (p:Counters) (k:Register) : (cached p 41 k).length≤2*(cap p+1)^2 := by
  obtain ⟨h9,hr,ht,hd,hg,ha,hb,hc,he,hprod,hwidth,hqa,hqb,hma,hmb,hct,hcr,ham,hbm,hdm,hbn⟩:=operand_caps p
  generalize hR:cap p=R at *
  clear hR
  have hsingle:R≤2*(R+1)^2:=by nlinarith
  have hdouble:2*R≤2*(R+1)^2:=by nlinarith
  cases k <;> dsimp [cached] <;>
    try simp only [SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  all_goals first
    | (apply madd_value <;> omega)
    | omega
/-- All acquired readonly input widths obey the same honest physical cap. -/
theorem input_length_le (p:Counters) (k:Input) : (words p k).length≤2*(cap p+1)^2 := by
  obtain ⟨h9,hr,ht,hd,hg,ha,hb,hc,he,_⟩:=operand_caps p
  generalize hR:cap p=R at *
  clear hR
  have hsingle:R≤2*(R+1)^2:=by nlinarith
  cases k <;> simp only [words,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  all_goals first | omega | (split <;> (simp; try omega))
/-- Every prepared physical role, including real comparison bits and all scratch, is bounded. -/
theorem prepared_length_le (p:Counters) (k:Stack) : (prepared p k).length≤2*(cap p+1)^2 := by
  rcases k with k|k
  · exact input_length_le p k
  · rcases k with k|k
    · exact cached_length_le p k
    · exact Nat.zero_le _
/-- Tag-consumption clears one actual counter and introduces no new word advice. -/
theorem ready_length_le (p:Counters) (k:Stack) : (ready p k).length≤2*(cap p+1)^2 := by
  by_cases he:k=reg .tagReader
  · subst k
    simp [ready]
  · rw [ready,Function.update_of_ne he]
    exact prepared_length_le p k
/-- Every selected scalar field comes from an actually bounded acquired role. -/
theorem mass_le (p:Counters) (recipe:Recipe) : mass p recipe≤12*(cap p+1)^2 := by
  have h0:=ready_length_le p (fields recipe 0)
  have h1:=ready_length_le p (fields recipe 1)
  have h2:=ready_length_le p (fields recipe 2)
  have h3:=ready_length_le p (fields recipe 3)
  have h4:=ready_length_le p (fields recipe 4)
  have h5:=ready_length_le p (fields recipe 5)
  unfold mass word
  omega
/-- The actual chronological preparation budget pays every site exactly once. -/
theorem remainingBudget_le (p:Counters) (fuel count:ℕ) :
    remainingBudget p fuel count≤fuel*(1000*(cap p+1)^2) := by
  induction fuel generalizing count with
  | zero=>simp [remainingBudget]
  | succ fuel ih=>
    unfold remainingBudget
    split_ifs with hc
    · have hs:=stepTime_le p ⟨count,hc⟩
      have ht:=ih (count+1)
      nlinarith
    · exact Nat.zero_le _
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeNumeric
