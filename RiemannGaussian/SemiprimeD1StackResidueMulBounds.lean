/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackResidueMulExecution

/-! # General-modulus product time, space and exact original residue
The total trace is bounded in physical input lengths. The original positive-
modulus byte interface follows from the proved divider, without changing clocks.
Operand/cache acquisition remains the enclosing caller's responsibility.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackResidueMulBounds
open SemiprimeD1StackResidueMul SemiprimeD1StackResidueMulExecution
open SemiprimeBitArithmetic

/-- Physical-input polynomial bound, independent of the operand VALUES. -/
def timeBound (n m p : ℕ) : ℕ :=
  SemiprimeD1StackMultiplierExecution.timeBound n m+1000*(2*n+m+p+2)^2+5*p+2*n+m+8

/-- Every literal instruction of the joined multiplier/divider/cleanup is paid. -/
theorem totalTime_le (a b cached : List Bool) :
    totalTime a b cached ≤ timeBound a.length b.length cached.length := by
  have hm:=SemiprimeD1StackMultiplierExecution.source_time a b
  change multiplyTime a b ≤ SemiprimeD1StackMultiplierExecution.timeBound a.length b.length at hm
  have hp:=SemiprimeBitArithmetic.mulBits_length a b
  change (product a b).length ≤ 2*a.length+b.length at hp
  have hd:=(SemiprimeD1StackDividerExecution.source_time (product a b) cached).trans
    (SemiprimeD1StackDividerExecution.timeBound_le_square (product a b).length cached.length)
  have hb : 1000*((product a b).length+cached.length+2)^2 ≤
      1000*(2*a.length+b.length+cached.length+2)^2 := by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (by omega) 2
  have hd':=hd.trans hb
  have hq:=(SemiprimeBitDivision.divideLoop_widths (product a b) cached).2.1
  change (quotient a b cached).length=(product a b).length at hq
  unfold totalTime timeBound
  omega

/-- One fixed cubic monomial bounds this actual complete component. -/
theorem timeBound_le_cube (n m p : ℕ) : timeBound n m p ≤ 10000*(n+m+p+3)^3 := by
  let u:=n+m+p+3
  have hu : 1 ≤ u := by omega
  have hm:SemiprimeD1StackMultiplierExecution.timeBound n m ≤ 1000*u^3 :=
    (SemiprimeD1StackMultiplierExecution.timeBound_le_cube n m).trans
      (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (by dsimp [u];omega) 3))
  have hd : 1000*(2*n+m+p+2)^2 ≤ 4000*u^2 := by
    calc
      _ ≤ 1000*(2*u)^2 := Nat.mul_le_mul_left 1000
        (Nat.pow_le_pow_left (by dsimp [u];omega) 2)
      _ = _ := by ring
  have hl : 5*p+2*n+m+8 ≤ 10*u := by dsimp [u];omega
  have h1 : u ≤ u^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hu (by decide : 1≤3)
  have h2 : u^2 ≤ u^3 := Nat.pow_le_pow_right hu (by decide : 2≤3)
  change timeBound n m p ≤ 10000*u^3
  unfold timeBound
  omega

/-- Proof certificate of actual source transitions, with no supplied elapsed count. -/
def sourceMultiply (a b cached : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial a b cached)
      (some (done a b cached)) (timeBound a.length b.length cached.length) :=
  ⟨⟨_,source_run a b cached⟩,totalTime_le a b cached⟩

/-- The exact source trace is the actual fixed finite-machine execution. -/
def machineMultiply (a b cached : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial a b cached))
      (some (SemiprimeD1StackCalls.configuration (done a b cached)))
      (timeBound a.length b.length cached.length) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) (Sum.inl M.input) output Label.start program
    _ _ _ (sourceMultiply a b cached)

/-- EVERY input, even a zero modulus encoding, returns a physically fixed-width remainder. -/
theorem residue_width (a b cached : List Bool) : (residue a b cached).length=cached.length :=
  (SemiprimeBitDivision.divideLoop_widths (product a b) cached).1

/-- Positive moduli give EXACT bytes of the frozen original modular product. -/
theorem residue_original (a b cached : List Bool) (hm : 0 < bitValue cached) :
    residue a b cached=(SemiprimeBitDivision.modMulBits a b cached).division.remainder := by
  change (SemiprimeBitDivision.divideLoop (product a b) cached).remainder=
    (SemiprimeBitDivision.divideBits (product a b) cached).remainder
  exact (SemiprimeD1StackDividerExecution.divideBits_outputs (product a b) cached hm).2.symm

/-- The actual output value is the literal product residue, without a value oracle. -/
theorem residue_value (a b cached : List Bool) (hm : 0 < bitValue cached) :
    bitValue (residue a b cached)=(bitValue a*bitValue b)%bitValue cached := by
  rw [residue_original a b cached hm]
  exact SemiprimeBitDivision.modMulBits_correct a b cached

/-- The binary modulus word is physically preserved by the whole execution. -/
theorem retained_modulus (a b cached : List Bool) : finalData a b cached modulus=cached := rfl
/-- The designated output is exactly the actual divider's remainder. -/
theorem output_residue (a b cached : List Bool) : finalData a b cached output=residue a b cached := rfl

/-- A successful prefix cannot continue past this actual complete halt. -/
theorem prefix_fuel_le (a b cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial a b cached)=some out) : fuel ≤ totalTime a b cached := by
  by_contra hn
  have he : fuel=totalTime a b cached+(1+(fuel-(totalTime a b cached+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hz : C.run program 1 (done a b cached)=none := rfl
  rw [hz,Option.bind_none] at hr
  cases hr

/-- ALL twenty-two Boolean stacks plus physical return tags fit a fixed cubic
bound at every executed prefix, including repeated copies and division work. -/
theorem prefix_cells (a b cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial a b cached)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 300000*(a.length+b.length+cached.length+3)^3 := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (a.length+b.length+cached.length) _ out (by
    intro k
    rcases k with k|k
    · rcases k with k|k
      · cases k <;> simp only [initial,input,store,M.payload,Sum.elim_inl,List.length_nil] <;> exact Nat.zero_le _
      · rcases k with k|k
        · fin_cases k <;> simp [initial,input,store,M.payload]
          omega
        · cases k <;> simp [initial,input,store,M.payload]
          omega
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;>
          simp [initial,input,store,D.payload]
      · cases k <;> simp [initial,input,store]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 22*(a.length+b.length+cached.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(a.length+b.length+cached.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=((prefix_fuel_le a b cached fuel out hr).trans (totalTime_le a b cached)).trans
    (timeBound_le_cube a.length b.length cached.length)
  have hu : 1 ≤ a.length+b.length+cached.length+3 := by omega
  have hbase : a.length+b.length+cached.length ≤ (a.length+b.length+cached.length+3)^3 := by
    have hh:=Nat.pow_le_pow_right hu (by decide : 1≤3)
    simp only [pow_one] at hh
    omega
  omega

/-- Same all-prefix storage theorem for the genuine compiled machine. -/
theorem machine_prefix_cells (a b cached : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a b cached)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      300000*(a.length+b.length+cached.length+3)^3 := by
  have he:=SemiprimeD1StackCalls.run_correct (.inl M.input) output .start program fuel (initial a b cached)
  change (C.run program fuel (initial a b cached)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a b cached))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial a b cached) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells a b cached fuel out hc

end RiemannGaussian.SemiprimeD1StackResidueMulBounds
