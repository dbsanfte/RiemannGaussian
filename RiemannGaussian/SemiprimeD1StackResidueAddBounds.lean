/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackResidueAddExecution
import RiemannGaussian.SemiprimeBitFermatArithmetic
import RiemannGaussian.SemiprimeD1StackAssignmentOrder
/-! # Actual general-modulus addition time, storage and original byte equality -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackResidueAddBounds
open SemiprimeD1StackResidueAdd SemiprimeD1StackResidueAddExecution
open SemiprimeBitArithmetic

/-- A polynomial in physical operand/cache LENGTHS, not modulus value. -/
def timeBound (n m p : ℕ) : ℕ :=
  1000*(n+m+p+3)^2+6*n+6*m+5*p+20

/-- Every real arithmetic, copy, quotient drain and final halt is paid. -/
theorem totalTime_le (a b cached : List Bool) :
    totalTime a b cached≤timeBound a.length b.length cached.length := by
  have ha := (SemiprimeD1StackAdderExecution.sourceAdd a b false).steps_le_m
  change addTime a b≤5*(a.length+b.length)+7 at ha
  have hs := (addBits_counts a b false).2.2.2.2
  change (sum a b).length≤max a.length b.length+1 at hs
  have hmax : max a.length b.length≤a.length+b.length := max_le (by omega) (by omega)
  have hd := (SemiprimeD1StackDividerExecution.source_time (sum a b) cached).trans
    (SemiprimeD1StackDividerExecution.timeBound_le_square (sum a b).length cached.length)
  have hb : 1000*((sum a b).length+cached.length+2)^2≤
      1000*(a.length+b.length+cached.length+3)^2 := by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (by omega) 2
  have hd' := hd.trans hb
  have hq := (SemiprimeBitDivision.divideLoop_widths (sum a b) cached).2.1
  change (quotient a b cached).length=(sum a b).length at hq
  unfold totalTime timeBound
  omega

/-- Fixed quadratic envelope for the complete actual component. -/
theorem timeBound_le_square (n m p : ℕ) : timeBound n m p≤2000*(n+m+p+3)^2 := by
  let u:=n+m+p+3
  have hu : 1≤u := by omega
  have hl : 6*n+6*m+5*p+20≤20*u := by dsimp [u];omega
  have h1 : u≤u^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hu (by decide : 1≤2)
  change timeBound n m p≤2000*u^2
  change 1000*u^2+6*n+6*m+5*p+20≤2000*u^2
  omega

/-- Actual source time certificate; no elapsed-count supplier is an argument. -/
def sourceAdd (a b cached : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial a b cached)
      (some (done a b cached)) (timeBound a.length b.length cached.length) :=
  ⟨⟨_,source_run a b cached⟩,totalTime_le a b cached⟩

/-- Genuine fixed finite-machine execution of the same addition trace. -/
def machineAdd (a b cached : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial a b cached))
      (some (SemiprimeD1StackCalls.configuration (done a b cached)))
      (timeBound a.length b.length cached.length) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) (.inl (.left : A.Stack)) output Label.start program
    _ _ _ (sourceAdd a b cached)

/-- Every input returns a literal cached-modulus-width remainder. -/
theorem residue_width (a b cached : List Bool) : (residue a b cached).length=cached.length :=
  (SemiprimeBitDivision.divideLoop_widths (sum a b) cached).1

/-- Positive cached moduli give the exact numerical sum residue. -/
theorem residue_value (a b cached : List Bool) (hm : 0<bitValue cached) :
    bitValue (residue a b cached)=(bitValue a+bitValue b)%bitValue cached := by
  change bitValue (SemiprimeBitDivision.divideLoop (sum a b) cached).remainder=_
  rw [←(SemiprimeD1StackDividerExecution.divideBits_outputs (sum a b) cached hm).2,
    (SemiprimeBitDivision.divideBits_correct (sum a b) cached).2]
  have hs := addBits_correct a b false
  simp only [bitNat,Bool.false_eq_true,ite_false,Nat.add_zero] at hs
  exact congrArg (fun n=>n%bitValue cached) hs

/-- Under ORIGINAL canonical-operand guards the returned physical padded word
is exactly frozen residueAddBits, including high-zero-padded modulus templates. -/
theorem residue_original (a b cached : List Bool)
    (ha : bitValue a<bitValue cached) (hb : bitValue b<bitValue cached) :
    residue a b cached=(SemiprimeBitFermatArithmetic.residueAddBits cached a b).output.bits := by
  apply SemiprimeD1StackAssignmentOrder.word_value_injective
  · exact (residue_width a b cached).trans (SemiprimeBitFermatArithmetic.residueAddBits_width cached a b).symm
  · rw [residue_value a b cached (by omega),(SemiprimeBitFermatArithmetic.residueAddBits_exact ha hb).1]

/-- The original raw binary modulus is physically retained by the complete run. -/
theorem retained_modulus (a b cached : List Bool) : finalData a b cached modulus=cached := rfl
/-- The designated output is exactly the computed physical remainder. -/
theorem output_residue (a b cached : List Bool) : finalData a b cached output=residue a b cached := rfl

/-- A reached source prefix cannot lie past this actual complete halt. -/
theorem prefix_fuel_le (a b cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial a b cached)=some out) : fuel≤totalTime a b cached := by
  by_contra hn
  have he : fuel=totalTime a b cached+(1+(fuel-(totalTime a b cached+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hz : C.run program 1 (done a b cached)=none := rfl
  rw [hz,Option.bind_none] at hr
  cases hr

/-- Every actual Boolean data cell and finite-label return cell is bounded at
EVERY executed prefix, including copies and the restoring divider workspace. -/
theorem prefix_cells (a b cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial a b cached)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤40000*(a.length+b.length+cached.length+3)^2 := by
  have hd := SemiprimeD1StackReturnLink.run_data_bound program fuel (a.length+b.length+cached.length)
    (initial a b cached) out (by
      intro k
      rcases k with k|k
      · cases k <;> simp [initial,input,store,A.store] <;> omega
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> simp [initial,input,store,D.payload]
        · cases k <;> simp [initial,input,store]) hr
  have hf := SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length)≤17*(a.length+b.length+cached.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(a.length+b.length+cached.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht := ((prefix_fuel_le a b cached fuel out hr).trans (totalTime_le a b cached)).trans
    (timeBound_le_square a.length b.length cached.length)
  have hu : 1≤a.length+b.length+cached.length+3 := by omega
  have hbase : a.length+b.length+cached.length≤(a.length+b.length+cached.length+3)^2 := by
    have hh := Nat.pow_le_pow_right hu (by decide : 1≤2)
    simp only [pow_one] at hh
    omega
  omega

/-- The same all-prefix bound for the genuine compiled finite machine. -/
theorem machine_prefix_cells (a b cached : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a b cached)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      40000*(a.length+b.length+cached.length+3)^2 := by
  have he := SemiprimeD1StackCalls.run_correct (.inl (.left : A.Stack)) output .start program fuel
    (initial a b cached)
  have hh := he.trans hr
  cases hc : C.run program fuel (initial a b cached) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells a b cached fuel out hc
end RiemannGaussian.SemiprimeD1StackResidueAddBounds
