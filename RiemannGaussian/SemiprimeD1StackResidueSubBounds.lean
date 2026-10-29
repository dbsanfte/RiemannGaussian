/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackResidueSubExecution
import RiemannGaussian.SemiprimeBitFermatArithmetic
import RiemannGaussian.SemiprimeD1StackAssignmentOrder
/-! # General-modulus subtraction machine time, all-prefix storage and exact bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackResidueSubBounds
open SemiprimeD1StackResidueSub SemiprimeD1StackResidueSubExecution
open SemiprimeBitArithmetic SemiprimeBitDivision

/-- Fixed physical-input polynomial; no operand VALUE determines this bound. -/
def timeBound (n m p : ℕ) : ℕ := 1000*(n+m+2*p+4)^2+30*(n+m+p+3)

/-- Original physical inputs derive all actual intermediate lengths and work. -/
theorem totalTime_le (a b cached : List Bool) :
    totalTime a b cached≤timeBound a.length b.length cached.length := by
  have ha := (SemiprimeD1StackAdderExecution.sourceAdd a cached false).steps_le_m
  change addTime a cached≤5*(a.length+cached.length)+7 at ha
  have hs := (addBits_counts a cached false).2.2.2.2
  change (sum a cached).length≤max a.length cached.length+1 at hs
  have hamax : max a.length cached.length≤a.length+cached.length := max_le (by omega) (by omega)
  have hb := (SemiprimeD1StackSubtractorExecution.sourceSubtract (sum a cached) b false).steps_le_m
  change subtractTime a b cached≤5*((sum a cached).length+b.length)+8 at hb
  have hl := (subBits_counts (sum a cached) b false).2.2.2.2
  change (difference a b cached).length=max (sum a cached).length b.length at hl
  have hdiff : (difference a b cached).length≤a.length+b.length+cached.length+1 := by
    rw [hl]
    exact max_le (by omega) (by omega)
  have hd := (SemiprimeD1StackDividerExecution.source_time (difference a b cached) cached).trans
    (SemiprimeD1StackDividerExecution.timeBound_le_square (difference a b cached).length cached.length)
  have hdBound : 1000*((difference a b cached).length+cached.length+2)^2≤
      1000*(a.length+b.length+2*cached.length+4)^2 := by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (by omega) 2
  have hd' := hd.trans hdBound
  have hq := (divideLoop_widths (difference a b cached) cached).2.1
  change (quotient a b cached).length=(difference a b cached).length at hq
  unfold totalTime timeBound
  omega

/-- One fixed quadratic monomial bounds the complete actual pipeline. -/
theorem timeBound_le_square (n m p : ℕ) : timeBound n m p≤5000*(n+m+p+3)^2 := by
  let u:=n+m+p+3
  have hu : 1≤u := by omega
  have hd : 1000*(n+m+2*p+4)^2≤4000*u^2 := by
    calc
      _ ≤ 1000*(2*u)^2 := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (by dsimp [u];omega) 2)
      _ = _ := by ring
  have h1 : u≤u^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hu (by decide : 1≤2)
  change 1000*(n+m+2*p+4)^2+30*u≤5000*u^2
  omega

/-- A cubic-compatible envelope is available for uniform public arithmetic joins. -/
theorem timeBound_le_cube (n m p : ℕ) : timeBound n m p≤5000*(n+m+p+3)^3 :=
  (timeBound_le_square n m p).trans (Nat.mul_le_mul_left 5000
    (Nat.pow_le_pow_right (by omega : 1≤n+m+p+3) (by decide : 2≤3)))

/-- Actual source execution certificate, with no supplied elapsed count. -/
def sourceSubtract (a b cached : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial a b cached)
      (some (done a b cached)) (timeBound a.length b.length cached.length) :=
  ⟨⟨_,source_run a b cached⟩,totalTime_le a b cached⟩

/-- Genuine FinTM2 certificate for exactly the same finite instruction table. -/
def machineSubtract (a b cached : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial a b cached))
      (some (SemiprimeD1StackCalls.configuration (done a b cached)))
      (timeBound a.length b.length cached.length) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) (.inl (.left : A.Stack)) output Label.start program
    _ _ _ (sourceSubtract a b cached)

/-- Every raw input returns exactly the physical cached-modulus width. -/
theorem residue_width (a b cached : List Bool) : (residue a b cached).length=cached.length :=
  (divideLoop_widths (difference a b cached) cached).1

/-- The actual binary sum has its original arithmetic value. -/
theorem sum_value (a cached : List Bool) : bitValue (sum a cached)=bitValue a+bitValue cached := by
  simpa only [sum,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero] using addBits_correct a cached false

/-- ORIGINAL right-residue validity proves the actual subtractor never underflows;
no intermediate borrow answer is supplied to runtime or to this conclusion. -/
theorem actual_borrow_false (a b cached : List Bool) (hb : bitValue b<bitValue cached) :
    borrow a b cached=false := by
  have hnot : (subBits (sum a cached) b false).borrow≠true := by
    intro h
    have hlt := (subBits_borrow_iff (sum a cached) b false).mp h
    simp only [bitNat,Bool.false_eq_true,ite_false,Nat.add_zero,sum_value] at hlt
    omega
  change (subBits (sum a cached) b false).borrow=false
  cases h : (subBits (sum a cached) b false).borrow with
  | false=>rfl
  | true=>exact (hnot h).elim

/-- The actually acquired difference is x+M-y, from original input validity. -/
theorem difference_equation (a b cached : List Bool) (hb : bitValue b<bitValue cached) :
    bitValue (difference a b cached)+bitValue b=bitValue a+bitValue cached := by
  have he := subBits_equation (sum a cached) b false
  have hborrow := actual_borrow_false a b cached hb
  change (subBits (sum a cached) b false).borrow=false at hborrow
  simp only [hborrow,bitNat,Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.add_zero,sum_value] at he
  change bitValue (subBits (sum a cached) b false).result.bits+bitValue b=_
  omega

/-- Actual positive-modulus restoring division value, with no quotient advice. -/
theorem residue_value (a b cached : List Bool) (hm : 0<bitValue cached) :
    bitValue (residue a b cached)=bitValue (difference a b cached)%bitValue cached := by
  change bitValue (divideLoop (difference a b cached) cached).remainder=_
  rw [←(SemiprimeD1StackDividerExecution.divideBits_outputs (difference a b cached) cached hm).2]
  exact (divideBits_correct (difference a b cached) cached).2

/-- ORIGINAL canonical operand guards give EXACT frozen residueSubBits bytes.
Literal-width equality preserves arbitrary high-zero padding in the cache. -/
theorem residue_original (a b cached : List Bool)
    (ha : bitValue a<bitValue cached) (hb : bitValue b<bitValue cached) :
    residue a b cached=(SemiprimeBitFermatArithmetic.residueSubBits cached a b).output.bits := by
  apply SemiprimeD1StackAssignmentOrder.word_value_injective
  · exact (residue_width a b cached).trans (SemiprimeBitFermatArithmetic.residueSubBits_width cached a b).symm
  · rw [residue_value a b cached (by omega)]
    have hold := SemiprimeBitFermatArithmetic.residueSubBits_exact ha hb
    have hnew := difference_equation a b cached hb
    cases h : (subBits a b false).borrow with
    | false=>
      simp only [h,bitNat,Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.add_zero] at hold
      have hd : bitValue (difference a b cached)=
          bitValue (SemiprimeBitFermatArithmetic.residueSubBits cached a b).output.bits+bitValue cached := by omega
      rw [hd,Nat.add_mod_right,Nat.mod_eq_of_lt hold.1]
    | true=>
      simp only [h,bitNat,ite_true,Nat.mul_one] at hold
      have hd : bitValue (difference a b cached)=
          bitValue (SemiprimeBitFermatArithmetic.residueSubBits cached a b).output.bits := by omega
      rw [hd,Nat.mod_eq_of_lt hold.1]

/-- The raw binary modulus cache survives literally, including all padding. -/
theorem retained_modulus (a b cached : List Bool) : finalData a b cached modulus=cached := rfl
/-- Only the actual computed remainder is designated as output. -/
theorem output_residue (a b cached : List Bool) : finalData a b cached output=residue a b cached := rfl

/-- Every reached prefix is before or at the actual complete source halt. -/
theorem prefix_fuel_le (a b cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial a b cached)=some out) : fuel≤totalTime a b cached := by
  by_contra hn
  have he : fuel=totalTime a b cached+(1+(fuel-(totalTime a b cached+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hz : C.run program 1 (done a b cached)=none := rfl
  rw [hz,Option.bind_none] at hr
  cases hr

/-- All twenty-one Boolean stacks and real finite-label return cells are paid
at EVERY actual prefix, including both modulus copies and all arithmetic work. -/
theorem prefix_cells (a b cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial a b cached)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤120000*(a.length+b.length+cached.length+3)^2 := by
  have hd := SemiprimeD1StackReturnLink.run_data_bound program fuel (a.length+b.length+cached.length)
    (initial a b cached) out (by
      intro k
      rcases k with k|k
      · cases k <;> simp [initial,input,store,A.store]; omega
      · rcases k with k|k
        · cases k <;> simp [initial,input,store,A.store]; omega
        · rcases k with k|k
          · rcases k with k|k <;> cases k <;> simp [initial,input,store,D.payload]
          · cases k <;> simp [initial,input,store]) hr
  have hf := SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length)≤21*(a.length+b.length+cached.length+fuel) := by
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

/-- Same complete all-prefix storage inventory for the genuine compiled machine. -/
theorem machine_prefix_cells (a b cached : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a b cached)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      120000*(a.length+b.length+cached.length+3)^2 := by
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
end RiemannGaussian.SemiprimeD1StackResidueSubBounds
