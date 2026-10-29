/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputWidthExecution
import RiemannGaussian.SemiprimeD1StackFermatWords

/-! # Actual active-digit acquisition: bit-time, space and strict-bound value -/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackInputWidthBounds
open SemiprimeD1StackInputWidth SemiprimeD1StackInputWidthExecution

/-- Physical cache cells are the only initial resource. -/
def inputSize (c : Cache) : ℕ := c.width.length+c.radix.length+c.index.length
/-- One fixed quadratic allowance, before every cache value and index. -/
def runBound (c : Cache) : ℕ := 1000*(inputSize c+1)^2
/-- Actual offset acquisition remains polynomial in the original physical
cache lengths; the numerical power-of-two bound is NEVER counted in unary. -/
theorem timeBound_le (c : Cache) : timeBound c≤runBound c := by
  let I:=inputSize c
  have hi : c.index.length≤I+1 := by dsimp [I,inputSize];omega
  have hb : c.radix.length≤I+1 := by dsimp [I,inputSize];omega
  have hp : c.index.length*c.radix.length≤(I+1)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hi hb
  have hI : I+1≤(I+1)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤I+1) (by decide : 1≤2)
  change 100*(I+c.index.length*c.radix.length+1)≤1000*(I+1)^2
  omega
/-- Whole actual source with no supplied elapsed count or bound word. -/
theorem source_run_bounded (c : Cache) :
    ∃t≤runBound c,C.run program t (initial c)=some (done c) := by
  obtain ⟨t,ht,hr⟩:=source_run c
  exact ⟨t,ht.trans (timeBound_le c),hr⟩
/-- Proof-side choice of a real proved trace, never a clock opcode. -/
noncomputable def sourceBound (c : Cache) :
    StateTransition.EvalsToInTime (C.step program) (initial c) (some (done c)) (runBound c) := by
  let h:=source_run_bounded c
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine fixed finite machine for the exact literal acquisition program. -/
noncomputable def boundInTime (c : Cache) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial c))
      (some (SemiprimeD1StackCalls.configuration (done c))) (runBound c) :=
  SemiprimeD1StackCalls.evalsCorrect Stack.widthCache Stack.output Label.start program _ _ _ (sourceBound c)
/-- The acquired bound has linearly many binary cells even at zero width. -/
theorem bound_length (c : Cache) : (bound c).length=width c+1 := by
  simp only [bound,List.length_append,List.length_replicate,List.length_singleton]
/-- The physically constructed word is exactly the needed strict integer bound. -/
theorem bound_value (c : Cache) : SemiprimeBitArithmetic.bitValue (bound c)=2^width c := by
  rw [bound,SemiprimeD1StackFermatWords.zeros_value]
  simp only [SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat,ite_true,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
/-- A real low-bit peek detects positive active width, without a size/arity or
digit-count comparison oracle; zero width has the actual singleton-one bound. -/
theorem bound_head (c : Cache) :
    (bound c).head?=some (if width c=0 then true else false) := by
  cases hw:width c with
  | zero=>simp only [bound,hw,ite_true,List.replicate_zero,List.nil_append,List.head?_cons]
  | succ n=>simp only [bound,hw,Nat.succ_ne_zero,ite_false,List.replicate_succ,List.cons_append,List.head?_cons]
/-- The width is paid from actual radix cells and can never exceed them. -/
theorem width_le_radix (c : Cache) : width c≤c.radix.length := Nat.min_le_left _ _
/-- No successful actual source prefix extends beyond the complete proved halt. -/
theorem prefix_fuel_le (c : Cache) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial c)=some out) : fuel≤runBound c := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded c
  have hf : fuel≤t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done c)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- EVERY prefix counts all nine data stacks and all actual return-label cells,
including product/copy workspace, all retained caches and the binary output. -/
theorem prefix_cells (c : Cache) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial c)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤20000*(inputSize c+1)^2 := by
  let I:=inputSize c
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ out (by
    intro k;cases k <;> simp [initial,store,I,inputSize] <;> omega) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length)≤9*(I+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(I+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le c fuel out hr
  change fuel≤1000*(I+1)^2 at ht
  have hI : I≤(I+1)^2 := by
    have h:=Nat.pow_le_pow_right (by omega : 1≤I+1) (by decide : 1≤2)
    simp only [pow_one] at h
    omega
  change _≤20000*(I+1)^2
  omega
/-- Same complete storage theorem for actual compiled finite-machine prefixes. -/
theorem machine_prefix_cells (c : Cache) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial c)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤20000*(inputSize c+1)^2 := by
  have he:=SemiprimeD1StackCalls.run_correct Stack.widthCache Stack.output Label.start program fuel (initial c)
  change (C.run program fuel (initial c)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial c))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial c) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells c fuel out hc
end RiemannGaussian.SemiprimeD1StackInputWidthBounds
