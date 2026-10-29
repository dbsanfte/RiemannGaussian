/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsBounds
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsStorage
/-! # Fixed-before-N source constants, genuine machine and all2011 prefix resources -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsResources
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsExecution
open SemiprimeD1StackMarkedRootRecordsBounds
open SemiprimeBitArithmetic (bitValue)
open SemiprimeReportPolynomialGrowth (Bound constant_bound identity_bound add_bound mul_bound pow_bound)
/-- The actual width-only coefficient is one fixed polynomial BEFORE every original input. -/
theorem widthPolynomial_monomial : Bound widthPolynomial := by
  have hr : Bound (fun n => RB.prefixPolynomial n 1) :=
    SemiprimeD1StackRootNetworkRecordsResources.polynomial_monomial
  have hv : Bound (fun n => 10^13*(n+1)^5) :=
    mul_bound (constant_bound (10^13)) (pow_bound (add_bound identity_bound (constant_bound 1)) 5)
  exact mul_bound (constant_bound 100) (add_bound (add_bound (add_bound identity_bound hr) hv) (constant_bound 2))
/-- Fixed constants precede N; the same actual source has exponent58 times the original local-scope cap. -/
theorem runBound_monomial : ∃ A d : Nat, ∀ bits : List Bool,
    runBound bits ≤ A*(bits.length+1)^d*2^(58*scopeCap bits) := by
  obtain ⟨A,d,h⟩ := widthPolynomial_monomial
  refine ⟨10^28*A^3,3*d,?_⟩
  intro bits
  have hp := Nat.pow_le_pow_left (h bits.length) 3
  rw [mul_pow,←pow_mul,Nat.mul_comm d 3] at hp
  have hc := Nat.mul_le_mul_right (2^(58*scopeCap bits)) (Nat.mul_le_mul_left (10^28) hp)
  exact hc.trans_eq (by ring)
/-- Complete SAME source and actual halt, with fixed constants before the input family. -/
theorem source_run_monomial : ∃ A d : Nat, ∀ (bits : List Bool)
    (_hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits),
    ∃ t ≤ A*(bits.length+1)^d*2^(58*scopeCap bits), C.run program t (initial bits)=some (done bits hN) := by
  obtain ⟨A,d,h⟩ := runBound_monomial
  refine ⟨A,d,?_⟩
  intro bits hc hN
  obtain ⟨t,ht,hr⟩ := source_run_bounded bits hc hN
  exact ⟨t,ht.trans (h bits),hr⟩
/-- Every actual source prefix counts ALL2011 roles, the shared-N shadow and every saved return. -/
theorem prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (fuel : Nat) (finish : C.State Stack Label) (hr : C.run program fuel (initial bits)=some finish) :
    (∑ k : Stack,(finish.data k).length)+finish.frames.length ≤ 2012*(bits.length+runBound bits) := by
  have hs := SemiprimeD1StackMarkedRootRecordsStorage.prefix_cells bits hc hN fuel finish hr
  have ht := timeBound_le bits hc hN
  omega
/-- Genuine binary-N-only compiled machine with the SAME fixed original-scope source budget. -/
noncomputable def machineSource (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits hN))) (runBound bits) := by
  rw [SemiprimeD1StackMarkedRootRecordsStorage.initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput (aux .output) (ctl .start) program
  let h := source_run_bounded bits hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every actual compiled prefix includes the full2011 words AND real finite-label return stack. -/
theorem machine_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q => q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑ k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 2012*(bits.length+runBound bits) := by
  have hs := SemiprimeD1StackMarkedRootRecordsStorage.machine_prefix_cells bits hc hN fuel cfg hr
  have ht := timeBound_le bits hc hN
  omega
/-- Fixed width-only coefficient for the entire source's all-role storage envelope. -/
def spaceWidth (n : Nat) : Nat := 2012*(n+10^28*(widthPolynomial n)^3)
/-- Storage coefficients too are fixed before the whole original input family. -/
theorem spaceWidth_monomial : Bound spaceWidth :=
  mul_bound (constant_bound 2012) (add_bound identity_bound
    (mul_bound (constant_bound (10^28)) (pow_bound widthPolynomial_monomial 3)))
/-- SAME actual-prefix resource bound at the original scope rate. -/
theorem prefix_scope_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (fuel : Nat) (finish : C.State Stack Label) (hr : C.run program fuel (initial bits)=some finish) :
    (∑ k : Stack,(finish.data k).length)+finish.frames.length ≤ spaceWidth bits.length*2^(58*scopeCap bits) := by
  have hs := prefix_cells bits hc hN fuel finish hr
  have hn := Nat.le_mul_of_pos_right bits.length (by positivity : 0 < (2:Nat)^(58*scopeCap bits))
  unfold spaceWidth runBound at *
  nlinarith only [hs,hn]
/-- All prefix cells and real returns admit fixed polynomial constants BEFORE N. -/
theorem prefix_monomial : ∃ A d : Nat, ∀ (bits : List Bool)
    (_hc : SemiprimeSourceCompactBits.Compact bits) (_hN : 0 < bitValue bits)
    (fuel : Nat) (finish : C.State Stack Label) (_hr : C.run program fuel (initial bits)=some finish),
    (∑ k : Stack,(finish.data k).length)+finish.frames.length ≤ A*(bits.length+1)^d*2^(58*scopeCap bits) := by
  obtain ⟨A,d,h⟩ := spaceWidth_monomial
  refine ⟨A,d,?_⟩
  intro bits hc hN fuel finish hr
  exact (prefix_scope_cells bits hc hN fuel finish hr).trans (Nat.mul_le_mul_right _ (h bits.length))
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsResources
