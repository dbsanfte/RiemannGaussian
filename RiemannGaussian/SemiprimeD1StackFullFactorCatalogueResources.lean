/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueBounds
/-! # Fixed growth and all compiled prefix cells for actual all-factor acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogueResources
open SemiprimeD1StackFullFactorCatalogue SemiprimeD1StackFullFactorCatalogueExecution
open SemiprimeD1StackFullFactorCatalogueBounds SemiprimeD1StackFullFactorCatalogueCapacities
open SemiprimeBitArithmetic (bitValue)
open SemiprimeReportPolynomialGrowth (Bound constant_bound identity_bound add_bound mul_bound pow_bound)
/-- Fixed natural coefficient and degree exist for the actual explicit width polynomial. -/
theorem polynomial_monomial :∃A d:Nat,∀n,runPolynomial n ≤ A*(n+1)^d:=by
  have hp:Bound polynomial:=⟨coefficient,108,fun _=>Nat.le_refl _⟩
  have hf:Bound factorAllowance:=mul_bound (constant_bound 12800) identity_bound
  have ha:Bound (fun n=>polynomial n+factorAllowance n*polynomial n+2):=
    add_bound (add_bound hp (mul_bound hf hp)) (constant_bound 2)
  have hr:Bound rowPolynomial:=add_bound
    (mul_bound (constant_bound (10^130)) (pow_bound ha 18))
    (mul_bound (constant_bound 2) hp)
  exact add_bound (add_bound (add_bound hp (mul_bound hf hr))
    (mul_bound (mul_bound (constant_bound 2) hf) hp)) (constant_bound 4)
/-- Complete genuine1454-role machine certificate under its own original-family rate bound. -/
noncomputable def machineBounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (runBound bits):=by
  rw [SemiprimeD1StackFullFactorCatalogueFinish.initial_configuration]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (.local .main) program
  have h:=source_run_bounded bits hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every original source prefix counts all1454 data roles and every actual return cell. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (finish:C.State Stack Label) (hr:C.run program fuel (initial bits)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length ≤ 1455*(bits.length+runBound bits):=by
  exact (SemiprimeD1StackFullFactorCatalogueExecution.prefix_cells bits hc hN fuel finish hr).trans
    (Nat.mul_le_mul_left 1455 (Nat.add_le_add_left (timeBound_le bits hc hN) bits.length))
/-- Same own clock bounds every compiled prefix, including the physical return stack. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1455*(bits.length+runBound bits):=by
  exact (SemiprimeD1StackFullFactorCatalogueExecution.machine_prefix_cells bits hc hN fuel cfg hr).trans
    (Nat.mul_le_mul_left 1455 (Nat.add_le_add_left (timeBound_le bits hc hN) bits.length))
/-- Fixed rate witnesses apply to the SAME actual source trace for the entire original family. -/
theorem source_run_monomial :∃A d:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (_hN:0<bitValue bits),
    ∃t ≤ A*(bits.length+1)^d*2^(19*R.arityCapacity bits),
      C.run program t (initial bits)=some (done bits):=by
  obtain ⟨A,d,ha⟩:=polynomial_monomial
  refine ⟨A,d,?_⟩
  intro bits hc hN
  obtain ⟨t,ht,hr⟩:=source_run_bounded bits hc hN
  exact ⟨t,ht.trans (Nat.mul_le_mul_right _ (ha bits.length)),hr⟩
/-- Fixed polynomial storage witnesses cover every compiled prefix of the same original source. -/
theorem machine_prefix_monomial :∃A d:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (_hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg),
    (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg →
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      A*(bits.length+1)^d*2^(19*R.arityCapacity bits):=by
  have hp:Bound runPolynomial:=polynomial_monomial
  have hs:Bound (fun n=>1455*(n+runPolynomial n)):=
    mul_bound (constant_bound 1455) (add_bound identity_bound hp)
  obtain ⟨A,d,ha⟩:=hs
  refine ⟨A,d,?_⟩
  intro bits hc hN fuel cfg hr
  have h:=machine_prefix_cells bits hc hN fuel cfg hr
  have he:1 ≤ (2:Nat)^(19*R.arityCapacity bits):=Nat.pow_pos (by decide)
  have hn:=Nat.mul_le_mul_left bits.length he
  have hpoly:=Nat.mul_le_mul_right (2^(19*R.arityCapacity bits)) (ha bits.length)
  unfold runBound at h
  nlinarith only [h,hn,hpoly]
/-- The exponent is the established original three-quarter-power cap, never a claimed square-root cap. -/
theorem scope_exponent_fourth (bits:List Bool) (h:0<bits.length) :
    (R.arityCapacity bits)^4 ≤ 512^4*bits.length^3:=
  SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity_fourth bits h
/-- Each actual compiled transition uses at most four fundamental commands. -/
theorem compile_depth (pc:Label) :SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤ 4:=
  SemiprimeD1StackCalls.compile_depth (.local .main:Label) (program pc)
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogueResources
