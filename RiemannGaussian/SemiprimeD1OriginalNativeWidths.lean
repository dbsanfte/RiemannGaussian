/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1NativeWordWidths
import RiemannGaussian.SemiprimeMacroEntryExecution

/-! # Original public and recursive native operand bit bounds
The original integer input is charged by N.size, not its numeric value. The
actual public radix powers/Fermat modulus/normalizer and original recursive
grid, schedule and working-precision values have internally derived bit caps.
These bounds are inputs to the forthcoming primitive compiler refinement;
they do not identify native arithmetic with one bit step.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1OriginalNativeWidths
open SemiprimeD1NativeWordWidths SemiprimeMacroParameters SemiprimeMacroFermatNetwork
open SemiprimeD1OriginalScalarResources SemiprimeD1OriginalEnvelopeRate
open SemiprimeD1OriginalStateResources SemiprimeD1RecursiveCallTree
open SemiprimeD1PackingReady SemiprimeD1TensorNetwork SemiprimeD1Schedule

/-- Actual public transform and all its native axis/radix/count parameters are
polynomial in original input LENGTH. This never bounds N itself by that length. -/
theorem public_dimensions (ell : ℕ) (hell:0<ell) :
    transformLength ell ≤ 64*ell ∧firstAxis ell ≤ 64*ell ∧secondAxis ell ≤ 64*ell ∧
      radixBits ell ≤ 64*ell ∧digitCount ell ≤ 64*ell := by
  have hp:1 ≤ transformLength ell:=Nat.one_le_two_pow
  have hs:transformLength ell ≤ (transformLength ell)^2:=le_self_pow hp (by decide:(2:ℕ)≠0)
  have ht:transformLength ell ≤ 64*ell:=hs.trans (transform_square_upper hell).le
  have hf:firstAxis ell ≤ transformLength ell:=Nat.pow_le_pow_right (by decide:0<(2:ℕ))
    (Nat.div_le_self _ _)
  have hsec:secondAxis ell ≤ transformLength ell:=Nat.div_le_self _ _
  have hr:radixBits ell ≤ transformLength ell:=Nat.div_le_self _ _
  exact ⟨ht,hf.trans ht,hsec.trans ht,hr.trans ht,(digitCount_bounds hell).2.trans (hr.trans ht)⟩

/-- Actual Fermat modulus exponent is the actual transform length. -/
theorem macroLength_le (ell : ℕ) (hell:0<ell) : macroLength (macroDepth ell) ≤ 64*ell := by
  rw [←transform_eq_macroLength hell]
  exact (public_dimensions ell hell).1

/-- Any actual canonical Fermat-ring operand has a short original magnitude. -/
theorem fermat_value_size (depth : ℕ) (x : MacroRing depth) : x.val.size ≤ macroLength depth+1 := by
  have hx:=ZMod.val_lt x
  have hb:x.val ≤ 2^(macroLength depth):=by omega
  exact (Nat.size_le_size hb).trans_eq Nat.size_pow

/-- The actual original public normalizer's magnitude has a fixed bit cap. -/
theorem explicitNormalizer_size (ell : ℕ) (hell:0<ell) :
    (SemiprimeMacroEntryExecution.explicitNormalizer (macroDepth ell)).val.size ≤ 64*ell+1 :=
  (fermat_value_size _ _).trans (Nat.add_le_add_right (macroLength_le ell hell) 1)

/-- Powering the normalizer pays an exponent VALUE bounded by the transform. -/
theorem normalizer_exponent_le (ell : ℕ) (hell:0<ell) :
    macroLength (macroDepth ell)-(macroDepth ell+1) ≤ 64*ell :=
  (Nat.sub_le _ _).trans (macroLength_le ell hell)

/-- The original Fermat modulus itself, not merely its residue values, is short. -/
theorem fermat_modulus_size (ell : ℕ) (hell:0<ell) :
    (2^(macroLength (macroDepth ell))+1).size ≤ 64*ell+2 := by
  have h:=add_size (2^(macroLength (macroDepth ell))) 1
  rw [Nat.size_pow,Nat.size_one] at h
  have hm:=macroLength_le ell hell
  omega

/-- Every actual denominator power in original target-digit extraction is paid. -/
theorem target_power_size (ell i : ℕ) (hell:0<ell) (hi:i<digitCount ell) :
    ((2^radixBits ell)^i).size ≤ (64*ell)^2+1 := by
  have h:=public_dimensions ell hell
  rw [←pow_mul,Nat.size_pow]
  have hm:=Nat.mul_le_mul h.2.2.2.1 (hi.le.trans h.2.2.2.2)
  nlinarith

/-- Native target division preserves original input bit width; its result and
the output digit never acquire a bound in terms of the numeric value of N. -/
theorem target_operand_sizes (ell N i : ℕ) (hell:0<ell) :
    (N/(2^radixBits ell)^i).size ≤ N.size ∧(targetDigit ell N i).size ≤ 64*ell := by
  constructor
  · exact div_size _ _
  · apply (Nat.size_le.mpr (Nat.mod_lt _ (by positivity))).trans
    exact (public_dimensions ell hell).2.2.2.1

/-- Actual input bits are exactly the original public length parameter. -/
theorem input_size (N : ℕ) : N.size=bitLength N := rfl

/-- The real original schedule's binary power outputs have derived width caps. -/
theorem schedule_power_sizes (s : ℕ) (call : Call) (a : ℕ)
    (hl:1000 ≤ logarithm s) (hb:Bound s call) (ha:a ≤ 4*(logarithm s/131072)) (i:Fin a) :
    (2^call.depth).size ≤ scalar s+1 ∧(2^(a-i.val)).size ≤ scalar s+1 ∧
      (2^(i.val+1)).size ≤ scalar s+2 ∧(64^a).size ≤ 6*scalar s+1 := by
  have hc:=of_bound s call a hl hb ha
  have hi:i.val ≤ a:=i.isLt.le
  have hd:=hc.depth
  have haCap:=hc.exponent
  simp only [Nat.size_pow]
  refine ⟨by omega,by omega,by omega,?_⟩
  rw [show (64:ℕ)=2^6 by norm_num,←pow_mul,Nat.size_pow]
  omega

/-- Actual D.11 precision arithmetic and its dyadic operand are bounded before
any machine simulation; no supplied precision answer is a premise. -/
theorem workingPrecision_sizes (s : ℕ) (call : Call) (a : ℕ)
    (hl:1000 ≤ logarithm s) (hb:Bound s call) (ha:a ≤ 4*(logarithm s/131072)) (i:Fin a) :
    let u:=levels (logarithm s) call.depth
    let P:=SemiprimeD1ModeRate.workingPrecision (edgeCount call.net) u a i.val call.ctx.precision
    P ≤ 40*(scalar s)^2+9*scalar s ∧P.size ≤ 40*(scalar s)^2+9*scalar s+1 := by
  dsimp only
  have hc:=of_bound s call a hl hb ha
  have hu:levels (logarithm s) call.depth ≤ scalar s:=
    (levels_le _ _).trans (by have h:=(base_caps s hl).2.2;omega)
  have hh:SemiprimeD1ModeRate.jetHeight (edgeCount call.net) (levels (logarithm s) call.depth) ≤
      4*scalar s:=by
    unfold SemiprimeD1ModeRate.jetHeight
    exact (Nat.div_le_self _ _).trans (by have hM:=hc.edges;omega)
  have hpow:2^(a-i.val) ≤ scalar s:=
    (Nat.pow_le_pow_right (by decide:0<(2:ℕ)) (by omega:a-i.val ≤ a+1)).trans hc.grid
  have hP:SemiprimeD1ModeRate.workingPrecision (edgeCount call.net)
      (levels (logarithm s) call.depth) a i.val call.ctx.precision ≤ 40*(scalar s)^2+9*scalar s:=by
    unfold SemiprimeD1ModeRate.workingPrecision
    calc
      _  ≤  scalar s+8*(4*scalar s)*scalar s+8*scalar s*(scalar s+1) := by
        gcongr
        · exact hc.precision
        · exact hc.edges
        · exact hc.exponent
      _ = _ := by ring
  exact ⟨hP,(size_le_value _).trans (Nat.add_le_add_right hP 1)⟩

/-- Every native geometry scalar comes from the same actual finite grid. -/
theorem geometry_sizes (s : ℕ) (call : Call) (a : ℕ)
    (hl:1000 ≤ logarithm s) (hb:Bound s call) (ha:a ≤ 4*(logarithm s/131072))
    (t:Fin (SemiprimeD1WireKernelOriginal.size a)) :
    (SemiprimeD1RecoveryWeightRun.geometry a t.val).size.size ≤ scalar s+1 ∧
    (SemiprimeD1RecoveryWeightRun.geometry a t.val).center.natAbs.size ≤ scalar s+1 ∧
    (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs.size ≤ scalar s+1 ∧
    (SemiprimeD1RecoveryWeightRun.geometry a t.val).alpha.natAbs.size ≤ scalar s+1 := by
  have hc:=of_bound s call a hl hb ha
  have hs:SemiprimeD1WireKernelOriginal.size a ≤ scalar s:=hc.grid
  have hcenter:SemiprimeD1WireKernelOriginal.center a ≤ scalar s:=
    (Nat.pow_le_pow_right (by decide:0<(2:ℕ)) (by omega:a ≤ a+1)).trans hs
  have hp:(SemiprimeD1WireKernelOriginal.point a t.val).natAbs ≤ scalar s:=
    (SemiprimeD1JetRecoveryScalarHeight.point_abs_lt a t.val t.isLt).le.trans hs
  refine ⟨?_,?_,?_,?_⟩
  · rw [SemiprimeD1RecoveryWeightRun.geometry_size]
    exact (size_le_value _).trans (Nat.add_le_add_right hs 1)
  · rw [SemiprimeD1RecoveryWeightRun.geometry_center_abs]
    exact (size_le_value _).trans (Nat.add_le_add_right hcenter 1)
  · rw [SemiprimeD1RecoveryWeightRun.geometry_point]
    exact (size_le_value _).trans (Nat.add_le_add_right hp 1)
  · rw [SemiprimeD1RecoveryWeightRun.geometry_alpha,Int.natAbs_pow]
    exact (size_le_value _).trans (Nat.add_le_add_right hc.grid 1)

end RiemannGaussian.SemiprimeD1OriginalNativeWidths
