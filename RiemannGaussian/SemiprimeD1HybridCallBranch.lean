/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCallModes
import RiemannGaussian.SemiprimeD1HybridCallEnvelope
import RiemannGaussian.SemiprimeD1HybridPathRate
import RiemannGaussian.SemiprimeD1HybridPathDecay

/-! # Actual whole-grid branching with a summable depth exponent
All grid points and64 group calls are charged. The mode menus are the actual
acquired lists on reachable calls, with their precision computed from input.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1HybridCallBranch
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState SemiprimeD1RecursiveCallInventory
open SemiprimeD1RecursiveCallPath SemiprimeD1RecursiveCallModes SemiprimeD1HybridCallEnvelope
open SemiprimeD1WireKernelOriginal SemiprimeD1Schedule
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Uniform paid grid/group multiplicity at the original input logarithm. -/
noncomputable def gridFactor (s : ℕ) : ℝ := 2^(4*SemiprimeD1PackingReady.logarithm s+7)

/-- Original mode exponent before its dyadically summable depth factor. -/
noncomputable def modeFactor (s : ℕ) : ℝ :=
  96*(s:ℝ)/Real.sqrt (SemiprimeD1PackingReady.logarithm s/epsilonDenominator:ℕ)

/-- The literal original grid and all64 groups obey a fixed input-only factor. -/
theorem grid_le (s depth : ℕ) :
    (size (exponent (SemiprimeD1PackingReady.logarithm s) depth):ℝ)*64 ≤ gridFactor s := by
  have he : (size (exponent (SemiprimeD1PackingReady.logarithm s) depth):ℝ)*64 =
      (2:ℝ)^(exponent (SemiprimeD1PackingReady.logarithm s) depth+7) := by
    simp only [size,Nat.cast_pow,Nat.cast_ofNat]
    rw [show exponent (SemiprimeD1PackingReady.logarithm s) depth+7 =
      (exponent (SemiprimeD1PackingReady.logarithm s) depth+1)+6 by omega,pow_add]
    simp only [pow_add]
    norm_num
  rw [he]
  exact pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right (exponent_le_lam _ _) 7)

/-- Exact phase lengths, including failed-point tests, are controlled by the
actual acquired menu bound for each possible executed valuation. -/
theorem phase_length_le (parent : Call) (a u : ℕ) (t : Fin (size a)) (E : ℝ) (hE : 0 ≤ E)
    (hmenu : ∀ i < u, ((SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount
      parent.net.rows.length 64 a u i parent.ctx.precision
      (arity parent.net.rows) (owner parent.net.rows)).modes.values.length:ℝ) ≤ E) :
    ((phaseChildren parent a u t).length:ℝ) ≤ 64*E := by
  by_cases hi : (SemiprimeD1RecoveryScalarRun.orderFuel
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).value < a ∧
      (SemiprimeD1RecoveryScalarRun.orderFuel
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).value < u ∧
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).point ≠ 0
  · rw [phaseChildren_length parent a u t hi,Nat.cast_mul,Nat.cast_ofNat]
    have h := hmenu _ hi.2.1
    nlinarith
  · dsimp only [phaseChildren]
    rw [dite_eq_right hi]
    simp only [List.length_nil,Nat.cast_zero]
    positivity

/-- ALL actual reachable calls have a depth-only branching envelope, after
retaining every grid and group multiplicity. No branching answer is supplied. -/
theorem eventually_reach_branch : ∀ᶠ s : ℕ in Filter.atTop,
    ∀ root call : Call, root.depth=0 → edgeCount root.net ≤ s → root.ctx.precision ≤ s →
      root.ctx.Positive → WellFormed root.net → Good root.ctx root.net →
      SemiprimeD1TensorNetworkRecursion.DegreeBound root.net (SemiprimeD1PackingReady.degreeCap s) →
      Reach s root call →
      ((children s call).length:ℝ) ≤ gridFactor s*
        Real.exp (modeFactor s*(1/8:ℝ)^call.depth) := by
  filter_upwards [eventually_reach_menu,SemiprimeD1HybridPathDecay.eventually_reach_sixteen] with s hmenu hdecay
  intro root call hr hM hp hpos hw hg hd hreach
  have hdec := hdecay root call hr hM hp hpos hw hg hd hreach
  by_cases ha : activeTest s (SemiprimeD1PackingReady.logarithm s) call.depth (edgeCount call.net)=true
  · have hactive := (activeTest_correct _ _ _ _).mp ha
    have hm := hmenu root call hr hM hp hpos hw hg hd hreach hactive
    have hlen := children_length s call ha
    have hsum : ((children s call).length:ℝ) ≤
        (size (exponent (SemiprimeD1PackingReady.logarithm s) call.depth):ℝ)*
        (64*Real.exp (48*(edgeCount call.net:ℝ)/
          Real.sqrt (levels (SemiprimeD1PackingReady.logarithm s) call.depth:ℕ))) := by
      rw [hlen,Nat.cast_list_sum]
      simp only [List.map_map,Function.comp_def]
      have hh := sum_map_le (List.finRange (size (exponent (SemiprimeD1PackingReady.logarithm s) call.depth)))
        (fun t => ((phaseChildren call (exponent (SemiprimeD1PackingReady.logarithm s) call.depth)
          (levels (SemiprimeD1PackingReady.logarithm s) call.depth) t).length:ℝ))
        (64*Real.exp (48*(edgeCount call.net:ℝ)/
          Real.sqrt (levels (SemiprimeD1PackingReady.logarithm s) call.depth:ℕ)))
        (fun t _ => phase_length_le call _ _ t _ (Real.exp_pos _).le hm)
      simpa only [List.length_finRange] using hh
    have hgrid := grid_le s call.depth
    have hnode := SemiprimeD1HybridPathRate.node_term_le s
      (SemiprimeD1PackingReady.logarithm s/epsilonDenominator) call.depth (edgeCount call.net)
      (active_positive _ _ _ _ hactive) hdec
    have hexp : 48*(edgeCount call.net:ℝ)/
        Real.sqrt (levels (SemiprimeD1PackingReady.logarithm s) call.depth:ℕ) ≤
        modeFactor s*(1/8:ℝ)^call.depth := by
      have hh := mul_le_mul_of_nonneg_left hnode (by norm_num : (0:ℝ) ≤ 48)
      convert hh using 1 <;> dsimp only [modeFactor,levels] <;> ring
    calc
      _ ≤ _ := hsum
      _ = ((size (exponent (SemiprimeD1PackingReady.logarithm s) call.depth):ℝ)*64)*
          Real.exp (48*(edgeCount call.net:ℝ)/
            Real.sqrt (levels (SemiprimeD1PackingReady.logarithm s) call.depth:ℕ)) := by ring
      _ ≤ gridFactor s*Real.exp (modeFactor s*(1/8:ℝ)^call.depth) :=
        mul_le_mul hgrid (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by dsimp only [gridFactor];positivity)
  · have hf : children s call=[] := by
      dsimp only [children]
      rw [ite_eq_right ha]
    rw [hf,List.length_nil,Nat.cast_zero]
    dsimp only [gridFactor]
    positivity

end RiemannGaussian.SemiprimeD1HybridCallBranch
