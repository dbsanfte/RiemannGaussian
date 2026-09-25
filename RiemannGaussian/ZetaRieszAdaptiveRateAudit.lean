/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszShiftedAllocation

/-!
# A logarithmic-order allocation cannot have a fixed exponential tail

This is an exact binomial marginal, not an assertion about the signed
arithmetic packet. It rules out paying logarithmic-mean exceptional mass
by a uniform exponential bound before the arithmetic cancellation is used.
-/

namespace RiemannGaussian.ZetaRieszShiftedCenter
noncomputable section
open Filter Topology

/-- An explicit shrinking share with logarithmic expected factorial order. -/
def logarithmicShare (N : ℕ) : ℝ := 16*Real.log ((N : ℝ)+1)/((N : ℝ)+1)

/-- The exact zero-order binomial mass, contained in the proposed d<2
exceptional event for any ordinary middle-prime leg. -/
def zeroOrderMass (N : ℕ) : ℝ := (1-logarithmicShare N)^N

/-- The zero-order probability is the sum over every allocation of all
other legs; this does not select a single factorial atom. -/
theorem zero_order_full_marginal {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι) (hp : p ∉ S) (x : ι → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.piAntidiag (S.cons p hp) N,
      if d p = 0 then ZetaRieszJointAllocation.allocationWeight (S.cons p hp) x d else 0) =
        (∑ q ∈ S, x q)^N := by
  rw [ZetaRieszJointAllocation.marked_allocation_cons S p hp x N (fun k => k = 0)]
  rw [Finset.sum_eq_single (0, N)]
  · simp
  · intro ij hij hne
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hfst : ij.1 ≠ 0 := by
      intro h
      apply hne
      ext <;> simp_all
    simp [hfst]
  · simp

theorem tendsto_logarithmicShare : Tendsto logarithmicShare atTop (nhds 0) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ht
  change Tendsto (fun N : ℕ => 16*Real.log ((N : ℝ)+1)/((N : ℝ)+1)) atTop (nhds 0)
  simpa only [Function.comp_def, pow_one, mul_zero, add_zero, one_mul,
    logarithmicShare, mul_div_assoc, mul_zero] using h.const_mul 16

private theorem log_one_sub_lower {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/2) :
    -2*x ≤ Real.log (1-x) := by
  have hd : 0 < 1-x := by linarith
  apply le_trans ?_ (Real.one_sub_inv_le_log_of_pos hd)
  apply (le_sub_iff_add_le).mpr
  rw [← one_div]
  rw [show -2*x+1/(1-x) = (-2*x*(1-x)+1)/(1-x) by field_simp]
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- The bad zero-order marginal is at least a fixed inverse polynomial;
it cannot be replaced by exp(-cN) for any c>0. -/
theorem zeroOrderMass_lower {N : ℕ} (hN : logarithmicShare N ≤ 1/2) :
    1/((N : ℝ)+1)^32 ≤ zeroOrderMass N := by
  have hx : 0 ≤ logarithmicShare N := by
    exact div_nonneg (mul_nonneg (by norm_num)
      (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N]))) (by positivity)
  have hpos : 0 < 1-logarithmicShare N := by linarith
  have hlog := log_one_sub_lower hx hN
  have hm : (N : ℝ)*logarithmicShare N ≤ 16*Real.log ((N : ℝ)+1) := by
    dsimp [logarithmicShare]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < (N : ℝ)+1)).mpr
    nlinarith [Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N] : (1 : ℝ) ≤ N+1)]
  have he : -32*Real.log ((N : ℝ)+1) ≤ (N : ℝ)*Real.log (1-logarithmicShare N) := by
    have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) N)
    nlinarith
  have hh := Real.exp_le_exp.mpr he
  have hp : Real.exp (32*Real.log ((N : ℝ)+1)) = ((N : ℝ)+1)^32 := by
    simpa only [Nat.cast_ofNat, Real.exp_log (by positivity : 0 < (N : ℝ)+1)] using
      Real.exp_nat_mul (Real.log ((N : ℝ)+1)) 32
  simpa only [neg_mul, Real.exp_neg, hp, Real.exp_nat_mul, Real.exp_log hpos,
    zeroOrderMass, one_div] using hh

theorem polynomial_source_ratio_tendsto {u : ℝ} (hu : 1/2 < u) (B : ℕ) :
    Tendsto (fun N : ℕ => (2*u)^N/((N : ℝ)+1)^B) atTop atTop := by
  have hrate : 1 < 2*u := by linarith
  have ht : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h := ((tendsto_exp_mul_div_rpow_atTop (B : ℝ) (Real.log (2*u))
    (Real.log_pos hrate)).comp ht).atTop_div_const (by linarith : 0 < 2*u)
  convert h using 1
  ext N
  dsimp only [Function.comp_def]
  rw [Real.rpow_natCast, mul_add, Real.exp_add, mul_one,
    mul_comm (Real.log (2*u)), Real.exp_nat_mul, Real.exp_log (by linarith : 0 < 2*u)]
  field_simp

/-- The rate obstruction is not specific to the exponent 16. For any
share tending to zero, its full zero-order marginal cannot pay a fixed
source growth factor before arithmetic cancellation is used. -/
theorem shrinking_share_source_mass_tendsto {u : ℝ} (hu : 1/2 < u)
    {x : ℕ → ℝ} (hx : Tendsto x atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (2*u)^N*(1-x N)^N) atTop atTop := by
  let c : ℝ := (1+2*u)/2
  have hc : 1 < c := by dsimp [c]; linarith
  have hlim : Tendsto (fun N : ℕ => 2*u*(1-x N)) atTop (nhds (2*u)) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using (h1.sub hx).const_mul (2*u)
  have he' : ∀ᶠ N : ℕ in atTop, c < 2*u*(1-x N) :=
    hlim (lt_mem_nhds (by dsimp [c]; linarith))
  have he : ∀ᶠ N : ℕ in atTop, c ≤ 2*u*(1-x N) := he'.mono (fun _ h => h.le)
  apply Filter.tendsto_atTop_mono' _ ?_ (tendsto_pow_atTop_atTop_of_one_lt hc)
  filter_upwards [he] with N hN
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith : 0 ≤ c) hN N

/-- Even a single discarded zero-order marginal has growing source-scale
mass in this admissible logarithmic-share model. Signed arithmetic
cancellation, or a different weighted bound, is required to discard it. -/
theorem normalized_zeroOrderMass_tendsto {u : ℝ} (hu : 1/2 < u) :
    Tendsto (fun N : ℕ => (2*u)^N*zeroOrderMass N) atTop atTop := by
  apply Filter.tendsto_atTop_mono' _ ?_ (polynomial_source_ratio_tendsto hu 32)
  filter_upwards [tendsto_logarithmicShare.eventually_le_const
    (by norm_num : (0 : ℝ) < 1/2)] with N hN
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (zeroOrderMass_lower hN)
    (pow_nonneg (by linarith : 0 ≤ 2*u) N)

end
end RiemannGaussian.ZetaRieszShiftedCenter
