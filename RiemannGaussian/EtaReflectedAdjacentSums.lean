/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaReflectedAdjacent
import RiemannGaussian.EtaMoebiusCompletedTail

/-!
# Exact eta prefixes and reflected endpoint sums

Adjacent-ratio summation holds at every cutoff in the open right
half-plane, including the finite range of large phase rotations. The
signed variation series is absolutely convergent. The reflected sector
bound transfers to actual power endpoints and to arbitrary nonnegative
finite or summable families before the sum's norm is taken.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Set Topology
open scoped Classical ComplexConjugate

/-- Every finite eta interval retains both endpoint phases and its full
signed adjacent variation, without a cutoff-to-height assumption. -/
theorem pairedEtaCorePartialSum_sub_eq_adjacent_of_re_pos {s : ℂ} (hs : 0 < s.re)
    (N M : ℕ) :
    pairedEtaCorePartialSum (M + N) s - pairedEtaCorePartialSum N s =
      pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ) -
        pairedEtaAdjacentBoundary s ((2 * (M + N) + 1 : ℕ) : ℝ) +
      ∑ n ∈ Finset.range M, pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h := cpow_pair_eq_adjacent_boundary_add_defect_of_re_pos hs
      (x := ((2 * (M + N) + 1 : ℕ) : ℝ)) (by positivity)
    have hη : pairedEtaCorePartialSum (M + 1 + N) s =
        pairedEtaCorePartialSum (M + N) s + pairedEtaCoreSummand s (M + N) := by
      rw [show M + 1 + N = (M + N) + 1 by omega]
      exact Finset.sum_range_succ _ _
    rw [hη, Finset.sum_range_succ]
    have hn : 2 * (M + 1 + N) + 1 = (2 * (M + N) + 1) + 2 := by omega
    rw [hn]
    simp only [pairedEtaCoreSummand] at h ⊢
    push_cast at h ih ⊢
    rw [show (2 * ((M : ℂ) + N) + 1 + 1 : ℂ) = 2 * ((M : ℂ) + N) + 2 by ring] at h
    linear_combination ih + h

/-- The actual signed variation series is absolutely summable from every
cutoff; only a finite initial interval lies outside the safe tail range. -/
theorem summable_pairedEtaAdjacentDefect_tail_of_re_pos {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Summable (fun n : ℕ => pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ)) := by
  obtain ⟨K, hK⟩ := exists_nat_ge ‖s‖
  have hscale : ‖s‖ ≤ ((2 * (K + N) + 1 : ℕ) : ℝ) := by
    apply hK.trans
    exact_mod_cast (show K ≤ 2 * (K + N) + 1 by omega)
  have h := summable_pairedEtaAdjacentDefect_tail hs.le (K + N) hscale
  apply (summable_nat_add_iff K).mp
  simpa only [Nat.add_assoc] using h

private theorem adjacent_boundary_tendsto_zero {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Tendsto (fun M : ℕ => pairedEtaAdjacentBoundary s ((2 * (M + N) + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
  obtain ⟨K, hK⟩ := exists_nat_ge ‖s‖
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun M : ℕ => ((2 * (M + N) + 1 : ℕ) : ℝ) ^ (-s.re))
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop K] with M hM
    apply norm_pairedEtaAdjacentBoundary_le (by positivity)
    apply hK.trans
    exact_mod_cast (show K ≤ 2 * (M + N) + 1 by omega)
  · exact (tendsto_pairedEtaOddEndpoint_rpow_zero hs).comp (tendsto_add_atTop_nat N)

/-- The complete complex eta tail equals its exact boundary plus an
absolutely convergent signed variation series at every cutoff. -/
theorem pairedEtaCore_tail_eq_adjacent_of_re_pos {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaCore s - pairedEtaCorePartialSum N s =
      pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ) +
        ∑' n : ℕ, pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ) := by
  have he := ((summable_pairedEtaCoreSummand hs).tendsto_sum_tsum_nat.comp
    (tendsto_add_atTop_nat N)).sub_const (pairedEtaCorePartialSum N s)
  change Tendsto (fun M => pairedEtaCorePartialSum (M + N) s - pairedEtaCorePartialSum N s)
    atTop (nhds (pairedEtaCore s - pairedEtaCorePartialSum N s)) at he
  simp_rw [pairedEtaCorePartialSum_sub_eq_adjacent_of_re_pos hs N] at he
  have hb := adjacent_boundary_tendsto_zero hs N
  have hr := (summable_pairedEtaAdjacentDefect_tail_of_re_pos hs N).tendsto_sum_tsum_nat
  have ht := ((tendsto_const_nhds
    (x := pairedEtaAdjacentBoundary s ((2 * N + 1 : ℕ) : ℝ))).sub hb).add hr
  simpa using tendsto_nhds_unique he ht

/-- Actual reflected endpoint powers cancel to the reciprocal physical
argument. Both inverse multiplier phases remain in the mixed product. -/
theorem pairedEtaAdjacentBoundary_mul_conj_reflected (s : ℂ) {x : ℝ} (hx : 0 < x) :
    pairedEtaAdjacentBoundary s x * conj (pairedEtaAdjacentBoundary (1 - conj s) x) =
      ((x⁻¹ : ℝ) : ℂ) * pairedEtaReflectedAdjacentProduct s x := by
  have hc : conj ((x : ℂ) ^ (-(1 - conj s))) = (x : ℂ) ^ (-(1 - s)) := by
    have h := Complex.cpow_conj (x : ℂ) (-(1 - conj s)) (by
      rw [Complex.arg_ofReal_of_nonneg hx.le]
      exact Real.pi_ne_zero.symm)
    simpa only [map_neg, map_sub, map_one, conj_conj, conj_ofReal] using h.symm
  have hp : (x : ℂ) ^ (-s) * conj ((x : ℂ) ^ (-(1 - conj s))) = (x : ℂ)⁻¹ := by
    rw [hc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    rw [show -s + -(1 - s) = (-1 : ℂ) by ring, Complex.cpow_neg_one]
  unfold pairedEtaAdjacentBoundary pairedEtaReflectedAdjacentProduct
  rw [map_mul, Complex.ofReal_inv, ← hp]
  ring

/-- The same uniform sector controls the actual reflected power endpoint,
including its inverse-cutoff size and complete mixed phase. -/
theorem pairedEtaAdjacentBoundary_reflected_norm_le_re {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    2 * Real.sqrt (s.re * (1 - s.re)) *
        ‖pairedEtaAdjacentBoundary s x * conj (pairedEtaAdjacentBoundary (1 - conj s) x)‖ ≤
      (pairedEtaAdjacentBoundary s x * conj (pairedEtaAdjacentBoundary (1 - conj s) x)).re := by
  rw [pairedEtaAdjacentBoundary_mul_conj_reflected s hx, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
    mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  have h := mul_le_mul_of_nonneg_left
    (pairedEtaReflectedAdjacentProduct_norm_le_re hs hs1 hx) (inv_nonneg.mpr hx.le)
  nlinarith only [h]

/-- Every nonnegative finite family preserves a fixed proportion of the
sum of the individual mixed magnitudes in its real channel. -/
theorem sum_pairedEtaReflectedAdjacentProduct_norm_le_re {ι : Type*} {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1) (F : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ F, 0 ≤ w i) (hx : ∀ i ∈ F, 0 < x i) :
    2 * Real.sqrt (s.re * (1 - s.re)) *
        (∑ i ∈ F, w i * ‖pairedEtaReflectedAdjacentProduct s (x i)‖) ≤
      (∑ i ∈ F, (w i : ℂ) * pairedEtaReflectedAdjacentProduct s (x i)).re := by
  rw [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i hi
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  have h := mul_le_mul_of_nonneg_left
    (pairedEtaReflectedAdjacentProduct_norm_le_re hs hs1 (hx i hi)) (hw i hi)
  nlinarith only [h]

/-- The finite-family estimate extends to every absolutely summable
nonnegative family, with the whole mixed sum still present. -/
theorem tsum_pairedEtaReflectedAdjacentProduct_norm_le_re {ι : Type*} {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1) (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 < x i)
    (hsum : Summable (fun i => w i * ‖pairedEtaReflectedAdjacentProduct s (x i)‖)) :
    2 * Real.sqrt (s.re * (1 - s.re)) *
        (∑' i, w i * ‖pairedEtaReflectedAdjacentProduct s (x i)‖) ≤
      (∑' i, (w i : ℂ) * pairedEtaReflectedAdjacentProduct s (x i)).re := by
  have hc : Summable (fun i => (w i : ℂ) * pairedEtaReflectedAdjacentProduct s (x i)) := by
    apply Summable.of_norm
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)] using hsum
  rw [Complex.re_tsum hc, ← tsum_mul_left]
  apply (hsum.mul_left _).tsum_le_tsum _ (Complex.hasSum_re hc.hasSum).summable
  intro i
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  have h := mul_le_mul_of_nonneg_left
    (pairedEtaReflectedAdjacentProduct_norm_le_re hs hs1 (hx i)) (hw i)
  nlinarith only [h]

/-- Every actual nontrivial zero inherits the sector estimate with its
literal repository reflection partner. -/
theorem nontrivialZetaZero_adjacent_reflected_norm_le_re (rho : NontrivialZetaZero)
    {x : ℝ} (hx : 0 < x) :
    2 * Real.sqrt (rho.1.re * (1 - rho.1.re)) *
        ‖pairedEtaAdjacentBoundary rho.1 x *
          conj (pairedEtaAdjacentBoundary (NontrivialZetaZero.conjugatePartner rho).1 x)‖ ≤
      (pairedEtaAdjacentBoundary rho.1 x *
        conj (pairedEtaAdjacentBoundary (NontrivialZetaZero.conjugatePartner rho).1 x)).re := by
  rw [NontrivialZetaZero.conjugatePartner_coe]
  exact pairedEtaAdjacentBoundary_reflected_norm_le_re
    (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho) hx

/-- The original completed zeroth moment equals the negative completed
boundary and signed variation at every cutoff, with no multiplicity restriction. -/
theorem pairedEtaFiniteCompletedMoment_zero_eq_adjacent (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaFiniteCompletedMoment rho N 0 = -pairedEtaXiCompletionFactor rho.1 *
      (pairedEtaAdjacentBoundary rho.1 ((2 * N + 1 : ℕ) : ℝ) +
        ∑' n : ℕ, pairedEtaAdjacentDefect rho.1 ((2 * (n + N) + 1 : ℕ) : ℝ)) := by
  rw [pairedEtaFiniteCompletedMoment_zero_eq_completed_prefix]
  have h := pairedEtaCore_tail_eq_adjacent_of_re_pos (NontrivialZetaZero.zero_lt_re rho) N
  rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
    (NontrivialZetaZero.zero_lt_re rho) rho.2.2.2, rho.2.1, mul_zero, zero_sub] at h
  linear_combination -pairedEtaXiCompletionFactor rho.1 * h

/-- The full current's zeroth signed pair retains both completed boundary
plus variation channels, rather than being replaced by their mixed product. -/
theorem pairedEtaFiniteCompletedMomentPair_zero_eq_adjacent (rho : NontrivialZetaZero) (N : ℕ) :
    let X := ((2 * N + 1 : ℕ) : ℝ)
    let A := fun s : ℂ => pairedEtaXiCompletionFactor s *
      (pairedEtaAdjacentBoundary s X +
        ∑' n : ℕ, pairedEtaAdjacentDefect s ((2 * (n + N) + 1 : ℕ) : ℝ))
    pairedEtaFiniteCompletedMomentPair rho N 0 0 =
      etaSignedCompletedPair (A (NontrivialZetaZero.conjugatePartner rho).1)
        (A (NontrivialZetaZero.conjugatePartner rho).1) (A rho.1) (A rho.1) := by
  dsimp only
  simp only [pairedEtaFiniteCompletedMomentPair, pairedEtaFiniteCompletedMoment_zero_eq_adjacent,
    etaSignedCompletedPair, neg_mul, map_neg]
  ring

/-- The linear-in-height tail error reaches the actual completed current
moment, with its full completion amplitude and physical decay. -/
theorem norm_pairedEtaFiniteCompletedMoment_zero_add_adjacent_le
    (rho : NontrivialZetaZero) (N : ℕ) (hscale : ‖rho.1‖ ≤ ((2 * N + 1 : ℕ) : ℝ)) :
    ‖pairedEtaFiniteCompletedMoment rho N 0 + pairedEtaXiCompletionFactor rho.1 *
        pairedEtaAdjacentBoundary rho.1 ((2 * N + 1 : ℕ) : ℝ)‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ *
        (‖rho.1‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re)) *
          pairedEtaStepLog ((2 * N + 1 : ℕ) : ℝ)) := by
  have h := norm_pairedEtaCore_tail_sub_adjacent_le (NontrivialZetaZero.zero_lt_re rho) N hscale
  rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
    (NontrivialZetaZero.zero_lt_re rho) rho.2.2.2, rho.2.1, mul_zero, zero_sub] at h
  rw [show -pairedEtaCorePartialSum N rho.1 -
        pairedEtaAdjacentBoundary rho.1 ((2 * N + 1 : ℕ) : ℝ) =
      -(pairedEtaCorePartialSum N rho.1 +
        pairedEtaAdjacentBoundary rho.1 ((2 * N + 1 : ℕ) : ℝ)) by ring, norm_neg] at h
  rw [pairedEtaFiniteCompletedMoment_zero_eq_completed_prefix, ← mul_add, norm_mul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

end
end RiemannGaussian
