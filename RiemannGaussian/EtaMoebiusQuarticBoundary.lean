import RiemannGaussian.EtaMoebiusQuarterQuotientMean
import RiemannGaussian.EtaMoebiusBoundaryFibreDecay

/-!
# The complete quotient carrier on quartic physical windows

Completing the only clipped quotient fibre at divisor cutoff `u^3`
adds at most `u^2` divisors when the physical cutoff is at least `u^4`.
The original completed term bound therefore makes this whole boundary
vanish in norm at every hypothetical right-half zero. Averaging preserves
its signed identity, and the complete quotient first mean has the same
nonzero source limit as the unchanged high first mean.

Only the boundary's mean square is controlled here. No mean-square bound
for the whole quartic quotient carrier or upper bound below the source
is inferred.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The single clipped fibre contains at most `u^2` extra divisors on a quartic physical window with cubic divisor cutoff. -/
theorem moebiusQuartic_boundary_card_le {M u : ℕ} (hu : 1 ≤ u) (hM : u ^ 4 ≤ M) :
    (Finset.Ioc (M / (M / (u ^ 3 + 1) + 1)) (u ^ 3)).card ≤ u ^ 2 := by
  have hsub : u - 1 + 1 = u := Nat.sub_add_cancel hu
  have hmul := congrArg (fun z : ℕ ↦ z * (u ^ 3 + 1)) hsub
  have hu3 : u ≤ u ^ 3 := Nat.le_self_pow (by decide : 3 ≠ 0) u
  have hq : u - 1 ≤ M / (u ^ 3 + 1) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
  have hprod : M / (u ^ 3 + 1) * (u ^ 3 + 1) ≤ M := Nat.div_mul_le_self M (u ^ 3 + 1)
  have hupper : M < (M / (M / (u ^ 3 + 1) + 1) + 1) * (M / (u ^ 3 + 1) + 1) :=
    (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_self _)
  have hRD : u ^ 3 ≤ M / (M / (u ^ 3 + 1) + 1) + u ^ 2 := by
    by_contra hn
    have hr : M / (M / (u ^ 3 + 1) + 1) + 1 + u ^ 2 ≤ u ^ 3 := by omega
    have hp := Nat.mul_le_mul_right (M / (u ^ 3 + 1) + 1) hr
    have hqu := Nat.mul_le_mul_left (u ^ 2) hq
    nlinarith
  simpa only [Nat.card_Ioc] using
    (show u ^ 3 - M / (M / (u ^ 3 + 1) + 1) ≤ u ^ 2 by omega)

/-- The entire original clipped boundary has norm at most `C_rho*u^(2-4*Re(rho))`, uniformly at every physical cutoff at least `u^4`. -/
theorem norm_pairedEtaCompletedMoebiusBoundaryFibre_quartic_le
    (rho : NontrivialZetaZero) {M u : ℕ} (hu : 1 ≤ u) (hM : u ^ 4 ≤ M) :
    ‖pairedEtaCompletedMoebiusBoundaryFibre rho M (u ^ 3)‖ ≤
      pairedEtaCompletedMoebiusTermConstant rho * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have h34 : u ^ 3 ≤ u ^ 4 := Nat.pow_le_pow_right hu (by norm_num)
  have hc := (pairedEtaCompletedMoebiusTermConstant_pos rho).le
  have hcard : ((Finset.Ioc (M / (M / (u ^ 3 + 1) + 1)) (u ^ 3)).card : ℝ) ≤ (u : ℝ) ^ 2 := by
    exact_mod_cast moebiusQuartic_boundary_card_le hu hM
  have hp : (M : ℝ) ^ (-rho.1.re) ≤ ((u : ℝ) ^ 4) ^ (-rho.1.re) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hM)
      (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)
  have he : (u : ℝ) ^ 2 * ((u : ℝ) ^ 4) ^ (-rho.1.re) = (u : ℝ) ^ (2 - 4 * rho.1.re) := by
    rw [← Real.rpow_natCast_mul huR.le,
      show 2 - 4 * rho.1.re = 2 + 4 * (-rho.1.re) by ring,
      Real.rpow_add huR, Real.rpow_ofNat]
    norm_num only [Nat.cast_ofNat]
  unfold pairedEtaCompletedMoebiusBoundaryFibre
  calc
    _ ≤ ∑ d ∈ Finset.Ioc (M / (M / (u ^ 3 + 1) + 1)) (u ^ 3),
        pairedEtaCompletedMoebiusTermConstant rho * (M : ℝ) ^ (-rho.1.re) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hl, hdU⟩ := Finset.mem_Ioc.mp hd
      exact norm_pairedEtaCompletedMoebiusTerm_le rho
        (Finset.mem_Icc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hl, hdU.trans (h34.trans hM)⟩)
    _ ≤ (u : ℝ) ^ 2 * (pairedEtaCompletedMoebiusTermConstant rho * (M : ℝ) ^ (-rho.1.re)) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg M) _))
    _ ≤ (u : ℝ) ^ 2 * (pairedEtaCompletedMoebiusTermConstant rho * ((u : ℝ) ^ 4) ^ (-rho.1.re)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hc) (sq_nonneg _)
    _ = _ := by rw [← mul_assoc, mul_comm ((u : ℝ) ^ 2), mul_assoc, he]

/-- The complex physical first mean of the unchanged boundary fibre. -/
def pairedEtaCompletedMoebiusBoundaryFirstMean (rho : NontrivialZetaZero) (A D : ℕ) : ℂ :=
  (∑ t ∈ Finset.range A, pairedEtaCompletedMoebiusBoundaryFibre rho (A + t) D) / A

/-- The boundary's full complex mean has the uniform quartic allowance. -/
theorem norm_pairedEtaCompletedMoebiusBoundaryFirstMean_quartic_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) :
    ‖pairedEtaCompletedMoebiusBoundaryFirstMean rho (u ^ 4) (u ^ 3)‖ ≤
      pairedEtaCompletedMoebiusTermConstant rho * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  unfold pairedEtaCompletedMoebiusBoundaryFirstMean
  rw [norm_div, Complex.norm_natCast]
  have hsum := (norm_sum_le (Finset.range (u ^ 4))
    (fun t ↦ pairedEtaCompletedMoebiusBoundaryFibre rho (u ^ 4 + t) (u ^ 3))).trans
      (Finset.sum_le_sum (fun t _ ↦ norm_pairedEtaCompletedMoebiusBoundaryFibre_quartic_le rho hu
        (Nat.le_add_right (u ^ 4) t)))
  apply (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (u ^ 4))).trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow]
  field_simp

/-- The original boundary mean square also decays on quartic windows; this theorem estimates only the added fibre. -/
theorem pairedEtaCompletedMoebiusBoundaryMeanSquare_quartic_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) :
    pairedEtaCompletedMoebiusBoundaryMeanSquare rho (u ^ 4) (u ^ 4) (u ^ 3) ≤
      pairedEtaCompletedMoebiusTermConstant rho ^ 2 * (u : ℝ) ^ (4 - 8 * rho.1.re) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  unfold pairedEtaCompletedMoebiusBoundaryMeanSquare
  have hpoint (t : ℕ) : ‖pairedEtaCompletedMoebiusBoundaryFibre rho (u ^ 4 + t) (u ^ 3)‖ ^ 2 ≤
      (pairedEtaCompletedMoebiusTermConstant rho * (u : ℝ) ^ (2 - 4 * rho.1.re)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_pairedEtaCompletedMoebiusBoundaryFibre_quartic_le rho hu
      (Nat.le_add_right _ _)) 2
  apply (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun t _ ↦ hpoint t)) (Nat.cast_nonneg _)).trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow]
  rw [mul_div_cancel_left₀ _ (pow_ne_zero 4 huR.ne'), mul_pow,
    ← Real.rpow_mul_natCast huR.le]
  congr 1
  norm_num only [Nat.cast_ofNat]
  congr 1
  ring

/-- The single boundary's entire mean square tends to zero on quartic physical windows at a hypothetical right-half zero. -/
theorem pairedEtaCompletedMoebiusBoundaryMeanSquare_quartic_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ pairedEtaCompletedMoebiusBoundaryMeanSquare rho (u ^ 4) (u ^ 4) (u ^ 3))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (4 - 8 * rho.1.re)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < 8 * rho.1.re - 4)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ by
    unfold pairedEtaCompletedMoebiusBoundaryMeanSquare
    positivity))
    ((eventually_ge_atTop 1).mono fun _ hu ↦ pairedEtaCompletedMoebiusBoundaryMeanSquare_quartic_le rho hu)
  simpa only [mul_zero] using hp.const_mul (pairedEtaCompletedMoebiusTermConstant rho ^ 2)

/-- The complex physical first mean of all selected complete quotient blocks. -/
def pairedEtaCompletedMoebiusCompleteQuotientFirstMean
    (rho : NontrivialZetaZero) (A D : ℕ) : ℂ :=
  (∑ t ∈ Finset.range A,
    pairedEtaCompletedMoebiusCompleteQuotientAggregate rho (A + t) D) / A

/-- Completion adds precisely the signed boundary mean; no complex interference is discarded. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientFirstMean_eq_boundary_add_large
    (rho : NontrivialZetaZero) {A D : ℕ} (hDA : D ≤ A) :
    pairedEtaCompletedMoebiusCompleteQuotientFirstMean rho A D =
      pairedEtaCompletedMoebiusBoundaryFirstMean rho A D +
        pairedEtaCompletedMoebiusLargeFirstMean rho A D := by
  unfold pairedEtaCompletedMoebiusCompleteQuotientFirstMean pairedEtaCompletedMoebiusBoundaryFirstMean
    pairedEtaCompletedMoebiusLargeFirstMean
  simp_rw [pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_boundary_add_large rho
    (hDA.trans (Nat.le_add_right _ _))]
  rw [Finset.sum_add_distrib, add_div]

/-- Completing every quotient block changes the original first mean by at most the whole quartic boundary allowance. -/
theorem norm_pairedEtaCompletedMoebiusCompleteQuotientFirstMean_sub_large_quartic_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) :
    ‖pairedEtaCompletedMoebiusCompleteQuotientFirstMean rho (u ^ 4) (u ^ 3) -
      pairedEtaCompletedMoebiusLargeFirstMean rho (u ^ 4) (u ^ 3)‖ ≤
        pairedEtaCompletedMoebiusTermConstant rho * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  rw [pairedEtaCompletedMoebiusCompleteQuotientFirstMean_eq_boundary_add_large rho
    (Nat.pow_le_pow_right hu (by norm_num)), add_sub_cancel_right]
  exact norm_pairedEtaCompletedMoebiusBoundaryFirstMean_quartic_le rho hu

/-- The full complete-quotient first mean has an explicit source error including both the entire low family and the single added boundary. -/
theorem norm_pairedEtaCompletedMoebiusCompleteQuotientFirstMean_quartic_sub_source_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 2 ≤ u) :
    ‖pairedEtaCompletedMoebiusCompleteQuotientFirstMean rho (u ^ 4) (u ^ 3) -
      pairedEtaCompletedMoebiusSource rho‖ ≤
        (pairedEtaCompletedMoebiusTermConstant rho + pairedEtaMoebiusFirstMeanConstant rho) *
          (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (pairedEtaCompletedMoebiusCompleteQuotientFirstMean rho (u ^ 4) (u ^ 3))
    (pairedEtaCompletedMoebiusLargeFirstMean rho (u ^ 4) (u ^ 3)) (pairedEtaCompletedMoebiusSource rho)
  exact (ht.trans (add_le_add
    (norm_pairedEtaCompletedMoebiusCompleteQuotientFirstMean_sub_large_quartic_le rho (by omega))
    (norm_pairedEtaCompletedMoebiusLargeFirstMean_quartic_sub_source_le rho hu))).trans_eq (by ring)

/-- At a hypothetical right-half zero, the complete quotient first mean retains the original nonzero source on quartic windows. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientFirstMean_quartic_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ pairedEtaCompletedMoebiusCompleteQuotientFirstMean rho (u ^ 4) (u ^ 3))
      atTop (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (2 - 4 * rho.1.re)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : 0 < 4 * rho.1.re - 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext u
    simp only [Function.comp_apply]
    congr 1
    ring
  have hz : Tendsto (fun u : ℕ ↦ pairedEtaCompletedMoebiusCompleteQuotientFirstMean rho
      (u ^ 4) (u ^ 3) - pairedEtaCompletedMoebiusSource rho) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
      ((eventually_ge_atTop 2).mono fun _ hu ↦
        norm_pairedEtaCompletedMoebiusCompleteQuotientFirstMean_quartic_sub_source_le rho hu)
    simpa only [mul_zero] using hp.const_mul
      (pairedEtaCompletedMoebiusTermConstant rho + pairedEtaMoebiusFirstMeanConstant rho)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [norm_zero] using hz.norm)

end

end RiemannGaussian
