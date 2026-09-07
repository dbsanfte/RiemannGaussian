import RiemannGaussian.EtaMomentDivisorAtom

/-!
# The common physical power of actual inverse-product atoms

The complete moment atom keeps its complex endpoint ratio and parity
amplitude. The ratio differs from one by an explicit divisor-over-cutoff
bound. This controls the normalized atom directly, including product
divisors whose own Möbius value vanishes.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The exact complex physical normalization ratio differs from one
by at most twice the zero norm times the divisor-over-cutoff ratio. -/
theorem norm_pairedEtaMomentPhysicalRatio_sub_one_le
    (rho : NontrivialZetaZero) {M d : ℕ} (hd : d ∈ Finset.Icc 1 M) :
    ‖pairedEtaMomentPhysicalRatio rho M d - 1‖ ≤ 2 * ‖rho.1‖ * d / M := by
  let p := d * pairedEtaUnpairedOddEndpoint (M / d)
  have hM : 1 ≤ M := (Finset.mem_Icc.mp hd).1.trans (Finset.mem_Icc.mp hd).2
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hhalf : (0 : ℝ) < (M : ℝ) / 2 := by positivity
  have hb := pairedEtaDivisorOddEndpoint_physical_bounds hd
  have hpR : (0 : ℝ) < p := hhalf.trans_le hb.1
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by exact_mod_cast hpR.ne')
  have hpowne : (p : ℂ) ^ rho.1 ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have he : pairedEtaMomentPhysicalRatio rho M d - 1 =
      ((M : ℂ) ^ rho.1 - (p : ℂ) ^ rho.1) / (p : ℂ) ^ rho.1 := by
    change (M : ℂ) ^ rho.1 / (p : ℂ) ^ rho.1 - 1 = _
    field_simp
  have hn : ‖(p : ℂ) ^ rho.1‖ = (p : ℝ) ^ rho.1.re := by
    simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hpR rho.1
  have hpow : ‖(M : ℂ) ^ rho.1 - (p : ℂ) ^ rho.1‖ ≤
      ‖rho.1‖ * ((M : ℝ) / 2) ^ (rho.1.re - 1) * d := by
    have h := norm_cpow_sub_cpow_le_above rho.1 hhalf (NontrivialZetaZero.re_lt_one rho).le
      hb.1 (by linarith : (M : ℝ) / 2 ≤ M)
    apply le_trans (by simpa only [Complex.ofReal_natCast] using h)
    exact mul_le_mul_of_nonneg_left hb.2 (by positivity)
  have hneg : (p : ℝ) ^ (-rho.1.re) ≤ ((M : ℝ) / 2) ^ (-rho.1.re) :=
    Real.rpow_le_rpow_of_nonpos hhalf hb.1 (by linarith [NontrivialZetaZero.zero_lt_re rho])
  have hcancel : ((M : ℝ) / 2) ^ (rho.1.re - 1) * ((M : ℝ) / 2) ^ (-rho.1.re) = 2 / M := by
    rw [← Real.rpow_add hhalf, show rho.1.re - 1 + -rho.1.re = -1 by ring, Real.rpow_neg_one]
    field_simp
  rw [he, norm_div, hn, div_eq_mul_inv, ← Real.rpow_neg hpR.le]
  calc
    _ ≤ (‖rho.1‖ * ((M : ℝ) / 2) ^ (rho.1.re - 1) * d) *
        ((M : ℝ) / 2) ^ (-rho.1.re) :=
      mul_le_mul hpow hneg (Real.rpow_nonneg hpR.le _) (by positivity)
    _ = (‖rho.1‖ * d) *
        (((M : ℝ) / 2) ^ (rho.1.re - 1) * ((M : ℝ) / 2) ^ (-rho.1.re)) := by ring
    _ = _ := by rw [hcancel]; ring

/-- The full atom's physical error coefficient retains the completion
amplitude and the complex-power normalization cost. -/
def pairedEtaMomentDivisorAtomPhysicalConstant (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  2 * (pairedEtaCompletedMomentPhaseErrorConstant rho k +
    ‖rho.1‖ * ‖pairedEtaMomentDivisorAmplitude rho k‖)

/-- The actual physical atom error coefficient is nonnegative. -/
theorem pairedEtaMomentDivisorAtomPhysicalConstant_nonneg (rho : NontrivialZetaZero) (k : ℕ) :
    0 ≤ pairedEtaMomentDivisorAtomPhysicalConstant rho k := by
  have h := pairedEtaCompletedMomentPhaseErrorConstant_nonneg rho k
  unfold pairedEtaMomentDivisorAtomPhysicalConstant
  positivity

/-- The exact physical atom error keeps its endpoint remainder and
normalization-ratio correction as separate complex terms. -/
theorem pairedEtaMomentDivisorAtom_physical_sub_parity
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) {M d : ℕ} (hd : d ∈ Finset.Icc 1 M) :
    (M : ℂ) ^ rho.1 * pairedEtaMomentDivisorAtom rho k a M d -
        pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / d) : ℂ) =
      pairedEtaMomentPhysicalRatio rho M d *
        (pairedEtaMomentDivisorEndpointAtom rho k a M d -
          pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / d) : ℂ)) +
      (pairedEtaMomentPhysicalRatio rho M d - 1) *
        (pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / d) : ℂ)) := by
  rw [← pairedEtaMomentPhysicalRatio_cancel rho hd]
  unfold pairedEtaMomentDivisorEndpointAtom
  ring

/-- The original completed product atom has a common physical parity
main term and an explicit uniform divisor-over-cutoff error at every
admissible moving center, below the actual zero multiplicity. -/
theorem norm_pairedEtaMomentDivisorAtom_physical_sub_parity_le
    (rho : NontrivialZetaZero) {k M d : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hd : d ∈ Finset.Icc 1 M) {a : ℝ}
    (ha : Real.log (M : ℝ) ≤ a ∧ a ≤ Real.log (M + 1 : ℝ)) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaMomentDivisorAtom rho k a M d -
        pairedEtaMomentDivisorAmplitude rho k * (pairedEtaDirichletSign (M / d) : ℂ)‖ ≤
      pairedEtaMomentDivisorAtomPhysicalConstant rho k * d / M := by
  have hsign : ‖(pairedEtaDirichletSign (M / d) : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast abs_pairedEtaDirichletSign (M / d)
  rw [pairedEtaMomentDivisorAtom_physical_sub_parity rho k a hd]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, hsign, mul_one]
  calc
    _ ≤ 2 * (pairedEtaCompletedMomentPhaseErrorConstant rho k * d / M) +
        (2 * ‖rho.1‖ * d / M) * ‖pairedEtaMomentDivisorAmplitude rho k‖ := by
      apply add_le_add
      · exact mul_le_mul (norm_pairedEtaMomentPhysicalRatio_le rho hd)
          (norm_pairedEtaMomentDivisorEndpointAtom_sub_parity_le rho hk hd ha)
          (norm_nonneg _) (by norm_num)
      · exact mul_le_mul_of_nonneg_right (norm_pairedEtaMomentPhysicalRatio_sub_one_le rho hd)
          (norm_nonneg _)
    _ = _ := by unfold pairedEtaMomentDivisorAtomPhysicalConstant; ring

end

end RiemannGaussian
