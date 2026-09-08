import RiemannGaussian.EtaGammaQuadraticGcd
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionMaximumRigidity

/-!
# The gamma source and the exact reflected completion amplitudes

The elementary eta factor cancels from the original Moebius source.
A nonzero normalization identifies that source with the existing completed
Laplace amplitude. Both conjugation and the partner are kept explicit.
The energy-ratio identity does not assert equality of the two energies.
The actual reflected diagonal has coefficient `mu(d)^2/d`; the full
cross expansion retains all off-diagonal interactions.
-/

open Complex Filter RiemannGaussian RiemannGaussian.EtaGammaSmoothing
open RiemannGaussian.EtaGammaGcd
open scoped Classical ComplexConjugate Topology ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaReflection

noncomputable section

/-- The original Moebius source is exactly the polynomial--Archimedean completion numerator. -/
theorem source_eq_completionNumerator (rho : NontrivialZetaZero) :
    pairedEtaCompletedMoebiusSource rho = pairedEtaXiCompletionNumerator rho.1 := by
  change (pairedEtaXiCompletionNumerator rho.1 / pairedEtaFactor rho.1) *
    pairedEtaFactor rho.1 = _
  exact div_mul_cancel₀ _ (pairedEtaFactor_ne_zero_of_re_lt_one (NontrivialZetaZero.re_lt_one rho))

/-- The nonzero scalar converting the gamma source to the existing Laplace amplitude. -/
def sourceNormalization (rho : NontrivialZetaZero) : ℂ := rho.1 / pairedEtaFactor rho.1

/-- The original nontrivial zero and eta factor make the normalization nonsingular. -/
theorem sourceNormalization_ne_zero (rho : NontrivialZetaZero) : sourceNormalization rho ≠ 0 := by
  apply div_ne_zero _ (pairedEtaFactor_ne_zero_of_re_lt_one (NontrivialZetaZero.re_lt_one rho))
  intro h
  have hr := NontrivialZetaZero.zero_lt_re rho
  rw [h] at hr
  norm_num at hr

/-- The normalized gamma source is the exact completed positive-Laplace amplitude. -/
theorem normalized_source_eq_amplitude (rho : NontrivialZetaZero) :
    sourceNormalization rho * pairedEtaCompletedMoebiusSource rho =
      pairedEtaCompletedLaplaceAmplitude rho.1 := by
  change (rho.1 / pairedEtaFactor rho.1) *
    (pairedEtaXiCompletionFactor rho.1 * pairedEtaFactor rho.1) =
      pairedEtaXiCompletionFactor rho.1 * rho.1
  have hfactor : pairedEtaFactor rho.1 ≠ 0 :=
    pairedEtaFactor_ne_zero_of_re_lt_one (NontrivialZetaZero.re_lt_one rho)
  rw [mul_left_comm, div_mul_cancel₀ _ hfactor]

/-- The conjugate partner's normalized source retains the conjugation of the complementary amplitude. -/
theorem normalized_partner_source_eq_conj_amplitude (rho : NontrivialZetaZero) :
    sourceNormalization (NontrivialZetaZero.conjugatePartner rho) *
      pairedEtaCompletedMoebiusSource (NontrivialZetaZero.conjugatePartner rho) =
        starRingEnd ℂ (pairedEtaCompletedLaplaceAmplitude (1 - rho.1)) := by
  rw [normalized_source_eq_amplitude, NontrivialZetaZero.conjugatePartner_coe]
  have he : 1 - starRingEnd ℂ rho.1 = starRingEnd ℂ (1 - rho.1) := by simp
  rw [he, pairedEtaCompletedLaplaceAmplitude_conj]

/-- The ratio of both normalized source energies is exactly the existing reflection multiplier's squared norm. -/
theorem normalized_source_energy_ratio (rho : NontrivialZetaZero) :
    Complex.normSq (sourceNormalization rho * pairedEtaCompletedMoebiusSource rho) /
      Complex.normSq (sourceNormalization (NontrivialZetaZero.conjugatePartner rho) *
        pairedEtaCompletedMoebiusSource (NontrivialZetaZero.conjugatePartner rho)) =
          Complex.normSq (pairedEtaLaplaceReflectionMultiplier rho.1) := by
  rw [normalized_source_eq_amplitude, normalized_partner_source_eq_conj_amplitude]
  simp only [Complex.normSq_conj, pairedEtaLaplaceReflectionMultiplier, Complex.normSq_div]

/-- Source-energy equality would force the critical line; this theorem does not supply that arithmetic equality. -/
theorem normalized_source_energy_eq_iff_re_eq_half (rho : NontrivialZetaZero) :
    Complex.normSq (sourceNormalization rho * pairedEtaCompletedMoebiusSource rho) =
      Complex.normSq (sourceNormalization (NontrivialZetaZero.conjugatePartner rho) *
        pairedEtaCompletedMoebiusSource (NontrivialZetaZero.conjugatePartner rho)) ↔
          rho.1.re = 1 / 2 := by
  have hn : Complex.normSq (sourceNormalization (NontrivialZetaZero.conjugatePartner rho) *
      pairedEtaCompletedMoebiusSource (NontrivialZetaZero.conjugatePartner rho)) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (mul_ne_zero (sourceNormalization_ne_zero _)
      (pairedEtaCompletedMoebiusSource_ne_zero _))).ne'
  rw [← div_eq_one_iff_eq hn, normalized_source_energy_ratio]
  exact normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_iff_re_eq_half
    (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho)

/-- Conjugation of a positive integer complex power preserves its real logarithm branch. -/
theorem conj_nat_cpow_neg (s : ℂ) (d : ℕ) :
    starRingEnd ℂ ((d : ℂ) ^ (-s)) = (d : ℂ) ^ (-starRingEnd ℂ s) := by
  have h := Complex.cpow_conj (d : ℂ) (-s) (by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm)
  simpa only [map_natCast, map_neg] using h.symm

/-- The exact repository partner and conjugate-original powers multiply to the reciprocal divisor. -/
theorem partner_mul_conj_original_nat_cpow (rho : NontrivialZetaZero)
    {d : ℕ} (hd : 1 ≤ d) :
    (d : ℂ) ^ (-(NontrivialZetaZero.conjugatePartner rho).1) *
      starRingEnd ℂ ((d : ℂ) ^ (-rho.1)) = (d : ℂ)⁻¹ := by
  rw [conj_nat_cpow_neg, NontrivialZetaZero.conjugatePartner_coe,
    ← Complex.cpow_add _ _ (by exact_mod_cast (show d ≠ 0 by omega))]
  rw [show -(1 - starRingEnd ℂ rho.1) + -starRingEnd ℂ rho.1 = (-1 : ℂ) by ring,
    Complex.cpow_neg_one]

/-- The entire common-divisor gamma kernel retains both damped eta factors and both completion phases. -/
def crossKernel (rho : NontrivialZetaZero) (A B : ℝ) (d : ℕ) : ℂ :=
  (pairedEtaXiCompletionFactor (NontrivialZetaZero.conjugatePartner rho).1 *
      starRingEnd ℂ (pairedEtaXiCompletionFactor rho.1)) *
    (gammaDampedEta (NontrivialZetaZero.conjugatePartner rho).1 ((d : ℝ) / A) *
      starRingEnd ℂ (gammaDampedEta rho.1 ((d : ℝ) / B)))

/-- The actual reflected diagonal has the squarefree weight `mu(d)^2/d`; its Moebius sign has been squared. -/
theorem gammaMoebiusTerm_partner_mul_conj (rho : NontrivialZetaZero)
    (A B : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    gammaMoebiusTerm (NontrivialZetaZero.conjugatePartner rho) A d *
      starRingEnd ℂ (gammaMoebiusTerm rho B d) =
        ((μ d : ℂ) ^ 2 / (d : ℂ)) * crossKernel rho A B d := by
  unfold gammaMoebiusTerm crossKernel
  simp only [map_mul, map_intCast]
  calc
    _ = (μ d : ℂ) ^ 2 *
        ((d : ℂ) ^ (-(NontrivialZetaZero.conjugatePartner rho).1) *
          starRingEnd ℂ ((d : ℂ) ^ (-rho.1))) *
        ((pairedEtaXiCompletionFactor (NontrivialZetaZero.conjugatePartner rho).1 *
            starRingEnd ℂ (pairedEtaXiCompletionFactor rho.1)) *
          (gammaDampedEta (NontrivialZetaZero.conjugatePartner rho).1 ((d : ℝ) / A) *
            starRingEnd ℂ (gammaDampedEta rho.1 ((d : ℝ) / B)))) := by ring
    _ = _ := by rw [partner_mul_conj_original_nat_cpow rho hd]; ring

/-- On a squarefree divisor the diagonal coefficient is positive reciprocal mass. -/
theorem gammaMoebiusTerm_partner_mul_conj_of_squarefree (rho : NontrivialZetaZero)
    (A B : ℝ) {d : ℕ} (hd : 1 ≤ d) (hsq : Squarefree d) :
    gammaMoebiusTerm (NontrivialZetaZero.conjugatePartner rho) A d *
      starRingEnd ℂ (gammaMoebiusTerm rho B d) =
        (d : ℂ)⁻¹ * crossKernel rho A B d := by
  rw [gammaMoebiusTerm_partner_mul_conj rho A B hd]
  have hm : (μ d : ℂ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
  rw [hm, one_div]

/-- The full off-diagonal selected cross term; no unequal-divisor interaction is dropped. -/
def crossOffDiagonal (rho : NontrivialZetaZero) (A B : ℝ) (S : Finset ℕ) : ℂ :=
  ∑ d ∈ S, ∑ e ∈ S.erase d,
    gammaMoebiusTerm (NontrivialZetaZero.conjugatePartner rho) A d *
      starRingEnd ℂ (gammaMoebiusTerm rho B e)

/-- The selected reflected product is exactly its reciprocal squarefree diagonal plus the full off-diagonal core. -/
theorem gammaMoebiusSelected_partner_mul_conj (rho : NontrivialZetaZero)
    (A B : ℝ) (S : Finset ℕ) (hS : ∀ d ∈ S, 1 ≤ d) :
    gammaMoebiusSelected (NontrivialZetaZero.conjugatePartner rho) S A *
      starRingEnd ℂ (gammaMoebiusSelected rho S B) =
        (∑ d ∈ S, ((μ d : ℂ) ^ 2 / (d : ℂ)) * crossKernel rho A B d) +
          crossOffDiagonal rho A B S := by
  unfold gammaMoebiusSelected crossOffDiagonal
  rw [map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← gammaMoebiusTerm_partner_mul_conj rho A B (hS d hd)]
  exact (Finset.add_sum_erase _ _ hd).symm


/-- Squaring the exact reflected power retains the reciprocal-square gcd weight. -/
theorem partner_mul_conj_original_square_cpow (rho : NontrivialZetaZero)
    {g : ℕ} (hg : 1 ≤ g) :
    (g : ℂ) ^ (-2 * (NontrivialZetaZero.conjugatePartner rho).1) *
      starRingEnd ℂ ((g : ℂ) ^ (-2 * rho.1)) = (g : ℂ)⁻¹ ^ 2 := by
  have he (s : ℂ) : -2 * s = (2 : ℕ) * (-s) := by push_cast; ring
  rw [he, he, Complex.cpow_nat_mul, Complex.cpow_nat_mul, map_pow, ← mul_pow,
    partner_mul_conj_original_nat_cpow rho hg]

/-- The actual reflected common-gcd diagonal keeps both reduced cores and the squarefree reciprocal-square weight. -/
theorem gcdBlock_partner_mul_conj (rho : NontrivialZetaZero)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (U V : ℕ) {g : ℕ} (hg : 1 ≤ g) :
    gcdBlock (NontrivialZetaZero.conjugatePartner rho) A U g *
      starRingEnd ℂ (gcdBlock rho B V g) =
        ((μ g : ℂ) ^ 2 / (g : ℂ) ^ 2) *
          (reducedGcdCore (NontrivialZetaZero.conjugatePartner rho) (A / (g : ℝ) ^ 2) (U / g) g *
            starRingEnd ℂ (reducedGcdCore rho (B / (g : ℝ) ^ 2) (V / g) g)) := by
  rw [gcdBlock_eq_factor_mul_reducedCore _ hA U hg, gcdBlock_eq_factor_mul_reducedCore _ hB V hg]
  simp only [map_mul, map_pow, map_intCast]
  have hm : (μ g : ℂ) ^ 4 = (μ g : ℂ) ^ 2 := by
    by_cases hs : Squarefree g
    · have h2 : (μ g : ℂ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2, one_pow]
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      simp
  calc
    _ = (μ g : ℂ) ^ 4 *
        ((g : ℂ) ^ (-2 * (NontrivialZetaZero.conjugatePartner rho).1) *
          starRingEnd ℂ ((g : ℂ) ^ (-2 * rho.1))) *
        (reducedGcdCore (NontrivialZetaZero.conjugatePartner rho) (A / (g : ℝ) ^ 2) (U / g) g *
          starRingEnd ℂ (reducedGcdCore rho (B / (g : ℝ) ^ 2) (V / g) g)) := by ring
    _ = _ := by rw [hm, partner_mul_conj_original_square_cpow rho hg]; ring

/-- All unequal-gcd interactions between the two actual smooth quadratics, with both physical scales retained. -/
def gcdCrossOffDiagonal (rho : NontrivialZetaZero) (A B : ℝ) (U : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 U, ∑ h ∈ (Finset.Icc 1 U).erase g,
    gcdBlock (NontrivialZetaZero.conjugatePartner rho) A U g * starRingEnd ℂ (gcdBlock rho B U h)

/-- The original reflected quadratic product is its full reciprocal-square diagonal plus every unequal-gcd interaction. -/
theorem smoothQuadratic_partner_mul_conj (rho : NontrivialZetaZero)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (U : ℕ) :
    EtaGammaQuadratic.smoothQuadratic (NontrivialZetaZero.conjugatePartner rho) A U *
      starRingEnd ℂ (EtaGammaQuadratic.smoothQuadratic rho B U) =
        (∑ g ∈ Finset.Icc 1 U, ((μ g : ℂ) ^ 2 / (g : ℂ) ^ 2) *
          (reducedGcdCore (NontrivialZetaZero.conjugatePartner rho) (A / (g : ℝ) ^ 2) (U / g) g *
            starRingEnd ℂ (reducedGcdCore rho (B / (g : ℝ) ^ 2) (U / g) g))) +
              gcdCrossOffDiagonal rho A B U := by
  rw [smoothQuadratic_eq_sum_gcdBlock _ hA, smoothQuadratic_eq_sum_gcdBlock _ hB]
  unfold gcdCrossOffDiagonal
  rw [map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← gcdBlock_partner_mul_conj rho hA hB U U (Finset.mem_Icc.mp hg).1]
  exact (Finset.add_sum_erase _ _ hg).symm

/-- The actual common-gcd diagonal above the threshold, retaining both full blocks. -/
def gcdCrossDiagonalTail (rho : NontrivialZetaZero) (A B : ℝ) (U G : ℕ) : ℂ :=
  ∑ g ∈ Finset.Ioc G U,
    gcdBlock (NontrivialZetaZero.conjugatePartner rho) A U g * starRingEnd ℂ (gcdBlock rho B U g)

/-- The complete reflected diagonal tail has reciprocal decay throughout the strip, without a factor singular at one half. -/
theorem norm_gcdCrossDiagonalTail_le (rho : NontrivialZetaZero)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (U : ℕ) {G : ℕ} (hG : 1 ≤ G)
    (hAG : 2 * A ≤ (G : ℝ) ^ 2) (hBG : 2 * B ≤ (G : ℝ) ^ 2) :
    ‖gcdCrossDiagonalTail rho A B U G‖ ≤
      4096 * ‖pairedEtaXiCompletionFactor (NontrivialZetaZero.conjugatePartner rho).1‖ *
        ‖pairedEtaXiCompletionFactor rho.1‖ / (G : ℝ) := by
  let C := 4096 * ‖pairedEtaXiCompletionFactor (NontrivialZetaZero.conjugatePartner rho).1‖ *
    ‖pairedEtaXiCompletionFactor rho.1‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp (g : ℕ) (hg : g ∈ Finset.Ioc G U) :
      ‖gcdBlock (NontrivialZetaZero.conjugatePartner rho) A U g * starRingEnd ℂ (gcdBlock rho B U g)‖ ≤
        C * (g : ℝ) ^ (-2 : ℝ) := by
    have hGg : G ≤ g := (Finset.mem_Ioc.mp hg).1.le
    have hg1 : 1 ≤ g := hG.trans hGg
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
    have hGgR : (G : ℝ) ≤ g := by exact_mod_cast hGg
    have hs : (G : ℝ) ^ 2 ≤ (g : ℝ) ^ 2 := by
      nlinarith [(Nat.cast_nonneg G : (0 : ℝ) ≤ G)]
    rw [norm_mul, Complex.norm_conj]
    apply (mul_le_mul (norm_gcdBlock_le _ hA U hg1 (hAG.trans hs))
      (norm_gcdBlock_le _ hB U hg1 (hBG.trans hs)) (norm_nonneg _) (by positivity)).trans_eq
    have he : (g : ℝ) ^ (-2 * (NontrivialZetaZero.conjugatePartner rho).1.re) *
        (g : ℝ) ^ (-2 * rho.1.re) = (g : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hgR]
      congr 1
      simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re,
        Complex.conj_re]
      ring
    calc
      _ = C * ((g : ℝ) ^ (-2 * (NontrivialZetaZero.conjugatePartner rho).1.re) *
          (g : ℝ) ^ (-2 * rho.1.re)) := by dsimp [C]; ring
      _ = _ := by rw [he]
  unfold gcdCrossDiagonalTail
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ g ∈ Finset.Ioc G U, C * (g : ℝ) ^ (-2 : ℝ) := Finset.sum_le_sum hp
    _ = C * (∑ g ∈ Finset.Ioc G U, (g : ℝ) ^ (-2 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ C * ((G : ℝ) ^ ((-2 : ℝ) + 1) / (-(-2 : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_rpow_le (by norm_num : (-2 : ℝ) < -1) hG U) hC
    _ = _ := by norm_num [Real.rpow_neg_one, C, div_eq_mul_inv]

/-- The reflected common-gcd diagonal tail vanishes on the near-square schedule at every actual nontrivial zero. -/
theorem gcdCrossDiagonalTail_eighth_tendsto_zero (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ gcdCrossDiagonalTail rho ((u : ℝ) ^ 8) ((u : ℝ) ^ 8) (u ^ 5) (2 * u ^ 4))
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun u : ℕ ↦ (u : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := (hinv.pow 4).const_mul
    (2048 * ‖pairedEtaXiCompletionFactor (NontrivialZetaZero.conjugatePartner rho).1‖ *
      ‖pairedEtaXiCompletionFactor rho.1‖)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop (1 : ℕ)).mono fun u hu ↦ ?_) (by simpa only [zero_pow (by decide : 4 ≠ 0),
      mul_zero] using ht)
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hG : 1 ≤ 2 * u ^ 4 := Nat.mul_pos (by norm_num) (pow_pos hu 4)
  have hAG : 2 * (u : ℝ) ^ 8 ≤ ((2 * u ^ 4 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith [pow_nonneg huR.le 8]
  apply (norm_gcdCrossDiagonalTail_le rho (pow_pos huR 8) (pow_pos huR 8) (u ^ 5) hG hAG hAG).trans_eq
  push_cast
  field_simp
  ring

end

end RiemannGaussian.EtaGammaReflection
