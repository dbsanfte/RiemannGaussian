import RiemannGaussian.EtaGammaSmoothQuadratic

/-!
# Complete inner Möbius cancellation with independent factor cutoffs

The exact inverse identity controls outer rows past a product threshold,
with the full complementary cofactor tail retained. The shorter rectangle
retains the original source with two short sums and a vanishing tail.
No independent signed saving for the remaining short outer sum is asserted.
-/

open Complex Filter MeasureTheory Set RiemannGaussian RiemannGaussian.EtaGammaSmoothing
open RiemannGaussian.EtaGammaQuadratic
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaRectangular

noncomputable section

/-- The complete cofactor allows independently chosen arithmetic factors. -/
def mixedCofactor (f g : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * (f * g)

/-- Two bounded arithmetic factors have their full product-fibre norm bounded. -/
theorem norm_mul_le_nat (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (n : ℕ) :
    ‖(f * g) n‖ ≤ n := by
  rw [ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, ‖f p.1 * g p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      rw [norm_mul]
      exact (mul_le_mul (hf _) (hg _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    _ = (n.divisors.card : ℝ) := by rw [← Nat.map_div_right_divisors]; simp
    _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n

/-- The mixed complete cofactor has the same uniform quadratic coefficient envelope. -/
theorem norm_mixedCofactor_le_square (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (n : ℕ) :
    ‖mixedCofactor f g n‖ ≤ (n : ℝ) ^ 2 := by
  rw [mixedCofactor, ArithmeticFunction.coe_zeta_mul_apply]
  calc
    _ ≤ ∑ d ∈ n.divisors, ‖(f * g) d‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (n : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact (norm_mul_le_nat f g hf hg d).trans (by exact_mod_cast Nat.divisor_le hd)
    _ ≤ (n : ℝ) * n := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self n) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The actual mixed kernel has a summable exponential majorant, with both factor bounds discharged separately. -/
theorem mixed_gamma_majorant (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f g : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (hAn : 2 * A ≤ n) :
    ‖mixedCofactor f g n * gammaCarrier rho A n‖ ≤
      (256 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2) *
        Real.exp (-(n : ℝ) / (4 * A)) := by
  rw [norm_mul]
  calc
    _ ≤ (n : ℝ) ^ 2 * (8 * ‖pairedEtaXiCompletionFactor rho.1‖ *
        Real.exp (-(n : ℝ) / (2 * A))) :=
      mul_le_mul (norm_mixedCofactor_le_square f g hf hg n) (norm_gammaCarrier_large rho hA hn hAn)
        (norm_nonneg _) (by positivity)
    _ = (8 * ‖pairedEtaXiCompletionFactor rho.1‖) *
        ((n : ℝ) ^ 2 * Real.exp (-(n : ℝ) / (2 * A))) := by ring
    _ ≤ (8 * ‖pairedEtaXiCompletionFactor rho.1‖) *
        (32 * A ^ 2 * Real.exp (-(n : ℝ) / (4 * A))) :=
      mul_le_mul_of_nonneg_left (square_mul_exp_le A hA n (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by ring

private theorem mixed_tail_majorant (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f g : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    {R : ℕ} (hR : 2 * A ≤ R) (n : ℕ) :
    ‖mixedCofactor f g (R + n + 1) * gammaCarrier rho A (R + n + 1)‖ ≤
      (256 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2) *
        Real.exp (-((R + n + 1 : ℕ) : ℝ) * (1 / (4 * A))) := by
  have hRn : (R : ℝ) ≤ ((R + n + 1 : ℕ) : ℝ) := by exact_mod_cast (show R ≤ R + n + 1 by omega)
  simpa only [div_eq_mul_inv, one_mul] using
    mixed_gamma_majorant rho hA f g hf hg (by omega : 1 ≤ R + n + 1) (hR.trans hRn)

/-- The mixed full series converges absolutely at every positive physical scale. -/
theorem summable_norm_mixed_gamma (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f g : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) :
    Summable (fun n : ℕ ↦ ‖mixedCofactor f g (n + 1) * gammaCarrier rho A (n + 1)‖) := by
  let R : ℕ := ⌈2 * A⌉₊
  have hR : 2 * A ≤ R := Nat.le_ceil _
  have hb := (hasSum_exp_nat_tail (show 0 < 1 / (4 * A) by positivity) R).summable.mul_left
    (256 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2)
  apply (summable_nat_add_iff R).mp
  apply hb.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro n
  simpa only [Nat.add_comm n R] using mixed_tail_majorant rho hA f g hf hg hR n

/-- Every full mixed tail has the original uniform cofactor allowance. -/
theorem norm_tsum_mixed_gamma_tail_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f g : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    {R : ℕ} (hR : 2 * A ≤ R) :
    ‖∑' n : ℕ, mixedCofactor f g (R + n + 1) * gammaCarrier rho A (R + n + 1)‖ ≤
      1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 3 * Real.exp (-(R : ℝ) / (4 * A)) := by
  have hx : 0 < 1 / (4 * A) := by positivity
  have hb := (hasSum_exp_nat_tail hx R).mul_left
    (256 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2)
  have hs : Summable (fun n : ℕ ↦ mixedCofactor f g (R + n + 1) * gammaCarrier rho A (R + n + 1)) := by
    apply Summable.of_norm
    exact hb.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (mixed_tail_majorant rho hA f g hf hg hR)
  have hnorm := hs.hasSum.norm_le_of_bounded hb (mixed_tail_majorant rho hA f g hf hg hR)
  have he : 1 / (4 * A) ≤ Real.exp (1 / (4 * A)) - 1 := by
    linarith [Real.add_one_le_exp (1 / (4 * A))]
  apply hnorm.trans
  rw [← mul_div_assoc]
  calc
    _ ≤ (256 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2 *
        Real.exp (-(R : ℝ) * (1 / (4 * A)))) / (1 / (4 * A)) :=
      div_le_div_of_nonneg_left (by positivity) hx he
    _ = _ := by
      simp only [one_div, div_inv_eq_mul]
      rw [show -(R : ℝ) * (4 * A)⁻¹ = -(R : ℝ) / (4 * A) by ring]
      ring

/-- The full product support is retained when both input factors vanish initially. -/
theorem mixedCofactor_vanishes_below (f g : ArithmeticFunction ℂ) {W V : ℕ}
    (hf : ∀ n ≤ W, f n = 0) (hg : ∀ n ≤ V, g n = 0)
    {n : ℕ} (hn : n ≤ W * V) : mixedCofactor f g n = 0 := by
  rw [mixedCofactor, ArithmeticFunction.coe_zeta_mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hdWV := (Nat.divisor_le hd).trans hn
  by_cases hleft : p.1 ≤ W
  · rw [hf _ hleft, zero_mul]
  · have hright : p.2 ≤ V := by
      by_contra h
      have hm := Nat.mul_le_mul (show W + 1 ≤ p.1 by omega) (show V + 1 ≤ p.2 by omega)
      nlinarith
    rw [hg _ hright, mul_zero]

/-- Full gamma evaluation of an arithmetic coefficient sequence. -/
def evaluate (rho : NontrivialZetaZero) (A : ℝ) (f : ArithmeticFunction ℂ) : ℂ :=
  ∑' n : ℕ, f (n + 1) * gammaCarrier rho A (n + 1)

/-- Both vanished factor ranges force the entire remaining value into the product tail. -/
theorem norm_evaluate_mixed_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f g : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    {W V : ℕ} (hf0 : ∀ n ≤ W, f n = 0) (hg0 : ∀ n ≤ V, g n = 0)
    (hWV : 2 * A ≤ ((W * V : ℕ) : ℝ)) :
    ‖evaluate rho A (mixedCofactor f g)‖ ≤
      1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 3 * Real.exp (-((W * V : ℕ) : ℝ) / (4 * A)) := by
  have hs := (summable_norm_mixed_gamma rho hA f g hf hg).of_norm
  have he := hs.sum_add_tsum_nat_add (W * V)
  have hh : (∑ n ∈ Finset.range (W * V), mixedCofactor f g (n + 1) * gammaCarrier rho A (n + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [mixedCofactor_vanishes_below f g hf0 hg0 (by have := Finset.mem_range.mp hn; omega), zero_mul]
  rw [hh, zero_add] at he
  unfold evaluate
  rw [← he]
  simpa only [Nat.add_comm _ (W * V)] using norm_tsum_mixed_gamma_tail_le rho hA f g hf hg hWV

/-- The literal Möbius coefficients in an outer interval, including both endpoints. -/
def bandMoebius (W L : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if W < n ∧ n ≤ L then (μ n : ℂ) else 0, by simp⟩

/-- The selected outer coefficients retain the bound of the actual Möbius function. -/
theorem norm_bandMoebius_le_one (W L n : ℕ) : ‖bandMoebius W L n‖ ≤ 1 := by
  change ‖if W < n ∧ n ≤ L then (μ n : ℂ) else 0‖ ≤ 1
  split_ifs
  · rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · simp

/-- The whole outer interval is supported above its lower endpoint. -/
theorem bandMoebius_apply_of_le (W L n : ℕ) (hn : n ≤ W) : bandMoebius W L n = 0 := by
  change (if W < n ∧ n ≤ L then (μ n : ℂ) else 0) = 0
  rw [if_neg (by omega)]

/-- The finite outer coefficient evaluation is exactly the original selected gamma sum. -/
theorem hasSum_band_gamma (rho : NontrivialZetaZero) (A : ℝ) (W L : ℕ) :
    HasSum (fun n : ℕ ↦ bandMoebius W L (n + 1) * gammaCarrier rho A (n + 1))
      (gammaMoebiusSelected rho (Finset.Ioc W L) A) := by
  have hf : ∀ n ∉ Finset.Ico W L,
      bandMoebius W L (n + 1) * gammaCarrier rho A (n + 1) = 0 := by
    intro n hn
    have hh : ¬ (W < n + 1 ∧ n + 1 ≤ L) := by simp only [Finset.mem_Ico] at hn; omega
    change (if W < n + 1 ∧ n + 1 ≤ L then (μ (n + 1) : ℂ) else 0) * _ = 0
    rw [if_neg hh, zero_mul]
  have hs : HasSum (fun n : ℕ ↦ bandMoebius W L (n + 1) * gammaCarrier rho A (n + 1))
      (∑ n ∈ Finset.Ico W L, bandMoebius W L (n + 1) * gammaCarrier rho A (n + 1)) :=
    hasSum_sum_of_ne_finset_zero hf
  convert! hs using 1
  symm
  unfold gammaMoebiusSelected
  apply Finset.sum_bij (fun n _ ↦ n + 1)
  · intro n hn
    have := Finset.mem_Ico.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro a _ b _ hab
    omega
  · intro n hn
    have := Finset.mem_Ioc.mp hn
    exact ⟨n - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro n hn
    have hh : W < n + 1 ∧ n + 1 ≤ L := by have := Finset.mem_Ico.mp hn; omega
    change (if W < n + 1 ∧ n + 1 ≤ L then (μ (n + 1) : ℂ) else 0) * _ = _
    rw [if_pos hh]
    simp only [gammaCarrier, gammaMoebiusTerm, mul_assoc]

/-- Completing the inner Möbius sum gives the exact original outer coefficients minus the complementary cofactor. -/
theorem mixedCofactor_short_eq_sub_long (f : ArithmeticFunction ℂ) (V : ℕ) :
    mixedCofactor f (shortMoebius V) = f - mixedCofactor f (longMoebius V) := by
  have he : mixedCofactor f (shortMoebius V) + mixedCofactor f (longMoebius V) = f := by
    unfold mixedCofactor longMoebius
    calc
      _ = f * ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * μ) := by ring
      _ = f := by rw [ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]
  exact eq_sub_iff_add_eq.mpr he

/-- The signed outer rows retain the entire complete inner short Möbius sum. -/
def foldedOuterBand (rho : NontrivialZetaZero) (A : ℝ) (W L V : ℕ) : ℂ :=
  -evaluate rho A (mixedCofactor (bandMoebius W L) (shortMoebius V))

/-- The whole folded outer band equals the negative original low band plus its full complementary cofactor. -/
theorem foldedOuterBand_eq_low_add_error (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (W L V : ℕ) :
    foldedOuterBand rho A W L V =
      -gammaMoebiusSelected rho (Finset.Ioc W L) A +
        evaluate rho A (mixedCofactor (bandMoebius W L) (longMoebius V)) := by
  have hl := hasSum_band_gamma rho A W L
  have he := (summable_norm_mixed_gamma rho hA (bandMoebius W L) (longMoebius V)
    (norm_bandMoebius_le_one W L) (norm_longMoebius_le_one V)).of_norm.hasSum
  have hs := hl.sub he
  have hi (n : ℕ) : mixedCofactor (bandMoebius W L) (shortMoebius V) (n + 1) *
      gammaCarrier rho A (n + 1) =
        bandMoebius W L (n + 1) * gammaCarrier rho A (n + 1) -
          mixedCofactor (bandMoebius W L) (longMoebius V) (n + 1) * gammaCarrier rho A (n + 1) := by
    rw [mixedCofactor_short_eq_sub_long]
    change (bandMoebius W L (n + 1) - mixedCofactor (bandMoebius W L) (longMoebius V) (n + 1)) * _ = _
    ring
  simp_rw [← hi] at hs
  have hsum := hs.tsum_eq
  unfold foldedOuterBand evaluate
  rw [hsum]
  ring

/-- Completing the inner signed sum bounds a whole outer strip by its low-family cost and a product tail. -/
theorem norm_foldedOuterBand_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (W L V : ℕ) (hWV : 2 * A ≤ ((W * V : ℕ) : ℝ)) :
    ‖foldedOuterBand rho A W L V‖ ≤
      gammaMoebiusConstant rho / A ^ 3 * (L : ℝ) ^ (4 - rho.1.re) +
        1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 3 * Real.exp (-((W * V : ℕ) : ℝ) / (4 * A)) := by
  rw [foldedOuterBand_eq_low_add_error rho hA]
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  apply add_le_add
  · exact norm_gammaMoebiusSelected_le rho hA (fun n hn ↦ by
      have hh := Finset.mem_Ioc.mp hn
      exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩)
  · exact norm_evaluate_mixed_le rho hA (bandMoebius W L) (longMoebius V)
      (norm_bandMoebius_le_one W L) (norm_longMoebius_le_one V)
      (bandMoebius_apply_of_le W L) (fun _ hn ↦ longMoebius_apply_of_le hn) hWV

/-- On the actual sixth-power scale the outer strip from the square to the cube has an explicit vanishing allowance. -/
theorem norm_foldedOuterBand_sixth_le (rho : NontrivialZetaZero) {u : ℕ} (hu : 2 ≤ u) :
    ‖foldedOuterBand rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 3) (u ^ 5)‖ ≤
      gammaMoebiusConstant rho * (u : ℝ) ^ (-6 - 3 * rho.1.re) +
        1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * (u : ℝ) ^ 18 * Real.exp (-(u : ℝ) / 4) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hu
  have hWV : 2 * (u : ℝ) ^ 6 ≤ ((u ^ 2 * u ^ 5 : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_nonneg (show 0 ≤ (u : ℝ) - 2 by linarith) (show 0 ≤ (u : ℝ) ^ 6 by positivity)]
  apply (norm_foldedOuterBand_le rho (pow_pos huR 6) (u ^ 2) (u ^ 3) (u ^ 5) hWV).trans_eq
  have hlow : gammaMoebiusConstant rho / ((u : ℝ) ^ 6) ^ 3 *
      ((u ^ 3 : ℕ) : ℝ) ^ (4 - rho.1.re) =
        gammaMoebiusConstant rho * (u : ℝ) ^ (-6 - 3 * rho.1.re) := by
    simp only [Nat.cast_pow]
    rw [← Real.rpow_natCast_mul huR.le, ← pow_mul, ← Real.rpow_natCast (u : ℝ) (6 * 3),
      div_mul_eq_mul_div, mul_div_assoc, ← Real.rpow_sub huR]
    congr 2
    norm_num
    ring
  have he : -((u ^ 2 * u ^ 5 : ℕ) : ℝ) / (4 * (u : ℝ) ^ 6) = -(u : ℝ) / 4 := by
    push_cast
    field_simp
  rw [hlow, he]
  ring

/-- The whole outer strip vanishes after completing the inner sum, at every actual nontrivial zero. -/
theorem foldedOuterBand_sixth_tendsto_zero (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ foldedOuterBand rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 3) (u ^ 5))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (-6 - 3 * rho.1.re)) atTop (𝓝 0) := by
    convert! (tendsto_rpow_neg_atTop (show 0 < 6 + 3 * rho.1.re by
      linarith [NontrivialZetaZero.zero_lt_re rho])).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    funext u
    simp only [Function.comp_def]
    congr 1
    ring
  have hx : Tendsto (fun u : ℕ ↦ (u : ℝ) / 4) atTop atTop := by
    simpa only [div_eq_mul_inv] using (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const
      (by norm_num : (0 : ℝ) < (4 : ℝ)⁻¹)
  have hraw := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 18).comp hx).const_mul
    (1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * (4 : ℝ) ^ 18)
  have he : Tendsto (fun u : ℕ ↦ 1024 * ‖pairedEtaXiCompletionFactor rho.1‖ *
      (u : ℝ) ^ 18 * Real.exp (-(u : ℝ) / 4)) atTop (𝓝 0) := by
    convert! hraw using 1
    · funext u
      simp only [Function.comp_def]
      rw [show -((u : ℝ) / 4) = -(u : ℝ) / 4 by ring]
      ring_nf
    · simp only [mul_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop 2).mono fun u hu ↦ norm_foldedOuterBand_sixth_le rho hu)
    (by simpa only [mul_zero, zero_add] using (hp.const_mul (gammaMoebiusConstant rho)).add he)

/-- The mixed identity retains both short factors and the complete complementary product. -/
theorem moebius_eq_mixed (L V : ℕ) :
    (μ : ArithmeticFunction ℂ) = shortMoebius L + shortMoebius V -
      mixedCofactor (shortMoebius L) (shortMoebius V) +
        mixedCofactor (longMoebius L) (longMoebius V) := by
  have he : mixedCofactor (longMoebius L) (longMoebius V) =
      (μ : ArithmeticFunction ℂ) - shortMoebius L - shortMoebius V +
        mixedCofactor (shortMoebius L) (shortMoebius V) := by
    unfold mixedCofactor longMoebius
    calc
      _ = ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * μ) * μ -
          ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * μ) * shortMoebius L -
          ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * μ) * shortMoebius V +
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * (shortMoebius L * shortMoebius V) := by ring
      _ = _ := by rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]; simp
  rw [he]
  ring

/-- The actual full smooth rectangle keeps the two independent factor cutoffs. -/
def smoothRectangle (rho : NontrivialZetaZero) (A : ℝ) (L V : ℕ) : ℂ :=
  -evaluate rho A (mixedCofactor (shortMoebius L) (shortMoebius V))

/-- The original source has both literal short sums and the full omitted mixed cofactor. -/
theorem source_eq_shorts_add_rectangle_add_error (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) (L V : ℕ) :
    gammaMoebiusSource rho A =
      gammaMoebiusSelected rho (Finset.Icc 1 L) A +
        gammaMoebiusSelected rho (Finset.Icc 1 V) A + smoothRectangle rho A L V +
          evaluate rho A (mixedCofactor (longMoebius L) (longMoebius V)) := by
  have hl := hasSum_short_gamma rho A L
  have hv := hasSum_short_gamma rho A V
  have hq := (summable_norm_mixed_gamma rho hA (shortMoebius L) (shortMoebius V)
    (norm_shortMoebius_le_one L) (norm_shortMoebius_le_one V)).of_norm.hasSum
  have he := (summable_norm_mixed_gamma rho hA (longMoebius L) (longMoebius V)
    (norm_longMoebius_le_one L) (norm_longMoebius_le_one V)).of_norm.hasSum
  have hs := ((hl.add hv).sub hq).add he
  have hc (n : ℕ) : gammaMoebiusTerm rho A (n + 1) =
      (shortMoebius L (n + 1) * gammaCarrier rho A (n + 1) +
        shortMoebius V (n + 1) * gammaCarrier rho A (n + 1) -
          mixedCofactor (shortMoebius L) (shortMoebius V) (n + 1) * gammaCarrier rho A (n + 1)) +
            mixedCofactor (longMoebius L) (longMoebius V) (n + 1) * gammaCarrier rho A (n + 1) := by
    have hm := DFunLike.congr_fun (moebius_eq_mixed L V) (n + 1)
    change (μ (n + 1) : ℂ) = shortMoebius L (n + 1) + shortMoebius V (n + 1) -
      mixedCofactor (shortMoebius L) (shortMoebius V) (n + 1) +
        mixedCofactor (longMoebius L) (longMoebius V) (n + 1) at hm
    rw [gammaMoebiusTerm, mul_assoc]
    change (μ (n + 1) : ℂ) * gammaCarrier rho A (n + 1) = _
    rw [hm]
    ring
  simp_rw [← hc] at hs
  have hh := hs.unique (hasSum_gammaMoebiusTerm rho hA)
  simpa only [smoothRectangle, evaluate, sub_eq_add_neg] using hh.symm

/-- Both actual short ranges and the product tail bound the complete source comparison. -/
theorem norm_smoothRectangle_sub_source_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) (L V : ℕ) (hLV : 2 * A ≤ ((L * V : ℕ) : ℝ)) :
    ‖smoothRectangle rho A L V - gammaMoebiusSource rho A‖ ≤
      gammaMoebiusConstant rho / A ^ 3 * (L : ℝ) ^ (4 - rho.1.re) +
        gammaMoebiusConstant rho / A ^ 3 * (V : ℝ) ^ (4 - rho.1.re) +
          1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 3 * Real.exp (-((L * V : ℕ) : ℝ) / (4 * A)) := by
  have hi : smoothRectangle rho A L V - gammaMoebiusSource rho A =
      -(gammaMoebiusSelected rho (Finset.Icc 1 L) A +
          gammaMoebiusSelected rho (Finset.Icc 1 V) A +
            evaluate rho A (mixedCofactor (longMoebius L) (longMoebius V))) := by
    rw [source_eq_shorts_add_rectangle_add_error rho hA L V]
    ring
  rw [hi, norm_neg]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    exact add_le_add (norm_gammaMoebiusSelected_le rho hA (fun _ h ↦ h))
      (norm_gammaMoebiusSelected_le rho hA (fun _ h ↦ h))
  · exact norm_evaluate_mixed_le rho hA (longMoebius L) (longMoebius V)
      (norm_longMoebius_le_one L) (norm_longMoebius_le_one V)
      (fun _ hn ↦ longMoebius_apply_of_le hn) (fun _ hn ↦ longMoebius_apply_of_le hn) hLV

/-- The outer coefficient band is the literal difference between nested short factors. -/
theorem bandMoebius_eq_sub_short {W L : ℕ} (hWL : W ≤ L) :
    bandMoebius W L = shortMoebius L - shortMoebius W := by
  ext n
  change (if W < n ∧ n ≤ L then (μ n : ℂ) else 0) =
    (if n ≤ L then (μ n : ℂ) else 0) - (if n ≤ W then (μ n : ℂ) else 0)
  by_cases hnW : n ≤ W
  · rw [if_neg (by omega), if_pos (hnW.trans hWL), if_pos hnW, sub_self]
  · by_cases hnL : n ≤ L
    · rw [if_pos ⟨by omega, hnL⟩, if_pos hnL, if_neg hnW, sub_zero]
    · rw [if_neg (by omega), if_neg hnL, if_neg hnW, sub_self]

/-- Removing the bounded outer strip leaves exactly the shorter rectangle, with every cross term retained. -/
theorem smoothRectangle_sub_eq_foldedOuterBand (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {W L : ℕ} (hWL : W ≤ L) (V : ℕ) :
    smoothRectangle rho A L V - smoothRectangle rho A W V = foldedOuterBand rho A W L V := by
  have hl := (summable_norm_mixed_gamma rho hA (shortMoebius L) (shortMoebius V)
    (norm_shortMoebius_le_one L) (norm_shortMoebius_le_one V)).of_norm.hasSum
  have hw := (summable_norm_mixed_gamma rho hA (shortMoebius W) (shortMoebius V)
    (norm_shortMoebius_le_one W) (norm_shortMoebius_le_one V)).of_norm.hasSum
  have hs := hl.sub hw
  have hi (n : ℕ) : mixedCofactor (bandMoebius W L) (shortMoebius V) (n + 1) * gammaCarrier rho A (n + 1) =
      mixedCofactor (shortMoebius L) (shortMoebius V) (n + 1) * gammaCarrier rho A (n + 1) -
        mixedCofactor (shortMoebius W) (shortMoebius V) (n + 1) * gammaCarrier rho A (n + 1) := by
    rw [bandMoebius_eq_sub_short hWL, mixedCofactor, sub_mul, mul_sub]
    change (mixedCofactor (shortMoebius L) (shortMoebius V) (n + 1) -
      mixedCofactor (shortMoebius W) (shortMoebius V) (n + 1)) * gammaCarrier rho A (n + 1) = _
    ring
  simp_rw [← hi] at hs
  unfold smoothRectangle foldedOuterBand evaluate
  rw [hs.tsum_eq]
  ring

/-- The short rectangle has an explicit vanishing source allowance on the sixth/square/fifth schedule. -/
theorem norm_smoothRectangle_sixth_sub_source_le (rho : NontrivialZetaZero)
    {u : ℕ} (hu : 2 ≤ u) :
    ‖smoothRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5) -
      gammaMoebiusSource rho ((u : ℝ) ^ 6)‖ ≤
      2 * gammaMoebiusConstant rho * (u : ℝ) ^ (2 - 5 * rho.1.re) +
        1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * (u : ℝ) ^ 18 * Real.exp (-(u : ℝ) / 4) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hu
  have hA : 0 < (u : ℝ) ^ 6 := pow_pos huR 6
  have hUV : u ^ 2 ≤ u ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hWV : 2 * (u : ℝ) ^ 6 ≤ ((u ^ 2 * u ^ 5 : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_nonneg (show 0 ≤ (u : ℝ) - 2 by linarith) (show 0 ≤ (u : ℝ) ^ 6 by positivity)]
  have hi : smoothRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5) -
      gammaMoebiusSource rho ((u : ℝ) ^ 6) =
      -(gammaMoebiusSelected rho (Finset.Icc 1 (u ^ 2)) ((u : ℝ) ^ 6) +
          gammaMoebiusSelected rho (Finset.Icc 1 (u ^ 5)) ((u : ℝ) ^ 6) +
            evaluate rho ((u : ℝ) ^ 6) (mixedCofactor (longMoebius (u ^ 2)) (longMoebius (u ^ 5)))) := by
    rw [source_eq_shorts_add_rectangle_add_error rho hA (u ^ 2) (u ^ 5)]
    ring
  rw [hi, norm_neg]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    have hl := norm_gammaMoebiusSelected_sixth_le rho (by omega : 1 ≤ u)
      (Finset.Icc_subset_Icc_right hUV)
    have hv := norm_gammaMoebiusSelected_sixth_le rho (by omega : 1 ≤ u)
      (S := Finset.Icc 1 (u ^ 5)) (fun _ h ↦ h)
    linarith
  · apply (norm_evaluate_mixed_le rho hA (longMoebius (u ^ 2)) (longMoebius (u ^ 5))
      (norm_longMoebius_le_one (u ^ 2)) (norm_longMoebius_le_one (u ^ 5))
      (fun _ hn ↦ longMoebius_apply_of_le hn) (fun _ hn ↦ longMoebius_apply_of_le hn) hWV).trans_eq
    have he : -((u ^ 2 * u ^ 5 : ℕ) : ℝ) / (4 * (u : ℝ) ^ 6) = -(u : ℝ) / 4 := by
      push_cast
      field_simp
    rw [he]
    ring

/-- The short rectangle retains the nonzero source for `Re(rho)>2/5`; its strict signed upper bound is not asserted. -/
theorem smoothRectangle_sixth_tendsto_source (rho : NontrivialZetaZero)
    (hrho : (2 : ℝ) / 5 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ smoothRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5))
      atTop (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (2 - 5 * rho.1.re)) atTop (𝓝 0) := by
    convert! (tendsto_rpow_neg_atTop (by linarith : 0 < 5 * rho.1.re - 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    funext u
    simp only [Function.comp_def]
    congr 1
    ring
  have hx : Tendsto (fun u : ℕ ↦ (u : ℝ) / 4) atTop atTop := by
    simpa only [div_eq_mul_inv] using (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const
      (by norm_num : (0 : ℝ) < (4 : ℝ)⁻¹)
  have hraw := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 18).comp hx).const_mul
    (1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * (4 : ℝ) ^ 18)
  have he : Tendsto (fun u : ℕ ↦ 1024 * ‖pairedEtaXiCompletionFactor rho.1‖ *
      (u : ℝ) ^ 18 * Real.exp (-(u : ℝ) / 4)) atTop (𝓝 0) := by
    convert! hraw using 1
    · funext u
      simp only [Function.comp_def]
      rw [show -((u : ℝ) / 4) = -(u : ℝ) / 4 by ring]
      ring_nf
    · simp only [mul_zero]
  have hdiff : Tendsto (fun u : ℕ ↦ smoothRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5) -
      gammaMoebiusSource rho ((u : ℝ) ^ 6)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
      ((eventually_ge_atTop 2).mono fun u hu ↦ norm_smoothRectangle_sixth_sub_source_le rho hu)
      (by simpa only [mul_zero, zero_add] using (hp.const_mul (2 * gammaMoebiusConstant rho)).add he)
  have ht := hdiff.add (source_sixth_tendsto_source rho)
  simpa only [sub_add_cancel, zero_add] using ht

end

end RiemannGaussian.EtaGammaRectangular
