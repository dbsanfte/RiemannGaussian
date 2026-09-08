import RiemannGaussian.EtaGammaRectangular
import RiemannGaussian.EtaMoebiusLogHarmonicBound

/-!
# Exact harmonic balancing for the actual smooth rectangle
The added coefficients lie above the unchanged Möbius prefix. The exact
harmonic moment vanishes; the signed rectangle still requires its upper bound.
-/

open Complex Filter RiemannGaussian RiemannGaussian.EtaGammaSmoothing
open RiemannGaussian.EtaGammaQuadratic RiemannGaussian.EtaGammaRectangular
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaBalancedOuter

noncomputable section

/-- The positive harmonic mass of the added interval, with both endpoints fixed. -/
def harmonicBlock (L : ℕ) : ℝ := ∑ n ∈ Finset.Ioc L (2 * L), 1 / (n : ℝ)

/-- The added interval always supplies at least one half of harmonic mass. -/
theorem half_le_harmonicBlock {L : ℕ} (hL : 1 ≤ L) : (1 : ℝ) / 2 ≤ harmonicBlock L := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    (1 : ℝ) / 2 = ∑ _n ∈ Finset.Ioc L (2 * L), 1 / (2 * (L : ℝ)) := by
      simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      rw [show 2 * L - L = L by omega]
      field_simp
    _ ≤ harmonicBlock L := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := Finset.mem_Ioc.mp hn
      exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < n by omega))
        (by exact_mod_cast hh.2)

/-- The exact added constant cancels the original harmonic prefix. -/
def balancingConstant (L : ℕ) : ℝ := -moebiusHarmonicPrefix L / harmonicBlock L

/-- The balancing rule has a uniform coefficient bound, without a sign-change assumption. -/
theorem abs_balancingConstant_le_four {L : ℕ} (hL : 1 ≤ L) : |balancingConstant L| ≤ 4 := by
  have hK := half_le_harmonicBlock hL
  have hKp : 0 < harmonicBlock L := by linarith
  rw [balancingConstant, abs_div, abs_neg, abs_of_pos hKp]
  apply (div_le_iff₀ hKp).mpr
  linarith [abs_moebiusHarmonicPrefix_le_two L]

/-- The added coefficient interval is an actual arithmetic function. -/
def unitBand (L : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if L < n ∧ n ≤ 2 * L then 1 else 0, by simp⟩

/-- The added interval has coefficient norm at most one. -/
theorem norm_unitBand_le_one (L n : ℕ) : ‖unitBand L n‖ ≤ 1 := by
  change ‖if L < n ∧ n ≤ 2 * L then (1 : ℂ) else 0‖ ≤ 1
  split_ifs <;> simp

/-- The added coefficients vanish on the entire unchanged prefix. -/
theorem unitBand_apply_of_le {L n : ℕ} (hn : n ≤ L) : unitBand L n = 0 := by
  change (if L < n ∧ n ≤ 2 * L then (1 : ℂ) else 0) = 0
  rw [if_neg (by omega)]

/-- The mathematically specified outer coefficients keep the full original prefix. -/
def balancedOuter (L : ℕ) : ArithmeticFunction ℂ :=
  shortMoebius L + (balancingConstant L : ℂ) • unitBand L

/-- Every original Möbius coefficient through the cutoff remains exact. -/
theorem balancedOuter_apply_of_le {L n : ℕ} (hn : n ≤ L) : balancedOuter L n = (μ n : ℂ) := by
  change shortMoebius L n + (balancingConstant L : ℂ) * unitBand L n = _
  rw [unitBand_apply_of_le hn, mul_zero, add_zero]
  change (if n ≤ L then (μ n : ℂ) else 0) = _
  rw [if_pos hn]

/-- The complete harmonic moment of the short factor is the original real harmonic prefix. -/
theorem harmonic_short (L : ℕ) :
    (∑ n ∈ Finset.Icc 1 (2 * L), shortMoebius L n / (n : ℂ)) = (moebiusHarmonicPrefix L : ℂ) := by
  have hs : Finset.Icc 1 L ⊆ Finset.Icc 1 (2 * L) := Finset.Icc_subset_Icc_right (by omega)
  have he := Finset.sum_subset hs (f := fun n ↦ shortMoebius L n / (n : ℂ)) (by
    intro n hmem hn
    have hn1 := (Finset.mem_Icc.mp hmem).1
    have hLn : ¬ n ≤ L := by simp only [Finset.mem_Icc] at hn; omega
    change (if n ≤ L then (μ n : ℂ) else 0) / _ = 0
    rw [if_neg hLn, zero_div])
  rw [← he]
  unfold moebiusHarmonicPrefix
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  change (if n ≤ L then (μ n : ℂ) else 0) / (n : ℂ) = _
  rw [if_pos (Finset.mem_Icc.mp hn).2]

/-- The added arithmetic interval has exactly its positive harmonic mass. -/
theorem harmonic_unitBand (L : ℕ) :
    (∑ n ∈ Finset.Icc 1 (2 * L), unitBand L n / (n : ℂ)) = (harmonicBlock L : ℂ) := by
  have hs : Finset.Ioc L (2 * L) ⊆ Finset.Icc 1 (2 * L) := by
    intro n hn
    have hh := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hh.2⟩
  have he := Finset.sum_subset hs (f := fun n ↦ unitBand L n / (n : ℂ)) (by
    intro n _ hn
    have hh : ¬ (L < n ∧ n ≤ 2 * L) := by simpa only [Finset.mem_Ioc] using hn
    change (if L < n ∧ n ≤ 2 * L then (1 : ℂ) else 0) / _ = 0
    rw [if_neg hh, zero_div])
  rw [← he]
  unfold harmonicBlock
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  change (if L < n ∧ n ≤ 2 * L then (1 : ℂ) else 0) / _ = _
  rw [if_pos (Finset.mem_Ioc.mp hn)]

/-- The actual balanced outer coefficients annihilate their entire harmonic moment exactly. -/
theorem harmonic_balancedOuter_eq_zero {L : ℕ} (hL : 1 ≤ L) :
    (∑ n ∈ Finset.Icc 1 (2 * L), balancedOuter L n / (n : ℂ)) = 0 := by
  have hKp : 0 < harmonicBlock L := by linarith [half_le_harmonicBlock hL]
  have hr : moebiusHarmonicPrefix L + balancingConstant L * harmonicBlock L = 0 := by
    rw [balancingConstant, div_mul_cancel₀ _ hKp.ne']
    ring
  change (∑ n ∈ Finset.Icc 1 (2 * L),
    (shortMoebius L n + (balancingConstant L : ℂ) * unitBand L n) / (n : ℂ)) = 0
  simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
    harmonic_short, harmonic_unitBand]
  exact_mod_cast hr

/-- Every constant multiple of the literal reciprocal-product mode is killed, with the other factor unrestricted. -/
theorem reciprocalProduct_balancedOuter_eq_zero {L : ℕ} (hL : 1 ≤ L)
    (V : ℕ) (g : ℕ → ℂ) (C : ℂ) :
    (∑ a ∈ Finset.Icc 1 (2 * L), ∑ b ∈ Finset.Icc 1 V,
      C * balancedOuter L a * g b / ((a : ℂ) * (b : ℂ))) = 0 := by
  have hi (a b : ℕ) : C * balancedOuter L a * g b / ((a : ℂ) * (b : ℂ)) =
      C * (balancedOuter L a / (a : ℂ)) * (g b / (b : ℂ)) := by ring
  simp_rw [hi, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum, harmonic_balancedOuter_eq_zero hL, mul_zero, zero_mul]

/-- The original carrier has a cubic envelope without a Möbius coefficient. -/
theorem norm_gammaCarrier_cubic_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖gammaCarrier rho A n‖ ≤ gammaMoebiusConstant rho / A ^ 3 * (n : ℝ) ^ 3 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (-rho.1.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hn) (by linarith [NontrivialZetaZero.zero_lt_re rho])
  rw [gammaCarrier, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  calc
    _ ≤ 1 * (‖pairedEtaXiCompletionFactor rho.1‖ *
        (Real.Gamma rho.1.re / (6 * ‖Complex.Gamma rho.1‖) * ((n : ℝ) / A) ^ 3)) :=
      mul_le_mul hp (mul_le_mul_of_nonneg_left (norm_gammaDampedEta_at_zero_le rho (div_pos hnR hA))
        (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := by simp only [gammaMoebiusConstant, div_pow]; ring

/-- The added short carrier keeps every original positive integer in the interval. -/
def unitBandLow (rho : NontrivialZetaZero) (A : ℝ) (L : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc L (2 * L), gammaCarrier rho A n

/-- The finite added interval agrees exactly with its full arithmetic evaluation. -/
theorem hasSum_unitBand_gamma (rho : NontrivialZetaZero) (A : ℝ) (L : ℕ) :
    HasSum (fun n : ℕ ↦ unitBand L (n + 1) * gammaCarrier rho A (n + 1))
      (unitBandLow rho A L) := by
  have hf : ∀ n ∉ Finset.Ico L (2 * L), unitBand L (n + 1) * gammaCarrier rho A (n + 1) = 0 := by
    intro n hn
    have hh : ¬ (L < n + 1 ∧ n + 1 ≤ 2 * L) := by simp only [Finset.mem_Ico] at hn; omega
    change (if L < n + 1 ∧ n + 1 ≤ 2 * L then (1 : ℂ) else 0) * _ = 0
    rw [if_neg hh, zero_mul]
  have hs : HasSum (fun n : ℕ ↦ unitBand L (n + 1) * gammaCarrier rho A (n + 1))
      (∑ n ∈ Finset.Ico L (2 * L), unitBand L (n + 1) * gammaCarrier rho A (n + 1)) :=
    hasSum_sum_of_ne_finset_zero hf
  convert! hs using 1
  symm
  unfold unitBandLow
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
    have hh : L < n + 1 ∧ n + 1 ≤ 2 * L := by have := Finset.mem_Ico.mp hn; omega
    change (if L < n + 1 ∧ n + 1 ≤ 2 * L then (1 : ℂ) else 0) * _ = _
    rw [if_pos hh, one_mul]

/-- The added interval has a small explicit allowance at the actual zero. -/
theorem norm_unitBandLow_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A) (L : ℕ) :
    ‖unitBandLow rho A L‖ ≤ 8 * gammaMoebiusConstant rho / A ^ 3 * (L : ℝ) ^ 4 := by
  unfold unitBandLow
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.Ioc L (2 * L), gammaMoebiusConstant rho / A ^ 3 * (2 * (L : ℝ)) ^ 3 := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := Finset.mem_Ioc.mp hn
      apply (norm_gammaCarrier_cubic_le rho hA (by omega : 1 ≤ n)).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (gammaMoebiusConstant_pos rho).le (by positivity))
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hh.2) 3
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      rw [show 2 * L - L = L by omega]
      ring

/-- Completing the added interval's inner sum retains its full complementary cofactor. -/
theorem evaluate_unitBand_short_eq (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A) (L V : ℕ) :
    evaluate rho A (mixedCofactor (unitBand L) (shortMoebius V)) = unitBandLow rho A L -
      evaluate rho A (mixedCofactor (unitBand L) (longMoebius V)) := by
  have hl := hasSum_unitBand_gamma rho A L
  have he := (summable_norm_mixed_gamma rho hA (unitBand L) (longMoebius V)
    (norm_unitBand_le_one L) (norm_longMoebius_le_one V)).of_norm.hasSum
  have hs := hl.sub he
  have hi (n : ℕ) : mixedCofactor (unitBand L) (shortMoebius V) (n + 1) * gammaCarrier rho A (n + 1) =
      unitBand L (n + 1) * gammaCarrier rho A (n + 1) -
        mixedCofactor (unitBand L) (longMoebius V) (n + 1) * gammaCarrier rho A (n + 1) := by
    rw [mixedCofactor_short_eq_sub_long]
    change (_ - _) * gammaCarrier rho A (n + 1) = _
    ring
  simp_rw [← hi] at hs
  exact hs.tsum_eq

/-- The whole added cofactor is controlled by its low interval and its product tail. -/
theorem norm_evaluate_unitBand_short_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (L V : ℕ) (hLV : 2 * A ≤ ((L * V : ℕ) : ℝ)) :
    ‖evaluate rho A (mixedCofactor (unitBand L) (shortMoebius V))‖ ≤
      8 * gammaMoebiusConstant rho / A ^ 3 * (L : ℝ) ^ 4 +
        1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 3 * Real.exp (-((L * V : ℕ) : ℝ) / (4 * A)) := by
  rw [evaluate_unitBand_short_eq rho hA]
  exact (norm_sub_le _ _).trans (add_le_add (norm_unitBandLow_le rho hA L)
    (norm_evaluate_mixed_le rho hA (unitBand L) (longMoebius V)
      (norm_unitBand_le_one L) (norm_longMoebius_le_one V)
      (fun _ hn ↦ unitBand_apply_of_le hn) (fun _ hn ↦ longMoebius_apply_of_le hn) hLV))

/-- The full smooth rectangle with the explicit balanced outer factor. -/
def balancedRectangle (rho : NontrivialZetaZero) (A : ℝ) (L V : ℕ) : ℂ :=
  -evaluate rho A (mixedCofactor (balancedOuter L) (shortMoebius V))

/-- The new rectangle differs from the original by its literal complete added rows. -/
theorem balancedRectangle_eq_original_sub (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A) (L V : ℕ) :
    balancedRectangle rho A L V = smoothRectangle rho A L V -
      (balancingConstant L : ℂ) * evaluate rho A (mixedCofactor (unitBand L) (shortMoebius V)) := by
  have hl := (summable_norm_mixed_gamma rho hA (shortMoebius L) (shortMoebius V)
    (norm_shortMoebius_le_one L) (norm_shortMoebius_le_one V)).of_norm.hasSum
  have hb := (summable_norm_mixed_gamma rho hA (unitBand L) (shortMoebius V)
    (norm_unitBand_le_one L) (norm_shortMoebius_le_one V)).of_norm.hasSum
  have hs := hl.add (hb.mul_left (balancingConstant L : ℂ))
  have hiAF : mixedCofactor (balancedOuter L) (shortMoebius V) =
      mixedCofactor (shortMoebius L) (shortMoebius V) +
        (balancingConstant L : ℂ) • mixedCofactor (unitBand L) (shortMoebius V) := by
    simp only [mixedCofactor, balancedOuter, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  have hi (n : ℕ) : mixedCofactor (balancedOuter L) (shortMoebius V) (n + 1) * gammaCarrier rho A (n + 1) =
      mixedCofactor (shortMoebius L) (shortMoebius V) (n + 1) * gammaCarrier rho A (n + 1) +
        (balancingConstant L : ℂ) * (mixedCofactor (unitBand L) (shortMoebius V) (n + 1) * gammaCarrier rho A (n + 1)) := by
    rw [hiAF]
    change (_ + (balancingConstant L : ℂ) * _) * _ = _
    ring
  simp_rw [← hi] at hs
  unfold balancedRectangle smoothRectangle evaluate
  rw [hs.tsum_eq]
  ring

/-- Exact harmonic balancing has a completely discharged source-transport cost. -/
theorem norm_balancedRectangle_sub_original_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {L : ℕ} (hL : 1 ≤ L) (V : ℕ) (hLV : 2 * A ≤ ((L * V : ℕ) : ℝ)) :
    ‖balancedRectangle rho A L V - smoothRectangle rho A L V‖ ≤
      4 * (8 * gammaMoebiusConstant rho / A ^ 3 * (L : ℝ) ^ 4 +
        1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 3 * Real.exp (-((L * V : ℕ) : ℝ) / (4 * A))) := by
  rw [balancedRectangle_eq_original_sub rho hA]
  rw [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (abs_balancingConstant_le_four hL) (norm_evaluate_unitBand_short_le rho hA L V hLV)
    (norm_nonneg _) (by norm_num)

/-- On the original rectangle schedule the entire balancing cost has a vanishing explicit bound. -/
theorem norm_balancedRectangle_sixth_sub_original_le (rho : NontrivialZetaZero)
    {u : ℕ} (hu : 2 ≤ u) :
    ‖balancedRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5) -
      smoothRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5)‖ ≤
      32 * gammaMoebiusConstant rho / (u : ℝ) ^ 10 +
        4096 * ‖pairedEtaXiCompletionFactor rho.1‖ * (u : ℝ) ^ 18 * Real.exp (-(u : ℝ) / 4) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hu
  have hUV : 2 * (u : ℝ) ^ 6 ≤ ((u ^ 2 * u ^ 5 : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_nonneg (show 0 ≤ (u : ℝ) - 2 by linarith) (show 0 ≤ (u : ℝ) ^ 6 by positivity)]
  apply (norm_balancedRectangle_sub_original_le rho (pow_pos huR 6)
    (one_le_pow₀ (by omega : 1 ≤ u)) (u ^ 5) hUV).trans_eq
  have he : -((u ^ 2 * u ^ 5 : ℕ) : ℝ) / (4 * (u : ℝ) ^ 6) = -(u : ℝ) / 4 := by
    push_cast
    field_simp
  rw [he]
  push_cast
  field_simp
  ring

/-- The balanced rectangle retains every original source error and its complete balancing allowance. -/
theorem norm_balancedRectangle_sixth_sub_source_le (rho : NontrivialZetaZero)
    {u : ℕ} (hu : 2 ≤ u) :
    ‖balancedRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5) - pairedEtaCompletedMoebiusSource rho‖ ≤
      2 * gammaMoebiusConstant rho * (u : ℝ) ^ (2 - 5 * rho.1.re) +
        32 * gammaMoebiusConstant rho / (u : ℝ) ^ 10 +
          5120 * ‖pairedEtaXiCompletionFactor rho.1‖ * (u : ℝ) ^ 18 * Real.exp (-(u : ℝ) / 4) +
            ‖pairedEtaXiCompletionFactor rho.1‖ * (1 + 16 * (2 : ℝ) ^ (-rho.1.re)) /
              (6 * ((u : ℝ) ^ 6) ^ 3) := by
  have hA : 0 < (u : ℝ) ^ 6 := pow_pos (by exact_mod_cast (show 0 < u by omega)) 6
  have he : balancedRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5) - pairedEtaCompletedMoebiusSource rho =
      ((balancedRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5) -
          smoothRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5)) +
        (smoothRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5) - gammaMoebiusSource rho ((u : ℝ) ^ 6))) +
          (gammaMoebiusSource rho ((u : ℝ) ^ 6) - pairedEtaCompletedMoebiusSource rho) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  apply (add_le_add
    (add_le_add (norm_balancedRectangle_sixth_sub_original_le rho hu)
      (norm_smoothRectangle_sixth_sub_source_le rho hu))
    (norm_gammaMoebiusSource_sub_le rho hA)).trans_eq
  ring

/-- The explicit harmonic balancing changes the rectangle by a quantity tending to zero. -/
theorem balancedRectangle_sixth_sub_original_tendsto_zero (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ balancedRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5) -
      smoothRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun u : ℕ ↦ (u : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp : Tendsto (fun u : ℕ ↦ 32 * gammaMoebiusConstant rho / (u : ℝ) ^ 10)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 10 ≠ 0), mul_zero] using
      (hinv.pow 10).const_mul (32 * gammaMoebiusConstant rho)
  have hx : Tendsto (fun u : ℕ ↦ (u : ℝ) / 4) atTop atTop := by
    simpa only [div_eq_mul_inv] using (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const
      (by norm_num : (0 : ℝ) < (4 : ℝ)⁻¹)
  have hraw := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 18).comp hx).const_mul
    (4096 * ‖pairedEtaXiCompletionFactor rho.1‖ * (4 : ℝ) ^ 18)
  have he : Tendsto (fun u : ℕ ↦ 4096 * ‖pairedEtaXiCompletionFactor rho.1‖ *
      (u : ℝ) ^ 18 * Real.exp (-(u : ℝ) / 4)) atTop (𝓝 0) := by
    convert! hraw using 1
    · funext u
      simp only [Function.comp_def]
      rw [show -((u : ℝ) / 4) = -(u : ℝ) / 4 by ring]
      ring_nf
    · simp only [mul_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop 2).mono fun _ hu ↦ norm_balancedRectangle_sixth_sub_original_le rho hu)
    (by simpa only [zero_add] using hp.add he)

/-- The completely specified balanced coefficients retain the original nonzero source, without a zero-simplicity assumption. -/
theorem balancedRectangle_sixth_tendsto_source (rho : NontrivialZetaZero)
    (hrho : (2 : ℝ) / 5 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ balancedRectangle rho ((u : ℝ) ^ 6) (u ^ 2) (u ^ 5))
      atTop (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have ht := (balancedRectangle_sixth_sub_original_tendsto_zero rho).add
    (smoothRectangle_sixth_tendsto_source rho hrho)
  simpa only [sub_add_cancel, zero_add] using ht

end

end RiemannGaussian.EtaGammaBalancedOuter
