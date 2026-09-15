/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCountFrequency
import RiemannGaussian.ZetaRieszSmoothHead

/-!
# Exponential moments of the actual squarefree prime count

Test whether count sparsity can pay the complete integer contribution,
including all of its frequencies, using the finite Euler product.
-/

namespace RiemannGaussian.ZetaRieszPrimeCountMass
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCountFrequency

/-- An arbitrary count weight factors over the exact squarefree primes. -/
theorem count_weight_eq_product {n : ℕ} (hn : Squarefree n) (sigma z : ℝ) :
    z ^ n.primeFactors.card * Real.exp (-sigma * Real.log n) =
      ∏ p ∈ n.primeFactors, (z * Real.exp (-sigma * Real.log p)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    CoprimeEulerPhase.squarefree_log_eq_prime_sum hn, Finset.mul_sum, Real.exp_sum]

/-- The prime-count exponential moment over every actual finite
squarefree selection is dominated by its literal Euler product. -/
theorem squarefree_count_mass_le_product (D S : Finset ℕ)
    (hD : ∀ n ∈ D, Squarefree n) (hS : ∀ n ∈ D, n.primeFactors ⊆ S)
    (sigma : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    (∑ n ∈ D, z ^ n.primeFactors.card * Real.exp (-sigma * Real.log n)) ≤
      ∏ p ∈ S, (1 + z * Real.exp (-sigma * Real.log p)) := by
  have hinj : Set.InjOn Nat.primeFactors (D : Set ℕ) := by
    intro n hn m hm he
    rw [← Nat.prod_primeFactors_of_squarefree (hD n hn),
      ← Nat.prod_primeFactors_of_squarefree (hD m hm), he]
  calc
    _ = ∑ n ∈ D, ∏ p ∈ n.primeFactors, (z * Real.exp (-sigma * Real.log p)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact count_weight_eq_product (hD n hn) sigma z
    _ = ∑ T ∈ D.image Nat.primeFactors, ∏ p ∈ T, (z * Real.exp (-sigma * Real.log p)) :=
      (Finset.sum_image (s := D) (g := Nat.primeFactors)
        (f := fun T : Finset ℕ => ∏ p ∈ T, (z * Real.exp (-sigma * Real.log p))) hinj).symm
    _ ≤ ∑ T ∈ S.powerset, ∏ p ∈ T, (z * Real.exp (-sigma * Real.log p)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro T hT
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hT
        exact Finset.mem_powerset.mpr (hS n hn)
      · intro T _ _
        exact Finset.prod_nonneg fun _ _ => mul_nonneg hz (Real.exp_pos _).le
    _ = _ := (Finset.prod_one_add S).symm

/-- The genuinely summable positive integer mass used to bound every
finite prime universe at the same exponent. -/
def countMass (sigma : ℝ) : ℝ := ∑' n : ℕ, zetaPrimeExpWeight sigma n

/-- The count mass is nonnegative; summability is required separately
whenever it is used as a uniform bound on finite prime selections. -/
theorem countMass_nonneg (sigma : ℝ) : 0 ≤ countMass sigma :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

/-- The whole count generating function has an exponential bound
independent of the finite arithmetic selection and its prime universe. -/
theorem squarefree_count_mass_le_exp (D : Finset ℕ) (hD : ∀ n ∈ D, Squarefree n)
    {sigma z : ℝ} (hsigma : 1 < sigma) (hz : 0 ≤ z) :
    (∑ n ∈ D, z ^ n.primeFactors.card * Real.exp (-sigma * Real.log n)) ≤
      Real.exp (z * countMass sigma) := by
  let S := D.biUnion Nat.primeFactors
  have hS : ∀ n ∈ D, n.primeFactors ⊆ S := by
    intro n hn p hp
    exact Finset.mem_biUnion.mpr ⟨n, hn, hp⟩
  apply (squarefree_count_mass_le_product D S hD hS sigma hz).trans
  apply (Real.prod_one_add_le_exp_sum S (fun _ => mul_nonneg hz (Real.exp_pos _).le)).trans
  apply Real.exp_le_exp.mpr
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hz
  exact (summable_zetaPrimeExpWeight hsigma).sum_le_tsum S (fun _ _ => (Real.exp_pos _).le)

/-- Keeping the full divisor count, an exponential moment bound pays
every high-count integer at once. This covers all of their frequencies. -/
theorem many_prime_mass_le (D : Finset ℕ) (hD : ∀ n ∈ D, Squarefree n)
    {K : ℕ} (hK : ∀ n ∈ D, K ≤ n.primeFactors.card)
    {sigma r : ℝ} (hsigma : 1 < sigma) (hr : 1 ≤ r) :
    (∑ n ∈ D, (2 : ℝ) ^ n.primeFactors.card * Real.exp (-sigma * Real.log n)) ≤
      Real.exp (2 * r * countMass sigma) / r ^ K := by
  have hr0 : 0 < r := by linarith
  apply (le_div_iff₀ (pow_pos hr0 K)).mpr
  calc
    _ = ∑ n ∈ D, (r ^ K * (2 : ℝ) ^ n.primeFactors.card) * Real.exp (-sigma * Real.log n) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ ∑ n ∈ D, (r ^ n.primeFactors.card * (2 : ℝ) ^ n.primeFactors.card) *
        Real.exp (-sigma * Real.log n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr (hK n hn)) (by positivity)) (Real.exp_pos _).le
    _ = ∑ n ∈ D, (2 * r) ^ n.primeFactors.card * Real.exp (-sigma * Real.log n) := by
      simp only [mul_pow, mul_comm]
    _ ≤ _ := squarefree_count_mass_le_exp D hD hsigma (by positivity)

/-- The complete signed integer response is bounded by its exact
squarefree divisor-count mass, before any count generating function is used. -/
theorem norm_squarefree_sum_le_mass (D : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {L q : ℝ} (hL : 0 < L) (hq : 0 < q)
    (hD : ∀ n ∈ D, Squarefree n) (hband : D ⊆ zetaPrimeLogBand N) :
    ‖∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
      ∑ n ∈ D, (2 : ℝ) ^ n.primeFactors.card * Real.exp (-(3 / 2 - q) * Real.log n) := by
  let C := 32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
    ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  calc
    _ ≤ ∑ n ∈ D, ‖SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ D, C * ((2 : ℝ) ^ n.primeFactors.card *
        Real.exp (-(3 / 2 - q) * Real.log n)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hb := hband hn
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
      have hc := (SquarefreeVaughanLogSource.norm_coefficient_le hL n).trans
        ((ZetaRieszSmoothHead.logMajorant_le_prime_count (hD n hn)).trans
          (mul_le_mul_of_nonneg_right (ZetaRieszSmoothHead.log_le_of_mem_band hb) (by positivity)))
      have hk := norm_zetaPrimeFilterKernel_le_tilt P N (3 / 2 + Complex.I * y) hn1 hq
      have h := mul_le_mul hc hk (norm_nonneg _) (by positivity)
      rw [norm_mul]
      apply h.trans_eq
      have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
      rw [hs]
      dsimp [C]
      ring
    _ = _ := (Finset.mul_sum ..).symm

/-- The full original-band contribution from a selected many-prime
class has an independent, height-uniform exponential-moment bound. The
allowance includes every divisor choice, filter shift and source factor,
and bounds the whole integer response rather than one frequency sector. -/
theorem norm_normalized_many_sum_le (D : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {L u U q r : ℝ} (hL : 0 < L) (hu : 0 ≤ u) (huU : u ≤ U)
    (hq : 0 < q) (hqhalf : q < 1 / 2) (hr : 1 ≤ r)
    (hD : ∀ n ∈ D, Squarefree n) (hband : D ⊆ zetaPrimeLogBand N)
    {K : ℕ} (hK : ∀ n ∈ D, K ≤ n.primeFactors.card) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (32 * U * Real.log 2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ((N : ℝ) * (U / q) ^ N) * Real.exp (2 * r * countMass (3 / 2 - q)) / r ^ K := by
  have hs := norm_squarefree_sum_le_mass D P N y hL hq hD hband
  have hm := many_prime_mass_le D hD hK (by linarith : 1 < 3 / 2 - q) hr
  have hU : 0 ≤ U := hu.trans huU
  have hf : 0 ≤ ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hM : 0 ≤ ∑ n ∈ D, (2 : ℝ) ^ n.primeFactors.card *
      Real.exp (-(3 / 2 - q) * Real.log n) := Finset.sum_nonneg fun _ _ => by positivity
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  calc
    _ ≤ u ^ (N + 1) * ((32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ∑ n ∈ D, (2 : ℝ) ^ n.primeFactors.card * Real.exp (-(3 / 2 - q) * Real.log n)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ U ^ (N + 1) * ((32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        (Real.exp (2 * r * countMass (3 / 2 - q)) / r ^ K)) := by gcongr
    _ = _ := by rw [pow_succ U N, div_pow]; simp only [inv_pow]; ring

/-- The Euler generating-function cost grows subexponentially in the
original cofinal moment order. Every fixed geometric slack absorbs it. -/
theorem eventually_exp_count_le_geometric (C : ℝ) {s : ℝ} (hs : 1 < s) :
    ∀ᶠ j : ℕ in atTop, Real.exp (C * (dyadicPrimeCount j : ℝ)) ≤ s ^ dyadicMomentOrder j := by
  have hlog : 0 < Real.log s := Real.log_pos hs
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (C / (8 * Real.log s)))] with j hj
  have hC : C ≤ 8 * ((j : ℝ) + 4) * Real.log s := by
    have h := (div_le_iff₀ (by positivity : 0 < 8 * Real.log s)).mp hj
    nlinarith
  have hN : (dyadicMomentOrder j : ℝ) = 8 * ((j : ℝ) + 4) * (dyadicPrimeCount j : ℝ) := by
    simp [dyadicMomentOrder]
  calc
    _ ≤ Real.exp ((dyadicMomentOrder j : ℝ) * Real.log s) := by
      apply Real.exp_le_exp.mpr
      rw [hN]
      exact (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)).trans_eq (by ring)
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < s)]

/-- The whole many-prime integer contribution retains the full count
saving. Its only additional cost is an explicitly subexponential Euler
mass, independent of the selected finite subband and the height. -/
theorem norm_normalized_many_dyadic_le (D : Finset ℕ) (P : Polynomial ℂ) (j : ℕ) (y : ℝ)
    {L u U q : ℝ} (hL : 0 < L) (hu : 0 ≤ u) (huU : u ≤ U)
    (hq : 0 < q) (hqhalf : q < 1 / 2)
    (hD : ∀ n ∈ D, Squarefree n) (hband : D ⊆ zetaPrimeLogBand (dyadicMomentOrder j))
    (hK : ∀ n ∈ D, dyadicPrimeCount j ≤ n.primeFactors.card) :
    ‖(u : ℂ) ^ (dyadicMomentOrder j + 1) * ∑ n ∈ D,
      SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P (dyadicMomentOrder j) (3 / 2 + Complex.I * y) n‖ ≤
      (32 * U * Real.log 2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ((dyadicMomentOrder j : ℝ) * (16 * U / (17 * q)) ^ dyadicMomentOrder j) *
          Real.exp (2 * (dyadicPrimeCount j : ℝ) * countMass (3 / 2 - q)) := by
  have hr : (1 : ℝ) ≤ dyadicPrimeCount j := by
    exact_mod_cast (show 1 ≤ dyadicPrimeCount j by have := four_le_dyadicPrimeCount j; omega)
  have hU := hu.trans huU
  have hF : 0 ≤ ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k := Finset.sum_nonneg fun _ _ => by positivity
  apply (norm_normalized_many_sum_le D P (dyadicMomentOrder j) y hL hu huU hq hqhalf hr hD hband hK).trans
  calc
    _ ≤ (32 * U * Real.log 2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ((dyadicMomentOrder j : ℝ) * (U / q) ^ dyadicMomentOrder j) *
          Real.exp (2 * (dyadicPrimeCount j : ℝ) * countMass (3 / 2 - q)) /
            (17 / 16 : ℝ) ^ dyadicMomentOrder j :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (dyadic_count_power_saving j)
    _ = _ := by
      have he : 16 * U / (17 * q) = (U / q) / (17 / 16) := by field_simp
      rw [he]
      simp only [div_pow, inv_pow, mul_comm]
      ring

/-- Every changing high-count squarefree subband has a complete
vanishing source-normalized response. All frequencies are covered, and
the radius, height and positive physical length may move arbitrarily.
This pays a genuine integer class without using a zero hypothesis. -/
theorem tendsto_normalized_many_sum (P : Polynomial ℂ) (D : ℕ → Finset ℕ)
    (u y L : ℕ → ℝ) {U : ℝ} (hu : ∀ j, 0 ≤ u j) (huU : ∀ j, u j ≤ U)
    (hU : 0 < U) (hU1 : U < 17 / 32) (hL : ∀ j, 0 < L j)
    (hD : ∀ j, ∀ n ∈ D j, Squarefree n)
    (hband : ∀ j, D j ⊆ zetaPrimeLogBand (dyadicMomentOrder j))
    (hK : ∀ j, ∀ n ∈ D j, dyadicPrimeCount j ≤ n.primeFactors.card) :
    Tendsto (fun j => (u j : ℂ) ^ (dyadicMomentOrder j + 1) * ∑ n ∈ D j,
      SquarefreeVaughanLogSource.coefficient (L j) n *
        zetaPrimeFilterKernel P (dyadicMomentOrder j) (3 / 2 + Complex.I * y j) n)
      atTop (𝓝 0) := by
  obtain ⟨q, hq, hqhalf, hrate⟩ := exists_many_prime_tilt hU hU1
  let R : ℝ := 16 * U / (17 * q)
  let C : ℝ := 32 * U * Real.log 2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R < 1 := (div_lt_one (by positivity)).mpr hrate
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  let s : ℝ := (1 + R) / (2 * R)
  have hs : 1 < s := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * R)).mpr
    linarith
  have hRs : R * s = (1 + R) / 2 := by dsimp [s]; field_simp
  have hRs0 : 0 < R * s := mul_pos hR (by linarith)
  have hRs1 : R * s < 1 := by rw [hRs]; linarith
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 hRs0 hRs1).comp
    tendsto_dyadicMomentOrder
  have hl : Tendsto (fun j => C * (((dyadicMomentOrder j : ℝ) + 1) *
      (R * s) ^ dyadicMomentOrder j)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, pow_one, mul_zero] using ht.const_mul C
  apply squeeze_zero_norm' (a := fun j => C * (((dyadicMomentOrder j : ℝ) + 1) *
    (R * s) ^ dyadicMomentOrder j)) _ hl
  filter_upwards [eventually_exp_count_le_geometric (2 * countMass (3 / 2 - q)) hs] with j hj
  have hb := norm_normalized_many_dyadic_le (D j) P j (y j) (hL j) (hu j) (huU j)
    hq hqhalf (hD j) (hband j) (hK j)
  have he : Real.exp (2 * (dyadicPrimeCount j : ℝ) * countMass (3 / 2 - q)) ≤
      s ^ dyadicMomentOrder j := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hj
  apply hb.trans
  calc
    _ ≤ C * ((dyadicMomentOrder j : ℝ) * R ^ dyadicMomentOrder j) * s ^ dyadicMomentOrder j :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = C * ((dyadicMomentOrder j : ℝ) * (R * s) ^ dyadicMomentOrder j) := by rw [mul_pow]; ring
    _ ≤ _ := by gcongr; linarith

/-- The central support retains its entire chain of earlier original-band
restrictions, at every radius and order. -/
theorem centralUnpairedBand_subset_original (u : ℝ) (N : ℕ) :
    ZetaRieszCentralPrimeLayers.centralUnpairedBand u N ⊆ zetaPrimeLogBand N := by
  intro n hn
  exact ZetaRieszSemiprimeSupport.adaptiveBand_subset u N
    (ZetaRieszSemiprimeDeletion.residualBand_subset u N
      (ZetaRieszNarrowCarrier.residualBand_subset u N
        (ZetaRieszFourExtremeDeletion.fourResidualBand_subset u N
          (ZetaRieszLowerDegreeDeletion.degreeResidualBand_subset u N
            (ZetaRieszPhysicalAnnulus.annulusBand_subset u N
              (ZetaRieszCentralPrimeLayers.centralUnpairedBand_subset_annulus u N hn))))))

/-- The actual many-prime integer class, with every old support mask and
its squarefree arithmetic condition retained. -/
def manyPrimeBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
    (fun n => Squarefree n ∧ K ≤ n.primeFactors.card)

/-- The complete original arithmetic response of the many-prime class.
It contains all frequencies and every original factorial-filter shift. -/
def manyPrimeResponse (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ manyPrimeBand u N K, SquarefreeVaughanLogSource.coefficient
    (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The complete actual many-prime integer response independently vanishes
at source scale. This removes its complementary frequencies as well as
the previously bounded low-frequency sector. -/
theorem tendsto_manyPrimeResponse_moving (P : Polynomial ℂ) (u y : ℕ → ℝ)
    {U : ℝ} (hu : ∀ j, 0 ≤ u j) (huU : ∀ j, u j ≤ U)
    (hU : 0 < U) (hU1 : U < 17 / 32) :
    Tendsto (fun j => (u j : ℂ) ^ (dyadicMomentOrder j + 1) *
      manyPrimeResponse P (u j) (y j) (dyadicMomentOrder j) (dyadicPrimeCount j)) atTop (𝓝 0) := by
  exact tendsto_normalized_many_sum P
    (fun j => manyPrimeBand (u j) (dyadicMomentOrder j) (dyadicPrimeCount j)) u y
    (fun j => SquarefreeVaughanLogSource.length (u j) (dyadicMomentOrder j)) hu huU hU hU1
    (fun _ => SquarefreeVaughanLogSource.length_pos _ _)
    (fun _ _ hn => (Finset.mem_filter.mp hn).2.1)
    (fun j _ hn => centralUnpairedBand_subset_original (u j) (dyadicMomentOrder j) (Finset.mem_filter.mp hn).1)
    (fun _ _ hn => (Finset.mem_filter.mp hn).2.2)

/-- The full many-prime sum is exactly the previously retained signed
frequency integral; the squarefree mask is the same on both sides. -/
theorem manyPrimeResponse_eq_integral (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) :
    manyPrimeResponse P u y N K = (1 / (2 * (Real.pi : ℂ))) *
      ∫ xi : ℝ in Set.Ioi 0, manyPrimeFrequency P u y N K xi := by
  unfold manyPrimeResponse
  rw [ZetaRieszPrimeFourier.sum_original_eq_primePair_integral]
  have he : ZetaRieszPrimeFourier.bandPrimePair (manyPrimeBand u N K)
      (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
      (SquarefreeVaughanLogSource.length u N) = manyPrimeFrequency P u y N K := by
    funext xi
    simp only [manyPrimeBand, manyPrimeFrequency, ZetaRieszPrimeFourier.bandPrimePair]
    apply Finset.sum_congr _ (by intros; rfl)
    ext n
    simp only [Finset.mem_filter]
    tauto
  rw [he]

/-- Removing the full high-count integer class leaves exactly the lower
count frequency integral, without an unpaid high-frequency boundary. -/
theorem nonlinearResponse_sub_many_eq (P : Polynomial ℂ) (u y : ℝ) (N : ℕ)
    {K : ℕ} (hK : 4 ≤ K) :
    ZetaRieszCentralPrimeLayers.centralThreePrimeResponse P u y N +
      ZetaRieszCentralPrimeLayers.centralHigherPrimeResponse P u y N - manyPrimeResponse P u y N K =
        (1 / (2 * (Real.pi : ℂ))) * ∫ xi : ℝ in Set.Ioi 0, fewPrimeFrequency P u y N K xi := by
  obtain ⟨hf, hm⟩ := integrable_few_many_frequency P u y N K
  rw [ZetaRieszSignedFrequency.nonlinearResponse_eq_integral, manyPrimeResponse_eq_integral]
  have he : ZetaRieszSignedFrequency.nonlinearFrequency P u y N =
      fun xi => fewPrimeFrequency P u y N K xi + manyPrimeFrequency P u y N K xi :=
    funext (nonlinearFrequency_eq_few_add_many P u y N hK)
  rw [he, MeasureTheory.integral_add hf hm]
  ring

/-- The entire many-prime component is now independently paid. The source
survives in only the remaining lower-count signed integral and tapered wing,
with all exposure, multiplicity and original source-domain data retained. -/
theorem tendsto_few_add_wing_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun j : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (dyadicMomentOrder j + 1) *
      ((1 / (2 * (Real.pi : ℂ))) *
        (∫ xi : ℝ in Set.Ioi 0,
          fewPrimeFrequency 1 (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j) xi) +
        ZetaRieszCompletedCarrier.taperedWing (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder j)))
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hd := tendsto_manyPrimeResponse_moving 1
    (fun _ => 3 / 2 - rho.1.re) (fun _ => rho.1.im) (fun _ => hu.le) (fun _ => le_rfl)
    hu (huh.trans exp_neg_two_thirds_lt_many_prime_radius)
  have hs := (ZetaRieszCentralHarmonicCost.tendsto_three_unpaid_exact_source
    rho hrho hexposed huh).comp tendsto_dyadicMomentOrder
  have h := hs.sub hd
  simp only [Function.comp_apply, sub_zero] at h
  apply h.congr'
  filter_upwards [] with j
  have he := nonlinearResponse_sub_many_eq 1 (3 / 2 - rho.1.re) rho.1.im
    (dyadicMomentOrder j) (four_le_dyadicPrimeCount j)
  linear_combination (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (dyadicMomentOrder j + 1)) * he

end
end RiemannGaussian.ZetaRieszPrimeCountMass
