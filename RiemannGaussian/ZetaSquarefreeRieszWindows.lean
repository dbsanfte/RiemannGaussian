/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaArithmeticBandCorrelation

/-!
# Prime insertion and signed Riesz divisor windows

The actual two-prime Riesz coefficient is an exact signed moving-window
integral. Full cofactor and phase weights survive. Exact finite examples
rule out a generic unit floor for bare divisor coefficients; they do not
refute the floor for the actual source-normalized zeta filter.
-/

namespace RiemannGaussian.ZetaSquarefreeRieszWindows
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory Set Filter Topology
open ZetaArithmeticAffine
open ZetaArithmeticBandCorrelation

/-- Multiplication by any coprime factor acts as a complete signed family
of translations of the logarithmic cutoff, retaining all divisor weights. -/
theorem riesz_coprime_mul (L : ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    VaughanLogAverage.riesz L (m * n) =
      ∑ a ∈ m.divisors, ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
        VaughanLogAverage.riesz (L - Real.log a) n := by
  apply Complex.ofReal_injective
  simp only [VaughanLogAverage.riesz, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [sum_divisors_coprime_product hmn, Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  have hcop := (hmn.of_dvd_left (Nat.dvd_of_mem_divisors ha)).of_dvd_right
    (Nat.dvd_of_mem_divisors he)
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors ha).ne'
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors he).ne'
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    Nat.cast_mul, Real.log_mul ha0 he0]
  have hshift : L - (Real.log a + Real.log e) = L - Real.log a - Real.log e := by ring
  rw [hshift]
  push_cast
  ring

/-- Inserting a new prime is exactly a first difference in logarithmic
cutoff. Multiplication of integers and cutoff translation stay coupled. -/
theorem riesz_prime_mul (L : ℝ) {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    VaughanLogAverage.riesz L (p * n) = VaughanLogAverage.riesz L n -
      VaughanLogAverage.riesz (L - Real.log p) n := by
  rw [riesz_coprime_mul L (hp.coprime_iff_not_dvd.mpr hpn), hp.sum_divisors]
  simp [ArithmeticFunction.moebius_apply_prime hp, sub_eq_add_neg]
  ring

/-- Two prime insertions retain the complete mixed cutoff difference of
the Riesz pair. Its four terms must remain coupled in a correlation bound. -/
theorem riesz_prime_pair (L K : ℝ) {p q m n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpm : ¬ p ∣ m) (hqn : ¬ q ∣ n) :
    VaughanLogAverage.riesz L (p * m) * VaughanLogAverage.riesz K (q * n) =
      VaughanLogAverage.riesz L m * VaughanLogAverage.riesz K n -
      VaughanLogAverage.riesz (L - Real.log p) m * VaughanLogAverage.riesz K n -
      VaughanLogAverage.riesz L m * VaughanLogAverage.riesz (K - Real.log q) n +
      VaughanLogAverage.riesz (L - Real.log p) m *
        VaughanLogAverage.riesz (K - Real.log q) n := by
  rw [riesz_prime_mul L hp hpm, riesz_prime_mul K hq hqn]
  ring

/-- The Riesz profile is Lipschitz in its cutoff, with its exact absolute
Mobius divisor mass as constant. -/
theorem riesz_cutoff_lipschitz (L K : ℝ) (n : ℕ) :
    |VaughanLogAverage.riesz L n - VaughanLogAverage.riesz K n| ≤
      |L - K| * ∑ a ∈ n.divisors, |((ArithmeticFunction.moebius a : ℤ) : ℝ)| := by
  unfold VaughanLogAverage.riesz
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [← mul_sub, abs_mul]
  have hmax : |max 0 (L - Real.log a) - max 0 (K - Real.log a)| ≤ |L - K| := by
    rw [max_comm 0 (L - Real.log a), max_comm 0 (K - Real.log a)]
    simpa only [sub_sub_sub_cancel_right] using
      abs_max_sub_max_le_abs (L - Real.log a) (K - Real.log a) 0
  exact (mul_le_mul_of_nonneg_left hmax (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- Cancelling the two prime fibres before taking absolute values removes
the full cutoff length: the cost is log p times the cofactor divisor mass. -/
theorem abs_riesz_prime_mul_le (L : ℝ) {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    |VaughanLogAverage.riesz L (p * n)| ≤
      Real.log p * ∑ a ∈ n.divisors, |((ArithmeticFunction.moebius a : ℤ) : ℝ)| := by
  rw [riesz_prime_mul L hp hpn]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  simpa only [sub_sub_cancel, abs_of_nonneg hlog] using
    riesz_cutoff_lipschitz L (L - Real.log p) n

/-- The prime-fibre gain applies directly to the literal original band
weight, with its full amplitude and filter norm explicitly retained. -/
theorem norm_bandWeight_prime_le (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P N t (p * n)‖ ≤
      ‖bandAmplitude L P N t (p * n)‖ *
        (Real.log p * ∑ a ∈ n.divisors, |((ArithmeticFunction.moebius a : ℤ) : ℝ)|) := by
  rw [bandWeight_eq_amplitude_mul_riesz, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_riesz_prime_mul_le L hp hpn) (norm_nonneg _)

/-- Both prime fibres can be cancelled before bounding the Riesz pair,
giving a cutoff-independent product of prime-logarithm costs. -/
theorem abs_riesz_prime_pair_le (L K : ℝ) {p q m n : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpm : ¬ p ∣ m) (hqn : ¬ q ∣ n) :
    |VaughanLogAverage.riesz L (p * m) * VaughanLogAverage.riesz K (q * n)| ≤
      (Real.log p * ∑ a ∈ m.divisors, |((ArithmeticFunction.moebius a : ℤ) : ℝ)|) *
      (Real.log q * ∑ a ∈ n.divisors, |((ArithmeticFunction.moebius a : ℤ) : ℝ)|) := by
  rw [abs_mul]
  exact mul_le_mul (abs_riesz_prime_mul_le L hp hpm) (abs_riesz_prime_mul_le K hq hqn)
    (abs_nonneg _) (le_trans (abs_nonneg _) (abs_riesz_prime_mul_le L hp hpm))

/-- A whole band of nearby lags is frozen together, retaining cross-lag
signs in one main term instead of estimating each lag separately. -/
theorem norm_bandPairSum_near_lags_freeze_le (S : Finset (ℕ × ℕ)) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (t b d H M : ℝ) (hb : 0 < b) (hd : 0 < d)
    (hM : 0 < M) (hS : ∀ z ∈ S,
      0 < z.1 ∧ 0 < z.2 ∧ M ≤ b * z.1 ∧ M ≤ d * z.2 ∧ |b * z.1 - d * z.2| ≤ H) :
    ‖bandPairSum S L P N t - unitPhase (-t * Real.log (d / b)) *
        bandPairSum S L P N 0‖ ≤
      (|t| * (H / M)) * ∑ z ∈ S,
        ‖ZetaRieszConditionedEnergy.bandWeight L P N 0 z.1‖ *
          ‖ZetaRieszConditionedEnergy.bandWeight L P N 0 z.2‖ := by
  apply norm_bandPairSum_freeze_le
  intro z hz
  obtain ⟨hx, hy, hMx, hMy, he⟩ := hS z hz
  exact (abs_log_ratio_deviation hb hd (by exact_mod_cast hx) (by exact_mod_cast hy)
    hM hMx hMy rfl).trans (div_le_div_of_nonneg_right he hM.le)

/-- The four divisor contributions from two distinct inserted primes.
The logarithms of those primes are the two translation lengths. -/
def primePairTent (a b u : ℝ) : ℝ :=
  max 0 u - max 0 (u - a) - max 0 (u - b) + max 0 (u - a - b)

/-- After exact four-term cancellation, the kernel is nonnegative and
costs at most the smaller of the two prime logarithms. -/
theorem primePairTent_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (u : ℝ) :
    0 ≤ primePairTent a b u ∧ primePairTent a b u ≤ min a b := by
  simp only [primePairTent, max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- Both complete affine tails vanish, including their exact endpoints. -/
theorem primePairTent_eq_zero_of_outside {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : u ≤ 0 ∨ a + b ≤ u) : primePairTent a b u = 0 := by
  rcases hu with hu | hu
  · simp only [primePairTent, max_eq_left hu,
      max_eq_left (by linarith : u - a ≤ 0),
      max_eq_left (by linarith : u - b ≤ 0),
      max_eq_left (by linarith : u - a - b ≤ 0)]
    ring
  · simp only [primePairTent, max_eq_right (by linarith : 0 ≤ u),
      max_eq_right (by linarith : 0 ≤ u - a),
      max_eq_right (by linarith : 0 ≤ u - b),
      max_eq_right (by linarith : 0 ≤ u - a - b)]
    ring

/-- The tent is exactly the overlap length of two intervals. This
description will retain signed divisor sums inside an integral. -/
theorem primePairTent_eq_overlap {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (u : ℝ) :
    primePairTent a b u = max (min u a - max (u - b) 0) 0 := by
  simp only [primePairTent, max_def, min_def]
  split_ifs <;> linarith

/-- Inserting two distinct primes into the same integer leaves one
compactly supported kernel per cofactor divisor, with its sign intact. -/
theorem riesz_two_primes_eq_tent (L : ℝ) {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpm : ¬ p ∣ m) (hqm : ¬ q ∣ m) :
    VaughanLogAverage.riesz L (p * (q * m)) =
      ∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        primePairTent (Real.log p) (Real.log q) (L - Real.log d) := by
  have hpqm : ¬ p ∣ q * m := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hpq ((Nat.dvd_prime_two_le hq hp.two_le).mp h)
    · exact hpm h
  rw [riesz_prime_mul L hp hpqm, riesz_prime_mul L hq hqm,
    riesz_prime_mul (L - Real.log p) hq hqm]
  simp only [VaughanLogAverage.riesz, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  have hqshift : L - Real.log q - Real.log d = L - Real.log d - Real.log q := by ring
  have hpshift : L - Real.log p - Real.log d = L - Real.log d - Real.log p := by ring
  have hpqshift : L - Real.log p - Real.log q - Real.log d =
      L - Real.log d - Real.log p - Real.log q := by ring
  rw [hqshift, hpshift, hpqshift]
  unfold primePairTent
  ring

/-- The absolute cost is confined to a strict logarithmic boundary
window. Divisors outside it cancel before any absolute value is taken. -/
theorem abs_sum_primePairTent_le {ι : Type*} (S : Finset ι) (c x : ι → ℝ)
    (L : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |∑ i ∈ S, c i * primePairTent a b (L - x i)| ≤
      min a b * ∑ i ∈ S.filter (fun i => L - a - b < x i ∧ x i < L), |c i| := by
  have he : (∑ i ∈ S, c i * primePairTent a b (L - x i)) =
      ∑ i ∈ S.filter (fun i => L - a - b < x i ∧ x i < L),
        c i * primePairTent a b (L - x i) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : L - a - b < x i ∧ x i < L
    · simp only [if_pos hi]
    · rw [if_neg hi, primePairTent_eq_zero_of_outside ha hb, mul_zero]
      by_cases hx : x i < L
      · right
        have hn : ¬ L - a - b < x i := fun h => hi ⟨h, hx⟩
        linarith [le_of_not_gt hn]
      · left
        linarith [le_of_not_gt hx]
  rw [he, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul, abs_of_nonneg (primePairTent_bounds ha hb _).1]
  exact (mul_le_mul_of_nonneg_left (primePairTent_bounds ha hb _).2
    (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- Two prime factors replace the total cofactor divisor mass by the
mass in the one window where their affine cancellation is incomplete. -/
theorem abs_riesz_two_primes_boundary_le (L : ℝ) {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpm : ¬ p ∣ m) (hqm : ¬ q ∣ m) :
    |VaughanLogAverage.riesz L (p * (q * m))| ≤
      min (Real.log p) (Real.log q) *
        ∑ d ∈ m.divisors.filter (fun d : ℕ =>
          L - Real.log p - Real.log q < Real.log d ∧ Real.log d < L),
          |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  rw [riesz_two_primes_eq_tent L hp hq hpq hpm hqm]
  exact abs_sum_primePairTent_le _ _ _ L
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q)

/-- The four-term tent is the exact integral of an interval indicator.
Strict endpoints have zero measure and no endpoint term is discarded. -/
theorem integral_primePairWindow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (u c : ℝ) :
    (∫ s in Ioo 0 a, if u - b < s ∧ s < u then c else 0) =
      c * primePairTent a b u := by
  have he : (fun s : ℝ => if u - b < s ∧ s < u then c else 0) =
      (Ioo (u - b) u).indicator (fun _ => c) := by
    funext s
    simp only [indicator_apply, mem_Ioo]
  rw [he, integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    Ioo_inter_Ioo, setIntegral_const, Real.volume_real_Ioo,
    primePairTent_eq_overlap ha hb, smul_eq_mul]
  ring

/-- Every signed finite coefficient family has the same moving-window
representation. No multiplicativity or randomness assumption is needed. -/
theorem sum_primePairTent_eq_window_integral {ι : Type*} (S : Finset ι)
    (c x : ι → ℝ) (L : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∑ i ∈ S, c i * primePairTent a b (L - x i)) =
      ∫ s in Ioo 0 a, ∑ i ∈ S,
        if L - s - b < x i ∧ x i < L - s then c i else 0 := by
  have he (i : ι) (s : ℝ) :
      (L - s - b < x i ∧ x i < L - s) ↔
        (L - x i - b < s ∧ s < L - x i) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp_rw [he]
  have hi (i : ι) :
      IntegrableOn (fun s => if L - x i - b < s ∧ s < L - x i then c i else 0)
        (Ioo 0 a) := by
    have hei : (fun s : ℝ => if L - x i - b < s ∧ s < L - x i then c i else 0) =
        (Ioo (L - x i - b) (L - x i)).indicator (fun _ => c i) := by
      funext s
      simp only [indicator_apply, mem_Ioo]
    rw [hei]
    exact
      (integrableOn_const (μ := volume) (s := Ioo 0 a) (C := c i) (hs := by simp)).indicator
        (t := Ioo (L - x i - b) (L - x i)) measurableSet_Ioo
  rw [integral_finsetSum S (fun i _ => hi i)]
  exact Finset.sum_congr rfl (fun i _ => (integral_primePairWindow ha hb _ _).symm)

/-- A bound for the signed moving-window sums, rather than their total
variation, suffices. All signs remain coupled until after integration. -/
theorem abs_sum_primePairTent_le_of_window_bound {ι : Type*} (S : Finset ι)
    (c x : ι → ℝ) (L : ℝ) {a b B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ s ∈ Ioo 0 a,
      |∑ i ∈ S, if L - s - b < x i ∧ x i < L - s then c i else 0| ≤ B) :
    |∑ i ∈ S, c i * primePairTent a b (L - x i)| ≤ a * B := by
  rw [sum_primePairTent_eq_window_integral S c x L ha hb]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (by simp : volume (Ioo 0 a) < ⊤)
    (fun s hs => show ‖∑ i ∈ S,
      if L - s - b < x i ∧ x i < L - s then c i else 0‖ ≤ B from
        (Real.norm_eq_abs _).trans_le (hB s hs))
  simpa only [Real.norm_eq_abs, Real.volume_real_Ioo, sub_zero, max_eq_left ha,
    mul_comm B a] using h

/-- The remaining arithmetic statistic counts positive and negative
Mobius divisors together in one open logarithmic window. -/
def signedDivisorWindow (b v : ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors,
    if v - b < Real.log d ∧ Real.log d < v then
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0

/-- An exact signed window average of the actual Riesz factor. The
window width is log q and its displacement ranges over log p. -/
theorem riesz_two_primes_eq_window_integral (L : ℝ) {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpm : ¬ p ∣ m) (hqm : ¬ q ∣ m) :
    VaughanLogAverage.riesz L (p * (q * m)) =
      ∫ s in Ioo 0 (Real.log p), signedDivisorWindow (Real.log q) (L - s) m := by
  rw [riesz_two_primes_eq_tent L hp hq hpq hpm hqm]
  exact sum_primePairTent_eq_window_integral _ _ _ L
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q)

/-- Signed divisor discrepancy on just these local windows controls
the Riesz factor without paying the absolute mass of every divisor. -/
theorem abs_riesz_two_primes_le_of_window_bound (L : ℝ) {p q m : ℕ} {B : ℝ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpm : ¬ p ∣ m) (hqm : ¬ q ∣ m)
    (hB : ∀ s ∈ Ioo 0 (Real.log p), |signedDivisorWindow (Real.log q) (L - s) m| ≤ B) :
    |VaughanLogAverage.riesz L (p * (q * m))| ≤ Real.log p * B := by
  rw [riesz_two_primes_eq_tent L hp hq hpq hpm hqm]
  exact abs_sum_primePairTent_le_of_window_bound _ _ _ L
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q) hB

/-- The same overlap identity retains an arbitrary complex amplitude. -/
theorem integral_primePairWindow_complex {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : ℝ) (c : ℂ) :
    (∫ s in Ioo 0 a, if u - b < s ∧ s < u then c else 0) =
      c * (primePairTent a b u : ℂ) := by
  have he : (fun s : ℝ => if u - b < s ∧ s < u then c else 0) =
      (Ioo (u - b) u).indicator (fun _ => c) := by
    funext s
    simp only [indicator_apply, mem_Ioo]
  rw [he, integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    Ioo_inter_Ioo, setIntegral_const, Real.volume_real_Ioo, primePairTent_eq_overlap ha hb]
  simp only [Complex.real_smul, mul_comm]

/-- The moving-window identity keeps every phase for arbitrary finite
complex coefficients, before taking any norm or splitting any family. -/
theorem sum_primePairTent_complex_eq_window_integral {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (x : ι → ℝ) (L : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∑ i ∈ S, c i * (primePairTent a b (L - x i) : ℂ)) =
      ∫ s in Ioo 0 a, ∑ i ∈ S,
        if L - s - b < x i ∧ x i < L - s then c i else 0 := by
  have he (i : ι) (s : ℝ) :
      (L - s - b < x i ∧ x i < L - s) ↔
        (L - x i - b < s ∧ s < L - x i) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp_rw [he]
  have hi (i : ι) :
      IntegrableOn (fun s => if L - x i - b < s ∧ s < L - x i then c i else 0)
        (Ioo 0 a) := by
    have hei : (fun s : ℝ => if L - x i - b < s ∧ s < L - x i then c i else 0) =
        (Ioo (L - x i - b) (L - x i)).indicator (fun _ => c i) := by
      funext s
      simp only [indicator_apply, mem_Ioo]
    rw [hei]
    exact
      (integrableOn_const (μ := volume) (s := Ioo 0 a) (C := c i) (hs := by simp)).indicator
        (t := Ioo (L - x i - b) (L - x i)) measurableSet_Ioo
  rw [integral_finsetSum S (fun i _ => hi i)]
  exact Finset.sum_congr rfl (fun i _ => (integral_primePairWindow_complex ha hb _ _).symm)

/-- A whole original band with a fixed prime pair is one signed complex
window integral. Its cofactor sums and filter amplitudes stay inside it. -/
theorem sum_bandWeight_two_primes_eq_window_integral (S : Finset ℕ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (t : ℝ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hS : ∀ m ∈ S, ¬ p ∣ m ∧ ¬ q ∣ m) :
    (∑ m ∈ S, ZetaRieszConditionedEnergy.bandWeight L P N t (p * (q * m))) =
      ∫ s in Ioo 0 (Real.log p), ∑ m ∈ S, bandAmplitude L P N t (p * (q * m)) *
        (signedDivisorWindow (Real.log q) (L - s) m : ℂ) := by
  have he : (∑ m ∈ S, ZetaRieszConditionedEnergy.bandWeight L P N t (p * (q * m))) =
      ∑ z ∈ S.sigma (fun m => m.divisors),
        (bandAmplitude L P N t (p * (q * z.1)) *
          (((ArithmeticFunction.moebius z.2 : ℤ) : ℝ) : ℂ)) *
          (primePairTent (Real.log p) (Real.log q) (L - Real.log z.2) : ℂ) := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro m hm
    rw [bandWeight_eq_amplitude_mul_riesz,
      riesz_two_primes_eq_tent L hp hq hpq (hS m hm).1 (hS m hm).2]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]
  rw [he, sum_primePairTent_complex_eq_window_integral _ _ _ L
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q)]
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [Finset.sum_sigma, signedDivisorWindow, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

/-- A uniform bound for the coupled window aggregate controls the
entire fixed-prime band. No absolute sum over cofactors is required. -/
theorem norm_sum_bandWeight_two_primes_le_of_window_bound (S : Finset ℕ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (t : ℝ) {p q : ℕ} {B : ℝ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hS : ∀ m ∈ S, ¬ p ∣ m ∧ ¬ q ∣ m)
    (hB : ∀ s ∈ Ioo 0 (Real.log p),
      ‖∑ m ∈ S, bandAmplitude L P N t (p * (q * m)) *
        (signedDivisorWindow (Real.log q) (L - s) m : ℂ)‖ ≤ B) :
    ‖∑ m ∈ S, ZetaRieszConditionedEnergy.bandWeight L P N t (p * (q * m))‖ ≤
      Real.log p * B := by
  rw [sum_bandWeight_two_primes_eq_window_integral S L P N t hp hq hpq hS]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (by simp : volume (Ioo 0 (Real.log p)) < ⊤) hB
  simpa only [Real.volume_real_Ioo, sub_zero, max_eq_left (Real.log_natCast_nonneg p),
    mul_comm B (Real.log p)] using h

/-- The boundary-window cost also transports pointwise to the original
band, with every support restriction and complex filter kept fixed. -/
theorem norm_bandWeight_two_primes_boundary_le (L : ℝ) (P : Polynomial ℂ) (N : ℕ)
    (t : ℝ) {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpm : ¬ p ∣ m) (hqm : ¬ q ∣ m) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P N t (p * (q * m))‖ ≤
      ‖bandAmplitude L P N t (p * (q * m))‖ *
        (min (Real.log p) (Real.log q) *
          ∑ d ∈ m.divisors.filter (fun d : ℕ =>
            L - Real.log p - Real.log q < Real.log d ∧ Real.log d < L),
            |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) := by
  rw [bandWeight_eq_amplitude_mul_riesz, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_riesz_two_primes_boundary_le L hp hq hpq hpm hqm)
    (norm_nonneg _)

/-- The positive unit divisor still survives on genuinely rough
windows. A uniform subunit pointwise discrepancy claim would be false. -/
theorem signedDivisorWindow_eq_one_of_rough {b v : ℝ} (hv : 0 < v) (hvb : v < b)
    {m : ℕ} (hm : 0 < m)
    (hrough : ∀ d ∈ m.divisors, d ≠ 1 → v ≤ Real.log d) :
    signedDivisorWindow b v m = 1 := by
  rw [signedDivisorWindow, Finset.sum_eq_single 1]
  · simp [sub_neg.mpr hvb, hv]
  · intro d hd hd1
    simp only [not_lt.mpr (hrough d hd hd1), and_false, if_false]
  · exact fun h => False.elim (h (Nat.mem_divisors.mpr ⟨one_dvd m, hm.ne'⟩))

/-- At logarithms of positive integers, the window membership test is
entirely arithmetic: no numerical logarithm comparison is needed. -/
theorem signedDivisorWindow_log_nat {Q V : ℕ} (hQ : 0 < Q) (hV : 0 < V) (m : ℕ) :
    signedDivisorWindow (Real.log Q) (Real.log V) m =
      ∑ d ∈ m.divisors, if V < Q * d ∧ d < V then
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
  unfold signedDivisorWindow
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hVR : (0 : ℝ) < V := by exact_mod_cast hV
  have he : Real.log V - Real.log Q < Real.log d ↔ V < Q * d := by
    rw [sub_lt_iff_lt_add, add_comm (Real.log d) (Real.log Q),
      ← Real.log_mul hQR.ne' hdR.ne', Real.log_lt_log_iff hVR (mul_pos hQR hdR)]
    exact_mod_cast (Iff.rfl : V < Q * d ↔ V < Q * d)
  simp only [he, Real.log_lt_log_iff hdR hVR, Nat.cast_lt]

/-- Three cofactor primes in the same window reinforce one another.
This rules out a universal unit bound even with p=2, q=3 and coprime cofactor. -/
theorem signedDivisorWindow_three_prime_cluster :
    signedDivisorWindow (Real.log 3) (Real.log 12) 385 = -3 := by
  have hw := signedDivisorWindow_log_nat (Q := 3) (V := 12) (by decide) (by decide) 385
  norm_num only [Nat.cast_ofNat] at hw
  rw [hw]
  have he : (∑ d ∈ Nat.divisors 385,
      if 12 < 3 * d ∧ d < 12 then (ArithmeticFunction.moebius d : ℤ) else 0) = -3 := by
    decide +kernel
  exact_mod_cast he

/-- At any positive real cutoff, the signed Riesz mean is the logarithm
of its exact finite multiplicative ratio. No numerical log approximation
is required when the cutoff is rational. -/
theorem riesz_log_eq_log_prod {X : ℝ} (hX : 0 < X) (n : ℕ) :
    VaughanLogAverage.riesz (Real.log X) n =
      Real.log (∏ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) < X),
        (X / (d : ℝ)) ^ (ArithmeticFunction.moebius d : ℤ)) := by
  rw [Real.log_prod (fun d hd =>
    zpow_ne_zero _ (div_ne_zero hX.ne'
      (by exact_mod_cast (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1).ne')))]
  rw [Finset.sum_filter, VaughanLogAverage.riesz]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  by_cases hdX : (d : ℝ) < X
  · rw [if_pos hdX, Real.log_zpow, Real.log_div hX.ne' hdR.ne',
      max_eq_right (sub_nonneg.mpr (Real.log_le_log hdR hdX.le))]
  · rw [if_neg hdX,
      max_eq_left (sub_nonpos.mpr (Real.log_le_log hX (le_of_not_gt hdX))), mul_zero]

/-- The integrated three-prime cluster is an exact rational logarithm;
averaging over every window does not force a unit-size bound. -/
theorem riesz_integrated_prime_cluster :
    VaughanLogAverage.riesz (Real.log 12) 2310 = Real.log (77 / 288 : ℝ) := by
  rw [riesz_log_eq_log_prod (by norm_num : (0 : ℝ) < 12)]
  have he : (∏ d ∈ (Nat.divisors 2310).filter (fun d => d < 12),
      ((12 : ℚ) / d) ^ (ArithmeticFunction.moebius d : ℤ)) = 77 / 288 := by
    decide +kernel
  have hf : (Nat.divisors 2310).filter (fun d : ℕ => (d : ℝ) < 12) =
      (Nat.divisors 2310).filter (fun d => d < 12) := by
    ext d
    simp only [Finset.mem_filter]
    norm_cast
  rw [hf]
  congr 1
  have her := congrArg (fun q : ℚ => (q : ℝ)) he
  push_cast at her
  exact her

/-- Even the signed integral, not just its pointwise maximum, can be
less than minus one on a squarefree admissible prime-pair cofactor. -/
theorem riesz_integrated_prime_cluster_lt_neg_one :
    VaughanLogAverage.riesz (Real.log 12) 2310 < -1 := by
  rw [riesz_integrated_prime_cluster]
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 77 / 288)
    (by norm_num : (77 / 288 : ℝ) < (2 / 3) ^ 3)
  rw [Real.log_pow] at h
  have hb := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2 / 3)
  norm_num at h hb
  linarith

/-- The literal moving-window integral exhibits the same obstruction,
with p=2, q=3 and m=385 avoiding both primes. -/
theorem signedWindow_integral_cluster_lt_neg_one :
    (∫ s in Ioo 0 (Real.log 2), signedDivisorWindow (Real.log 3) (Real.log 12 - s) 385) <
      -1 := by
  have he := riesz_two_primes_eq_window_integral (Real.log 12)
    (p := 2) (q := 3) (m := 385) (by decide) (by decide) (by decide) (by decide) (by decide)
  norm_num only [Nat.cast_ofNat, Nat.reduceMul] at he
  rw [← he]
  exact riesz_integrated_prime_cluster_lt_neg_one

end
end RiemannGaussian.ZetaSquarefreeRieszWindows
