import RiemannGaussian.EtaGammaQuadraticExpansion
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The full reduced gamma quadratic above the square-root gcd scale

The complete cofactor row is kept inside each coprime reduced block.
When `g^2 >= 2*A`, geometric summation bounds that whole block uniformly
by `64 norm(chi) g^(-2 Re(rho))`. No bound for its reduced arithmetic
core is assumed. The remaining small-gcd core still needs cancellation.
-/

open Complex Filter MeasureTheory Set RiemannGaussian RiemannGaussian.EtaGammaSmoothing
open RiemannGaussian.EtaGammaQuadratic
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaGcd

noncomputable section

private theorem norm_carrier_large (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {n : ℕ} (hn : 1 ≤ n) (hAn : 2 * A ≤ n) :
    ‖gammaCarrier rho A n‖ ≤ 8 * ‖pairedEtaXiCompletionFactor rho.1‖ *
      (n : ℝ) ^ (-rho.1.re) * Real.exp (-(n : ℝ) / (2 * A)) := by
  rw [gammaCarrier, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  have hg := norm_gammaDampedEta_le_exp_half (NontrivialZetaZero.zero_lt_re rho)
    ((le_div_iff₀ hA).mpr hAn)
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq
  rw [show -((n : ℝ) / A) / 2 = -(n : ℝ) / (2 * A) by ring]
  ring

private theorem inv_exp_sub_one_le {x : ℝ} (hx : 1 ≤ x) :
    1 / (Real.exp x - 1) ≤ 2 * Real.exp (-x) := by
  have hE : 2 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hb : 1 / (Real.exp x - 1) ≤ 2 / Real.exp x :=
    (div_le_div_iff₀ (by linarith : 0 < Real.exp x - 1) (Real.exp_pos x)).mpr (by linarith)
  simpa only [Real.exp_neg, div_eq_mul_inv] using hb

/-- The complete row has a geometric bound with its actual complex-power decay retained. -/
theorem norm_gammaRow_large_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {m : ℕ} (hm : 1 ≤ m) (hAm : 2 * A ≤ m) :
    ‖gammaRow rho A m‖ ≤ 16 * ‖pairedEtaXiCompletionFactor rho.1‖ *
      (m : ℝ) ^ (-rho.1.re) * Real.exp (-(m : ℝ) / (2 * A)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx : 0 < (m : ℝ) / (2 * A) := by positivity
  have hb := (hasSum_exp_nat_tail hx 0).mul_left
    (8 * ‖pairedEtaXiCompletionFactor rho.1‖ * (m : ℝ) ^ (-rho.1.re))
  have hp (k : ℕ) : ‖gammaCarrier rho A (m * (k + 1))‖ ≤
      (8 * ‖pairedEtaXiCompletionFactor rho.1‖ * (m : ℝ) ^ (-rho.1.re)) *
        Real.exp (-((0 + k + 1 : ℕ) : ℝ) * ((m : ℝ) / (2 * A))) := by
    have hmn : m ≤ m * (k + 1) := Nat.le_mul_of_pos_right m (by omega)
    have hmnR : (m : ℝ) ≤ ((m * (k + 1) : ℕ) : ℝ) := by exact_mod_cast hmn
    apply (norm_carrier_large rho hA (hm.trans hmn) (hAm.trans hmnR)).trans
    have hpow := Real.rpow_le_rpow_of_nonpos hmR hmnR
      (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow
      (by positivity : 0 ≤ 8 * ‖pairedEtaXiCompletionFactor rho.1‖)) (Real.exp_pos _).le).trans_eq
    congr 2
    push_cast
    ring
  have hn := hb.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hp
  have ht := hn.of_norm.hasSum.norm_le_of_bounded hb hp
  change ‖gammaRow rho A m‖ ≤ _ at ht
  apply ht.trans
  simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero]
  have hx1 : 1 ≤ (m : ℝ) / (2 * A) := by
    exact (le_div_iff₀ (by positivity : 0 < 2 * A)).mpr (by simpa only [one_mul] using hAm)
  apply (mul_le_mul_of_nonneg_left (inv_exp_sub_one_le hx1) (by positivity :
    0 ≤ 8 * ‖pairedEtaXiCompletionFactor rho.1‖ * (m : ℝ) ^ (-rho.1.re))).trans_eq
  rw [neg_div]
  ring

private theorem sum_exp_half_le_two (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, Real.exp (-(n : ℝ) / 2)) ≤ 2 := by
  have hsum := hasSum_exp_nat_tail (by norm_num : (0 : ℝ) < 1 / 2) 0
  have he : (∑ n ∈ Finset.Icc 1 N, Real.exp (-(n : ℝ) / 2)) =
      ∑ k ∈ Finset.range N, Real.exp (-((0 + k + 1 : ℕ) : ℝ) * (1 / 2)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.zero_add, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ring
  rw [he]
  apply (hsum.summable.sum_le_tsum (Finset.range N) (fun _ _ ↦ (Real.exp_pos _).le)).trans
  rw [hsum.tsum_eq]
  norm_num only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero]
  have hE := Real.add_one_le_exp (1 / 2 : ℝ)
  exact (div_le_iff₀ (by linarith : 0 < Real.exp (1 / 2 : ℝ) - 1)).mpr (by linarith)

/-- The actual gcd block retains the divided cutoffs, coprimality, and all original Moebius factors. -/
def gcdBlock (rho : NontrivialZetaZero) (A : ℝ) (U g : ℕ) : ℂ :=
  -(∑ r ∈ Finset.Icc 1 (U / g), ∑ s ∈ Finset.Icc 1 (U / g),
    if r.Coprime s then (μ (g * r) : ℂ) * (μ (g * s) : ℂ) *
      gammaRow rho A (g ^ 2 * r * s) else 0)

/-- These are exactly the gcd blocks of the original smooth quadratic, with no omitted cofactor rows. -/
theorem smoothQuadratic_eq_sum_gcdBlock (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (U : ℕ) : smoothQuadratic rho A U = ∑ g ∈ Finset.Icc 1 U, gcdBlock rho A U g := by
  rw [smoothQuadratic_eq_sum_gammaRow rho hA, sum_square_eq_sum_gcd]
  have he (g r s : ℕ) : g * r * (g * s) = g ^ 2 * r * s := by ring
  simp only [gcdBlock, he, Finset.sum_neg_distrib]

/-- The signed reduced core retains the complete rows and all three coprimality relations. -/
def reducedGcdCore (rho : NontrivialZetaZero) (T : ℝ) (N g : ℕ) : ℂ :=
  -(∑ r ∈ Finset.Icc 1 N, ∑ s ∈ Finset.Icc 1 N,
    if r.Coprime s ∧ g.Coprime r ∧ g.Coprime s then
      (μ r : ℂ) * (μ s : ℂ) * gammaRow rho T (r * s) else 0)

/-- The actual gcd block exposes its exact complex power and squarefree weight before any norm estimate. -/
theorem gcdBlock_eq_factor_mul_reducedCore (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (U : ℕ) {g : ℕ} (hg : 1 ≤ g) :
    gcdBlock rho A U g =
      ((μ g : ℂ) ^ 2 * (g : ℂ) ^ (-2 * rho.1)) *
        reducedGcdCore rho (A / (g : ℝ) ^ 2) (U / g) g := by
  unfold gcdBlock reducedGcdCore
  rw [mul_neg]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [mul_assoc (g ^ 2), gammaRow_square_scale rho hA hg, moebius_common_factor]
  split_ifs <;> simp_all
  ring

private theorem norm_gcd_row_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {g : ℕ} (hg : 1 ≤ g) (hAg : 2 * A ≤ (g : ℝ) ^ 2)
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ‖(μ (g * r) : ℂ) * (μ (g * s) : ℂ) * gammaRow rho A (g ^ 2 * r * s)‖ ≤
      (16 * ‖pairedEtaXiCompletionFactor rho.1‖ * (g : ℝ) ^ (-2 * rho.1.re)) *
        (Real.exp (-(r : ℝ) / 2) * Real.exp (-(s : ℝ) / 2)) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hn : 1 ≤ g ^ 2 * r * s :=
    Nat.mul_pos (Nat.mul_pos (pow_pos (by omega : 0 < g) 2) (by omega)) (by omega)
  have hnR : (g : ℝ) ^ 2 ≤ ((g ^ 2 * r * s : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_nonneg (sq_nonneg (g : ℝ)) (show 0 ≤ (r : ℝ) * s - 1 by nlinarith)]
  have hp : (((g ^ 2 * r * s : ℕ) : ℝ)) ^ (-rho.1.re) ≤ (g : ℝ) ^ (-2 * rho.1.re) := by
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (g : ℝ) ^ 2) hnR
      (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)
    rw [← Real.rpow_natCast_mul hgR.le] at h
    simpa only [Nat.cast_ofNat, mul_neg, neg_mul] using h
  have he : Real.exp (-(((g ^ 2 * r * s : ℕ) : ℝ)) / (2 * A)) ≤
      Real.exp (-(r : ℝ) / 2) * Real.exp (-(s : ℝ) / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hprod : (r : ℝ) + s ≤ 2 * (r : ℝ) * s := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (sub_nonneg.mpr hsR)]
    have hbound : ((r : ℝ) + s) / 2 ≤ ((g ^ 2 * r * s : ℕ) : ℝ) / (2 * A) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * A)).mpr
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr hAg) (show 0 ≤ (r : ℝ) * s by positivity)]
    convert! neg_le_neg hbound using 1 <;> ring
  have hm (n : ℕ) : ‖(μ n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  rw [norm_mul, norm_mul]
  apply (mul_le_mul (mul_le_mul (hm _) (hm _) (norm_nonneg _) (by norm_num))
    (norm_gammaRow_large_le rho hA hn (hAg.trans hnR)) (norm_nonneg _) (by positivity)).trans
  simp only [one_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) he
    (Real.exp_pos _).le (by positivity)

/-- Above the square-root gcd scale the entire reduced coprime block has a uniform summable outer weight. -/
theorem norm_gcdBlock_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (U : ℕ) {g : ℕ} (hg : 1 ≤ g) (hAg : 2 * A ≤ (g : ℝ) ^ 2) :
    ‖gcdBlock rho A U g‖ ≤ 64 * ‖pairedEtaXiCompletionFactor rho.1‖ *
      (g : ℝ) ^ (-2 * rho.1.re) := by
  unfold gcdBlock
  rw [norm_neg]
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 (U / g), ∑ s ∈ Finset.Icc 1 (U / g),
        (16 * ‖pairedEtaXiCompletionFactor rho.1‖ * (g : ℝ) ^ (-2 * rho.1.re)) *
          (Real.exp (-(r : ℝ) / 2) * Real.exp (-(s : ℝ) / 2)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro s hs
      split_ifs with hc
      · exact norm_gcd_row_le rho hA hg hAg (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hs).1
      · rw [norm_zero]
        positivity
    _ = (16 * ‖pairedEtaXiCompletionFactor rho.1‖ * (g : ℝ) ^ (-2 * rho.1.re)) *
        (∑ r ∈ Finset.Icc 1 (U / g), Real.exp (-(r : ℝ) / 2)) ^ 2 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ _ := by
      have hs := sum_exp_half_le_two (U / g)
      have hn : 0 ≤ ∑ r ∈ Finset.Icc 1 (U / g), Real.exp (-(r : ℝ) / 2) := by positivity
      have hp : (∑ r ∈ Finset.Icc 1 (U / g), Real.exp (-(r : ℝ) / 2)) ^ 2 ≤ 4 := by nlinarith
      apply (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq
      ring

/-- The entire sum of reduced blocks above a gcd threshold, including every finite cutoff. -/
def largeGcd (rho : NontrivialZetaZero) (A : ℝ) (U G : ℕ) : ℂ :=
  ∑ g ∈ Finset.Ioc G U, gcdBlock rho A U g

/-- A finite outer power tail is bounded by its complete improper integral, including an empty interval. -/
theorem sum_Ioc_rpow_le {p : ℝ} (hp : p < -1) {G : ℕ} (hG : 1 ≤ G) (U : ℕ) :
    (∑ g ∈ Finset.Ioc G U, (g : ℝ) ^ p) ≤ (G : ℝ) ^ (p + 1) / (-p - 1) := by
  have hGR : (0 : ℝ) < G := by exact_mod_cast hG
  have hs := (Real.summable_nat_rpow.mpr hp).comp_injective
    (show Function.Injective (fun n : ℕ ↦ n + G + 1) by intro a b h; dsimp only at h; omega)
  have ha : AntitoneOn (fun x : ℝ ↦ x ^ p) (Ici (G : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hGR.trans_le hx) hxy (by linarith)
  have hb := ha.tsum_comp_add_le_integral G (integrableOn_Ioi_rpow_of_lt hp hGR)
    (fun x hx ↦ Real.rpow_nonneg (hGR.trans hx).le p)
  have he : (∑ g ∈ Finset.Ioc G U, (g : ℝ) ^ p) =
      ∑ n ∈ Finset.range (U - G), ((n + G + 1 : ℕ) : ℝ) ^ p := by
    rw [show Finset.Ioc G U = Finset.Ico (G + 1) (U + 1) by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_add_right]
    apply Finset.sum_congr rfl
    intro n hn
    congr 2
    omega
  rw [he]
  apply (hs.sum_le_tsum (Finset.range (U - G))
    (fun n hn ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
  apply hb.trans_eq
  rw [integral_Ioi_rpow_of_lt hp hGR]
  rw [show -p - 1 = -(p + 1) by ring, div_neg, neg_div]

/-- The full large-gcd contribution has a power-decaying allowance, with no unproved reduced-core hypothesis. -/
theorem norm_largeGcd_le (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {A : ℝ} (hA : 0 < A) (U : ℕ) {G : ℕ} (hG : 1 ≤ G)
    (hAG : 2 * A ≤ (G : ℝ) ^ 2) :
    ‖largeGcd rho A U G‖ ≤ 64 * ‖pairedEtaXiCompletionFactor rho.1‖ *
      ((G : ℝ) ^ (1 - 2 * rho.1.re) / (2 * rho.1.re - 1)) := by
  unfold largeGcd
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ g ∈ Finset.Ioc G U, 64 * ‖pairedEtaXiCompletionFactor rho.1‖ *
        (g : ℝ) ^ (-2 * rho.1.re) := by
      apply Finset.sum_le_sum
      intro g hg
      have hGg : G ≤ g := (Finset.mem_Ioc.mp hg).1.le
      have hGgR : (G : ℝ) ≤ g := by exact_mod_cast hGg
      exact norm_gcdBlock_le rho hA U (hG.trans hGg)
        (hAG.trans (by nlinarith [(Nat.cast_nonneg G : (0 : ℝ) ≤ G)]))
    _ = 64 * ‖pairedEtaXiCompletionFactor rho.1‖ *
        (∑ g ∈ Finset.Ioc G U, (g : ℝ) ^ (-2 * rho.1.re)) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      have h := sum_Ioc_rpow_le (p := -2 * rho.1.re) (by linarith) hG U
      have he : -2 * rho.1.re + 1 = 1 - 2 * rho.1.re := by ring
      have hd : -(-2 * rho.1.re) - 1 = 2 * rho.1.re - 1 := by ring
      rw [he, hd] at h
      exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The smaller-gcd contribution retains all original blocks up to the chosen threshold. -/
def smallGcd (rho : NontrivialZetaZero) (A : ℝ) (U G : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 (min G U), gcdBlock rho A U g

/-- The original quadratic splits exactly into its smaller and larger gcd contributions. -/
theorem smoothQuadratic_eq_small_add_large (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (U G : ℕ) : smoothQuadratic rho A U = smallGcd rho A U G + largeGcd rho A U G := by
  rw [smoothQuadratic_eq_sum_gcdBlock rho hA]
  unfold smallGcd largeGcd
  by_cases hGU : G ≤ U
  · rw [min_eq_left hGU]
    have he : Finset.Icc 1 G ∪ Finset.Ioc G U = Finset.Icc 1 U := by
      ext g
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hd : Disjoint (Finset.Icc 1 G) (Finset.Ioc G U) := by
      apply Finset.disjoint_left.mpr
      intro g hg hh
      have := Finset.mem_Icc.mp hg
      have := Finset.mem_Ioc.mp hh
      omega
    rw [← he, Finset.sum_union hd]
  · rw [min_eq_right (by omega : U ≤ G), Finset.Ioc_eq_empty_of_le (by omega : U ≤ G)]
    simp

/-- Removing the entire large-gcd part changes the original quadratic by only the proved explicit allowance. -/
theorem norm_smallGcd_sub_smoothQuadratic_le (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {A : ℝ} (hA : 0 < A) (U : ℕ) {G : ℕ} (hG : 1 ≤ G)
    (hAG : 2 * A ≤ (G : ℝ) ^ 2) :
    ‖smallGcd rho A U G - smoothQuadratic rho A U‖ ≤
      64 * ‖pairedEtaXiCompletionFactor rho.1‖ *
        ((G : ℝ) ^ (1 - 2 * rho.1.re) / (2 * rho.1.re - 1)) := by
  rw [smoothQuadratic_eq_small_add_large rho hA, sub_add_cancel_left, norm_neg]
  exact norm_largeGcd_le rho hrho hA U hG hAG

/-- On the proposed eighth/fifth schedule the complete large-gcd part has a negative power at every zero right of one half. -/
theorem norm_largeGcd_eighth_fifth_le (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {u : ℕ} (hu : 1 ≤ u) :
    ‖largeGcd rho ((u : ℝ) ^ 8) (u ^ 5) (2 * u ^ 4)‖ ≤
      (64 * ‖pairedEtaXiCompletionFactor rho.1‖ / (2 * rho.1.re - 1)) *
        (u : ℝ) ^ (4 - 8 * rho.1.re) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hG : 1 ≤ 2 * u ^ 4 := Nat.mul_pos (by norm_num) (pow_pos hu 4)
  have hAG : 2 * (u : ℝ) ^ 8 ≤ ((2 * u ^ 4 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith [pow_nonneg huR.le 8]
  apply (norm_largeGcd_le rho hrho (pow_pos huR 8) (u ^ 5) hG hAG).trans
  have hp : (((2 * u ^ 4 : ℕ) : ℝ)) ^ (1 - 2 * rho.1.re) ≤
      (u : ℝ) ^ (4 - 8 * rho.1.re) := by
    have h := Real.rpow_le_rpow_of_nonpos (pow_pos huR 4)
      (show (u : ℝ) ^ 4 ≤ ((2 * u ^ 4 : ℕ) : ℝ) by push_cast; nlinarith [pow_nonneg huR.le 4])
      (by linarith : 1 - 2 * rho.1.re ≤ 0)
    rw [← Real.rpow_natCast_mul huR.le] at h
    convert! h using 1
    congr 1
    ring
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp (by linarith))
    (by positivity : 0 ≤ 64 * ‖pairedEtaXiCompletionFactor rho.1‖)).trans_eq
  ring

/-- The complete large-gcd contribution tends to zero on the actual near-square schedule. -/
theorem largeGcd_eighth_fifth_tendsto_zero (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ largeGcd rho ((u : ℝ) ^ 8) (u ^ 5) (2 * u ^ 4)) atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (4 - 8 * rho.1.re)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < 8 * rho.1.re - 4)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    convert! h using 1
    funext u
    simp only [Function.comp_def]
    congr 1
    ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop 1).mono fun u hu ↦ norm_largeGcd_eighth_fifth_le rho hrho hu)
    (by simpa only [mul_zero] using (hp.const_mul
      (64 * ‖pairedEtaXiCompletionFactor rho.1‖ / (2 * rho.1.re - 1))))

end

end RiemannGaussian.EtaGammaGcd
