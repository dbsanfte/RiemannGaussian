import RiemannGaussian.ZetaRieszPrimePairConvolution
import RiemannGaussian.ZetaRieszHeadAdaptiveTransport

/-!
# Independent outer pair bounds and the shared prime quadratic

Exact order reflection pays both outer finite-pair ranges. The surviving
head and pair terms use the same finite prime moments, retaining the
derivative shift, every fixed filter and the entire exposed-zero source.
An independent floor for the whole remaining response is still open.
-/

namespace RiemannGaussian.ZetaRieszPairOrders
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimePairConvolution ZetaRieszHeadAdaptive
open ZetaRieszHeadAdaptiveTransport ZetaRieszShiftedHeadBudget
open ZetaRieszHeadOrders ZetaRieszAnnulusJoint

/-- Unlogged finite moments have an independent tilted bound retaining
their common logarithmic ceiling until the source radius is used. -/
theorem norm_finiteMoment_le_tilt (A : Finset ℕ) (k : ℕ) (y L : ℝ)
    {q σ : ℝ} (hq : 0 < q) (hσ : 1 < σ) (hcoeff : 0 ≤ q + σ - 3 / 2)
    (hA : ∀ a ∈ A, Real.log a ≤ L) :
    ‖finiteMoment A k (3 / 2 + Complex.I * y)‖ ≤
      q⁻¹ ^ k * Real.exp ((q + σ - 3 / 2) * L) * ∑' n, zetaPrimeExpWeight σ n := by
  have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  unfold finiteMoment
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ A, (q⁻¹ ^ k * Real.exp ((q + σ - 3 / 2) * L)) * zetaPrimeExpWeight σ a := by
      apply Finset.sum_le_sum
      intro a ha
      have hk := norm_zetaPrimeLogKernel_le k (3 / 2 + Complex.I * y) a hq
      rw [hs] at hk
      have he : zetaPrimeExpWeight (3 / 2 - q) a =
          Real.exp ((q + σ - 3 / 2) * Real.log a) * zetaPrimeExpWeight σ a := by
        unfold zetaPrimeExpWeight
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he] at hk
      have hx := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hA a ha) hcoeff)
      exact (hk.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le) (by positivity))).trans_eq (by ring)
    _ = (q⁻¹ ^ k * Real.exp ((q + σ - 3 / 2) * L)) * ∑ a ∈ A, zetaPrimeExpWeight σ a := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_zetaPrimeExpWeight hσ).sum_le_tsum A (fun _ _ => (Real.exp_pos _).le)) (by positivity)

/-- Every finite unlogged moment has a complete Euler majorant,
uniformly over the finite mask and the ordinate. -/
theorem norm_finiteMoment_le_euler (A : Finset ℕ) (k : ℕ) (y : ℝ)
    {q : ℝ} (hq : 0 < q) (hqhalf : q < 1 / 2) :
    ‖finiteMoment A k (3 / 2 + Complex.I * y)‖ ≤
      q⁻¹ ^ k * ∑' n, zetaPrimeExpWeight (3 / 2 - q) n := by
  unfold finiteMoment
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ A, q⁻¹ ^ k * zetaPrimeExpWeight (3 / 2 - q) a := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [show (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) by simp] using
        norm_zetaPrimeLogKernel_le k (3 / 2 + Complex.I * y) a hq
    _ = q⁻¹ ^ k * ∑ a ∈ A, zetaPrimeExpWeight (3 / 2 - q) a := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_zetaPrimeExpWeight (by linarith : 1 < (3 / 2 : ℝ) - q)).sum_le_tsum A
        (fun _ _ => (Real.exp_pos _).le)) (by positivity)

/-- Every high factorial order of the finite pair convolution is
independently paid while both prime factors keep their original phases. -/
theorem norm_finite_pair_high_atom (A : Finset ℕ) (M k : ℕ) (y : ℝ)
    {u L : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hkM : k ≤ M) (hk : 7 * M ≤ 8 * k) (hL : L ≤ -2 * Real.log u * M)
    (hA : ∀ a ∈ A, Real.log a ≤ L) :
    ‖(u : ℂ) ^ (M + 1) * (finiteMoment A k (3 / 2 + Complex.I * y) *
      finiteMoment A (M - k) (3 / 2 + Complex.I * y))‖ ≤
        Real.exp (-(7 / 9216 : ℝ) * M) *
          (u * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2) := by
  have hG := norm_finiteMoment_le_tilt A k y L (q := 2 / 3) (σ := 1025 / 1024)
    (by norm_num) (by norm_num) (by norm_num) hA
  rw [show (2 / 3 : ℝ) + 1025 / 1024 - 3 / 2 = 515 / 3072 by norm_num] at hG
  have hB := norm_finiteMoment_le_euler A (M - k) y (q := 511 / 1024) (by norm_num) (by norm_num)
  rw [show (3 / 2 : ℝ) - 511 / 1024 = 1025 / 1024 by norm_num] at hB
  have hZ : 0 ≤ ∑' n, zetaPrimeExpWeight (1025 / 1024) n := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le, norm_mul]
  calc
    _ ≤ u ^ (M + 1) *
        (((2 / 3 : ℝ)⁻¹ ^ k * Real.exp ((515 / 3072 : ℝ) * L) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n) *
          ((511 / 1024 : ℝ)⁻¹ ^ (M - k) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hG hB (norm_nonneg _) (by positivity)
    _ = (u ^ (M + 1) * ((2 / 3 : ℝ)⁻¹ ^ k * Real.exp ((515 / 3072 : ℝ) * L)) *
        (511 / 1024 : ℝ)⁻¹ ^ (M - k)) * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2 := by ring
    _ ≤ (u * Real.exp (-(7 / 9216 : ℝ) * M)) * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2 :=
      mul_le_mul_of_nonneg_right (adaptive_high_scalar hu huh M k hkM hk hL) (sq_nonneg _)
    _ = _ := by ring

/-- The exact upper-order portion of the finite prime-pair convolution. -/
def highPairConvolution (A : Finset ℕ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ adaptiveHighOrders M, finiteMoment A k s * finiteMoment A (M - k) s

/-- The whole high-order finite-pair contribution has an explicit
independent allowance at the literal physical prime cutoff. -/
theorem norm_actual_highPairConvolution (N M : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hN : 3 ≤ N) (hNM : N ≤ M) :
    ‖(u : ℂ) ^ (M + 1) * highPairConvolution (intermediatePrimes u N) M (3 / 2 + Complex.I * y)‖ ≤
      (M + 1 : ℝ) * adaptiveRate ^ M * (u * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2) := by
  have hterm (k : ℕ) (hk : k ∈ adaptiveHighOrders M) :
      ‖(u : ℂ) ^ (M + 1) * (finiteMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) *
        finiteMoment (intermediatePrimes u N) (M - k) (3 / 2 + Complex.I * y))‖ ≤
        adaptiveRate ^ M * (u * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2) := by
    obtain ⟨hkr, hfrac⟩ := Finset.mem_filter.mp hk
    have hkM : k ≤ M := by simpa using Finset.mem_range.mp hkr
    have hb := norm_finite_pair_high_atom (intermediatePrimes u N) M k y hu huh hkM hfrac
      le_rfl (intermediate_log_le_source_order hu huh hN hNM)
    have he : Real.exp (-(7 / 9216 : ℝ) * M) = adaptiveRate ^ M := by
      rw [mul_comm, Real.exp_nat_mul]
      rfl
    simpa only [he] using hb
  unfold highPairConvolution
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ adaptiveHighOrders M, adaptiveRate ^ M *
        (u * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2) := Finset.sum_le_sum hterm
    _ = ((adaptiveHighOrders M).card : ℝ) * (adaptiveRate ^ M *
        (u * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2)) := by simp
    _ ≤ _ := by
      have hc : ((adaptiveHighOrders M).card : ℝ) ≤ M + 1 := by
        exact_mod_cast (Finset.card_filter_le (Finset.range (M + 1)) (fun k => 7 * M ≤ 8 * k)).trans_eq
          (Finset.card_range (M + 1))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
        (mul_nonneg (pow_nonneg adaptiveRate_bounds.1.le _) (mul_nonneg hu.le (sq_nonneg _)))

/-- The central cofactor orders keep both complementary orders away
from the independently bounded outer ranges. -/
def middleOrders (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter (fun k => M < 8 * k ∧ 8 * k < 7 * M)

/-- Reflection of the complementary factorial orders retains the full
complex product and identifies the lower and upper contributions exactly. -/
theorem low_order_sum_eq_high (v : ℕ → ℂ) (M : ℕ) :
    (∑ k ∈ (Finset.range (M + 1)).filter (fun k => 8 * k ≤ M), v k * v (M - k)) =
      ∑ k ∈ adaptiveHighOrders M, v k * v (M - k) := by
  have href := Finset.sum_range_reflect
    (fun k => if 7 * M ≤ 8 * k then v k * v (M - k) else 0) (M + 1)
  simp only [Nat.add_sub_cancel] at href
  calc
    _ = ∑ k ∈ Finset.range (M + 1),
        if 7 * M ≤ 8 * (M - k) then v (M - k) * v (M - (M - k)) else 0 := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      have hkM : k ≤ M := by simpa using Finset.mem_range.mp hk
      have he : 7 * M ≤ 8 * (M - k) ↔ 8 * k ≤ M := by omega
      simp only [Nat.sub_sub_self hkM, he]
      simp only [mul_comm]
    _ = _ := by simpa only [adaptiveHighOrders, Finset.sum_filter] using href

/-- At every positive total order, both independently paid outer
ranges are exactly twice the upper range, including their boundary orders. -/
theorem full_sub_middle_eq_twice_high (v : ℕ → ℂ) (M : ℕ) (hM : 0 < M) :
    (∑ k ∈ Finset.range (M + 1), v k * v (M - k)) -
      (∑ k ∈ middleOrders M, v k * v (M - k)) =
        2 * ∑ k ∈ adaptiveHighOrders M, v k * v (M - k) := by
  calc
    _ = (∑ k ∈ (Finset.range (M + 1)).filter (fun k => 8 * k ≤ M), v k * v (M - k)) +
        ∑ k ∈ adaptiveHighOrders M, v k * v (M - k) := by
      simp only [middleOrders, adaptiveHighOrders, Finset.sum_filter,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hl : 8 * k ≤ M
      · have hh : ¬7 * M ≤ 8 * k := by omega
        have hm : ¬(M < 8 * k ∧ 8 * k < 7 * M) := by omega
        simp [hl, hh, hm]
      · by_cases hh : 7 * M ≤ 8 * k
        · have hm : ¬(M < 8 * k ∧ 8 * k < 7 * M) := by omega
          simp [hl, hh, hm]
        · have hm : M < 8 * k ∧ 8 * k < 7 * M := by omega
          simp [hl, hh, hm]
    _ = _ := by rw [low_order_sum_eq_high]; ring

/-- The finite prime-pair convolution with only central cofactor
orders retained, keeping its exact unordered normalization. -/
def middlePairResponse (A : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ P.support, (P.coeff j * ((N + j + 1 : ℕ) : ℂ) / 2) *
    ∑ k ∈ middleOrders (N + j + 1), finiteMoment A k s * finiteMoment A (N + j + 1 - k) s

/-- Both outer ranges of the half ordered correction. Reflection
cancels precisely its factor one half; no prime incidence is lost. -/
def outerPairResponse (A : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ P.support, (P.coeff j * ((N + j + 1 : ℕ) : ℂ)) * highPairConvolution A (N + j + 1) s

/-- The actual fixed-filter pair convolution splits exactly into
central orders and the complete two-sided outer response. -/
theorem pairConvolution_sub_middle (A : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) :
    pairConvolution A P N s - middlePairResponse A P N s = outerPairResponse A P N s := by
  unfold pairConvolution middlePairResponse outerPairResponse
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_sub, full_sub_middle_eq_twice_high (fun k => finiteMoment A k s) (N + j + 1) (by omega)]
  unfold highPairConvolution
  ring

/-- The finite coefficient cost of the complete two-sided pair deletion. -/
def outerPairCost (P : Polynomial ℂ) (u : ℝ) : ℝ :=
  (u * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2) *
    ∑ j ∈ P.support, ‖P.coeff j‖ * u⁻¹ ^ (j + 1) * (j + 2 : ℝ) ^ 2

/-- The full outer pair response is independently bounded, for every
fixed filter and every height, at the unchanged physical prime cutoff. -/
theorem norm_outerPairResponse_le (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) (hN : 3 ≤ N) :
    ‖(u : ℂ) ^ (N + 1) * outerPairResponse (intermediatePrimes u N) P N (3 / 2 + Complex.I * y)‖ ≤
      ((N + 1 : ℝ) ^ 2 * adaptiveRate ^ N) * outerPairCost P u := by
  have hC : 0 ≤ u * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2 :=
    mul_nonneg hu.le (sq_nonneg _)
  have hb := norm_fixedFilter_of_shiftedBounds P
    (fun j => highPairConvolution (intermediatePrimes u N) (N + j + 1) (3 / 2 + Complex.I * y)) N hu
    (L := 1) (by norm_num) hC adaptiveRate_bounds.1.le adaptiveRate_bounds.2.le (fun j _ => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        norm_actual_highPairConvolution N (N + j + 1) y hu huh hN (by omega))
  have he : (∑ j ∈ P.support, -(P.coeff j * ((N + j + 1 : ℕ) : ℂ) / (1 : ℂ)) *
      highPairConvolution (intermediatePrimes u N) (N + j + 1) (3 / 2 + Complex.I * y)) =
      -outerPairResponse (intermediatePrimes u N) P N (3 / 2 + Complex.I * y) := by
    simp only [div_one, neg_mul, Finset.sum_neg_distrib, outerPairResponse]
  simp only [Complex.ofReal_one] at hb
  rw [he, mul_neg, norm_neg] at hb
  exact hb

/-- Both outer cofactor-order ranges of the actual finite pair
response now decay independently at the original source normalization. -/
theorem tendsto_outerPairResponse (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      outerPairResponse (intermediatePrimes u N) P N (3 / 2 + Complex.I * y)) atTop (nhds 0) := by
  apply squeeze_zero_norm' (by
    filter_upwards [eventually_ge_atTop 3] with N hN
    exact norm_outerPairResponse_le P N y hu huh hN)
  simpa only [zero_mul] using (tendsto_quadratic_geometric
    adaptiveRate_bounds.1.le adaptiveRate_bounds.2).mul_const (outerPairCost P u)

/-- The actual central pair correction is now transported to the
middle cofactor orders with the diagonal and both outer ranges paid. -/
theorem tendsto_centralPair_sub_middle (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (ZetaRieszCentralPair.centralPairResponse P u y N -
        middlePairResponse (intermediatePrimes u N) P N (3 / 2 + Complex.I * y))) atTop (nhds 0) := by
  have h := (tendsto_outerPairResponse P y (by linarith : 0 < u) huh).sub
    (tendsto_pairConvolution_sub_central P y hu huh)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [← pairConvolution_sub_middle]
  ring


/-- The complete remaining carrier after independently paying the
high head orders, pair diagonal, and both outer finite-pair order ranges. -/
def middleJoint (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ZetaRieszCentralPair.centralUnpairedResponse P u y N + adaptiveRemainingHead P u y N +
    middlePairResponse (intermediatePrimes u N) P N (3 / 2 + Complex.I * y)

/-- The exact whole-carrier difference records every independently
bounded term and its original sign before a norm or limit is taken. -/
theorem centralJoint_sub_middleJoint (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    ZetaRieszCentralPair.centralJoint P u y N - middleJoint P u y N =
      adaptiveHead P u y N +
        (ZetaRieszCentralPair.centralPairResponse P u y N -
          pairConvolution (intermediatePrimes u N) P N (3 / 2 + Complex.I * y)) +
        outerPairResponse (intermediatePrimes u N) P N (3 / 2 + Complex.I * y) := by
  rw [ZetaRieszCentralPair.centralJoint, middleJoint, completedHead_eq_adaptive_split,
    ← pairConvolution_sub_middle]
  ring

/-- All deleted components of the literal joint carrier have
independently vanishing source error on the annular source interval. -/
theorem tendsto_centralJoint_sub_middleJoint (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (ZetaRieszCentralPair.centralJoint P u y N - middleJoint P u y N)) atTop (nhds 0) := by
  have h := ((tendsto_adaptiveHead P y (by linarith : 0 < u) huh).sub
    (tendsto_pairConvolution_sub_central P y hu huh)).add
      (tendsto_outerPairResponse P y (by linarith : 0 < u) huh)
  simp only [sub_zero, zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [centralJoint_sub_middleJoint]
  ring

/-- The smaller whole signed response retains the entire negative
multiplicity source. Its independent cofinal real floor remains open. -/
theorem tendsto_middleJoint_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      middleJoint 1 (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (ZetaRieszCentralPair.tendsto_centralJoint_exposed rho hrho hexposed huh).sub
    (tendsto_centralJoint_sub_middleJoint 1 rho.1.im hu huh)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  ring

/-- The shared finite/complete prime arrays in a single signed
quadratic expression, with the head derivative shift and pair half retained. -/
def jointPrimeForm (A : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ∑ j ∈ P.support, (P.coeff j * ((N + j + 1 : ℕ) : ℂ)) *
    ((1 / 2 : ℂ) * ∑ k ∈ middleOrders (N + j + 1),
      finiteMoment A k s * finiteMoment A (N + j + 1 - k) s -
      (1 / (L : ℂ)) * ∑ k ∈ (Finset.range (N + j + 2)).filter (fun k => 8 * k < 7 * (N + j + 1)),
        ((k + 1 : ℕ) : ℂ) * finiteMoment A (k + 1) s *
          ZetaExposedPrimeMoments.ordinaryPrimeMoment (N + j + 1 - k) s)

/-- Both surviving prime components use the same finite moment array;
their complex signs remain coupled in this exact quadratic expression. -/
theorem remainingHead_add_middlePair_eq_form (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    adaptiveRemainingHead P u y N +
      middlePairResponse (intermediatePrimes u N) P N (3 / 2 + Complex.I * y) =
        jointPrimeForm (intermediatePrimes u N) P N (3 / 2 + Complex.I * y)
          (SquarefreeVaughanLogSource.length u N) := by
  simp only [adaptiveRemainingHead, middlePairResponse, jointPrimeForm,
    ← Finset.sum_add_distrib, cofactorMoment_eq_succ]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual remaining carrier is its original unpaired arithmetic
sum plus one correlated prime quadratic, rather than separate norm costs. -/
theorem middleJoint_eq_unpaired_add_form (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    middleJoint P u y N = ZetaRieszCentralPair.centralUnpairedResponse P u y N +
      jointPrimeForm (intermediatePrimes u N) P N (3 / 2 + Complex.I * y)
        (SquarefreeVaughanLogSource.length u N) := by
  rw [middleJoint, ← remainingHead_add_middlePair_eq_form]
  ring


end
end RiemannGaussian.ZetaRieszPairOrders
