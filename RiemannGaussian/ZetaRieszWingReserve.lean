/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCentralHarmonicCost
import RiemannGaussian.ZetaRieszPrimeCountMass

/-!
# A positive reserve inside the original tapered wing

On a smaller source-radius interval, independent prime completion reaches
three fifths of the original order. This exposes a positive part of the
existing tapered wing, while leaving its complement and the lower-count
arithmetic response coupled. The whole remaining floor is still open.
-/

namespace RiemannGaussian.ZetaRieszWingReserve
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCompletionRate ZetaRieszPrimeCompletionPhase
open ZetaRieszPrimePairConvolution ZetaRieszAnnulusJoint ZetaExposedPrimeMoments
open ZetaRieszMatchedMiddle ZetaRieszReflectedCompletion ZetaRieszEndpointTaper

/-- The smaller interval is contained in the original harmonic-cost range. -/
theorem reserve_radius_lt_annular :
    Real.exp (-(11 / 16 : ℝ)) < Real.exp (-(2 / 3 : ℝ)) := by
  exact Real.exp_lt_exp.mpr (by norm_num)

/-- A strict, summable completion rate through three fifths of the order. -/
theorem reserve_completion_rate {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(11 / 16 : ℝ))) :
    completionExponent u (3 / 5) (11 / 8) (4 / 9) (8193 / 8192) ≤ -(1 / 1024) := by
  have hlu : Real.log u ≤ -(11 / 16 : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log hu huh).le
  have hlog : Real.log (9 / 4 : ℝ) ≤ 13 / 16 := by
    have h3 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
      simpa only [show (3 : ℝ) ^ 2 = 9 by norm_num, Nat.cast_ofNat] using
        (Real.log_pow (3 : ℝ) (2 : ℕ))
    have h2 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using
        (Real.log_pow (2 : ℝ) (2 : ℕ))
    rw [Real.log_div (by norm_num) (by norm_num), h3, h2]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  have he : Real.log (u / (4 / 9 : ℝ)) = Real.log u + Real.log (9 / 4 : ℝ) := by
    rw [show u / (4 / 9 : ℝ) = u * (9 / 4) by ring,
      Real.log_mul hu.ne' (by norm_num)]
  unfold completionExponent
  rw [he]
  linarith

/-- Both actual omitted prime ranges have a uniform geometric allowance
on the longer interval. All ordinates are covered independently of zeros. -/
theorem eventually_norm_reserve_completion {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u < Real.exp (-(11 / 16 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 3 * k → 5 * k ≤ 3 * N → ∀ y : ℝ,
      ‖(u : ℂ) ^ k * (finiteMoment (intermediatePrimes u N) k
        (3 / 2 + Complex.I * y) - ordinaryPrimeMoment k (3 / 2 + Complex.I * y))‖ ≤
        Real.exp (-(1 / 1024 : ℝ) * N) *
          ((∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
            ∑' n, zetaPrimeExpWeight (8193 / 8192) n) := by
  have hu0 : 0 < u := by linarith
  have h := eventually_norm_finite_sub_complete_of_rate hu0
    (huh.trans reserve_radius_lt_annular) (show (0 : ℝ) ≤ 11 / 8 by norm_num)
    (by norm_num; exact huh) (show (0 : ℝ) < 4 / 9 by norm_num)
    (show (4 / 9 : ℝ) ≤ u by linarith) (show (1 : ℝ) < 8193 / 8192 by norm_num)
    (by norm_num) (reserve_completion_rate hu0 huh)
  filter_upwards [h] with N hN
  intro k hklo hkhi y
  have hk : (k : ℝ) ≤ (3 / 5 : ℝ) * N := by
    have hkc : 5 * (k : ℝ) ≤ 3 * N := by exact_mod_cast hkhi
    linarith
  have he : Real.exp (-(95 / 3072 : ℝ) * N) ≤ Real.exp (-(1 / 1024 : ℝ) * N) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  apply (hN k hklo hk y).trans
  rw [mul_add]
  exact add_le_add
    (mul_le_mul_of_nonneg_right he (tsum_nonneg (fun _ => (Real.exp_pos _).le))) le_rfl

/-- The extra derivative weight is paid on all moving eligible orders,
with arbitrary moving height and the original physical prime cutoffs. -/
theorem tendsto_reserve_weighted_error (k : ℕ → ℕ) (y : ℕ → ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(11 / 16 : ℝ)))
    (hk : ∀ᶠ N : ℕ in atTop, N ≤ 3 * k N ∧ 5 * k N ≤ 3 * N) :
    Tendsto (fun N : ℕ => (k N : ℂ) * ((u : ℂ) ^ k N *
      (finiteMoment (intermediatePrimes u N) (k N) (3 / 2 + Complex.I * y N) -
        ordinaryPrimeMoment (k N) (3 / 2 + Complex.I * y N)))) atTop (𝓝 0) := by
  let r : ℝ := Real.exp (-(1 / 1024 : ℝ))
  let Z : ℝ := (∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
    ∑' n, zetaPrimeExpWeight (8193 / 8192) n
  have hZ : 0 ≤ Z := add_nonneg (tsum_nonneg (fun _ => (Real.exp_pos _).le))
    (tsum_nonneg (fun _ => (Real.exp_pos _).le))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have he (N : ℕ) : Real.exp (-(1 / 1024 : ℝ) * N) = r ^ N := by
    rw [mul_comm, Real.exp_nat_mul]
  apply squeeze_zero_norm' (a := fun N : ℕ => (N + 1 : ℝ) ^ 2 * r ^ N * Z) (by
    filter_upwards [eventually_norm_reserve_completion hu huh, hk] with N hN hkN
    have hNk : k N ≤ N := by omega
    have hc : (k N : ℝ) ≤ (N + 1 : ℝ) ^ 2 := by
      have hcast : (k N : ℝ) ≤ N := by exact_mod_cast hNk
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    rw [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (k N : ℝ) * (Real.exp (-(1 / 1024 : ℝ) * N) * Z) :=
        mul_le_mul_of_nonneg_left (hN (k N) hkN.1 hkN.2 (y N)) (Nat.cast_nonneg _)
      _ = (k N : ℝ) * r ^ N * Z := by rw [he]; ring
      _ ≤ (N + 1 : ℝ) ^ 2 * r ^ N * Z :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 _)) hZ)
  simpa only [zero_mul] using
    (ZetaRieszShiftedHeadBudget.tendsto_quadratic_geometric hr0 hr1).mul_const Z

/-- Complete exposed phases transfer to every selected order through
three fifths after the independent completion estimate has been paid. -/
theorem tendsto_reserve_weighted_finite (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ)))
    (k : ℕ → ℕ)
    (hk : ∀ᶠ N : ℕ in atTop, N ≤ 3 * k N ∧ 5 * k N ≤ 3 * N) :
    Tendsto (fun N : ℕ => weightedFinite (3 / 2 - rho.1.re) rho.1.im N (k N))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hkt : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hk, eventually_ge_atTop (3 * b)] with N hkN hNb
    omega
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have h := ((ZetaRieszPrimeCompletionPhase.tendsto_weighted_complete rho hrho hexposed).comp hkt).add
    (tendsto_reserve_weighted_error k (fun _ => rho.1.im) hu huh hk)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  dsimp only [Function.comp_def, weightedFinite]
  ring

/-- The exposed finite phases are uniformly controlled on the longer
moving interval, with one threshold for all its orders. -/
theorem eventually_uniform_reserve_phase (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 3 * k → 5 * k ≤ 3 * N →
      ‖weightedFinite (3 / 2 - rho.1.re) rho.1.im N k +
        (analyticZetaZeroMultiplicity rho : ℂ)‖ ≤ ε := by
  apply ZetaRieszInfinitePhysical.eventually_forall_of_all_selections
  intro f
  let k : ℕ → ℕ := fun N => if N ≤ 3 * f N ∧ 5 * f N ≤ 3 * N then f N else N / 2
  have hk : ∀ᶠ N : ℕ in atTop, N ≤ 3 * k N ∧ 5 * k N ≤ 3 * N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    by_cases hf : N ≤ 3 * f N ∧ 5 * f N ≤ 3 * N
    · simpa only [k, if_pos hf] using hf
    · simp only [k, if_neg hf]
      omega
  have h := ((tendsto_reserve_weighted_finite rho hrho hexposed huh k hk).add_const
    (analyticZetaZeroMultiplicity rho : ℂ)).norm
  simp only [neg_add_cancel, norm_zero] at h
  filter_upwards [h.eventually (eventually_lt_nhds hε)] with N hN
  intro hlow hhigh
  simpa only [k, if_pos (And.intro hlow hhigh)] using hN.le

/-- A fixed interior interval of the actual tapered-wing orders. -/
def reserveOrders (N : ℕ) : Finset ℕ :=
  Finset.Icc (13 * N / 32 + 1) ((15 * N + 64) / 32)

/-- Every selected order and the high-leg derivative successor remain
inside the proved completion range and the original wing. -/
theorem reserveOrders_bounds {N k : ℕ} (hN : 320 ≤ N) (hk : k ∈ reserveOrders N) :
    k ∈ lowerWing N ∧ 0 < k ∧ k ≤ N + 1 ∧ 0 < N + 1 - k ∧
      N ≤ 3 * k ∧ N ≤ 3 * (N + 1 - k) ∧ 5 * (N + 1 - k + 1) ≤ 3 * N := by
  have hki := Finset.mem_Icc.mp hk
  constructor
  · simp only [lowerWing, ZetaRieszPairOrders.middleOrders,
      Finset.mem_filter, Finset.mem_range]
    omega
  · omega

/-- The selected block contains a positive proportion of factorial
orders; this is a count of orders, not a claim about prime mass. -/
theorem reserveOrders_card (N : ℕ) :
    N + 1 ≤ 17 * (reserveOrders N).card := by
  simp only [reserveOrders, Nat.card_Icc]
  omega

/-- The literal endpoint subtraction keeps a strict positive fraction
of the main product on every selected order. -/
theorem relative_taper_bounds {u L : ℝ} (hu : 1 / 2 ≤ u) (hL : 0 < L)
    {N l : ℕ} (hl : 5 * l ≤ 3 * N) (hLN : (11 / 8 : ℝ) * N ≤ L) :
    0 ≤ (l : ℝ) / (u * L) ∧ (l : ℝ) / (u * L) ≤ 7 / 8 := by
  have hu0 : 0 < u := by linarith
  have hden := mul_pos hu0 hL
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hden.le
  · apply (div_le_iff₀ hden).mpr
    have hlc : 5 * (l : ℝ) ≤ 3 * N := by exact_mod_cast hl
    have hprod := mul_le_mul_of_nonneg_right hu hL.le
    nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- A finer phase error pays for both products before the small positive
endpoint margin is used. The actual moments are not normed separately. -/
theorem norm_product_sub_square_fine {a b : ℂ} {m : ℝ} (hm : 0 ≤ m)
    (ha : ‖a + (m : ℂ)‖ ≤ m / 1000) (hb : ‖b + (m : ℂ)‖ ≤ m / 1000) :
    ‖a * b - (m : ℂ) ^ 2‖ ≤ m ^ 2 / 240 := by
  have hmc : ‖(m : ℂ)‖ = m := by rw [Complex.norm_real, Real.norm_of_nonneg hm]
  have hbn : ‖b‖ ≤ 2 * m := by
    calc
      _ = ‖(b + (m : ℂ)) - m‖ := by congr 1; ring
      _ ≤ ‖b + (m : ℂ)‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
      _ ≤ m / 1000 + m := by rw [hmc]; linarith
      _ ≤ _ := by linarith
  have he : a * b - (m : ℂ) ^ 2 = (a + m) * b - (m : ℂ) * (b + m) := by ring
  rw [he]
  calc
    _ ≤ ‖(a + (m : ℂ)) * b‖ + ‖(m : ℂ) * (b + m)‖ := norm_sub_le _ _
    _ = ‖a + (m : ℂ)‖ * ‖b‖ + m * ‖b + (m : ℂ)‖ := by rw [norm_mul, norm_mul, hmc]
    _ ≤ (m / 1000) * (2 * m) + m * (m / 1000) :=
      add_le_add (mul_le_mul ha hbn (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left hb hm)
    _ ≤ _ := by nlinarith [sq_nonneg m]

/-- Both neighboring high-leg moments keep their phases through the
endpoint subtraction, yielding a quantitative positive real reserve. -/
theorem re_tapered_product_ge {A B : ℂ} {m r : ℝ}
    (hA : ‖A - (m : ℂ) ^ 2‖ ≤ m ^ 2 / 240)
    (hB : ‖B - (m : ℂ) ^ 2‖ ≤ m ^ 2 / 240)
    (hr : r ≤ 7 / 8) :
    (15 / 128 : ℝ) * m ^ 2 ≤ (A - (r : ℂ) * B).re := by
  have he : ((m : ℂ) ^ 2).re = m ^ 2 := by simp [pow_two]
  have ha := (Complex.abs_re_le_norm (A - (m : ℂ) ^ 2)).trans hA
  have hb := (Complex.abs_re_le_norm (B - (m : ℂ) ^ 2)).trans hB
  rw [Complex.sub_re, he] at ha hb
  obtain ⟨ha0, ha1⟩ := abs_le.mp ha
  obtain ⟨hb0, hb1⟩ := abs_le.mp hb
  have hbpos : 0 ≤ B.re := by nlinarith [sq_nonneg m]
  have hprod := mul_le_mul_of_nonneg_right hr hbpos
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith

/-- One original wing atom, including the product-log prefactor. -/
def wingAtom (u y : ℝ) (N k : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) * ordinaryPrimeMoment k (3 / 2 + Complex.I * y) *
    taperedMoment (intermediatePrimes u N) (N + 1 - k)
      (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u N)

/-- The exact positive-weighted product identity for the original wing
atom, retaining both consecutive high moments and their common phase. -/
theorem normalized_wingAtom_eq (u y : ℝ) (N k : ℕ) (hu : u ≠ 0)
    (hk : 0 < k) (hkM : k ≤ N + 1) (hl : 0 < N + 1 - k) :
    (u : ℂ) ^ (N + 1) * wingAtom u y N k =
      (((N + 1 : ℕ) : ℂ) / ((k : ℂ) * ((N + 1 - k : ℕ) : ℂ))) *
        (weightedComplete u y k * weightedFinite u y N (N + 1 - k) -
          (((N + 1 - k : ℕ) : ℂ) /
            ((u : ℂ) * (SquarefreeVaughanLogSource.length u N : ℂ))) *
            (weightedComplete u y k * weightedFinite u y N (N + 1 - k + 1))) := by
  have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  have hkc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hlc : ((N + 1 - k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
  have hLc : (SquarefreeVaughanLogSource.length u N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (SquarefreeVaughanLogSource.length_pos u N).ne'
  have hpow : (u : ℂ) ^ (N + 1) = (u : ℂ) ^ k * (u : ℂ) ^ (N + 1 - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkM]
  unfold wingAtom weightedComplete weightedFinite
  rw [taperedMoment_eq, hpow]
  simp only [pow_succ, Nat.cast_add, Nat.cast_one]
  field_simp

/-- The selected positive block is an exact part of the original wing. -/
def reserve (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ reserveOrders N, wingAtom u y N k

/-- Complementary positive factorial orders supply a uniform lower
weight, without losing either moment or changing the order interval. -/
theorem wing_weight_lower (N k : ℕ) (hk : 0 < k) (hkM : k ≤ N + 1)
    (hl : 0 < N + 1 - k) :
    4 / ((N + 1 : ℕ) : ℝ) ≤
      ((N + 1 : ℕ) : ℝ) / ((k : ℝ) * ((N + 1 - k : ℕ) : ℝ)) := by
  have hkc : (0 : ℝ) < k := by exact_mod_cast hk
  have hlc : (0 : ℝ) < (N + 1 - k : ℕ) := by exact_mod_cast hl
  apply (div_le_div_iff₀ (by positivity) (mul_pos hkc hlc)).mpr
  have he : (k : ℝ) + ((N + 1 - k : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_sub_of_le hkM)
  nlinarith [sq_nonneg ((k : ℝ) - ((N + 1 - k : ℕ) : ℝ))]

/-- Each actual selected wing atom has a positive source-normalized
real floor. Only the independently completable high orders are selected. -/
theorem eventually_re_wingAtom_ge (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ reserveOrders N,
      (15 / 32 : ℝ) * (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / ((N + 1 : ℕ) : ℝ) ≤
        ((((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)) *
          wingAtom (3 / 2 - rho.1.re) rho.1.im N k).re := by
  let u : ℝ := 3 / 2 - rho.1.re
  let m : ℝ := analyticZetaZeroMultiplicity rho
  have hu : 1 / 2 ≤ u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu0 : 0 < u := by linarith
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  filter_upwards [eventually_uniform_reserve_phase rho hrho hexposed huh
    (ε := m / 1000) (by positivity),
    eventually_uniform_complete_phase rho hrho hexposed (ε := m / 1000) (by positivity),
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu0
      (by norm_num : (0 : ℝ) ≤ 11 / 16) huh,
    eventually_ge_atTop 320] with N hf hc hLN hN
  intro k hk
  obtain ⟨_, hk0, hkM, hl0, hklo, hllo, hlhi⟩ := reserveOrders_bounds hN hk
  let l := N + 1 - k
  let L := SquarefreeVaughanLogSource.length u N
  let w : ℝ := ((N + 1 : ℕ) : ℝ) / ((k : ℝ) * (l : ℝ))
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have hLL : (11 / 8 : ℝ) * N ≤ L := by dsimp [L]; nlinarith [hLN]
  have ha := norm_product_sub_square_fine hm.le (hc k hklo) (hf l hllo (by dsimp [l]; omega))
  have hb := norm_product_sub_square_fine hm.le (hc k hklo) (hf (l + 1) (by dsimp [l]; omega) hlhi)
  have hr := (relative_taper_bounds hu hL (show 5 * l ≤ 3 * N by dsimp [l]; omega) hLL).2
  have hsign := re_tapered_product_ge ha hb hr
  have hweight : 0 ≤ ((N + 1 : ℕ) : ℝ) / ((k : ℝ) * (l : ℝ)) := by positivity
  have hprod := mul_le_mul_of_nonneg_left hsign hweight
  have hsmall := mul_le_mul_of_nonneg_left (wing_weight_lower N k hk0 hkM hl0)
    (show 0 ≤ (15 / 128 : ℝ) * m ^ 2 by positivity)
  have he : (u : ℂ) ^ (N + 1) * wingAtom u rho.1.im N k =
      (w : ℂ) *
        (weightedComplete u rho.1.im k * weightedFinite u rho.1.im N l -
          (((l : ℝ) / (u * L)) : ℂ) *
            (weightedComplete u rho.1.im k * weightedFinite u rho.1.im N (l + 1))) := by
    rw [normalized_wingAtom_eq u rho.1.im N k hu0.ne' hk0 hkM hl0]
    simp only [w, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, L, l]
  change (15 / 32 : ℝ) * m ^ 2 / ((N + 1 : ℕ) : ℝ) ≤ _
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have htotal := hsmall.trans (by simpa only [mul_comm] using hprod)
  have hleft : (15 / 128 : ℝ) * m ^ 2 * (4 / ((N + 1 : ℕ) : ℝ)) =
      (15 / 32 : ℝ) * m ^ 2 / ((N + 1 : ℕ) : ℝ) := by ring
  rw [hleft] at htotal
  simpa only [w, u, l, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast] using htotal

/-- A whole positive block of the original wing supplies a fixed reserve
at source scale. The other wing orders and lower prime counts stay unpaid. -/
theorem eventually_re_reserve_ge (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, (15 / 544 : ℝ) * (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 ≤
      ((((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)) *
        reserve (3 / 2 - rho.1.re) rho.1.im N).re := by
  filter_upwards [eventually_re_wingAtom_ge rho hrho hexposed huh,
    eventually_ge_atTop 320] with N hfloor hN
  have hcard : ((N + 1 : ℕ) : ℝ) ≤ 17 * ((reserveOrders N).card : ℝ) := by
    exact_mod_cast reserveOrders_card N
  have hmass := mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 by positivity)
  have hsum := Finset.sum_le_sum hfloor
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hlo : (15 / 544 : ℝ) * (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 ≤
      ((reserveOrders N).card : ℝ) *
        ((15 / 32 : ℝ) * (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / ((N + 1 : ℕ) : ℝ)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  simpa only [reserve, Finset.mul_sum, Complex.re_sum] using hlo.trans hsum

/-- All unselected original wing orders, with their signed endpoint
weights unchanged. No assertion about their sign is included. -/
def remainingWing (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ lowerWing N \ reserveOrders N, wingAtom u y N k

/-- The positive reserve and its complement partition the literal wing,
including the original product-log prefactor, without overlap or error. -/
theorem taperedWing_eq_reserve_add_remaining (u y : ℝ) (N : ℕ) (hN : 320 ≤ N) :
    ZetaRieszCompletedCarrier.taperedWing u y N = reserve u y N + remainingWing u y N := by
  have hsub : reserveOrders N ⊆ lowerWing N := fun _ hk => (reserveOrders_bounds hN hk).1
  have hs := Finset.sum_sdiff (f := wingAtom u y N) hsub
  unfold ZetaRieszCompletedCarrier.taperedWing reserve remainingWing
  rw [Finset.mul_sum]
  simpa only [wingAtom, mul_assoc, add_comm] using hs.symm

open ZetaRieszPrimeCountFrequency

/-- The exact unpaid part of the existing harmonic-cost route after
the full high-count deletion and the proved positive wing reserve. -/
def unpaid (u y : ℝ) (j : ℕ) : ℂ :=
  (u : ℂ) ^ (dyadicMomentOrder j + 1) *
    ((1 / (2 * (Real.pi : ℂ))) *
      (∫ xi : ℝ in Set.Ioi 0,
        fewPrimeFrequency 1 u y (dyadicMomentOrder j) (dyadicPrimeCount j) xi) +
      remainingWing u y (dyadicMomentOrder j))

/-- The pre-existing lower-count source equals the new unpaid response
plus the controlled wing block at every eligible order. -/
theorem few_add_wing_eq (u y : ℝ) (j : ℕ) (hj : 320 ≤ dyadicMomentOrder j) :
    (u : ℂ) ^ (dyadicMomentOrder j + 1) *
      ((1 / (2 * (Real.pi : ℂ))) *
        (∫ xi : ℝ in Set.Ioi 0,
          fewPrimeFrequency 1 u y (dyadicMomentOrder j) (dyadicPrimeCount j) xi) +
        ZetaRieszCompletedCarrier.taperedWing u y (dyadicMomentOrder j)) =
      unpaid u y j + (u : ℂ) ^ (dyadicMomentOrder j + 1) * reserve u y (dyadicMomentOrder j) := by
  rw [taperedWing_eq_reserve_add_remaining u y (dyadicMomentOrder j) hj]
  unfold unpaid
  ring

/-- The positive block increases the admissible negative arithmetic
budget for the exact remaining sum. The whole-sum floor is still an
explicit unproved premise, and the zero is explicitly simple and exposed. -/
theorem false_of_unpaid_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ)))
    (hsimple : analyticZetaZeroMultiplicity rho = 1)
    {eta : ℝ}
    (heta : eta < 1 - RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) + 15 / 544)
    (hfloor : ∃ᶠ j in atTop, -eta ≤ (unpaid (3 / 2 - rho.1.re) rho.1.im j).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp
    (ZetaRieszPrimeCountMass.tendsto_few_add_wing_source rho hrho hexposed
      (huh.trans reserve_radius_lt_annular))
  simp only [hsimple, Nat.cast_one, one_pow, one_mul, Complex.add_re,
    Complex.neg_re, Complex.one_re, Complex.ofReal_re] at hs
  have hr := tendsto_dyadicMomentOrder.eventually
    (eventually_re_reserve_ge rho hrho hexposed huh)
  simp only [hsimple, Nat.cast_one, one_pow, mul_one] at hr
  have hj := tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 320)
  have hfreq := hfloor.and_eventually (hr.and hj)
  have hbound := hfreq.mono (fun j hj => by
    have he := congrArg Complex.re (few_add_wing_eq (3 / 2 - rho.1.re) rho.1.im j hj.2.2)
    rw [Complex.add_re] at he
    have hg := add_le_add hj.1 hj.2.1
    rw [← he] at hg
    exact hg)
  have hc := ge_of_tendsto_of_frequently hs hbound
  linarith

end
end RiemannGaussian.ZetaRieszWingReserve
