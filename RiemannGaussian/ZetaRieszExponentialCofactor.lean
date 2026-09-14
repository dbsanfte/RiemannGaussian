/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGrowingCofactor

/-!
# Exponential cofactor decay and the adaptive arithmetic source

A three-halves factorial tilt gives a geometric source-scale estimate for
the entire composite-cofactor class in an explicit unbounded range when
2/3<u<1. The range eventually exceeds every fixed polynomial in the order.
An adaptive deletion combines this with the universal polynomial range
and preserves the original source at every hypothetical right-half zero.
Semiprimes and larger composite cofactors retain an unproved joint floor.
-/

namespace RiemannGaussian.ZetaRieszExponentialCofactor
noncomputable section
open scoped BigOperators Classical Topology
open Filter ZetaRieszFixedCofactor ZetaRieszGrowingCofactor

/-- The three-halves tilt cancels all spatial exponential growth and
retains an order-geometric bound for the complete fixed filter. -/
theorem norm_filter_le_three_halves (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {n : ℕ} (hn : 0 < n) :
    ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (2 / 3 : ℝ) ^ N * ∑ k ∈ P.support, ‖P.coeff k‖ * (2 / 3 : ℝ) ^ k := by
  have h := norm_zetaPrimeFilterKernel_le_tilt P N (3 / 2 + Complex.I * y)
    (by exact_mod_cast hn : (1 : ℝ) ≤ n) (by norm_num : (0 : ℝ) < 3 / 2)
  norm_num at h
  exact h

/-- Counting the original finite support after the three-halves tilt
leaves every coefficient and polynomial shift present in the estimate. -/
theorem norm_sum_filter_le_count (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (T : Finset ℕ) (X : ℕ) (f : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ n ∈ T, 0 < n ∧ n ≤ X) (hf : ∀ n ∈ T, ‖f n‖ ≤ C) :
    ‖∑ n ∈ T, f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      C * (2 / 3 : ℝ) ^ N *
        (∑ k ∈ P.support, ‖P.coeff k‖ * (2 / 3 : ℝ) ^ k) * X := by
  let S : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * (2 / 3 : ℝ) ^ k
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hcard : T.card ≤ X := by
    have hsub : T ⊆ Finset.Icc 1 X := fun n hn => Finset.mem_Icc.mpr (hT n hn)
    simpa using Finset.card_le_card hsub
  calc
    _ ≤ ∑ n ∈ T, ‖f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ T, C * ((2 / 3 : ℝ) ^ N * S) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul (hf n hn) (norm_filter_le_three_halves P N y (hT n hn).1)
        (norm_nonneg _) hC
    _ = C * (2 / 3 : ℝ) ^ N * S * T.card := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)

/-- The uniform cofactor cost including the counting range is at most
an explicit fourth power; this pays a geometric cofactor budget. -/
theorem rangeCost_mul_le {A : ℕ} (hA : 1 ≤ A) :
    rangeCost A * A ≤ 2 * (1 + 1 / Real.log 4) * (A : ℝ) ^ 4 := by
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hl := Real.log_le_self (Nat.cast_nonneg A)
  have hl0 := Real.log_natCast_nonneg A
  have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hquot : 1 + Real.log A / Real.log 4 ≤ (1 + 1 / Real.log 4) * A := by
    have hdiv := div_le_div_of_nonneg_right hl h4.le
    calc
      _ ≤ (A : ℝ) + A / Real.log 4 := add_le_add hA1 hdiv
      _ = _ := by ring
  calc
    _ ≤ (2 * (A : ℝ) * A * ((1 + 1 / Real.log 4) * A)) * A := by
      unfold rangeCost
      gcongr
    _ = _ := by ring

/-- A uniform geometric ceiling for the original damped cutoff.
This deliberately relaxes only its polynomial damping. -/
theorem cutoff_add_two_le {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (N : ℕ) :
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) + 2 ≤ 3 * u⁻¹ ^ N := by
  have hfloor : (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) ≤
      u⁻¹ ^ N / (N + 1) := Nat.floor_le (by positivity)
  have hdiv : u⁻¹ ^ N / (N + 1) ≤ u⁻¹ ^ N :=
    div_le_self (by positivity) (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hinv : 1 ≤ u⁻¹ := (one_le_inv₀ hu).mpr hu1
  have hpow := one_le_pow₀ hinv (n := N)
  linarith

/-- The source normalization converts the three-halves tilt and the
squared inverse-source cutoff to one explicit geometric base. -/
theorem geometric_scale_identity {u : ℝ} (hu : 0 < u) (N : ℕ) :
    u ^ (N + 1) * (2 / 3 : ℝ) ^ N * (u⁻¹ ^ N) ^ 2 =
      u * ((2 / 3 : ℝ) / u) ^ N := by
  calc
    _ = u * ((u * (2 / 3 : ℝ) * u⁻¹ ^ 2) ^ N) := by
      simp only [mul_pow, ← pow_mul, pow_succ]
      ring
    _ = _ := by congr 2; field_simp

/-- A geometric estimate for every clipped cofactor range. Unlike the
unit tilt, its base is strictly below one for source scales u>2/3. -/
theorem norm_clipped_range_band_le_geometric (P : Polynomial ℂ) (N A : ℕ) (y : ℝ)
    (T : Finset ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hT : ∀ n ∈ T, ∃ a p : ℕ, 1 < a ∧ a ≤ A ∧ p.Prime ∧ ¬ p ∣ a ∧ n = p * a ∧
      n ≤ A * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ T,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      9 * u * rangeCost A * A *
        (∑ k ∈ P.support, ‖P.coeff k‖ * (2 / 3 : ℝ) ^ k) * ((2 / 3 : ℝ) / u) ^ N := by
  let S : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * (2 / 3 : ℝ) ^ k
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hC := rangeCost_nonneg A
  have hb := norm_sum_filter_le_count P N y T
    (A * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
    hC (fun n hn => by
      obtain ⟨a, p, ha, _haA, hp, _hpa, rfl, hc⟩ := hT n hn
      exact ⟨Nat.mul_pos hp.pos (by omega), hc⟩)
    (fun n hn => by
      obtain ⟨a, p, ha, haA, hp, hpa, rfl, hc⟩ := hT n hn
      exact norm_coefficient_le_range u N ha haA hp hpa hc)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] at hb
  calc
    _ ≤ u ^ (N + 1) * (rangeCost A * (2 / 3 : ℝ) ^ N * S *
        (A * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ u ^ (N + 1) * (rangeCost A * (2 / 3 : ℝ) ^ N * S *
        (A * (3 * u⁻¹ ^ N) ^ 2)) := by
      gcongr
      exact cutoff_add_two_le hu hu1 N
    _ = (9 * rangeCost A * A * S) *
        (u ^ (N + 1) * (2 / 3 : ℝ) ^ N * (u⁻¹ ^ N) ^ 2) := by ring
    _ = _ := by rw [geometric_scale_identity hu N]; ring

/-- The eighth-power geometric range budget leaves a square-root
geometric allowance, retaining every order and integer cofactor endpoint. -/
theorem eighth_power_geometric_budget {r : ℝ} (hr : 0 < r) {A N : ℕ}
    (hAN : (A : ℝ) ^ 8 ≤ r ^ N) :
    (A : ℝ) ^ 4 * r⁻¹ ^ N ≤ Real.sqrt (r⁻¹ ^ N) := by
  have hc : r ^ N * r⁻¹ ^ N = 1 := by rw [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow]
  apply Real.le_sqrt_of_sq_le
  calc
    _ = (A : ℝ) ^ 8 * (r⁻¹ ^ N) ^ 2 := by ring
    _ ≤ r ^ N * (r⁻¹ ^ N) ^ 2 := mul_le_mul_of_nonneg_right hAN (sq_nonneg _)
    _ = (r ^ N * r⁻¹ ^ N) * r⁻¹ ^ N := by ring
    _ = _ := by rw [hc, one_mul]

/-- Every original clipped subband in the exponential eighth-power
cofactor budget has independently vanishing full-filter contribution
throughout the source-scale range 2/3<u<1. -/
theorem tendsto_geometric_clipped_band (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 2 / 3 < u) (hu1 : u < 1)
    (A : ℕ → ℕ) (hA : ∀ N, 1 ≤ A N)
    (hAN : ∀ N, (A N : ℝ) ^ 8 ≤ (3 * u / 2) ^ N)
    (T : ℕ → Finset ℕ)
    (hT : ∀ N n, n ∈ T N → ∃ a p : ℕ,
      1 < a ∧ a ≤ A N ∧ p.Prime ∧ ¬ p ∣ a ∧ n = p * a ∧
        n ≤ A N * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * ∑ n ∈ T N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  have hu0 : 0 < u := by linarith
  let S : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * (2 / 3 : ℝ) ^ k
  let C : ℝ := 18 * u * (1 + 1 / Real.log 4) * S
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hr : 1 < 3 * u / 2 := by linarith
  have hrinv : (3 * u / 2)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hr
  have he : (2 / 3 : ℝ) / u = (3 * u / 2)⁻¹ := by field_simp
  have ht := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ (3 * u / 2)⁻¹) hrinv)
  apply squeeze_zero_norm (fun N => ?_)
    (by simpa only [Real.sqrt_zero, mul_zero] using ht.const_mul C)
  calc
    _ ≤ 9 * u * rangeCost (A N) * A N * S * ((2 / 3 : ℝ) / u) ^ N :=
      norm_clipped_range_band_le_geometric P N (A N) y (T N) hu0 hu1.le (hT N)
    _ = (9 * u * S) * (rangeCost (A N) * A N) * ((3 * u / 2)⁻¹) ^ N := by rw [he]; ring
    _ ≤ (9 * u * S) * (2 * (1 + 1 / Real.log 4) * (A N : ℝ) ^ 4) *
        ((3 * u / 2)⁻¹) ^ N := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rangeCost_mul_le (hA N)) (by positivity)) (by positivity)
    _ = C * ((A N : ℝ) ^ 4 * ((3 * u / 2)⁻¹) ^ N) := by dsimp [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (eighth_power_geometric_budget (by linarith) (hAN N)) hC

/-- A concrete geometrically growing integer cofactor budget. The
minimum keeps it inside the original physical cutoff at every order. -/
def exponentialSchedule (u : ℝ) (N : ℕ) : ℕ :=
  min (Nat.sqrt (Nat.sqrt (Nat.sqrt ⌊(3 * u / 2) ^ N⌋₊)))
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 1)

/-- The exponential cofactor range is positive throughout its stated
source-scale regime, including every integer rounding. -/
theorem exponentialSchedule_pos {u : ℝ} (hu : 2 / 3 < u) (N : ℕ) :
    1 ≤ exponentialSchedule u N := by
  have hr : 1 ≤ 3 * u / 2 := by linarith
  have hf : 1 ≤ ⌊(3 * u / 2) ^ N⌋₊ := Nat.le_floor (by simpa using one_le_pow₀ hr (n := N))
  exact le_min (Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr hf))) (by omega)

/-- The concrete range satisfies the exponential eighth-power budget
at each order without rounding or cutoff assumptions. -/
theorem exponentialSchedule_pow_le {u : ℝ} (hu : 0 < u) (N : ℕ) :
    (exponentialSchedule u N : ℝ) ^ 8 ≤ (3 * u / 2) ^ N := by
  let Q : ℕ := ⌊(3 * u / 2) ^ N⌋₊
  have h1 := Nat.sqrt_le' (Nat.sqrt (Nat.sqrt Q))
  have h2 := Nat.sqrt_le' (Nat.sqrt Q)
  have h3 := Nat.sqrt_le' Q
  have h4 : (Nat.sqrt (Nat.sqrt (Nat.sqrt Q))) ^ 4 ≤ Nat.sqrt Q := by
    calc
      _ = ((Nat.sqrt (Nat.sqrt (Nat.sqrt Q))) ^ 2) ^ 2 := by ring
      _ ≤ (Nat.sqrt (Nat.sqrt Q)) ^ 2 := pow_le_pow_left' h1 2
      _ ≤ _ := h2
  have h8 : exponentialSchedule u N ^ 8 ≤ Q := by
    calc
      _ ≤ (Nat.sqrt (Nat.sqrt (Nat.sqrt Q))) ^ 8 := pow_le_pow_left' (min_le_left _ _) 8
      _ = ((Nat.sqrt (Nat.sqrt (Nat.sqrt Q))) ^ 4) ^ 2 := by ring
      _ ≤ (Nat.sqrt Q) ^ 2 := pow_le_pow_left' h4 2
      _ ≤ _ := h3
  exact (show (exponentialSchedule u N : ℝ) ^ 8 ≤ Q by exact_mod_cast h8).trans
    (Nat.floor_le (by positivity))

/-- The full geometric cofactor schedule grows without bound for
2/3<u<1; its physical-cutoff minimum does not freeze the range. -/
theorem exponentialSchedule_tendsto {u : ℝ} (hu : 2 / 3 < u) (hu1 : u < 1) :
    Tendsto (exponentialSchedule u) atTop atTop := by
  have hroot := nat_sqrt_tendsto.comp (nat_sqrt_tendsto.comp (nat_sqrt_tendsto.comp
    (tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt
      (show 1 < 3 * u / 2 by linarith)))))
  have hcut := (tendsto_add_atTop_nat 1).comp (tendsto_linearDampedCutoff (by linarith) hu1)
  apply tendsto_atTop.2
  intro b
  filter_upwards [hroot.eventually_ge_atTop b, hcut.eventually_ge_atTop b] with N hN hD
  exact le_min hN hD

/-- The common physical cutoff contains the entire chosen cofactor
range at every order, so large-prime cancellation has no unpaid boundary. -/
theorem exponentialSchedule_log_le_length {u : ℝ} (hu : 2 / 3 < u) (N : ℕ) :
    Real.log (exponentialSchedule u N) ≤ SquarefreeVaughanLogSource.length u N := by
  apply Real.log_le_log (by exact_mod_cast exponentialSchedule_pos hu N :
    (0 : ℝ) < exponentialSchedule u N)
  have hm : exponentialSchedule u N ≤ ZetaVaughanCutoffBudget.linearDampedCutoff u N + 1 :=
    min_le_right _ _
  have hmR : (exponentialSchedule u N : ℝ) ≤
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) + 1 := by exact_mod_cast hm
  have hD := Nat.cast_nonneg (α := ℝ) (ZetaVaughanCutoffBudget.linearDampedCutoff u N)
  change (exponentialSchedule u N : ℝ) ≤
    ((ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) + 2) ^ 2
  nlinarith

/-- The arithmetic predicate for the paid growing composite-cofactor
range, retaining the distinct prime insertion. -/
def exponentialCompositeInsertion (u : ℝ) (N n : ℕ) : Prop := ∃ a p : ℕ,
  1 < a ∧ a ≤ exponentialSchedule u N ∧ Squarefree a ∧ ¬ a.Prime ∧
    p.Prime ∧ ¬ p ∣ a ∧ n = p * a

/-- The original band with any squarefree composite cofactor in the
explicit growing range. No restriction on the inserted prime's size is added. -/
def exponentialCompositeBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter (exponentialCompositeInsertion u N)

/-- Its single common compact range, used only to prove the estimate. -/
def exponentialClippedBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  (exponentialCompositeBand u N).filter fun n => n ≤ exponentialSchedule u N *
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2

/-- The full original filter is paid on the compact part of the growing
composite-cofactor class. -/
theorem tendsto_exponential_clipped_composite_band (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 2 / 3 < u) (hu1 : u < 1) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * ∑ n ∈ exponentialClippedBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  apply tendsto_geometric_clipped_band P y hu hu1 (exponentialSchedule u)
    (exponentialSchedule_pos hu) (exponentialSchedule_pow_le (by linarith))
    (exponentialClippedBand u)
  intro N n hn
  obtain ⟨hb, hc⟩ := Finset.mem_filter.mp hn
  obtain ⟨_hband, a, p, ha, haA, _hasf, _hap, hp, hpa, he⟩ := Finset.mem_filter.mp hb
  exact ⟨a, p, ha, haA, hp, hpa, he, hc⟩

/-- Once the common cutoff contains the growing cofactor range, every
term outside the compact range is exactly zero by the complete two-moment
cancellation. Thus no additional boundary estimate is assumed. -/
theorem exponential_band_eq_clipped (P : Polynomial ℂ) (y u : ℝ) (N : ℕ)
    (hL : Real.log (exponentialSchedule u N) ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ n ∈ exponentialCompositeBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
    ∑ n ∈ exponentialClippedBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  rw [exponentialClippedBand, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with hc
  · rfl
  · obtain ⟨_hband, a, p, ha1, haA, hasf, hap, hp, hpa, rfl⟩ := Finset.mem_filter.mp hn
    have hLa : Real.log a ≤ SquarefreeVaughanLogSource.length u N :=
      (Real.log_le_log (by exact_mod_cast (show 0 < a by omega) : (0 : ℝ) < a)
        (by exact_mod_cast haA)).trans hL
    have hpa' : a * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p * a :=
      (Nat.mul_le_mul_right _ haA).trans_lt (Nat.lt_of_not_ge hc)
    have hgt : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p := by
      nlinarith
    have hLp : SquarefreeVaughanLogSource.length u N ≤ Real.log p := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hgt.le
    rw [coefficient_prime_mul_eq_zero_of_large hasf (by omega) hap hp hpa hLa hLp, zero_mul]

/-- The whole original-band contribution from the exponential-budget
composite-cofactor range has independent source-scale decay, including
its full moving cutoff, signed coefficient and polynomial factorial filter. -/
theorem tendsto_exponential_composite_band (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 2 / 3 < u) (hu1 : u < 1) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * ∑ n ∈ exponentialCompositeBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  apply (tendsto_exponential_clipped_composite_band P y hu hu1).congr'
  filter_upwards [] with N
  rw [exponential_band_eq_clipped P y u N (exponentialSchedule_log_le_length hu N)]

/-- The literal original-band complement of the independently paid
growing cofactor class. -/
def exponentialReducedBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter fun n => ¬ exponentialCompositeInsertion u N n

/-- The original carrier splits exactly across the growing cofactor
cut, retaining the same physical length and full fixed filter. -/
theorem actual_band_eq_exponential_add_reduced (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      (∑ n ∈ exponentialCompositeBand u N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      ∑ n ∈ exponentialReducedBand u N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  exact (Finset.sum_filter_add_sum_filter_not (zetaPrimeLogBand N)
    (exponentialCompositeInsertion u N) (fun n => SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)).symm

/-- After removing the exponential-budget arithmetic class, the exact
remaining band still has the original hypothetical-zero source. -/
theorem tendsto_exponential_reduced_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (hbeta : rho.1.re < 5 / 6) :
    Tendsto (fun N => (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
      ∑ n ∈ exponentialReducedBand (3 / 2 - rho.1.re) N,
        SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + Complex.I * rho.1.im) n)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 2 / 3 < (3 / 2 - rho.1.re : ℝ) := by linarith
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have h := (SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho).sub
    (tendsto_exponential_composite_band (zetaRightHalfPoleJetFilter rho hrho) rho.1.im hu hu1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by
    push_cast
    rfl
  rw [hcast, actual_band_eq_exponential_add_reduced, mul_add, add_sub_cancel_left]

/-- Every composite cofactor of a surviving prime insertion exceeds
the explicit growing threshold. Prime cofactors are deliberately excluded:
their semiprime tails remain in the original source. -/
theorem surviving_exponential_cofactor_gt {u : ℝ} {N n a p : ℕ}
    (hn : n ∈ exponentialReducedBand u N) (ha1 : 1 < a) (hasf : Squarefree a)
    (hap : ¬ a.Prime) (hp : p.Prime) (hpa : ¬ p ∣ a) (he : n = p * a) :
    exponentialSchedule u N < a := by
  have hnot := (Finset.mem_filter.mp hn).2
  by_contra hsmall
  exact hnot ⟨a, p, ha1, by omega, hasf, hap, hp, hpa, he⟩

/-- The original damped inverse-source cutoff eventually exceeds every
fixed power of the factorial order, with its damping retained. -/
theorem eventually_pow_le_cutoff {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, N ^ k ≤ ZetaVaughanCutoffBudget.linearDampedCutoff u N := by
  have ht := ((tendsto_pow_const_mul_const_pow_of_lt_one (k + 1) hu.le hu1).comp
    (tendsto_add_atTop_nat 1)).div_const u
  have hzero : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (k + 1) * u ^ N) atTop (𝓝 0) := by
    convert ht using 1
    · funext N
      simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
    · simp
  filter_upwards [hzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN
  apply Nat.le_floor
  change ((N ^ k : ℕ) : ℝ) ≤ u⁻¹ ^ N / (N + 1)
  rw [Nat.cast_pow]
  rw [le_div_iff₀ (by positivity), inv_pow, ← one_div, le_div_iff₀ (by positivity)]
  have hp : (N : ℝ) ^ k ≤ ((N : ℝ) + 1) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg N) (by linarith) k
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp
    (by positivity : (0 : ℝ) ≤ N + 1)) (pow_pos hu N).le
  rw [← pow_succ] at hm
  exact hm.trans hN.le

/-- The explicit geometric cofactor schedule eventually dominates every
fixed polynomial range, even after the original-cutoff minimum. -/
theorem eventually_pow_le_exponentialSchedule {u : ℝ}
    (hu : 2 / 3 < u) (hu1 : u < 1) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, N ^ k ≤ exponentialSchedule u N := by
  have hu0 : 0 < u := by linarith
  have hr : 1 < 3 * u / 2 := by linarith
  have hr0 : 0 < 3 * u / 2 := by linarith
  have ht := tendsto_pow_const_mul_const_pow_of_lt_one (k * 8)
    (inv_nonneg.mpr hr0.le) ((inv_lt_one₀ hr0).mpr hr)
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_pow_le_cutoff hu0 hu1 k] with N hN hD
  apply le_min _ (hD.trans (Nat.le_succ _))
  rw [Nat.le_sqrt', Nat.le_sqrt', Nat.le_sqrt']
  apply Nat.le_floor
  simp only [Nat.cast_pow, ← pow_mul]
  have hc : (3 * u / 2)⁻¹ ^ N * (3 * u / 2) ^ N = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr0.ne', one_pow]
  have hm := mul_le_mul_of_nonneg_right hN.le (pow_pos hr0 N).le
  rw [mul_assoc, hc, mul_one, one_mul] at hm
  convert hm using 1; ring

/-- A pointwise geometric bound for the entire actual exponential-budget
composite-cofactor class, including all prime sizes and the full filter. -/
theorem norm_exponential_composite_band_le (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 2 / 3 < u) (hu1 : u ≤ 1) (N : ℕ) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ exponentialCompositeBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      18 * u * (1 + 1 / Real.log 4) *
        (∑ k ∈ P.support, ‖P.coeff k‖ * (2 / 3 : ℝ) ^ k) *
          Real.sqrt ((3 * u / 2)⁻¹ ^ N) := by
  have hu0 : 0 < u := by linarith
  let S : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * (2 / 3 : ℝ) ^ k
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have he : (2 / 3 : ℝ) / u = (3 * u / 2)⁻¹ := by field_simp
  rw [exponential_band_eq_clipped P y u N (exponentialSchedule_log_le_length hu N)]
  have hb := norm_clipped_range_band_le_geometric P N (exponentialSchedule u N) y
    (exponentialClippedBand u N) hu0 hu1 (fun n hn => by
      obtain ⟨hb, hc⟩ := Finset.mem_filter.mp hn
      obtain ⟨_hband, a, p, ha, haA, _hasf, _hap, hp, hpa, he⟩ := Finset.mem_filter.mp hb
      exact ⟨a, p, ha, haA, hp, hpa, he, hc⟩)
  calc
    _ ≤ 9 * u * rangeCost (exponentialSchedule u N) * exponentialSchedule u N * S *
        ((2 / 3 : ℝ) / u) ^ N := hb
    _ = (9 * u * S) * (rangeCost (exponentialSchedule u N) * exponentialSchedule u N) *
        ((3 * u / 2)⁻¹) ^ N := by rw [he]; ring
    _ ≤ (9 * u * S) * (2 * (1 + 1 / Real.log 4) * (exponentialSchedule u N : ℝ) ^ 4) *
        ((3 * u / 2)⁻¹) ^ N := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rangeCost_mul_le (exponentialSchedule_pos hu N))
          (by positivity)) (by positivity)
    _ = (18 * u * (1 + 1 / Real.log 4) * S) *
        ((exponentialSchedule u N : ℝ) ^ 4 * ((3 * u / 2)⁻¹) ^ N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (eighth_power_geometric_budget (by positivity) (exponentialSchedule_pow_le hu0 N))
        (by positivity)

/-- The stronger geometric cofactor class is used where it is paid;
the proved universal eighth-root class supplies every other source scale. -/
def adaptiveCompositeBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  if 2 / 3 < u then exponentialCompositeBand u N else growingCompositeBand N

/-- The exact complementary original band for the adaptive deletion. -/
def adaptiveReducedBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  if 2 / 3 < u then exponentialReducedBand u N else growingReducedBand N

/-- The adaptive deletion has independent full-filter decay on the
entire source-scale interval, with no zero-location premise. -/
theorem tendsto_adaptive_composite_band (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * ∑ n ∈ adaptiveCompositeBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  by_cases h : 2 / 3 < u
  · simpa only [adaptiveCompositeBand, if_pos h] using
      tendsto_exponential_composite_band P y h hu1
  · simpa only [adaptiveCompositeBand, if_neg h] using
      tendsto_growing_composite_band P y hu hu1

/-- The two actual bands partition the original carrier exactly at
every scale, including the transition where the geometric estimate stops. -/
theorem actual_band_eq_adaptive_add_reduced (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      (∑ n ∈ adaptiveCompositeBand u N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      ∑ n ∈ adaptiveReducedBand u N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  by_cases h : 2 / 3 < u
  · simpa only [adaptiveCompositeBand, adaptiveReducedBand, if_pos h] using
      actual_band_eq_exponential_add_reduced P N y L u
  · simpa only [adaptiveCompositeBand, adaptiveReducedBand, if_neg h] using
      actual_band_eq_growing_add_reduced P N y L

/-- Every hypothetical right-half zero retains the same source after
the adaptive arithmetic deletion. The geometric gain in the inner strip
is combined with the universal polynomial range, without excluding zeros. -/
theorem tendsto_adaptive_reduced_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N => (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
      ∑ n ∈ adaptiveReducedBand (3 / 2 - rho.1.re) N,
        SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + Complex.I * rho.1.im) n)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have h := (SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho).sub
    (tendsto_adaptive_composite_band (zetaRightHalfPoleJetFilter rho hrho) rho.1.im hu hu1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by
    push_cast
    rfl
  rw [hcast, actual_band_eq_adaptive_add_reduced, mul_add, add_sub_cancel_left]

end
end RiemannGaussian.ZetaRieszExponentialCofactor
