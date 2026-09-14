/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFixedCofactor

/-!
# Growing cofactor arithmetic decay

An explicit unbounded cofactor schedule has a vanishing allowance at the
original source scale. Complete divisor mass and log-moment cancellation
remove every term above its compact range. The entire growing class can
therefore be deleted without changing the hypothetical-zero source.
The surviving semiprimes and larger composite cofactors retain their signs,
phases, original band and full fixed factorial filter. Their joint floor
remains open. The eighth-root schedule is sufficient, not claimed optimal.
-/

namespace RiemannGaussian.ZetaRieszGrowingCofactor
noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius Topology
open Filter ZetaRieszFixedCofactor

/-- A uniform finite-size estimate for the preserved cofactor cost. -/
theorem divisorLogMass_le_mul_log (a : ℕ) : divisorLogMass a ≤ a * Real.log a := by
  by_cases ha : a = 0
  · subst a
    simp [divisorLogMass]
  calc
    _ ≤ ∑ d ∈ a.divisors, Real.log a := by
      apply Finset.sum_le_sum
      intro d hd
      have hmu : |((μ d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hlog : Real.log d ≤ Real.log a := Real.log_le_log
        (by exact_mod_cast Nat.pos_of_mem_divisors hd : (0 : ℝ) < d)
        (by exact_mod_cast (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) (Nat.dvd_of_mem_divisors hd)))
      exact (mul_le_mul_of_nonneg_right hmu (Real.log_natCast_nonneg d)).trans
        (by simpa only [one_mul] using hlog)
    _ = (a.divisors.card : ℝ) * Real.log a := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self a)
      (Real.log_natCast_nonneg a)

/-- The finite-size bound is uniform over the entire cofactor interval. -/
theorem divisorLogMass_le_range {a A : ℕ} (ha : 0 < a) (haA : a ≤ A) :
    divisorLogMass a ≤ A * Real.log A := by
  apply (divisorLogMass_le_mul_log a).trans
  exact mul_le_mul (by exact_mod_cast haA)
    (Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast haA))
    (Real.log_natCast_nonneg a) (Nat.cast_nonneg A)

/-- Explicit coefficient cost for any cofactor in a finite size range;
the range may later depend on the factorial order. -/
def rangeCost (A : ℕ) : ℝ := 2 * (A : ℝ) * Real.log A *
  (1 + Real.log A / Real.log 4)

/-- The uniform range cost is nonnegative at every natural endpoint. -/
theorem rangeCost_nonneg (A : ℕ) : 0 ≤ rangeCost A := by
  unfold rangeCost
  have hlog := Real.log_natCast_nonneg A
  have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  positivity

/-- On the actual damped squared range, one fixed coefficient allowance
controls every prime insertion with nonunit cofactor at most A. -/
theorem norm_coefficient_le_range (u : ℝ) (N : ℕ) {a p A : ℕ}
    (ha : 1 < a) (haA : a ≤ A) (hp : p.Prime) (hpa : ¬ p ∣ a)
    (hc : p * a ≤ A * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ‖SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u N) (p * a)‖ ≤ rangeCost A := by
  have hb := norm_coefficient_prime_mul_le (SquarefreeVaughanLogSource.length_pos u N)
    (Real.log_pos (by norm_num)) (length_ge_log_four u N) (by omega) hp hpa
    (Real.log_natCast_nonneg A)
    (log_le_length_add_log (by omega) (Nat.mul_pos hp.pos (by omega)) u N hc)
  apply hb.trans
  unfold rangeCost
  rw [mul_assoc 2 (A : ℝ) (Real.log A)]
  apply mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (divisorLogMass_le_range (by omega) haA) (by norm_num))
  have hlog := Real.log_natCast_nonneg A
  have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  positivity

/-- A bound for every prime-insertion subband in a variable cofactor
range, after the actual complete factorial filter and source normalization.
Whether a chosen growing range makes this explicit allowance vanish is
a separate numerical-exponent estimate, not a hypothesis hidden here. -/
theorem norm_clipped_range_band_le (P : Polynomial ℂ) (N A : ℕ) (y : ℝ)
    (T : Finset ℕ) {u : ℝ} (hu : 0 < u)
    (hT : ∀ n ∈ T, ∃ a p : ℕ, 1 < a ∧ a ≤ A ∧ p.Prime ∧ ¬ p ∣ a ∧ n = p * a ∧
      n ≤ A * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ T,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (2 * rangeCost A * (∑ k ∈ P.support, ‖P.coeff k‖) * Real.sqrt A) *
        (u / (N + 1) + 2 * u ^ (N + 1)) := by
  apply norm_sum_filter_square_cutoff_le P N A y T
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
    (rangeCost_nonneg A) hu
  · intro n hn
    obtain ⟨a, p, ha, _haA, hp, _hpa, rfl, hc⟩ := hT n hn
    exact ⟨Nat.mul_pos hp.pos (by omega), hc⟩
  · intro n hn
    obtain ⟨a, p, ha, haA, hp, hpa, rfl, hc⟩ := hT n hn
    exact norm_coefficient_le_range u N ha haA hp hpa hc

/-- A coarse polynomial envelope for the complete cofactor-range cost,
including the square-root spatial mass. -/
theorem rangeCost_mul_sqrt_le {A : ℕ} (hA : 1 ≤ A) :
    rangeCost A * Real.sqrt A ≤ 2 * (1 + 1 / Real.log 4) * (A : ℝ) ^ 4 := by
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hl := Real.log_le_self (Nat.cast_nonneg A)
  have hl0 := Real.log_natCast_nonneg A
  have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hs : Real.sqrt A ≤ A := Real.sqrt_le_self_iff.mpr (Or.inr hA1)
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

/-- The eighth-power range condition pays both the inverse-order term
and the geometric term in one explicit allowance. -/
theorem eighth_power_budget {A N : ℕ} (hAN : A ^ 8 ≤ N + 1)
    {u : ℝ} (hu : 0 < u) :
    (A : ℝ) ^ 4 * (u / (N + 1) + 2 * u ^ (N + 1)) ≤
      u / Real.sqrt (N + 1) + 2 * (N + 1) * u ^ (N + 1) := by
  have hpow : ((A : ℝ) ^ 4) ^ 2 ≤ (N : ℝ) + 1 := by
    rw [← pow_mul]
    norm_num only [Nat.reduceMul]
    exact_mod_cast hAN
  have hs : (A : ℝ) ^ 4 ≤ Real.sqrt (N + 1) := Real.le_sqrt_of_sq_le hpow
  have hsN : Real.sqrt (N + 1) ≤ (N : ℝ) + 1 :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by have := Nat.cast_nonneg (α := ℝ) N; linarith))
  have hA4N := hs.trans hsN
  have hsqrt : 0 < Real.sqrt (N + 1) := Real.sqrt_pos.mpr (by positivity)
  have he : u * Real.sqrt (N + 1) / (N + 1) = u / Real.sqrt (N + 1) := by
    have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ N + 1 by positivity)
    field_simp
    nlinarith
  calc
    _ = u * (A : ℝ) ^ 4 / (N + 1) + 2 * (A : ℝ) ^ 4 * u ^ (N + 1) := by ring
    _ ≤ u * Real.sqrt (N + 1) / (N + 1) + 2 * (N + 1) * u ^ (N + 1) := by
      apply add_le_add
      · gcongr
      · gcongr
    _ = _ := by rw [he]

/-- The explicit eighth-power allowance tends to zero at every fixed
source scale in (0,1), independently of the cofactor schedule. -/
theorem tendsto_eighth_power_allowance {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => u / Real.sqrt (N + 1) + 2 * (N + 1) * u ^ (N + 1))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hd := (Real.tendsto_sqrt_atTop.comp hn).const_div_atTop u
  have hp := ((tendsto_self_mul_const_pow_of_lt_one hu.le hu1).comp
    (tendsto_add_atTop_nat 1)).const_mul 2
  convert hd.add hp using 1
  · funext N
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
    ring
  · simp

/-- Every actual clipped subband whose cofactor range obeys A_N^8<=N+1
has vanishing full-filter source-normalized contribution. The range is
allowed to grow; no prime cancellation or unproved analytic bound is assumed. -/
theorem tendsto_eighth_power_clipped_band (P : Polynomial ℂ) (y : ℝ)
    (A : ℕ → ℕ) (hA : ∀ N, 1 ≤ A N) (hAN : ∀ N, A N ^ 8 ≤ N + 1)
    (T : ℕ → Finset ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hT : ∀ N n, n ∈ T N → ∃ a p : ℕ,
      1 < a ∧ a ≤ A N ∧ p.Prime ∧ ¬ p ∣ a ∧ n = p * a ∧
        n ≤ A N * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * ∑ n ∈ T N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  let S : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖
  let C : ℝ := 4 * (1 + 1 / Real.log 4) * S
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply squeeze_zero_norm (fun N => ?_)
    (by simpa only [mul_zero] using (tendsto_eighth_power_allowance hu hu1).const_mul C)
  have hb := norm_clipped_range_band_le P N (A N) y (T N) hu (hT N)
  calc
    _ ≤ (2 * rangeCost (A N) * S * Real.sqrt (A N)) *
        (u / (N + 1) + 2 * u ^ (N + 1)) := hb
    _ = (2 * S * (rangeCost (A N) * Real.sqrt (A N))) *
        (u / (N + 1) + 2 * u ^ (N + 1)) := by ring
    _ ≤ (2 * S * (2 * (1 + 1 / Real.log 4) * (A N : ℝ) ^ 4)) *
        (u / (N + 1) + 2 * u ^ (N + 1)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rangeCost_mul_sqrt_le (hA N)) (by positivity))
        (by positivity)
    _ = C * ((A N : ℝ) ^ 4 * (u / (N + 1) + 2 * u ^ (N + 1))) := by dsimp [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (eighth_power_budget (hAN N) hu) hC

/-- A concrete cofactor range growing like the eighth root of the
factorial order, with every integer rounding retained. -/
def eighthRootSchedule (N : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt (N + 1)))

/-- The concrete cofactor range is always nonempty. -/
theorem eighthRootSchedule_pos (N : ℕ) : 1 ≤ eighthRootSchedule N :=
  Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr (by omega)))

/-- Every rounding in the concrete range preserves the paid eighth-power budget. -/
theorem eighthRootSchedule_pow_le (N : ℕ) : eighthRootSchedule N ^ 8 ≤ N + 1 := by
  have h1 := Nat.sqrt_le' (Nat.sqrt (Nat.sqrt (N + 1)))
  have h2 := Nat.sqrt_le' (Nat.sqrt (N + 1))
  have h3 := Nat.sqrt_le' (N + 1)
  have h4 : eighthRootSchedule N ^ 4 ≤ Nat.sqrt (N + 1) := by
    calc
      _ = (eighthRootSchedule N ^ 2) ^ 2 := by ring
      _ ≤ (Nat.sqrt (Nat.sqrt (N + 1))) ^ 2 := pow_le_pow_left' h1 2
      _ ≤ _ := h2
  calc
    _ = (eighthRootSchedule N ^ 4) ^ 2 := by ring
    _ ≤ (Nat.sqrt (N + 1)) ^ 2 := pow_le_pow_left' h4 2
    _ ≤ _ := h3

/-- The natural square-root map is cofinal. -/
theorem nat_sqrt_tendsto : Tendsto Nat.sqrt atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  exact (eventually_ge_atTop (b * b)).mono fun n hn => Nat.le_sqrt.mpr hn

/-- The paid range really grows without bound; it is not a fixed finite head. -/
theorem eighthRootSchedule_tendsto : Tendsto eighthRootSchedule atTop atTop :=
  nat_sqrt_tendsto.comp (nat_sqrt_tendsto.comp
    (nat_sqrt_tendsto.comp (tendsto_add_atTop_nat 1)))

/-- The original clipped prime-insertion band has independently vanishing
full-filter mass for this explicit unbounded cofactor schedule. -/
theorem tendsto_concrete_growing_clipped_band (P : Polynomial ℂ) (y : ℝ)
    (T : ℕ → Finset ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hT : ∀ N n, n ∈ T N → ∃ a p : ℕ,
      1 < a ∧ a ≤ eighthRootSchedule N ∧ p.Prime ∧ ¬ p ∣ a ∧ n = p * a ∧
        n ≤ eighthRootSchedule N * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * ∑ n ∈ T N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) :=
  tendsto_eighth_power_clipped_band P y eighthRootSchedule eighthRootSchedule_pos
    eighthRootSchedule_pow_le T hu hu1 hT

/-- The damped inverse-source cutoff eventually exceeds the moment
order itself; the polynomial damping cannot defeat its exponential growth. -/
theorem eventually_order_le_cutoff {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∀ᶠ N : ℕ in atTop, N ≤ ZetaVaughanCutoffBudget.linearDampedCutoff u N := by
  have h2 := ((tendsto_pow_const_mul_const_pow_of_lt_one 2 hu.le hu1).comp
    (tendsto_add_atTop_nat 1)).div_const u
  have hzero : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ 2 * u ^ N) atTop (𝓝 0) := by
    convert h2 using 1
    · funext N
      simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
    · simp
  filter_upwards [hzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN
  apply Nat.le_floor
  change (N : ℝ) ≤ u⁻¹ ^ N / (N + 1)
  rw [le_div_iff₀ (by positivity), inv_pow, ← one_div, le_div_iff₀ (by positivity)]
  nlinarith [pow_pos hu N, mul_nonneg (Nat.cast_nonneg N) (pow_pos hu N).le]

/-- The explicit growing cofactor range eventually lies inside the
same original physical logarithmic cutoff. -/
theorem eventually_schedule_log_le_length {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∀ᶠ N in atTop, Real.log (eighthRootSchedule N) ≤ SquarefreeVaughanLogSource.length u N := by
  filter_upwards [eventually_order_le_cutoff hu hu1] with N hN
  have hA : eighthRootSchedule N ≤ N + 1 :=
    (Nat.sqrt_le_self _).trans ((Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _))
  apply Real.log_le_log (by exact_mod_cast eighthRootSchedule_pos N :
    (0 : ℝ) < eighthRootSchedule N)
  have hAR : (eighthRootSchedule N : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hA
  have hNR : (N : ℝ) ≤ ZetaVaughanCutoffBudget.linearDampedCutoff u N := by exact_mod_cast hN
  have hD := Nat.cast_nonneg (α := ℝ) (ZetaVaughanCutoffBudget.linearDampedCutoff u N)
  nlinarith

/-- The arithmetic predicate for the paid growing composite-cofactor
range, retaining the distinct prime insertion. -/
def growingCompositeInsertion (N n : ℕ) : Prop := ∃ a p : ℕ,
  1 < a ∧ a ≤ eighthRootSchedule N ∧ Squarefree a ∧ ¬ a.Prime ∧
    p.Prime ∧ ¬ p ∣ a ∧ n = p * a

/-- The original band with any squarefree composite cofactor in the
explicit growing range. No restriction on the inserted prime's size is added. -/
def growingCompositeBand (N : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter (growingCompositeInsertion N)

/-- Its single common compact range, used only to prove the estimate. -/
def growingClippedBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  (growingCompositeBand N).filter fun n => n ≤ eighthRootSchedule N *
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2

/-- The full original filter is paid on the compact part of the growing
composite-cofactor class. -/
theorem tendsto_growing_clipped_composite_band (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * ∑ n ∈ growingClippedBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  apply tendsto_concrete_growing_clipped_band P y (growingClippedBand u) hu hu1
  intro N n hn
  obtain ⟨hb, hc⟩ := Finset.mem_filter.mp hn
  obtain ⟨_hband, a, p, ha, haA, _hasf, _hap, hp, hpa, he⟩ := Finset.mem_filter.mp hb
  exact ⟨a, p, ha, haA, hp, hpa, he, hc⟩

/-- Once the common cutoff contains the growing cofactor range, every
term outside the compact range is exactly zero by the complete two-moment
cancellation. Thus no additional boundary estimate is assumed. -/
theorem growing_band_eq_clipped (P : Polynomial ℂ) (y u : ℝ) (N : ℕ)
    (hL : Real.log (eighthRootSchedule N) ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ n ∈ growingCompositeBand N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
    ∑ n ∈ growingClippedBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  rw [growingClippedBand, Finset.sum_filter]
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

/-- The whole original-band contribution from the explicitly unbounded
composite-cofactor range has independent source-scale decay, including
its full moving cutoff, signed coefficient and polynomial factorial filter. -/
theorem tendsto_growing_composite_band (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * ∑ n ∈ growingCompositeBand N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  apply (tendsto_growing_clipped_composite_band P y hu hu1).congr'
  filter_upwards [eventually_schedule_log_le_length hu hu1] with N hN
  rw [growing_band_eq_clipped P y u N hN]

/-- The literal original-band complement of the independently paid
growing cofactor class. -/
def growingReducedBand (N : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter fun n => ¬ growingCompositeInsertion N n

/-- The original carrier splits exactly across the growing cofactor
cut, retaining the same physical length and full fixed filter. -/
theorem actual_band_eq_growing_add_reduced (P : Polynomial ℂ) (N : ℕ) (y L : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      (∑ n ∈ growingCompositeBand N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      ∑ n ∈ growingReducedBand N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  exact (Finset.sum_filter_add_sum_filter_not (zetaPrimeLogBand N)
    (growingCompositeInsertion N) (fun n => SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)).symm

/-- After removing the explicitly growing arithmetic class, the exact
remaining band still has the original hypothetical-zero source. -/
theorem tendsto_growing_reduced_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N => (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
      ∑ n ∈ growingReducedBand N,
        SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + Complex.I * rho.1.im) n)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have h := (SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho).sub
    (tendsto_growing_composite_band (zetaRightHalfPoleJetFilter rho hrho) rho.1.im hu hu1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by
    push_cast
    rfl
  rw [hcast, actual_band_eq_growing_add_reduced, mul_add, add_sub_cancel_left]

/-- Every composite cofactor of a surviving prime insertion exceeds
the explicit growing threshold. Prime cofactors are deliberately excluded:
their semiprime tails remain in the original source. -/
theorem surviving_composite_cofactor_gt {N n a p : ℕ}
    (hn : n ∈ growingReducedBand N) (ha1 : 1 < a) (hasf : Squarefree a)
    (hap : ¬ a.Prime) (hp : p.Prime) (hpa : ¬ p ∣ a) (he : n = p * a) :
    eighthRootSchedule N < a := by
  have hnot := (Finset.mem_filter.mp hn).2
  by_contra hsmall
  exact hnot ⟨a, p, ha1, by omega, hasf, hap, hp, hpa, he⟩

end
end RiemannGaussian.ZetaRieszGrowingCofactor
