/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeVaughanProjection
import RiemannGaussian.ZetaSquarefreeEulerPrimeInsertion

/-!
# Retaining the logarithmic cancellation in the projected Vaughan prefix

The physical logarithm and the marked divisor logarithm must be combined
before taking norms. Their exact difference removes the leading derivative
of the mark, leaving a prime incidence with two local Euler atoms. Averaging
that complete incidence has a summable prime cost on the closed half-plane
`Re(s) >= 1/2`.

The full projected small part therefore has the original square-root
product budget for every cutoff pair. Independent nonsquarefree deletion
extends to all schedules with a vanishing normalized budget. Every moving
finite probability mixture in the admissible hyperbolic cutoff region
retains the conditional negative-multiplicity source in the original
squarefree finite band. No independent signed floor or RH proof follows.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius LSeries.notation

namespace RiemannGaussian.SquarefreeVaughanBudget
noncomputable section
open SquarefreeEulerQuadratic SquarefreeVaughanProjection

/-- The complete local logarithmic correction belonging to a squarefree mark. -/
def markLog (a : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ a.primeFactors, (Real.log p : ℂ) * atom s p

/-- The physical logarithm minus the divisor logarithm, in its exact
analytic form. There is no division by the squarefree quotient. -/
def markedLogResponse (a : ℕ) (s : ℂ) : ℂ :=
  -(atom s a * deriv squarefreeEulerResponse s) -
    atom s a * squarefreeEulerResponse s * markLog a s

private theorem atom_eq_multiplier {a : ℕ} (ha : Squarefree a) (s : ℂ) :
    atom s a = squarefreeEulerMultiplier ∅ a s := by
  rw [atom_eq_feature_product ha]
  simp only [squarefreeEulerMultiplier, Finset.empty_union]

/-- The divisor logarithm cancels exactly against the leading local
derivative. Both prime phases and every residual local factor remain. -/
theorem markedLogResponse_eq {a : ℕ} (ha : Squarefree a) {s : ℂ}
    (hs : 0 < s.re) (hQ : AnalyticAt ℂ squarefreeEulerResponse s) :
    markedLogResponse a s =
      -deriv (fun z ↦ atom z a * squarefreeEulerResponse z) s -
        (Real.log a : ℂ) * (atom s a * squarefreeEulerResponse s) := by
  have hl : (∑ p ∈ a.primeFactors, (Real.log p : ℂ)) = (Real.log a : ℂ) := by
    have h := congrArg (fun n : ℕ ↦ Real.log n) (Nat.prod_primeFactors_of_squarefree ha)
    rw [Nat.cast_prod, Real.log_prod (fun p hp ↦ by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)] at h
    exact_mod_cast h
  have hd := (atom_hasDerivAt ha.ne_zero hs).mul hQ.differentiableAt.hasDerivAt
  change HasDerivAt (fun z ↦ atom z a * squarefreeEulerResponse z) _ s at hd
  rw [hd.deriv, markedLogResponse]
  have he : (∑ p ∈ a.primeFactors, (Real.log p : ℂ) * (1 - atom s p)) =
      (Real.log a : ℂ) - markLog a s := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hl, markLog]
  rw [he]
  ring

/-- Prime incidence is an exact coprime dilation of the squarefree prefix. -/
theorem squarefree_multiples_eq_image (U : ℕ) {p : ℕ} (hp : p.Prime) :
    ((Finset.Icc 1 U).filter Squarefree).filter (fun a ↦ p ∣ a) =
      (((Finset.Icc 1 (U / p)).filter Squarefree).filter (fun m ↦ p.Coprime m)).image
        (fun m ↦ p * m) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨ha0, haU⟩, hsf⟩, hpa⟩
    have he : p * (a / p) = a := Nat.mul_div_cancel' hpa
    have hsfp : Squarefree (p * (a / p)) := he.symm ▸ hsf
    exact ⟨a / p, ⟨⟨⟨Nat.div_pos (Nat.le_of_dvd ha0 hpa) hp.pos,
      Nat.div_le_div_right haU⟩, hsfp.of_mul_right⟩,
      Nat.coprime_of_squarefree_mul hsfp⟩, he⟩
  · rintro ⟨m, ⟨⟨⟨hm0, hmU⟩, hsf⟩, hcop⟩, rfl⟩
    refine ⟨⟨⟨Nat.mul_pos hp.pos hm0, ?_⟩,
      (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hsf⟩⟩, dvd_mul_right p m⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hmU

/-- A marked-prime subfamily pays for its true coprime dilation,
before dropping the coprimality condition in the upper bound. -/
theorem sum_squarefree_prime_multiples_le (U : ℕ) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    (∑ a ∈ ((Finset.Icc 1 U).filter Squarefree).filter (fun a ↦ p ∣ a), ‖atom s a‖) ≤
      ‖atom s p‖ * (2 * Real.sqrt (U / p : ℕ) * divisorSquareDirichletMass (3 / 2)) := by
  rw [squarefree_multiples_eq_image U hp,
    Finset.sum_image (fun a _ b _ hab ↦ Nat.eq_of_mul_eq_mul_left hp.pos hab)]
  calc
    _ = ‖atom s p‖ *
        ∑ m ∈ ((Finset.Icc 1 (U / p)).filter Squarefree).filter (fun m ↦ p.Coprime m),
          ‖atom s m‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [(atom_multiplicative s).map_mul_of_coprime (Finset.mem_filter.mp hm).2, norm_mul]
    _ ≤ ‖atom s p‖ * ∑ m ∈ (Finset.Icc 1 (U / p)).filter Squarefree, ‖atom s m‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_squarefree_norm_atom_le (U / p) hs)
      (norm_nonneg _)

private theorem sqrt_div_nat_le (U : ℕ) {p : ℕ} (hp : 0 < p) :
    Real.sqrt (U / p : ℕ) ≤ Real.sqrt U / Real.sqrt p := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hp))).mpr
  rw [← Real.sqrt_mul (Nat.cast_nonneg (U / p))]
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.div_mul_le_self U p

private theorem exp_weight_three_halves {p : ℕ} (hp : 0 < p) :
    zetaPrimeExpWeight (3 / 2) p = 1 / ((p : ℝ) * Real.sqrt p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [zetaPrimeExpWeight, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpR,
    show -(3 / 2 : ℝ) * Real.log p = -(Real.log p + Real.log p * (1 / 2)) by ring,
    Real.exp_neg, Real.exp_add, Real.exp_log hpR, one_div]
  simp only [one_div]

private theorem primeFactors_eq_filter (U : ℕ) {a : ℕ}
    (ha : a ∈ (Finset.Icc 1 U).filter Squarefree) :
    a.primeFactors = (zetaSquarePrimesThrough U).filter (fun p ↦ p ∣ a) := by
  have ha0 : 0 < a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
  have haU : a ≤ U := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
  ext p
  simp only [Nat.mem_primeFactors, zetaSquarePrimesThrough, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨hp, hpa, _⟩
    exact ⟨⟨⟨hp.pos, (Nat.le_of_dvd ha0 hpa).trans haU⟩, hp⟩, hpa⟩
  · rintro ⟨⟨_, hp⟩, hpa⟩
    exact ⟨hp, hpa, ha0.ne'⟩

/-- Averaging the complete logarithmic correction retains two copies
of its prime atom. The resulting prime mass is genuinely summable. -/
theorem exists_markLog_average_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℕ) (s : ℂ), 1 / 2 ≤ s.re →
      (∑ a ∈ (Finset.Icc 1 U).filter Squarefree, ‖atom s a‖ * ‖markLog a s‖) ≤
        C * Real.sqrt U := by
  let M := divisorSquareDirichletMass (3 / 2)
  let P := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * zetaPrimeExpWeight (3 / 2) n
  have hM : 0 ≤ M := divisorSquareDirichletMass_nonneg _
  have hsum : Summable (fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * zetaPrimeExpWeight (3 / 2) n) :=
    summable_zetaPrimeExpWeight_mul ArithmeticFunction.vonMangoldt (by simp)
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  have hP : 0 ≤ P := tsum_nonneg (fun n ↦ mul_nonneg
    ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le)
  refine ⟨32 * M * P + 1, by positivity, ?_⟩
  intro U s hs
  let T := (Finset.Icc 1 U).filter Squarefree
  let S := zetaSquarePrimesThrough U
  have hnorm (a : ℕ) (ha : a ∈ T) :
      ‖markLog a s‖ ≤ ∑ p ∈ S, if p ∣ a then Real.log p * ‖atom s p‖ else 0 := by
    rw [markLog]
    apply (norm_sum_le _ _).trans_eq
    simp only [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_natCast_nonneg _)]
    rw [primeFactors_eq_filter U ha, Finset.sum_filter]
  have hprime (p : ℕ) (hp : p ∈ S) :
      (Real.log p * ‖atom s p‖) *
        (∑ a ∈ T.filter (fun a ↦ p ∣ a), ‖atom s a‖) ≤
      (32 * M * Real.sqrt U) *
        (ArithmeticFunction.vonMangoldt p * zetaPrimeExpWeight (3 / 2) p) := by
    have hpr : p.Prime := (Finset.mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    have hpS : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
    calc
      _ ≤ (Real.log p * ‖atom s p‖) *
          (‖atom s p‖ * (2 * Real.sqrt (U / p : ℕ) * M)) :=
        mul_le_mul_of_nonneg_left (sum_squarefree_prime_multiples_le U hpr hs) (by positivity)
      _ ≤ (Real.log p * (4 / Real.sqrt p)) *
          ((4 / Real.sqrt p) * (2 * (Real.sqrt U / Real.sqrt p) * M)) := by
        gcongr
        · exact norm_prime_atom_le hs hpr
        · exact norm_prime_atom_le hs hpr
        · exact sqrt_div_nat_le U hpr.pos
      _ = _ := by
        rw [ArithmeticFunction.vonMangoldt_apply_prime hpr, exp_weight_three_halves hpr.pos]
        field_simp
        rw [Real.sq_sqrt hp0.le]
        ring
  calc
    _ ≤ ∑ a ∈ T, ‖atom s a‖ *
        ∑ p ∈ S, if p ∣ a then Real.log p * ‖atom s p‖ else 0 := by
      exact Finset.sum_le_sum (fun a ha ↦ mul_le_mul_of_nonneg_left (hnorm a ha) (norm_nonneg _))
    _ = ∑ p ∈ S, (Real.log p * ‖atom s p‖) *
        ∑ a ∈ T.filter (fun a ↦ p ∣ a), ‖atom s a‖ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      conv_rhs => rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> ring
    _ ≤ ∑ p ∈ S, (32 * M * Real.sqrt U) *
        (ArithmeticFunction.vonMangoldt p * zetaPrimeExpWeight (3 / 2) p) :=
      Finset.sum_le_sum hprime
    _ = (32 * M * Real.sqrt U) * ∑ p ∈ S,
        ArithmeticFunction.vonMangoldt p * zetaPrimeExpWeight (3 / 2) p :=
      (Finset.mul_sum ..).symm
    _ ≤ (32 * M * Real.sqrt U) * P := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hsum.sum_le_tsum S (fun _ _ ↦ mul_nonneg
        ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le)
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg (U : ℝ)]

/-- The full weighted analytic logarithmic prefix, before any norm. -/
def headResponse (U : ℕ) (w : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ a ∈ (Finset.Icc 1 U).filter Squarefree, w a * markedLogResponse a s

/-- The literal squarefree divisor family with its cofactor logarithm. -/
def headCoefficient (U : ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ (Finset.Icc 1 U).filter Squarefree, w a *
    RoughSquarefreeBare.coefficient ∅ a n * ((Real.log n : ℂ) - (Real.log a : ℂ))

private theorem analyticAt_atom {a : ℕ} (ha : Squarefree a) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z ↦ atom z a) s := by
  have he : (fun z ↦ atom z a) = squarefreeEulerMultiplier ∅ a := funext (atom_eq_multiplier ha)
  rw [he]
  exact analyticAt_squarefreeEulerMultiplier ∅ (by simp) a hs

/-- All logarithmic corrections are analytic on the positive half-plane. -/
theorem analyticAt_markLog (a : ℕ) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (markLog a) s := by
  apply Finset.analyticAt_fun_sum
  intro p hp
  exact analyticAt_const.mul (analyticAt_atom (Nat.prime_of_mem_primeFactors hp).squarefree hs)

/-- The full signed prefix remains analytic through zeros of the quotient;
the construction never uses its logarithmic derivative. -/
theorem analyticAt_headResponse (U : ℕ) (w : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re)
    (hQ : AnalyticAt ℂ squarefreeEulerResponse s) : AnalyticAt ℂ (headResponse U w) s := by
  apply Finset.analyticAt_fun_sum
  intro a ha
  have hA := analyticAt_atom (Finset.mem_filter.mp ha).2 hs
  exact analyticAt_const.mul ((hA.mul hQ.deriv).neg.sub
    ((hA.mul hQ).mul (analyticAt_markLog a hs)))

private theorem unit_disc_re {y : ℝ} {s : ℂ}
    (hs : s ∈ Metric.closedBall (3 / 2 + I * y) 1) : 1 / 2 ≤ s.re := by
  have h := (Complex.abs_re_le_norm (s - (3 / 2 + I * y))).trans
    (mem_closedBall_iff_norm.mp hs)
  norm_num at h
  linarith [(abs_le.mp h).1]

private theorem unit_disc_analytic {y : ℝ} (hy : 1 < |y|) :
    AnalyticOnNhd ℂ squarefreeEulerResponse (Metric.closedBall (3 / 2 + I * y) 1) :=
  (analyticOnNhd_squarefreeEulerResponse hy).mono
    (Metric.closedBall_subset_closedBall (squarefreeEulerRadius_bounds hy).1.le)

/-- One fixed-ordinate constant bounds the entire projected logarithmic
prefix by the square root of its cutoff, uniformly on the unit disc. -/
theorem exists_headResponse_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℕ) (w : ℕ → ℂ),
      (∀ a ∈ (Finset.Icc 1 U).filter Squarefree, ‖w a‖ ≤ 1) →
      ∀ s ∈ Metric.closedBall (3 / 2 + I * y) 1, ‖headResponse U w s‖ ≤ C * Real.sqrt U := by
  let B := Metric.closedBall (3 / 2 + I * y) 1
  have hQ := unit_disc_analytic hy
  have hQ' : AnalyticOnNhd ℂ (deriv squarefreeEulerResponse) B := fun s hs ↦ (hQ s hs).deriv
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (3 / 2 + I * y) 1).image_of_continuousOn
    hQ.continuousOn.norm).isBounded.exists_norm_le
  obtain ⟨M', hM'⟩ := ((isCompact_closedBall (3 / 2 + I * y) 1).image_of_continuousOn
    hQ'.continuousOn.norm).isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM _ ⟨3 / 2 + I * y, Metric.mem_closedBall_self (by norm_num), rfl⟩)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans
    (hM' _ ⟨3 / 2 + I * y, Metric.mem_closedBall_self (by norm_num), rfl⟩)
  obtain ⟨K, hK, hKbound⟩ := exists_markLog_average_bound
  let A := divisorSquareDirichletMass (3 / 2)
  have hA : 0 ≤ A := divisorSquareDirichletMass_nonneg _
  refine ⟨2 * A * M' + K * M + 1, by positivity, ?_⟩
  intro U w hw s hs
  have hq : ‖squarefreeEulerResponse s‖ ≤ M := by
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hM _ ⟨s, hs, rfl⟩
  have hq' : ‖deriv squarefreeEulerResponse s‖ ≤ M' := by
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hM' _ ⟨s, hs, rfl⟩
  have hhalf := unit_disc_re hs
  calc
    _ ≤ ∑ a ∈ (Finset.Icc 1 U).filter Squarefree,
        (‖atom s a‖ * M' + ‖atom s a‖ * ‖markLog a s‖ * M) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_right (hw a ha) (norm_nonneg _)).trans
      rw [one_mul, markedLogResponse]
      apply (norm_sub_le _ _).trans
      simp only [norm_neg, norm_mul]
      have h1 := mul_le_mul_of_nonneg_left hq' (norm_nonneg (atom s a))
      have h2 := mul_le_mul_of_nonneg_left hq
        (mul_nonneg (norm_nonneg (atom s a)) (norm_nonneg (markLog a s)))
      nlinarith
    _ = (∑ a ∈ (Finset.Icc 1 U).filter Squarefree, ‖atom s a‖) * M' +
        (∑ a ∈ (Finset.Icc 1 U).filter Squarefree, ‖atom s a‖ * ‖markLog a s‖) * M := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    _ ≤ (2 * Real.sqrt U * A) * M' + (K * Real.sqrt U) * M :=
      add_le_add (mul_le_mul_of_nonneg_right (sum_squarefree_norm_atom_le U hhalf) hM'0)
        (mul_le_mul_of_nonneg_right (hKbound U s hhalf) hM0)
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg (U : ℝ)]

private theorem analyticAt_quotient {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ squarefreeEulerResponse s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have h2 : 1 < (2 * s).re := by norm_num; linarith
  have hs2 : 2 * s ≠ 1 := by intro h; simp [h] at h2
  exact (analyticOn_riemannZeta s (by simpa using hs1)).div
    ((analyticOn_riemannZeta (2 * s) (by simpa using hs2)).comp
      (analyticAt_const.mul analyticAt_id)) (riemannZeta_ne_zero_of_one_lt_re h2)

/-- The cancellation formula represents the genuine logarithmically
weighted marked series in its half-plane of absolute convergence. -/
theorem LSeriesHasSum_markedLogResponse {a : ℕ} (ha : Squarefree a)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ RoughSquarefreeBare.coefficient ∅ a n *
      ((Real.log n : ℂ) - (Real.log a : ℂ))) s (markedLogResponse a s) := by
  let f : ℂ → ℂ := fun z ↦ atom z a * squarefreeEulerResponse z
  have he : (fun z ↦ squarefreeEulerMultiplier ∅ a z * squarefreeEulerResponse z) = f := by
    funext z
    rw [← atom_eq_multiplier ha]
  have hlog : LSeriesHasSum (fun n ↦ RoughSquarefreeBare.coefficient ∅ a n *
      (Real.log n : ℂ)) s (-deriv f s) := by
    have h := hasSum_markedSquarefreeEuler_moment ∅ (by simp) ha (by simp) 1 hs
    rw [he] at h
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
    have hm : signedTaylorMoment 1 f s = -deriv f s := by simp [signedTaylorMoment]
    rw [hm] at h
    apply h.congr_fun
    intro n
    rw [LSeries_term_eq_zetaPrimeFeature _ (by simp [RoughSquarefreeBare.coefficient])]
  have hbare : LSeriesHasSum (RoughSquarefreeBare.coefficient ∅ a) s (f s) := by
    simpa only [← atom_eq_multiplier ha] using
      LSeriesHasSum_markedSquarefreeEuler ∅ (by simp) ha (by simp) hs
  rw [markedLogResponse_eq ha (by linarith) (analyticAt_quotient hs)]
  convert hlog.sub (hbare.smul (Real.log a : ℂ)) using 1
  funext n
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The whole weighted prefix has a convergent arithmetic series,
with squarefree support and both logarithms identified exactly. -/
theorem LSeriesHasSum_headResponse (U : ℕ) (w : ℕ → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (headCoefficient U w) s (headResponse U w s) := by
  have h := LSeriesHasSum.sum (S := (Finset.Icc 1 U).filter Squarefree) (fun a ha ↦
    (LSeriesHasSum_markedLogResponse (Finset.mem_filter.mp ha).2 hs).smul (w a))
  convert h using 1
  · funext n
    simp only [headCoefficient, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
  · rfl

/-- Every factorial moment of the analytic prefix is its original
convergent arithmetic moment, with no restriction on the finite weights. -/
theorem hasSum_head_moment (U : ℕ) (w : ℕ → ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ headCoefficient U w n *
      ((Real.log n : ℂ) ^ N / (N.factorial : ℂ)) * zetaPrimeFeature s n)
      (signedTaylorMoment N (headResponse U w) s) := by
  have hab : LSeries.abscissaOfAbsConv (headCoefficient U w) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro y hy
    exact (LSeriesHasSum_headResponse U w (by simpa using hy)).LSeriesSummable
  have he : headResponse U w =ᶠ[𝓝 s] LSeries (headCoefficient U w) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (LSeriesHasSum_headResponse U w hz).LSeries_eq.symm
  rw [signedTaylorMoment_congr N he]
  exact hasSum_signedTaylorMoment_LSeries _
    (by simp [headCoefficient, RoughSquarefreeBare.coefficient])
    (lt_of_le_of_lt hab (by exact_mod_cast hs)) N

/-- The full polynomial acts on the exact logarithmic cancellation,
including every complex coefficient and factorial shift. -/
theorem hasSum_head_filter (U : ℕ) (w : ℕ → ℂ) (p : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ headCoefficient U w n * zetaPrimeFilterKernel p N s n)
      (zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k (headResponse U w) s) N) := by
  have h := hasSum_sum (s := p.support) (fun k _ ↦
    (hasSum_head_moment U w (N + k) hs).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

/-- Every bounded coefficient family has the square-root filtered
budget, without a moment-order factor or a logarithm of the cutoff. -/
theorem exists_head_filter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℕ) (w : ℕ → ℂ),
      (∀ a ∈ (Finset.Icc 1 U).filter Squarefree, ‖w a‖ ≤ 1) →
      ∀ (p : Polynomial ℂ) (N : ℕ),
        ‖zetaArithmeticFilter (headCoefficient U w) p N (3 / 2 + I * y)‖ ≤
          C * Real.sqrt U * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_headResponse_bound y hy
  refine ⟨C, hC, ?_⟩
  intro U w hw p N
  have ha : AnalyticOnNhd ℂ (headResponse U w) (Metric.closedBall (3 / 2 + I * y) 1) :=
    fun s hs ↦ analyticAt_headResponse U w (by linarith [unit_disc_re hs])
      (unit_disc_analytic hy s hs)
  have hd : DiffContOnCl ℂ (headResponse U w) (Metric.ball (3 / 2 + I * y) 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
    exact ha.differentiableOn
  have hm (k : ℕ) : ‖signedTaylorMoment k (headResponse U w) (3 / 2 + I * y)‖ ≤
      C * Real.sqrt U := by
    simpa only [one_pow, div_one] using norm_signedTaylorMoment_le (by norm_num) hd
      (fun s hs ↦ hb U w hw s (Metric.sphere_subset_closedBall hs)) k
  rw [zetaArithmeticFilter, (hasSum_head_filter U w p N (by norm_num)).tsum_eq,
    zetaMomentSequenceFilter, Polynomial.sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * (C * Real.sqrt U) := by
      exact Finset.sum_le_sum (fun k _ ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hm (N + k)) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The bounded-family construction is exactly the squarefree
projection of the actual truncated arithmetic convolution. -/
theorem headCoefficient_eq_projected_head_log (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    headCoefficient U (fun a ↦ (f a : ℂ)) n =
      squarefreePart (ZetaVaughanReduction.head U f * ArithmeticFunction.log) n := by
  rw [squarefreePart, projected_head_log_eq, headCoefficient, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : Squarefree a
  · exact if_pos ha
  · have hz : RoughSquarefreeBare.coefficient ∅ a n = 0 := by
      have h : ¬(Squarefree n ∧ (¬∃ p ∈ (∅ : Finset ℕ), p ∣ n) ∧ a ∣ n) :=
        fun h ↦ ha (h.1.squarefree_of_dvd h.2.2)
      exact if_neg h
    simp [ha, hz]

private theorem moebius_weight_le (a : ℕ) : ‖((μ : ArithmeticFunction ℝ) a : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  change |((μ a : ℤ) : ℝ)| ≤ 1
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)

/-- The original projected Möbius--log term inherits the improved
square-root budget for every cutoff and every polynomial filter. -/
theorem exists_projected_head_log_sqrt_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℕ) (p : Polynomial ℂ) (N : ℕ),
      ‖zetaArithmeticFilter (squarefreePart (ZetaVaughanReduction.head U
        (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)) p N (3 / 2 + I * y)‖ ≤
          C * Real.sqrt U * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_head_filter_bound y hy
  refine ⟨C, hC, ?_⟩
  intro U p N
  have h := hb U (fun a ↦ ((μ : ArithmeticFunction ℝ) a : ℂ))
    (fun a _ ↦ moebius_weight_le a) p N
  have he : headCoefficient U (fun a ↦ ((μ : ArithmeticFunction ℝ) a : ℂ)) =
      squarefreePart (ZetaVaughanReduction.head U (μ : ArithmeticFunction ℝ) *
        ArithmeticFunction.log) := funext (headCoefficient_eq_projected_head_log U μ)
  rwa [he] at h

private theorem sqrt_cutoffs_le_budget (U V : ℕ) :
    Real.sqrt U ≤ ZetaVaughanCutoffBudget.budget U V ∧
      Real.sqrt V ≤ ZetaVaughanCutoffBudget.budget U V := by
  have hU : 1 ≤ Real.sqrt (U + 1 : ℝ) := Real.one_le_sqrt.mpr (by
    linarith [Nat.cast_nonneg (α := ℝ) U])
  have hV : 1 ≤ Real.sqrt (V + 1 : ℝ) := Real.one_le_sqrt.mpr (by
    linarith [Nat.cast_nonneg (α := ℝ) V])
  constructor
  · exact (Real.sqrt_le_sqrt (show (U : ℝ) ≤ U + 1 by linarith)).trans
      (le_mul_of_one_le_right (Real.sqrt_nonneg _) hV)
  · exact (Real.sqrt_le_sqrt (show (V : ℝ) ≤ V + 1 by linarith)).trans
      (le_mul_of_one_le_left (Real.sqrt_nonneg _) hU)

/-- The complete squarefree small part has the original symmetric
square-root product budget for all cutoff pairs, including asymmetric ones. -/
theorem exists_projected_small_budget_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (U V N : ℕ),
      ‖zetaArithmeticFilter (squarefreePart (ZetaVaughanReduction.small U V))
        p N (3 / 2 + I * y)‖ ≤
          C * ZetaVaughanCutoffBudget.budget U V * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨A, hA, hbA⟩ := exists_projected_head_log_sqrt_bound y hy
  obtain ⟨C, hC, hbC⟩ := exists_prefix_filter_bound y hy
  refine ⟨3 + A + C, by positivity, ?_⟩
  intro p U V N
  let W := ∑ k ∈ p.support, ‖p.coeff k‖
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have ⟨hU, hV⟩ := sqrt_cutoffs_le_budget U V
  have hc : ‖zetaArithmeticFilter (squarefreePart (ZetaVaughanReduction.head U
      (μ : ArithmeticFunction ℝ) * ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ))) p N (3 / 2 + I * y)‖ ≤
      C * ZetaVaughanCutoffBudget.budget U V * W := by
    have h := hbC U V (fun a ↦ ((μ : ArithmeticFunction ℝ) a : ℂ))
      (fun a _ ↦ moebius_weight_le a) p N
    have he : coprimeCoefficient U V (fun a ↦ ((μ : ArithmeticFunction ℝ) a : ℂ)) =
        squarefreePart (ZetaVaughanReduction.head U (μ : ArithmeticFunction ℝ) *
          ZetaVaughanReduction.head V ArithmeticFunction.vonMangoldt *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) :=
      funext (coprimeCoefficient_eq_projected_convolution U V μ)
    rw [zetaArithmeticFilter, ← he, (hasSum_coprime_filter U V
      (fun a ↦ ((μ : ArithmeticFunction ℝ) a : ℂ)) p N (by norm_num)).tsum_eq]
    exact h
  have hl := hbA U p N
  have hp := norm_primePrefixFilter_le V p N y
  rw [zetaArithmeticFilter, (hasSum_projected_small U V p N (by norm_num)).tsum_eq]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  have hprime := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 3)) hW
  have hlog := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU hA.le) hW
  dsimp only [W] at *
  nlinarith

/-- Every moving cutoff pair with a vanishing explicit product budget
has an independently vanishing entire projected small part. -/
theorem tendsto_projected_small_of_budget (p : Polynomial ℂ) (y : ℝ) (hy : 1 < |y|)
    {u : ℝ} (hu : 0 < u) (U V : ℕ → ℕ)
    (hb : Tendsto (fun N ↦ u ^ (N + 1) * ZetaVaughanCutoffBudget.budget (U N) (V N))
      atTop (𝓝 0)) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * zetaArithmeticFilter
      (squarefreePart (ZetaVaughanReduction.small (U N) (V N))) p N (3 / 2 + I * y))
      atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_projected_small_budget_bound y hy
  have hlim := hb.mul_const (C * ∑ k ∈ p.support, ‖p.coeff k‖)
  simp only [zero_mul] at hlim
  apply squeeze_zero_norm (fun N ↦ ?_) hlim
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  exact (mul_le_mul_of_nonneg_left (hC p (U N) (V N) N) (by positivity)).trans_eq (by ring)

/-- The entire nonsquarefree response decays for every admissible
asymmetric cutoff schedule, independently of any hypothetical zero. -/
theorem tendsto_nonsquarefree_of_budget (p : Polynomial ℂ) (y : ℝ)
    (hy : 1 < |y|) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (U V : ℕ → ℕ)
    (hb : Tendsto (fun N ↦ u ^ (N + 1) * ZetaVaughanCutoffBudget.budget (U N) (V N))
      atTop (𝓝 0)) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) *
      (zetaArithmeticFilter (fun n ↦ (ZetaVaughanReduction.bilinear (U N) (V N) n : ℂ))
        p N (3 / 2 + I * y) -
      zetaArithmeticFilter (squarefreePart (ZetaVaughanReduction.bilinear (U N) (V N)))
        p N (3 / 2 + I * y))) atTop (𝓝 0) := by
  have hp := tendsto_zetaProperPrimePowerFilter_mul_pow p y (a := (u : ℂ)) (by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)
  have hsf := tendsto_projected_small_of_budget p y hy hu U V hb
  have hsmall := ZetaVaughanCutoffBudget.tendsto_smallFilter_of_budget p y hy hu U V hb
  have h := (hp.add hsf).sub hsmall
  simp only [zero_add, sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  simp only [zetaArithmeticFilter]
  rw [(ZetaVaughanReduction.hasSum_responseFilter p (U N) (V N) N
      (s := 3 / 2 + I * y) (by norm_num)).tsum_eq,
    (hasSum_projected_bilinear (U N) (V N) p N (s := 3 / 2 + I * y) (by norm_num)).tsum_eq,
    ZetaVaughanReduction.filter_identity p (U N) (V N) N (by norm_num)]
  simp only [zetaArithmeticFilter]
  ring

private theorem projected_bilinear_majorant (U V n : ℕ) :
    ‖squarefreePart (ZetaVaughanReduction.bilinear U V) n‖ ≤ zetaMoebiusLogMajorant n := by
  by_cases hn : Squarefree n
  · simpa only [squarefreePart, if_pos hn] using ZetaVaughanReduction.norm_bilinear_le U V n
  · simpa only [squarefreePart, if_neg hn, norm_zero] using zetaMoebiusLogMajorant_nonneg n

/-- The actual squarefree finite band keeps the original source for
every cutoff schedule whose explicit product budget vanishes. -/
theorem tendsto_actual_squarefree_band_of_budget (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (U V : ℕ → ℕ)
    (hb : Tendsto (fun N ↦ (3 / 2 - rho.1.re) ^ (N + 1) *
      ZetaVaughanCutoffBudget.budget (U N) (V N)) atTop (𝓝 0)) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℂ) ^ (N + 1) * zetaArithmeticBand
      (squarefreePart (ZetaVaughanReduction.bilinear (U N) (V N)))
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  let u : ℝ := 3 / 2 - rho.1.re
  let p := zetaRightHalfPoleJetFilter rho hrho
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hp := tendsto_zetaProperPrimePowerFilter_mul_pow p rho.1.im (a := (u : ℂ)) (by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)
  have hs := tendsto_projected_small_of_budget p rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hu U V hb
  have hpow : Tendsto (fun N : ℕ ↦ (u : ℂ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)).comp (tendsto_add_atTop_nat 1)
  have he := hpow.mul (tendsto_zetaDominatedFilter_sub_band
    (fun N ↦ squarefreePart (ZetaVaughanReduction.bilinear (U N) (V N)))
      (fun N ↦ projected_bilinear_majorant (U N) (V N)) p rho.1.im)
  simp only [mul_zero] at he
  dsimp only [u, p] at hp hs he
  push_cast at hp hs he
  have h := (((tendsto_zetaRightHalfPoleJetFilter rho hrho).sub hp).sub hs).sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  simp only [zetaArithmeticFilter]
  rw [(hasSum_projected_bilinear _ _ _ _ (s := 3 / 2 + I * rho.1.im) (by norm_num)).tsum_eq]
  simp only [zetaArithmeticFilter]
  push_cast
  ring

/-- The independent nonsquarefree deletion also holds on the original
finite band for every admissible cutoff schedule. -/
theorem tendsto_nonsquarefree_band_of_budget (p : Polynomial ℂ) (y : ℝ)
    (hy : 1 < |y|) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (U V : ℕ → ℕ)
    (hb : Tendsto (fun N ↦ u ^ (N + 1) * ZetaVaughanCutoffBudget.budget (U N) (V N))
      atTop (𝓝 0)) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * ∑ n ∈ zetaPrimeLogBand N,
      if Squarefree n then 0 else (ZetaVaughanReduction.bilinear (U N) (V N) n : ℂ) *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) n) atTop (𝓝 0) := by
  have hfull := tendsto_zetaDominatedFilter_sub_band
    (fun N n ↦ (ZetaVaughanReduction.bilinear (U N) (V N) n : ℂ))
      (fun N ↦ ZetaVaughanReduction.norm_bilinear_le (U N) (V N)) p y
  have hsf := tendsto_zetaDominatedFilter_sub_band
    (fun N ↦ squarefreePart (ZetaVaughanReduction.bilinear (U N) (V N)))
      (fun N ↦ projected_bilinear_majorant (U N) (V N)) p y
  have hpow : Tendsto (fun N : ℕ ↦ (u : ℂ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)).comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_nonsquarefree_of_budget p y hy hu hu1 U V hb).sub
    (hpow.mul (hfull.sub hsf))
  simp only [sub_zero, mul_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have he : (∑ n ∈ zetaPrimeLogBand N,
      if Squarefree n then 0 else (ZetaVaughanReduction.bilinear (U N) (V N) n : ℂ) *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) n) =
      zetaArithmeticBand (fun n ↦ (ZetaVaughanReduction.bilinear (U N) (V N) n : ℂ)) p N y -
        zetaArithmeticBand (squarefreePart (ZetaVaughanReduction.bilinear (U N) (V N))) p N y := by
    rw [zetaArithmeticBand, zetaArithmeticBand, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ ↦ by
      by_cases hn : Squarefree n <;> simp [squarefreePart, hn])
  rw [he]
  ring

/-- A complete finite mixture of the original squarefree coefficients.
The weights act on whole cutoff pairs, never on selected phase terms. -/
def mixture {ι : Type*} (S : Finset ι) (w : ι → ℝ) (U V : ι → ℕ) (n : ℕ) : ℂ :=
  ∑ i ∈ S, (w i : ℂ) * squarefreePart (ZetaVaughanReduction.bilinear (U i) (V i)) n

/-- All nonnegative finite mixtures share the same exact weighted
product budget; their number and cutoff allocation do not enter the constant. -/
theorem exists_small_mixture_bound {ι : Type*} (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (N : ℕ) (S : Finset ι)
      (w : ι → ℝ) (U V : ι → ℕ), (∀ i ∈ S, 0 ≤ w i) →
      ‖∑ i ∈ S, (w i : ℂ) * zetaArithmeticFilter
        (squarefreePart (ZetaVaughanReduction.small (U i) (V i))) p N (3 / 2 + I * y)‖ ≤
          C * (∑ i ∈ S, w i * ZetaVaughanCutoffBudget.budget (U i) (V i)) *
            ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_projected_small_budget_bound y hy
  refine ⟨C, hC, ?_⟩
  intro p N S w U V hw
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ S, w i *
        (C * ZetaVaughanCutoffBudget.budget (U i) (V i) * ∑ k ∈ p.support, ‖p.coeff k‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw i hi)]
      exact mul_le_mul_of_nonneg_left (hb p (U i) (V i) N) (hw i hi)
    _ = _ := by
      have he (i : ι) : w i * (C * ZetaVaughanCutoffBudget.budget (U i) (V i) *
          ∑ k ∈ p.support, ‖p.coeff k‖) =
        (w i * ZetaVaughanCutoffBudget.budget (U i) (V i)) *
          (C * ∑ k ∈ p.support, ‖p.coeff k‖) := by ring
      simp only [he, ← Finset.sum_mul]
      ring

/-- Arbitrary moving finite mixtures have independent small-part decay
whenever their explicit average budget is paid. -/
theorem tendsto_small_mixture_of_budget {ι : Type*} (p : Polynomial ℂ) (y : ℝ)
    (hy : 1 < |y|) {u : ℝ} (hu : 0 < u) (S : ℕ → Finset ι)
    (w : ℕ → ι → ℝ) (U V : ℕ → ι → ℕ) (hw : ∀ N i, i ∈ S N → 0 ≤ w N i)
    (hb : Tendsto (fun N ↦ u ^ (N + 1) *
      ∑ i ∈ S N, w N i * ZetaVaughanCutoffBudget.budget (U N i) (V N i)) atTop (𝓝 0)) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * ∑ i ∈ S N, (w N i : ℂ) *
      zetaArithmeticFilter (squarefreePart (ZetaVaughanReduction.small (U N i) (V N i)))
        p N (3 / 2 + I * y)) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_small_mixture_bound (ι := ι) y hy
  have hlim := hb.mul_const (C * ∑ k ∈ p.support, ‖p.coeff k‖)
  simp only [zero_mul] at hlim
  apply squeeze_zero_norm (fun N ↦ ?_) hlim
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  exact (mul_le_mul_of_nonneg_left (hC p N (S N) (w N) (U N) (V N) (hw N))
    (by positivity)).trans_eq (by ring)

/-- Mixtures of unit total weight retain exactly one copy of the
original prime response and every projected small correction. -/
theorem hasSum_mixture {ι : Type*} (S : Finset ι) (w : ι → ℝ) (U V : ι → ℕ)
    (hmass : ∑ i ∈ S, w i = 1) (p : Polynomial ℂ) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ mixture S w U V n * zetaPrimeFilterKernel p N s n)
      (zetaPrimeLogFilter p N s - zetaProperPrimePowerFilter p N s -
        ∑ i ∈ S, (w i : ℂ) * zetaArithmeticFilter
          (squarefreePart (ZetaVaughanReduction.small (U i) (V i))) p N s) := by
  have h := hasSum_sum (s := S) (fun i _ ↦
    (hasSum_projected_bilinear (U i) (V i) p N hs).mul_left (w i : ℂ))
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Complex.ofReal_sum, hmass, Complex.ofReal_one, one_mul] at h
  apply h.congr_fun
  intro n
  rw [mixture, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

/-- The full original divisor-log majorant survives every nonnegative
unit-mass mixture, so its complete finite-band error remains uniform. -/
theorem norm_mixture_le {ι : Type*} (S : Finset ι) (w : ι → ℝ) (U V : ι → ℕ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hmass : ∑ i ∈ S, w i = 1) (n : ℕ) :
    ‖mixture S w U V n‖ ≤ zetaMoebiusLogMajorant n := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ S, w i * zetaMoebiusLogMajorant n := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw i hi)]
      exact mul_le_mul_of_nonneg_left (projected_bilinear_majorant (U i) (V i) n) (hw i hi)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

/-- Every moving finite probability mixture with a paid average budget
retains the actual negative-multiplicity source in the original finite band.
No particular cutoff pair or coefficient family is chosen. -/
theorem tendsto_actual_mixture_band_of_budget {ι : Type*} (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (S : ℕ → Finset ι) (w : ℕ → ι → ℝ)
    (U V : ℕ → ι → ℕ) (hw : ∀ N i, i ∈ S N → 0 ≤ w N i)
    (hmass : ∀ N, ∑ i ∈ S N, w N i = 1)
    (hb : Tendsto (fun N ↦ (3 / 2 - rho.1.re) ^ (N + 1) *
      ∑ i ∈ S N, w N i * ZetaVaughanCutoffBudget.budget (U N i) (V N i)) atTop (𝓝 0)) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℂ) ^ (N + 1) * zetaArithmeticBand
      (mixture (S N) (w N) (U N) (V N)) (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  let u : ℝ := 3 / 2 - rho.1.re
  let p := zetaRightHalfPoleJetFilter rho hrho
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hp := tendsto_zetaProperPrimePowerFilter_mul_pow p rho.1.im (a := (u : ℂ)) (by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)
  have hs := tendsto_small_mixture_of_budget p rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hu S w U V hw hb
  have hpow : Tendsto (fun N : ℕ ↦ (u : ℂ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1)).comp (tendsto_add_atTop_nat 1)
  have he := hpow.mul (tendsto_zetaDominatedFilter_sub_band
    (fun N ↦ mixture (S N) (w N) (U N) (V N))
      (fun N ↦ norm_mixture_le (S N) (w N) (U N) (V N) (hw N) (hmass N)) p rho.1.im)
  simp only [mul_zero] at he
  dsimp only [u, p] at hp hs he
  push_cast at hp hs he
  have h := (((tendsto_zetaRightHalfPoleJetFilter rho hrho).sub hp).sub hs).sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  simp only [zetaArithmeticFilter]
  rw [(hasSum_mixture (S N) (w N) (U N) (V N) (hmass N)
    _ _ (s := 3 / 2 + I * rho.1.im) (by norm_num)).tsum_eq]
  simp only [zetaArithmeticFilter]
  push_cast
  ring

/-- The exact cutoff product controls the budget, without requiring
either factor separately to lie below the symmetric cutoff. -/
theorem budget_le_of_product {U V D : ℕ} (h : (U + 1) * (V + 1) ≤ (D + 1) ^ 2) :
    ZetaVaughanCutoffBudget.budget U V ≤ D + 1 := by
  rw [ZetaVaughanCutoffBudget.budget, ← Real.sqrt_mul (by positivity)]
  calc
    _ ≤ Real.sqrt ((D + 1 : ℝ) ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast h
    _ = _ := Real.sqrt_sq (by positivity)

/-- Every finite probability mixture anywhere in the entire admissible
hyperbolic cutoff region has an independently vanishing average budget. -/
theorem tendsto_hyperbolic_mixture_budget {ι : Type*} {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (S : ℕ → Finset ι) (w : ℕ → ι → ℝ) (U V : ℕ → ι → ℕ)
    (hw : ∀ N i, i ∈ S N → 0 ≤ w N i) (hmass : ∀ N, ∑ i ∈ S N, w N i = 1)
    (hcut : ∀ N i, i ∈ S N → (U N i + 1) * (V N i + 1) ≤
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 1) ^ 2) :
    Tendsto (fun N ↦ u ^ (N + 1) *
      ∑ i ∈ S N, w N i * ZetaVaughanCutoffBudget.budget (U N i) (V N i)) atTop (𝓝 0) := by
  apply squeeze_zero (fun N ↦ mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun i hi ↦ mul_nonneg (hw N i hi)
      (ZetaVaughanCutoffBudget.budget_pos _ _).le))) (fun N ↦ ?_)
    (ZetaVaughanCutoffBudget.tendsto_budget_linearDampedCutoff hu hu1)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ i ∈ S N, w N i * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 1 : ℝ) :=
      Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left (budget_le_of_product (hcut N i hi))
        (hw N i hi))
    _ = (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 1 : ℝ) := by
      rw [← Finset.sum_mul, hmass, one_mul]
    _ = _ := by
      rw [ZetaVaughanCutoffBudget.budget, Real.mul_self_sqrt (by positivity)]

/-- The original source is uniform over all finite probability mixtures
of the full admissible hyperbola. The signed arithmetic floor is still open. -/
theorem tendsto_actual_hyperbolic_mixture_band {ι : Type*} (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (S : ℕ → Finset ι) (w : ℕ → ι → ℝ)
    (U V : ℕ → ι → ℕ) (hw : ∀ N i, i ∈ S N → 0 ≤ w N i)
    (hmass : ∀ N, ∑ i ∈ S N, w N i = 1)
    (hcut : ∀ N i, i ∈ S N → (U N i + 1) * (V N i + 1) ≤
      (ZetaVaughanCutoffBudget.linearDampedCutoff (3 / 2 - rho.1.re) N + 1) ^ 2) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℂ) ^ (N + 1) * zetaArithmeticBand
      (mixture (S N) (w N) (U N) (V N)) (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  exact tendsto_actual_mixture_band_of_budget rho hrho S w U V hw hmass
    (tendsto_hyperbolic_mixture_budget (by linarith [NontrivialZetaZero.re_lt_one rho])
      (by linarith) S w U V hw hmass hcut)

end
end RiemannGaussian.SquarefreeVaughanBudget
