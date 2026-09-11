/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerDecay
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Module

/-!
# Prime density in the finite squarefree Euler allowance

Chebyshev's bound is applied before replacing prime sums by integer sums.
The resulting logarithmic saving controls the growing prime-exclusion
factor on a Cauchy circle whose radius approaches one from above.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Topology
open scoped Classical

private theorem weighted_prefix_le (c f : ℕ → ℝ) (C : ℝ)
    (hc : ∀ n, (∑ k ∈ Finset.range n, c k) ≤ C * n)
    (hf : ∀ n, 0 ≤ f n) (hanti : Antitone f) (N : ℕ) :
    (∑ k ∈ Finset.range N, f k * c k) ≤ C * ∑ k ∈ Finset.range N, f k := by
  have hr : C * ∑ k ∈ Finset.range N, f k = ∑ k ∈ Finset.range N, f k * C := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)
  rw [hr]
  simp_rw [← smul_eq_mul]
  rw [Finset.sum_range_by_parts f c, Finset.sum_range_by_parts f (fun _ ↦ C)]
  simp only [smul_eq_mul, Finset.sum_const, nsmul_eq_mul]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (by simpa [mul_comm] using hc N) (hf _)
  · apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonpos_left (by simpa [mul_comm] using hc (k + 1))
      (sub_nonpos.mpr (hanti (Nat.le_succ k)))

private theorem sum_range_succ_eq (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, f (k + 1)) = ∑ k ∈ Finset.Icc 1 N, f k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm]

/-- The logarithmically weighted prime mass has a square-root bound
coming from the actual Chebyshev prime sum, rather than integer density. -/
theorem sum_prime_log_inv_sqrt_le (R : ℕ) :
    (∑ a ∈ zetaSquarePrimesThrough R, Real.log a / Real.sqrt a) ≤ 3 * Real.sqrt R := by
  let c : ℕ → ℝ := fun k ↦ if (k + 1).Prime then Real.log (k + 1) else 0
  let f : ℕ → ℝ := fun k ↦ 1 / Real.sqrt (k + 1)
  have hc (n : ℕ) : (∑ k ∈ Finset.range n, c k) ≤ Real.log 4 * n := by
    have he : (∑ k ∈ Finset.range n, c k) = Chebyshev.theta n := by
      rw [show c = fun k ↦ (fun a : ℕ ↦ if a.Prime then Real.log a else 0) (k + 1) by
        funext k; simp [c], sum_range_succ_eq, ← Finset.sum_filter,
        Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
      apply Finset.sum_congr
      · ext a
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · exact fun h ↦ ⟨⟨Nat.zero_le _, h.1.2⟩, h.2⟩
        · exact fun h ↦ ⟨⟨h.2.pos, h.1.2⟩, h.2⟩
      · intro a _
        rfl
    rw [he]
    exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
  have hf (k : ℕ) : 0 ≤ f k := by dsimp [f]; positivity
  have hanti : Antitone f := by
    intro a b hab
    dsimp [f]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.succ_le_succ hab))
  have hw := weighted_prefix_le c f (Real.log 4) hc hf hanti R
  have hleft : (∑ k ∈ Finset.range R, f k * c k) =
      ∑ a ∈ zetaSquarePrimesThrough R, Real.log a / Real.sqrt a := by
    simp only [f, c]
    rw [zetaSquarePrimesThrough, Finset.sum_filter,
      ← sum_range_succ_eq (fun a : ℕ ↦ if a.Prime then Real.log a / Real.sqrt a else 0) R]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm]
  have hright : (∑ k ∈ Finset.range R, f k) =
      ∑ a ∈ Finset.Icc 1 R, 1 / Real.sqrt a := by
    simpa only [Nat.cast_add, Nat.cast_one] using sum_range_succ_eq
      (fun a : ℕ ↦ 1 / Real.sqrt a) R
  rw [hleft, hright] at hw
  have hlog : 2 * Real.log 4 ≤ 3 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  exact hw.trans ((mul_le_mul_of_nonneg_left (sum_inv_sqrt_Icc_le R)
    (Real.log_nonneg (by norm_num))).trans (by nlinarith [Real.sqrt_nonneg (R : ℝ)]))

private theorem sum_prime_inv_sqrt_split (R : ℕ) {x : ℝ} (hx : 1 < x) :
    (∑ a ∈ zetaSquarePrimesThrough R, 1 / Real.sqrt a) ≤
      2 * Real.sqrt x + 3 * Real.sqrt R / Real.log x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hpoint (a : ℕ) (ha : a ∈ zetaSquarePrimesThrough R) :
      1 / Real.sqrt a ≤ (if (a : ℝ) ≤ x then 1 / Real.sqrt a else 0) +
        (Real.log a / Real.sqrt a) / Real.log x := by
    have hp : a.Prime := (Finset.mem_filter.mp ha).2
    have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 (by exact_mod_cast hp.pos)
    by_cases hax : (a : ℝ) ≤ x
    · rw [if_pos hax]
      have : 0 ≤ (Real.log a / Real.sqrt a) / Real.log x := by positivity
      linarith
    · rw [if_neg hax, zero_add]
      have hlog : Real.log x ≤ Real.log a := Real.log_le_log hx0 (by linarith)
      apply (le_div_iff₀ hl).mpr
      apply (le_div_iff₀ hs).mpr
      field_simp [hs.ne']
      exact hlog
  have hlow : (∑ a ∈ zetaSquarePrimesThrough R,
      if (a : ℝ) ≤ x then 1 / Real.sqrt a else 0) ≤ 2 * Real.sqrt x := by
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ a ∈ Finset.Icc 1 ⌊x⌋₊, 1 / Real.sqrt a :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun a ha ↦ by
          have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
          exact Finset.mem_Icc.mpr ⟨hp.pos, Nat.le_floor (Finset.mem_filter.mp ha).2⟩)
          (fun _ _ _ ↦ by positivity)
      _ ≤ 2 * Real.sqrt ⌊x⌋₊ := sum_inv_sqrt_Icc_le _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (Nat.floor_le hx0.le)) (by norm_num)
  calc
    _ ≤ ∑ a ∈ zetaSquarePrimesThrough R,
        ((if (a : ℝ) ≤ x then 1 / Real.sqrt a else 0) +
          (Real.log a / Real.sqrt a) / Real.log x) := Finset.sum_le_sum hpoint
    _ = (∑ a ∈ zetaSquarePrimesThrough R, if (a : ℝ) ≤ x then 1 / Real.sqrt a else 0) +
        (∑ a ∈ zetaSquarePrimesThrough R, Real.log a / Real.sqrt a) / Real.log x := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ _ := add_le_add hlow (div_le_div_of_nonneg_right (sum_prime_log_inv_sqrt_le R) hl.le)

/-- The actual inverse-square-root prime mass saves a logarithm over
integer density. The bound is unconditional and uniform over every
prime subset of the cutoff. -/
theorem eventually_sum_prime_inv_sqrt_le :
    ∀ᶠ R : ℕ in atTop, ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      (∑ a ∈ S, 1 / Real.sqrt a) ≤ 8 * Real.sqrt R / Real.log (R + 2) := by
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hnat : ∀ᶠ R : ℕ in atTop,
      ‖Real.log (R : ℝ)‖ ≤ 1 / 4 * ‖(R : ℝ) ^ (1 / 4 : ℝ)‖ :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
  have hbig := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
    (6 * Real.log 2)
  filter_upwards [hnat, hbig, eventually_ge_atTop 2] with R hsmall hbig hR S hS
  change 6 * Real.log 2 ≤ Real.log (R : ℝ) at hbig
  have hR1 : (1 : ℝ) < R := by exact_mod_cast (show 1 < R by omega)
  have hR0 : (0 : ℝ) < R := zero_lt_one.trans hR1
  have hl : 0 < Real.log (R : ℝ) := Real.log_pos hR1
  have hL : 0 < Real.log (R + 2 : ℝ) := Real.log_pos (by linarith)
  have he : (R : ℝ) ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt R) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hR0.le]
    norm_num
  rw [Real.norm_of_nonneg (Real.log_nonneg hR1.le),
    Real.norm_of_nonneg (Real.rpow_nonneg hR0.le _), he] at hsmall
  have hlog : Real.log (R + 2 : ℝ) ≤ Real.log R + Real.log 2 := by
    have h := Real.log_le_log (show (0 : ℝ) < R + 2 by positivity)
      (show (R + 2 : ℝ) ≤ R * 2 by exact_mod_cast (show R + 2 ≤ R * 2 by omega))
    rwa [Real.log_mul hR0.ne' (by norm_num)] at h
  have hlogratio : 6 * Real.log (R + 2 : ℝ) ≤ 7 * Real.log R := by linarith
  have hs1 : 1 < Real.sqrt (R : ℝ) := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hR1)
  have hb := sum_prime_inv_sqrt_split R hs1
  rw [Real.log_sqrt hR0.le] at hb
  have hfirst : 2 * Real.sqrt (Real.sqrt R) ≤ Real.sqrt R / Real.log (R + 2 : ℝ) := by
    apply (le_div_iff₀ hL).mpr
    have hs := Real.sq_sqrt (Real.sqrt_nonneg (R : ℝ))
    nlinarith [Real.sqrt_nonneg (Real.sqrt (R : ℝ))]
  have hsecond : 3 * Real.sqrt R / (Real.log R / 2) ≤
      7 * Real.sqrt R / Real.log (R + 2 : ℝ) := by
    apply (div_le_div_iff₀ (by linarith : 0 < Real.log (R : ℝ) / 2) hL).mpr
    nlinarith [Real.sqrt_nonneg (R : ℝ)]
  calc
    _ ≤ ∑ a ∈ zetaSquarePrimesThrough R, 1 / Real.sqrt a :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun a ha ↦
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hS a ha).1.pos, (hS a ha).2⟩, (hS a ha).1⟩)
        (fun _ _ _ ↦ by positivity)
    _ ≤ 2 * Real.sqrt (Real.sqrt R) + 3 * Real.sqrt R / (Real.log R / 2) := hb
    _ ≤ Real.sqrt R / Real.log (R + 2 : ℝ) + 7 * Real.sqrt R / Real.log (R + 2 : ℝ) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

private theorem expWeight_lt_one {σ : ℝ} (hσ : 0 < σ) {a : ℕ} (ha : a.Prime) :
    zetaPrimeExpWeight σ a < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha.one_lt)
  nlinarith

private theorem expWeight_antitone {σ τ : ℝ} (h : σ ≤ τ) (a : ℕ) :
    zetaPrimeExpWeight τ a ≤ zetaPrimeExpWeight σ a := by
  apply Real.exp_le_exp.mpr
  have := Real.log_natCast_nonneg a
  nlinarith

private theorem budget_antitone {σ τ : ℝ} (hσ : 0 < σ) (h : σ ≤ τ)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (P : ℕ) :
    squarefreeEulerBudget τ S P ≤ squarefreeEulerBudget σ S P := by
  have hp (a : ℕ) (ha : a ∈ S ∪ P.primeFactors) : a.Prime := by
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hS a ha
    · exact Nat.prime_of_mem_primeFactors ha
  apply mul_le_mul (expWeight_antitone h P)
    (Finset.prod_le_prod (fun a ha ↦ inv_nonneg.mpr
      (sub_nonneg.mpr (expWeight_lt_one (hσ.trans_le h) (hp a ha)).le))
      (fun a ha ↦ inv_anti₀ (sub_pos.mpr (expWeight_lt_one hσ (hp a ha)))
        (by linarith [expWeight_antitone h a])))
    (Finset.prod_nonneg (fun a ha ↦ inv_nonneg.mpr
      (sub_nonneg.mpr (expWeight_lt_one (hσ.trans_le h) (hp a ha)).le)))
    (Real.exp_pos _).le

/-- Uniform control of all squarefree marks leaves only the true
prime-weight mass in the sieve cost. The exponent may move throughout
the half-line starting at one quarter. -/
theorem exists_squarefreeEulerBudget_prime_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), 1 / 4 ≤ σ →
      ∀ (S : Finset ℕ), (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
          squarefreeEulerBudget σ S P ≤
            C * Real.exp (5 / 4 * ∑ a ∈ S, zetaPrimeExpWeight σ a) := by
  let q := zetaPrimeExpWeight (1 / 4)
  let K := (1 - q 2)⁻¹
  have hq2 : q 2 < 1 := expWeight_lt_one (by norm_num) Nat.prime_two
  have hden : 0 < 1 - q 2 := by linarith
  have hK : 1 ≤ K := by
    dsimp only [K]
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hden).mpr
    have : 0 < q 2 := Real.exp_pos _
    linarith
  have hqt : Tendsto q atTop (𝓝 0) := by
    apply ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).congr'
    filter_upwards [eventually_ge_atTop 1] with a ha
    dsimp only [Function.comp_apply]
    rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < a by omega))]
    dsimp [q, zetaPrimeExpWeight]
    congr 1
    ring
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hqt.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 5)))
  obtain ⟨_, _, B, hB, hb⟩ := exists_squarefreeEulerBudget_card_bound (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨B * K ^ M, mul_pos hB (pow_pos (zero_lt_one.trans_le hK) _), ?_⟩
  intro σ hσ S hS P hP hPS
  have hσ0 : 0 < σ := by linarith
  have hlocal (a : ℕ) (ha : a.Prime) :
      (1 - zetaPrimeExpWeight σ a)⁻¹ ≤
        (if a < M then K else 1) * Real.exp (5 / 4 * zetaPrimeExpWeight σ a) := by
    have hqa := expWeight_lt_one hσ0 ha
    have hqa0 : 0 < zetaPrimeExpWeight σ a := Real.exp_pos _
    have hbase : zetaPrimeExpWeight σ a ≤ q 2 := by
      apply (expWeight_antitone hσ a).trans
      apply Real.exp_le_exp.mpr
      have hl : Real.log 2 ≤ Real.log a := Real.log_le_log (by norm_num)
        (by exact_mod_cast ha.two_le)
      dsimp [q]
      norm_num only [Nat.cast_ofNat]
      linarith
    have hqK : (1 - zetaPrimeExpWeight σ a)⁻¹ ≤ K :=
      inv_anti₀ hden (by linarith)
    by_cases haM : a < M
    · rw [if_pos haM]
      exact hqK.trans (le_mul_of_one_le_right (zero_lt_one.trans_le hK).le
        (Real.one_le_exp (by positivity)))
    · rw [if_neg haM, one_mul]
      have ht : zetaPrimeExpWeight σ a ≤ 1 / 5 :=
        (expWeight_antitone hσ a).trans (hM a (by omega)).le
      have hd : 0 < 1 - zetaPrimeExpWeight σ a := by linarith
      have hi : (1 - zetaPrimeExpWeight σ a)⁻¹ ≤ 5 / 4 := by
        have h := inv_anti₀ (by norm_num : (0 : ℝ) < 4 / 5)
          (show (4 / 5 : ℝ) ≤ 1 - zetaPrimeExpWeight σ a by linarith)
        norm_num at h
        exact h
      apply Real.le_exp_of_log_le
      apply (Real.log_le_sub_one_of_pos (inv_pos.mpr hd)).trans
      have he : (1 - zetaPrimeExpWeight σ a)⁻¹ - 1 =
          zetaPrimeExpWeight σ a * (1 - zetaPrimeExpWeight σ a)⁻¹ := by
        field_simp
        ring
      rw [he]
      nlinarith
  have hsieve : (∏ a ∈ S, (1 - zetaPrimeExpWeight σ a)⁻¹) ≤
      K ^ M * Real.exp (5 / 4 * ∑ a ∈ S, zetaPrimeExpWeight σ a) := by
    calc
      _ ≤ ∏ a ∈ S, (if a < M then K else 1) * Real.exp (5 / 4 * zetaPrimeExpWeight σ a) :=
        Finset.prod_le_prod (fun a ha ↦ inv_nonneg.mpr
          (sub_nonneg.mpr (expWeight_lt_one hσ0 (hS a ha)).le)) (fun a ha ↦ hlocal a (hS a ha))
      _ = K ^ (S.filter (fun a ↦ a < M)).card *
          Real.exp (5 / 4 * ∑ a ∈ S, zetaPrimeExpWeight σ a) := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite, ← Real.exp_sum, ← Finset.mul_sum]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (by
        have hsub : S.filter (fun a ↦ a < M) ⊆ Finset.range M :=
          fun _ ha ↦ Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
        simpa using Finset.card_le_card hsub)) (Real.exp_pos _).le
  have hmark : squarefreeEulerBudget σ ∅ P ≤ B := by
    apply (budget_antitone (by norm_num : (0 : ℝ) < 1 / 4) hσ ∅ (by simp) P).trans
    simpa using hb ∅ (by simp) P hP (by simp)
  have he : squarefreeEulerBudget σ S P =
      (∏ a ∈ S, (1 - zetaPrimeExpWeight σ a)⁻¹) * squarefreeEulerBudget σ ∅ P := by
    have hd : Disjoint S P.primeFactors := Finset.disjoint_left.mpr
      (fun a haS haP ↦ hPS a haP haS)
    rw [squarefreeEulerBudget, Finset.prod_union hd, squarefreeEulerBudget]
    simp only [Finset.empty_union]
    ring
  rw [he]
  have hn : 0 ≤ squarefreeEulerBudget σ ∅ P := by
    apply mul_nonneg (Real.exp_pos _).le
    exact Finset.prod_nonneg (fun a ha ↦ inv_nonneg.mpr (sub_nonneg.mpr
      (expWeight_lt_one hσ0 (Nat.prime_of_mem_primeFactors (by simpa using ha))).le))
  calc
    _ ≤ (K ^ M * Real.exp (5 / 4 * ∑ a ∈ S, zetaPrimeExpWeight σ a)) * B :=
      mul_le_mul hsieve hmark hn (by positivity)
    _ = _ := by ring

/-- A Cauchy radius just beyond one, adapted to the prime cutoff.
Its logarithmic displacement keeps each excluded prime's additional
Euler cost bounded by a constant. -/
def squarefreeEulerMovingRadius (R : ℕ) : ℝ := 1 + (Real.log ((R : ℝ) + 2))⁻¹

/-- The adapted radius approaches one from above as the sieve grows. -/
theorem tendsto_squarefreeEulerMovingRadius :
    Tendsto squarefreeEulerMovingRadius atTop (𝓝 1) := by
  have hx : Tendsto (fun R : ℕ ↦ (R : ℝ) + 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  change Tendsto (fun R : ℕ ↦ 1 + (Real.log ((R : ℝ) + 2))⁻¹) atTop (𝓝 1)
  simpa only [add_zero, Pi.inv_apply, Function.comp_apply] using
    (Real.tendsto_log_atTop.comp hx).inv_tendsto_atTop.const_add 1

/-- With the moving radius, every excluded-prime set and every valid
moving mark have a uniform allowance of order exp(sqrt(R)/log(R)).
The estimate uses only the actual prime density and local Euler factors. -/
theorem exists_squarefreeEulerBudget_moving_radius_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop,
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime ∧ a ≤ R) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
          squarefreeEulerBudget (3 / 2 - squarefreeEulerMovingRadius R) S P ≤
            C * Real.exp (30 * Real.sqrt R / Real.log (R + 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_squarefreeEulerBudget_prime_mass_bound
  have hx : Tendsto (fun R : ℕ ↦ (R : ℝ) + 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  have hlarge := (Real.tendsto_log_atTop.comp hx).eventually_ge_atTop 4
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_sum_prime_inv_sqrt_le, hlarge] with R hmass hlarge S hS P hP hPS
  change 4 ≤ Real.log (R + 2 : ℝ) at hlarge
  let L := Real.log (R + 2 : ℝ)
  have hL : 0 < L := by dsimp [L]; linarith
  have hi : L⁻¹ ≤ 1 / 4 := by
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlarge
    norm_num at h
    exact h
  have hσ : 1 / 4 ≤ 3 / 2 - squarefreeEulerMovingRadius R := by
    dsimp [squarefreeEulerMovingRadius, L] at *
    linarith
  have hweight (a : ℕ) (ha : a ∈ S) :
      zetaPrimeExpWeight (3 / 2 - squarefreeEulerMovingRadius R) a ≤ 3 * (1 / Real.sqrt a) := by
    have ha0 := (hS a ha).1.pos
    have hlog : Real.log a ≤ L := Real.log_le_log (by exact_mod_cast ha0)
      (by have h := (hS a ha).2; exact_mod_cast (show a ≤ R + 2 by omega))
    have hex : Real.exp (L⁻¹ * Real.log a) ≤ 3 := by
      apply (Real.exp_le_exp.mpr ?_).trans Real.exp_one_lt_three.le
      rw [mul_comm, ← div_eq_mul_inv]
      exact (div_le_one hL).mpr hlog
    have hhalf : zetaPrimeExpWeight (1 / 2) a ≤ 1 / Real.sqrt a := by
      simpa only [norm_zetaPrimeFeature, Complex.ofReal_re] using
        norm_zetaPrimeFeature_le_inv_sqrt (s := ((1 / 2 : ℝ) : ℂ)) (by norm_num) ha0
    have he : zetaPrimeExpWeight (3 / 2 - squarefreeEulerMovingRadius R) a =
        zetaPrimeExpWeight (1 / 2) a * Real.exp (L⁻¹ * Real.log a) := by
      rw [zetaPrimeExpWeight, zetaPrimeExpWeight, ← Real.exp_add]
      congr 1
      dsimp [squarefreeEulerMovingRadius, L]
      ring
    rw [he]
    exact (mul_le_mul hhalf hex (Real.exp_pos _).le (by positivity)).trans_eq (by ring)
  apply (hb _ hσ S (fun a ha ↦ (hS a ha).1) P hP hPS).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have hw : (∑ a ∈ S, zetaPrimeExpWeight (3 / 2 - squarefreeEulerMovingRadius R) a) ≤
      24 * Real.sqrt R / Real.log (R + 2 : ℝ) := by
    calc
      _ ≤ ∑ a ∈ S, 3 * (1 / Real.sqrt a) := Finset.sum_le_sum hweight
      _ = 3 * ∑ a ∈ S, 1 / Real.sqrt a := (Finset.mul_sum _ _ _).symm
      _ ≤ 3 * (8 * Real.sqrt R / Real.log (R + 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hmass S hS) (by norm_num)
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 5 / 4)).trans_eq (by ring)

end
end RiemannGaussian
