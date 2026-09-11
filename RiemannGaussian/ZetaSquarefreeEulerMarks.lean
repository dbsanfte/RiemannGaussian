/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerResponse

/-!
# Exact Euler factors for the marked squarefree arithmetic

Small-prime exclusion and squarefree divisibility marks are finite local
modifications of the complete squarefree quotient. The identities below
retain their full complex factors and identify the original convergent
arithmetic series before using analytic continuation or norm bounds.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Topology
open scoped Classical LSeries.notation

/-- The exact multiplier for a squarefree mark disjoint from the excluded
primes. Its validity for the actual coefficients is proved below. -/
def squarefreeEulerMultiplier (S : Finset ℕ) (P : ℕ) (s : ℂ) : ℂ :=
  zetaPrimeFeature s P * ∏ a ∈ S ∪ P.primeFactors, (1 + zetaPrimeFeature s a)⁻¹

private theorem feature_eq_cpow {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    zetaPrimeFeature s n = (n : ℂ) ^ (-s) := by
  rw [zetaPrimeFeature, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
    ← Complex.natCast_log]
  congr 1
  ring

private theorem avoidance_mul (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (m n : ℕ) :
    (¬∃ a ∈ S, a ∣ m * n) ↔ (¬∃ a ∈ S, a ∣ m) ∧ (¬∃ a ∈ S, a ∣ n) := by
  constructor
  · intro h
    exact ⟨fun ⟨a, ha, hd⟩ ↦ h ⟨a, ha, hd.trans (dvd_mul_right m n)⟩,
      fun ⟨a, ha, hd⟩ ↦ h ⟨a, ha, hd.trans (dvd_mul_left n m)⟩⟩
  · rintro ⟨hm, hn⟩ ⟨a, ha, hd⟩
    rcases (hS a ha).dvd_mul.mp hd with hd | hd
    · exact hm ⟨a, ha, hd⟩
    · exact hn ⟨a, ha, hd⟩

private theorem bare_one (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) :
    RoughSquarefreeBare.coefficient S 1 1 = 1 := by
  have h : ¬∃ a ∈ S, a ∣ 1 := fun ⟨a, ha, hd⟩ ↦ (hS a ha).not_dvd_one hd
  simp only [RoughSquarefreeBare.coefficient, h, not_false_eq_true, one_dvd,
    and_self, if_true, squarefree_one]

private theorem bare_prime (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {p : ℕ} (hp : p.Prime) :
    RoughSquarefreeBare.coefficient S 1 p = if p ∈ S then 0 else 1 := by
  have he : (∃ a ∈ S, a ∣ p) ↔ p ∈ S := by
    constructor
    · rintro ⟨a, ha, hd⟩
      exact (hp.dvd_iff_eq (hS a ha).ne_one).mp hd ▸ ha
    · intro h
      exact ⟨p, h, dvd_rfl⟩
  by_cases h : p ∈ S <;> simp [RoughSquarefreeBare.coefficient, hp.squarefree, he, h]

private theorem rough_hasProd (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ if p.val ∈ S then 1 else 1 + (p : ℂ) ^ (-s))
      (LSeries (RoughSquarefreeBare.coefficient S 1) s) := by
  let g := riemannZetaSummandHom (ne_zero_of_one_lt_re hs)
  let f : ℕ → ℂ := fun n ↦ RoughSquarefreeBare.coefficient S 1 n * g n
  have hsum : Summable (fun n ↦ ‖f n‖) := by
    apply (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    intro n
    dsimp [f, g, RoughSquarefreeBare.coefficient]
    split_ifs <;> simp
  have h1 : f 1 = 1 := by simp [f, bare_one S hS]
  have h0 : f 0 = 0 := by simp [f]
  have hmul {m n : ℕ} (hc : m.Coprime n) : f (m * n) = f m * f n := by
    simp only [f, RoughSquarefreeBare.coefficient, Nat.squarefree_mul hc,
      avoidance_mul S hS, one_dvd, and_true, map_mul]
    split_ifs <;> simp_all
  have h := EulerProduct.eulerProduct_hasProd h1 (fun {_ _} hc ↦ hmul hc) hsum h0
  have hlocal (p : Nat.Primes) : (∑' k : ℕ, f (p.val ^ k)) =
      if p.val ∈ S then 1 else 1 + (p : ℂ) ^ (-s) := by
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [f, Finset.sum_range_succ, bare_one S hS, bare_prime S hS p.property,
        g, riemannZetaSummandHom]
      split_ifs <;> simp
    · intro k hk
      have hk2 : 2 ≤ k := by simp only [Finset.mem_range] at hk; omega
      have hsf : ¬Squarefree (p.val ^ k) := by
        rw [Nat.squarefree_pow_iff p.property.ne_one (by omega)]
        omega
      simp [f, RoughSquarefreeBare.coefficient, hsf]
  simp only [hlocal] at h
  convert h using 1
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, f]
  · simp [LSeries.term_of_ne_zero hn, f, g, riemannZetaSummandHom, Complex.cpow_neg,
      div_eq_mul_inv]

/-- The genuine rough squarefree series converges in the Euler half-plane. -/
theorem LSeriesSummable_roughSquarefreeEuler (S : Finset ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (RoughSquarefreeBare.coefficient S 1) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
  intro n
  unfold RoughSquarefreeBare.coefficient
  split_ifs <;> simp

/-- Finite prime exclusion has its exact reciprocal local Euler factors.
This is an identity for the convergent original arithmetic series. -/
theorem LSeriesHasSum_roughSquarefreeEuler (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (RoughSquarefreeBare.coefficient S 1) s
      ((∏ a ∈ S, (1 + zetaPrimeFeature s a)⁻¹) * squarefreeEulerResponse s) := by
  have hp (p : Nat.Primes) : 1 + (p : ℂ) ^ (-s) ≠ 0 := by
    have hb := (summable_riemannZetaSummand hs).of_norm.norm_lt_one
      (f := (riemannZetaSummandHom (ne_zero_of_one_lt_re hs)).toMonoidHom) p.property.one_lt
    change ‖(p : ℂ) ^ (-s)‖ < 1 at hb
    intro he
    have he' : (p : ℂ) ^ (-s) = -1 := by linear_combination he
    simp [he'] at hb
  let T : Finset Nat.Primes := S.subtype Nat.Prime
  have h := (hasProd_squarefreeEuler hs).congr_cofinite₀ (s := T)
    (fun p _ ↦ hp p) (g := fun p : Nat.Primes ↦ if p.val ∈ S then 1 else 1 + (p : ℂ) ^ (-s))
    (by
      intro p hp
      have hn : p.val ∉ S := fun hm ↦ hp (Finset.mem_subtype.mpr hm)
      simp only [hn, if_false])
  have ht : (∏ p ∈ T,
      if p.val ∈ S then (1 : ℂ) else 1 + (p : ℂ) ^ (-s)) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    simp [Finset.mem_subtype.mp hp]
  have hd : (∏ p ∈ T, (1 + (p : ℂ) ^ (-s))) =
      ∏ a ∈ S, (1 + (a : ℂ) ^ (-s)) := by
    exact Finset.prod_subtype_of_mem (fun a : ℕ ↦ 1 + (a : ℂ) ^ (-s)) hS
  rw [ht, hd, one_div, ← Finset.prod_inv_distrib] at h
  have he := h.unique (rough_hasProd S hS hs)
  have hfac : (∏ a ∈ S, (1 + (a : ℂ) ^ (-s))⁻¹) =
      ∏ a ∈ S, (1 + zetaPrimeFeature s a)⁻¹ := by
    exact Finset.prod_congr rfl (fun a ha ↦ by rw [feature_eq_cpow (hS a ha).ne_zero])
  rw [hfac, mul_comm] at he
  rw [he]
  exact (LSeriesSummable_roughSquarefreeEuler S hs).LSeriesHasSum

/-- Requiring a squarefree divisor is an exact dilation. The cofactor
must avoid both the original sieve and every prime of the divisor. -/
theorem squarefreeEuler_coefficient_eq_dilation (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {P : ℕ} (hP : Squarefree P)
    (hPS : ∀ a ∈ P.primeFactors, a ∉ S) :
    RoughSquarefreeBare.coefficient S P =
      zetaDilationCoefficient P (RoughSquarefreeBare.coefficient (S ∪ P.primeFactors) 1) := by
  funext n
  by_cases hd : P ∣ n
  · have hmul : P * (n / P) = n := Nat.mul_div_cancel' hd
    have hpavoid : ¬∃ a ∈ S, a ∣ P := by
      rintro ⟨a, ha, hap⟩
      exact hPS a (Nat.mem_primeFactors.mpr ⟨hS a ha, hap, hP.ne_zero⟩) ha
    have he : (Squarefree n ∧ (¬∃ a ∈ S, a ∣ n)) ↔
        Squarefree (n / P) ∧ (¬∃ a ∈ S ∪ P.primeFactors, a ∣ n / P) := by
      constructor
      · rintro ⟨hsf, hrough⟩
        have hsfmul : Squarefree (P * (n / P)) := hmul.symm ▸ hsf
        have hc := Nat.coprime_of_squarefree_mul hsfmul
        refine ⟨hsfmul.of_mul_right, ?_⟩
        rintro ⟨a, ha, had⟩
        rcases Finset.mem_union.mp ha with ha | ha
        · exact hrough ⟨a, ha, had.trans (Nat.div_dvd_of_dvd hd)⟩
        · have hp := Nat.prime_of_mem_primeFactors ha
          exact hp.not_dvd_one (hc ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors ha) had)
      · rintro ⟨hsf, hrough⟩
        have hc : P.Coprime (n / P) := by
          apply Nat.coprime_of_dvd
          intro a ha hap had
          exact hrough ⟨a, Finset.mem_union_right S
            (Nat.mem_primeFactors.mpr ⟨ha, hap, hP.ne_zero⟩), had⟩
        have hsfn : Squarefree n := hmul ▸ (Nat.squarefree_mul hc).mpr ⟨hP, hsf⟩
        refine ⟨hsfn, ?_⟩
        rw [← hmul, avoidance_mul S hS]
        exact ⟨hpavoid, fun ⟨a, ha, had⟩ ↦ hrough ⟨a, Finset.mem_union_left _ ha, had⟩⟩
    simp only [RoughSquarefreeBare.coefficient, zetaDilationCoefficient, hd, if_true,
      one_dvd, and_true, he]
  · simp [RoughSquarefreeBare.coefficient, zetaDilationCoefficient, hd]

/-- The original rough marked squarefree series has the exact finite
Euler multiplier of the complete quotient, with genuine convergence. -/
theorem LSeriesHasSum_markedSquarefreeEuler (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {P : ℕ} (hP : Squarefree P)
    (hPS : ∀ a ∈ P.primeFactors, a ∉ S) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (RoughSquarefreeBare.coefficient S P) s
      (squarefreeEulerMultiplier S P s * squarefreeEulerResponse s) := by
  rw [squarefreeEuler_coefficient_eq_dilation S hS hP hPS]
  have hpr : ∀ a ∈ S ∪ P.primeFactors, a.Prime := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hS a ha
    · exact Nat.prime_of_mem_primeFactors ha
  have h := LSeriesHasSum_zetaDilationCoefficient (Nat.pos_of_ne_zero hP.ne_zero)
    (by simp [RoughSquarefreeBare.coefficient])
    (LSeriesHasSum_roughSquarefreeEuler (S ∪ P.primeFactors) hpr hs)
  simpa only [squarefreeEulerMultiplier, mul_assoc] using h

/-- The explicit finite-product allowance at a real lower edge. It
retains the divisibility scale and every prime intersection. -/
def squarefreeEulerBudget (σ : ℝ) (S : Finset ℕ) (P : ℕ) : ℝ :=
  zetaPrimeExpWeight σ P *
    ∏ a ∈ S ∪ P.primeFactors, (1 - zetaPrimeExpWeight σ a)⁻¹

private theorem feature_weight_le {s : ℂ} {σ : ℝ} (hs : σ ≤ s.re) (n : ℕ) :
    ‖zetaPrimeFeature s n‖ ≤ zetaPrimeExpWeight σ n := by
  rw [norm_zetaPrimeFeature]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.log_natCast_nonneg n]

private theorem prime_weight_lt_one {σ : ℝ} (hσ : 0 < σ) {a : ℕ} (ha : a.Prime) :
    zetaPrimeExpWeight σ a < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have hlog : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha.one_lt)
  nlinarith

private theorem local_factor_ne_zero {s : ℂ} (hs : 0 < s.re) {a : ℕ} (ha : a.Prime) :
    1 + zetaPrimeFeature s a ≠ 0 := by
  have hb : ‖zetaPrimeFeature s a‖ < 1 := by
    rw [norm_zetaPrimeFeature]
    exact prime_weight_lt_one hs ha
  intro he
  have he' : zetaPrimeFeature s a = -1 := by linear_combination he
  simp [he'] at hb

private theorem local_inverse_bound {σ : ℝ} (hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re)
    {a : ℕ} (ha : a.Prime) :
    ‖(1 + zetaPrimeFeature s a)⁻¹‖ ≤ (1 - zetaPrimeExpWeight σ a)⁻¹ := by
  have hpos : 0 < 1 - zetaPrimeExpWeight σ a := sub_pos.mpr (prime_weight_lt_one hσ ha)
  have hb : 1 - zetaPrimeExpWeight σ a ≤ ‖1 + zetaPrimeFeature s a‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-zetaPrimeFeature s a)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at h
    linarith [feature_weight_le hs a]
  rw [norm_inv]
  exact inv_anti₀ hpos hb

/-- All finite local factors are analytic throughout the open right
half-plane; their possible zeros on its boundary are explicitly avoided. -/
theorem analyticAt_squarefreeEulerMultiplier (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (P : ℕ) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (squarefreeEulerMultiplier S P) s := by
  have hf (a : ℕ) : AnalyticAt ℂ (fun z ↦ zetaPrimeFeature z a) s := by
    have hd : Differentiable ℂ (fun z ↦ zetaPrimeFeature z a) := by
      unfold zetaPrimeFeature
      fun_prop
    exact hd.analyticAt s
  apply (hf P).mul
  apply Finset.analyticAt_fun_prod
  intro a ha
  have hap : a.Prime := by
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hS a ha
    · exact Nat.prime_of_mem_primeFactors ha
  exact (analyticAt_const.add (hf a)).inv (local_factor_ne_zero hs hap)

/-- The exact Euler multiplier obeys its explicit finite allowance
throughout any positive half-plane. No unspecified analytic bound remains. -/
theorem norm_squarefreeEulerMultiplier_le (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (P : ℕ) {σ : ℝ} (hσ : 0 < σ)
    {s : ℂ} (hs : σ ≤ s.re) :
    ‖squarefreeEulerMultiplier S P s‖ ≤ squarefreeEulerBudget σ S P := by
  have hpr (a : ℕ) (ha : a ∈ S ∪ P.primeFactors) : a.Prime := by
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hS a ha
    · exact Nat.prime_of_mem_primeFactors ha
  rw [squarefreeEulerMultiplier, norm_mul, norm_prod, squarefreeEulerBudget]
  apply mul_le_mul (feature_weight_le hs P)
    (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun a ha ↦ local_inverse_bound hσ hs (hpr a ha)))
    (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _)) (Real.exp_pos _).le

/-- Each marked factorial moment remains the literal convergent
arithmetic moment of the exact Euler quotient with its full multiplier. -/
theorem hasSum_markedSquarefreeEuler_moment (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {P : ℕ} (hP : Squarefree P)
    (hPS : ∀ a ∈ P.primeFactors, a ∉ S) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ RoughSquarefreeBare.coefficient S P n *
      ((Real.log n : ℂ) ^ N / (N.factorial : ℂ)) * zetaPrimeFeature s n)
      (signedTaylorMoment N (fun z ↦ squarefreeEulerMultiplier S P z * squarefreeEulerResponse z) s) := by
  have hab : LSeries.abscissaOfAbsConv (RoughSquarefreeBare.coefficient S P) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro y hy
    exact (LSeriesHasSum_markedSquarefreeEuler S hS hP hPS (by simpa using hy)).LSeriesSummable
  have he : (fun z ↦ squarefreeEulerMultiplier S P z * squarefreeEulerResponse z) =ᶠ[𝓝 s]
      LSeries (RoughSquarefreeBare.coefficient S P) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (LSeriesHasSum_markedSquarefreeEuler S hS hP hPS hz).LSeries_eq.symm
  rw [signedTaylorMoment_congr N he]
  exact hasSum_signedTaylorMoment_LSeries _ (by simp [RoughSquarefreeBare.coefficient])
    (lt_of_le_of_lt hab (by exact_mod_cast hs)) N

/-- Every polynomial filter has the identical signed finite combination
of the marked quotient's factorial moments. -/
theorem hasSum_markedSquarefreeEuler_filter (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {P : ℕ} (hP : Squarefree P)
    (hPS : ∀ a ∈ P.primeFactors, a ∉ S) (p : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ RoughSquarefreeBare.coefficient S P n * zetaPrimeFilterKernel p N s n)
      (zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k
        (fun z ↦ squarefreeEulerMultiplier S P z * squarefreeEulerResponse z) s) N) := by
  have h := hasSum_sum (s := p.support) (fun k _ ↦
    (hasSum_markedSquarefreeEuler_moment S hS hP hPS (N + k) hs).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ ↦ by ring)

/-- The larger Cauchy radius applies to every genuine marked and sieved
arithmetic filter. All dependence on the moving arithmetic data is an
explicit finite Euler product, separate from the common geometric rate. -/
theorem exists_markedSquarefreeEuler_filter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ), (∀ a ∈ S, a.Prime) →
      ∀ (P : ℕ), Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
      ∀ (p : Polynomial ℂ) (N : ℕ),
        ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
          C * squarefreeEulerBudget (3 / 2 - squarefreeEulerRadius y) S P *
            (squarefreeEulerRadius y)⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * (squarefreeEulerRadius y)⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_squarefreeEuler_multiplier_filter_bound y hy
  refine ⟨C, hC, ?_⟩
  intro S hS P hP hPS p N
  have hσ : 0 < 3 / 2 - squarefreeEulerRadius y := by
    linarith [(squarefreeEulerRadius_bounds hy).2.2.1]
  have hedge (s : ℂ) (hs : s ∈ Metric.closedBall (3 / 2 + I * y) (squarefreeEulerRadius y)) :
      3 / 2 - squarefreeEulerRadius y ≤ s.re := by
    have h := (Complex.abs_re_le_norm (s - (3 / 2 + I * y))).trans
      (mem_closedBall_iff_norm.mp hs)
    norm_num at h
    linarith [(abs_le.mp h).1]
  have ha : AnalyticOnNhd ℂ (squarefreeEulerMultiplier S P)
      (Metric.closedBall (3 / 2 + I * y) (squarefreeEulerRadius y)) := by
    intro s hs
    exact analyticAt_squarefreeEulerMultiplier S hS P (hσ.trans_le (hedge s hs))
  have hA : 0 ≤ squarefreeEulerBudget (3 / 2 - squarefreeEulerRadius y) S P := by
    apply (norm_nonneg (squarefreeEulerMultiplier S P (3 / 2 + I * y))).trans
    exact norm_squarefreeEulerMultiplier_le S hS P hσ (by
      norm_num
      linarith [(squarefreeEulerRadius_bounds hy).1])
  have h := hb (squarefreeEulerMultiplier S P) ha _ hA
    (fun s hs ↦ norm_squarefreeEulerMultiplier_le S hS P hσ (hedge s hs)) p N
  rw [RoughSquarefreeBare.response,
    (hasSum_markedSquarefreeEuler_filter S hS hP hPS p N (by norm_num)).tsum_eq]
  exact h

end
end RiemannGaussian
