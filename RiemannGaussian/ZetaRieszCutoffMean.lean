/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSharpSieve

/-!
# Joint mean bounds for changes of the literal Riesz cutoff

A finite summation by parts transfers the uniform sharp Möbius quadratic
bound to the original difference of two Riesz hinges. The signed divisor
cross terms are retained across every prime count before Cauchy--Schwarz.
The finite population error remains explicit.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCutoffMean

/-- Positive mixtures of sharp prefixes inherit the same second-moment
bound. This summation by parts is used only to prove the signed inequality. -/
theorem monotone_weight_mean_le (S : Finset ℕ) (z : ℕ → ℕ → ℝ)
    (R : ℕ) (hR : 0 < R) (f : ℕ → ℝ) (Q : ℝ)
    (hend : f (R+1) = 0)
    (hmono : ∀ k ∈ Finset.Icc 1 R, f (k+1) ≤ f k)
    (hQ : ∀ k ∈ Finset.Icc 1 R,
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 k, z n d)^2) ≤ Q) :
    (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R, f d*z n d)^2) ≤ (f 1)^2*Q := by
  let b := fun k => f k-f (k+1)
  have hb k (hk : k ∈ Finset.Icc 1 R) : 0 ≤ b k := sub_nonneg.mpr (hmono k hk)
  have htail d (hd : d ≤ R+1) : (∑ k ∈ Finset.Icc d R, b k) = f d := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    calc
      _ = -(∑ k ∈ Finset.Ico d (R+1), (f (k+1)-f k)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        dsimp [b]
        ring
      _ = f d := by rw [Finset.sum_Ico_sub f hd,hend]; ring
  have htotal : (∑ k ∈ Finset.Icc 1 R, b k) = f 1 := htail 1 (by omega)
  have hf : 0 ≤ f 1 := htotal ▸ Finset.sum_nonneg hb
  have he n : (∑ d ∈ Finset.Icc 1 R, f d*z n d) =
      ∑ k ∈ Finset.Icc 1 R, b k*(∑ d ∈ Finset.Icc 1 k, z n d) := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 R, ∑ k ∈ Finset.Icc d R, b k*z n d := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [← Finset.sum_mul,htail d (by have := (Finset.mem_Icc.mp hd).2; omega)]
      _ = _ := by
        have h := Finset.sum_Ico_Ico_comm 1 (R+1) (fun d k => b k*z n d)
        simp only [Finset.Ico_add_one_right_eq_Icc,← Finset.mul_sum] at h
        exact h
  have hcs n : (∑ d ∈ Finset.Icc 1 R, f d*z n d)^2 ≤
      f 1*(∑ k ∈ Finset.Icc 1 R, b k*(∑ d ∈ Finset.Icc 1 k, z n d)^2) := by
    rw [he,← htotal]
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ hb
      (fun k hk => mul_nonneg (hb k hk) (sq_nonneg _)) (fun k _ => by ring_nf; rfl)
  calc
    _ ≤ ∑ n ∈ S, f 1*(∑ k ∈ Finset.Icc 1 R,
        b k*(∑ d ∈ Finset.Icc 1 k, z n d)^2) := Finset.sum_le_sum (fun n _ => hcs n)
    _ = f 1*(∑ k ∈ Finset.Icc 1 R,
        b k*(∑ n ∈ S, (∑ d ∈ Finset.Icc 1 k, z n d)^2)) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
    _ ≤ f 1*(∑ k ∈ Finset.Icc 1 R, b k*Q) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hQ k hk) (hb k hk))) hf
    _ = (f 1)^2*Q := by rw [← Finset.sum_mul,htotal]; ring

private theorem hinge_difference_eq_min {A B t : ℝ} (hAB : A ≤ B) :
    max 0 (B-t)-max 0 (A-t) = min (B-A) (max 0 (B-t)) := by
  simp only [min_def,max_def]
  split_ifs <;> linarith

/-- Both hinges use the same literal finite divisor set. No cutoff
rounding or signed divisor contribution is omitted. -/
theorem riesz_difference_eq_prefix (R : ℕ) {A B : ℝ} (hAB : A ≤ B)
    (hhi : Real.exp B < R+1) {n : ℕ} (hn : 0 < n) :
    VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n =
      ∑ d ∈ Finset.Icc 1 R, (max 0 (B-Real.log d)-max 0 (A-Real.log d))*
        (if d ∣ n then (μ d : ℝ) else 0) := by
  have hset : (Finset.Icc 1 R).filter (fun d => d ∣ n) =
      n.divisors.filter (fun d => d ≤ R) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_,hdR⟩,hdn⟩
      exact ⟨⟨hdn,hn.ne'⟩,hdR⟩
    · rintro ⟨⟨hdn,_⟩,hdR⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn,hdR⟩,hdn⟩
  simp_rw [mul_ite,mul_zero]
  rw [← Finset.sum_filter,hset,Finset.sum_filter,VaughanLogAverage.riesz,
    VaughanLogAverage.riesz,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hdR : d ≤ R
  · rw [if_pos hdR]
    ring
  · have hdx : Real.exp B < d := hhi.trans_le (by exact_mod_cast (by omega : R+1 ≤ d))
    have hlog : B < Real.log d := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos B) hdx
    rw [if_neg hdR,max_eq_left (by linarith : B-Real.log d ≤ 0),
      max_eq_left (by linarith : A-Real.log d ≤ 0)]
    ring

/-- The exact two-hinge difference inherits any common sharp-prefix
second-moment bound on the same literal labels. -/
theorem riesz_difference_mean_le (S : Finset ℕ) (R : ℕ) (Q A B : ℝ)
    (hS : ∀ n ∈ S, 0 < n) (hQ0 : 0 ≤ Q) (hAB : A ≤ B)
    (hhi : Real.exp B < R+1)
    (hQ : ∀ k ∈ Finset.Icc 1 R,
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 k, if d ∣ n then (μ d : ℝ) else 0)^2) ≤ Q) :
    (∑ n ∈ S, (VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)^2) ≤
      (B-A)^2*Q := by
  let f := fun d : ℕ => max 0 (B-Real.log d)-max 0 (A-Real.log d)
  have he n (hn : n ∈ S) :
      VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n =
        ∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0) :=
    riesz_difference_eq_prefix R hAB hhi (hS n hn)
  have hmean : (∑ n ∈ S,
      (VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)^2) =
        ∑ n ∈ S,
          (∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0))^2 :=
    Finset.sum_congr rfl (fun n hn => by rw [he n hn])
  rw [hmean]
  by_cases hR : R = 0
  · subst R
    simpa using mul_nonneg (sq_nonneg (B-A)) hQ0
  have hend : f (R+1) = 0 := by
    have hlog : B < Real.log (R+1 : ℕ) := by
      simpa only [Real.log_exp,Nat.cast_add,Nat.cast_one] using
        Real.log_lt_log (Real.exp_pos B) hhi
    dsimp [f]
    rw [max_eq_left (by linarith : B-Real.log (R+1 : ℕ) ≤ 0),
      max_eq_left (by linarith : A-Real.log (R+1 : ℕ) ≤ 0)]
    ring
  have hmono k (hk : k ∈ Finset.Icc 1 R) : f (k+1) ≤ f k := by
    dsimp only [f]
    rw [hinge_difference_eq_min hAB,hinge_difference_eq_min hAB]
    apply min_le_min_left
    apply max_le_max_left
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    exact sub_le_sub_left (Real.log_le_log hk0 (by norm_cast; omega)) B
  have hf0 : 0 ≤ f 1 := by
    dsimp only [f]
    rw [hinge_difference_eq_min hAB]
    exact le_min (sub_nonneg.mpr hAB) (le_max_left _ _)
  have hf : f 1 ≤ B-A := by
    dsimp only [f]
    rw [hinge_difference_eq_min hAB]
    exact min_le_left _ _
  exact (monotone_weight_mean_le S
    (fun n d => if d ∣ n then (μ d : ℝ) else 0) R (Nat.pos_of_ne_zero hR)
      f Q hend hmono hQ).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hf0 hf 2) hQ0)

/-- The cutoff-change mean over every interval is quadratic in the
displacement, with a single constant independent of cutoff and prime count. -/
theorem exists_riesz_difference_interval_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X Y R : ℕ) (A B : ℝ),
      Y ≤ X → A ≤ B → Real.exp B < R+1 →
      (∑ n ∈ Finset.Ioc Y X,
        (VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)^2) ≤
          (B-A)^2*(E*((X : ℝ)-Y)+R^2) := by
  obtain ⟨E,hE,hsharp⟩ := ZetaRieszSharpSieve.exists_sharp_interval_bound
  refine ⟨E,hE,fun X Y R A B hYX hAB hhi => ?_⟩
  have hlen : 0 ≤ (X : ℝ)-Y := sub_nonneg.mpr (by exact_mod_cast hYX)
  apply riesz_difference_mean_le (Finset.Ioc Y X) R (E*((X : ℝ)-Y)+R^2) A B
    (fun n hn => by have := (Finset.mem_Ioc.mp hn).1; omega) (by positivity) hAB hhi
  intro k hk
  apply (hsharp X Y k hYX).trans
  have hh : (k : ℝ)^2 ≤ (R : ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast (Finset.mem_Icc.mp hk).2) 2
  linarith only [hh]

/-- Both signed sides of any selected cutoff-change sum have one joint
all-count budget. Weights may include the original phase, ownership,
allocation and factorial kernel; no geometry-dependent count factor enters. -/
theorem exists_masked_difference_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (S : Finset ℕ) (w : ℕ → ℝ) (X Y R : ℕ) (A B : ℝ),
      S ⊆ Finset.Ioc Y X → Y ≤ X → A ≤ B → Real.exp B < R+1 →
      let J := ∑ n ∈ S, w n*(VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n);
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*(B-A)^2*(E*((X : ℝ)-Y)+R^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_riesz_difference_interval_bound
  refine ⟨E,hE,fun S w X Y R A B hS hYX hAB hhi => ?_⟩
  dsimp only
  have hlen : 0 ≤ (X : ℝ)-Y := sub_nonneg.mpr (by exact_mod_cast hYX)
  have hcost : 0 ≤ (∑ n ∈ S, (w n)^2)*(B-A)^2*(E*((X : ℝ)-Y)+R^2) := by positivity
  have hms : (∑ n ∈ S, (VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)^2) ≤
      (B-A)^2*(E*((X : ℝ)-Y)+R^2) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)).trans
      (hmean X Y R A B hYX hAB hhi)
  have hsq := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)).trans
      (mul_le_mul_of_nonneg_left hms (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt hcost]
  simpa only [mul_assoc] using hsq

end RiemannGaussian.ZetaRieszCutoffMean
