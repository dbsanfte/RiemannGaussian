/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSharpSieve
import RiemannGaussian.ZetaRieszCutoffMean
import RiemannGaussian.ZetaRieszCrossCutoff
import RiemannGaussian.ZetaRieszGlobalPrimePeriod

/-!
# Paying large sharp cutoffs by squarefree divisor reflection

The existing sharp divisor sum is unchanged. Its complementary divisor
cutoff has an exact moving integer endpoint. Grouping those endpoints
before using the proved interval mean replaces the large finite counting
error by a cubic complementary-cutoff error. No prime-density model or
zero hypothesis enters the resulting signed bounds.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSquarefreeDualMean

private theorem prefix_eq_divisors (R : ℕ) {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0) =
      ∑ d ∈ n.divisors, if d ≤ R then (μ d : ℝ) else 0 := by
  have he : (Finset.Icc 1 R).filter (fun d => d ∣ n) =
      n.divisors.filter (fun d => d ≤ R) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_,hR⟩,hd⟩
      exact ⟨⟨hd,hn.ne'⟩,hR⟩
    · rintro ⟨⟨hd,_⟩,hR⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,hR⟩,hd⟩
  rw [← Finset.sum_filter,he,Finset.sum_filter]

/-- Exact reflection of the sharp prefix, retaining the strict
complementary endpoint and the original squarefree Möbius sign. -/
theorem sharp_reflection {n R : ℕ} (hn : Squarefree n) (hn1 : n ≠ 1)
    (hR : 0 < R) :
    (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0) =
      -(μ n : ℝ)*(∑ d ∈ Finset.Icc 1 ((n-1)/R),
        if d ∣ n then (μ d : ℝ) else 0) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  rw [prefix_eq_divisors R hn0,prefix_eq_divisors _ hn0]
  have hzero : (∑ d ∈ n.divisors, (μ d : ℝ)) = 0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero hn1
  have hs : (∑ d ∈ n.divisors, if d ≤ R then (μ d : ℝ) else 0)+
      (∑ d ∈ n.divisors, if R < d then (μ d : ℝ) else 0) = 0 := by
    rw [← Finset.sum_add_distrib]
    convert hzero using 1
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ≤ R <;> simp [hd,Nat.lt_of_not_ge]
  have he : (∑ d ∈ n.divisors, if R < d then (μ d : ℝ) else 0) =
      (μ n : ℝ)*(∑ d ∈ n.divisors, if d ≤ (n-1)/R then (μ d : ℝ) else 0) := by
    rw [← Nat.sum_div_divisors n (fun d => if R < d then (μ d : ℝ) else 0),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    have hd0 := Nat.pos_of_mem_divisors hd
    have hm : (μ (n/d) : ℝ) = (μ n : ℝ)*(μ d : ℝ) := by
      exact_mod_cast RoughMoebiusHyperbola.moebius_cofactor hn hdn
    have hi : R < n/d ↔ d ≤ (n-1)/R := by
      rw [Nat.le_div_iff_mul_le hR,Nat.mul_comm d R]
      have heq := Nat.div_mul_cancel hdn
      constructor
      · intro h
        have ht := Nat.mul_lt_mul_of_pos_right h hd0
        rw [heq] at ht
        omega
      · intro h
        have ht : R*d < (n/d)*d := by rw [heq]; omega
        exact (Nat.mul_lt_mul_right hd0).mp ht
    by_cases h : R < n/d
    · simp only [if_pos h,if_pos (hi.mp h),hm]
    · simp only [if_neg h,if_neg (fun h' => h (hi.mpr h')),mul_zero]
  rw [he] at hs
  linarith only [hs]

private theorem square_reflection {n R : ℕ} (hn : Squarefree n) (hn1 : n ≠ 1)
    (hR : 0 < R) :
    (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2 =
      (∑ d ∈ Finset.Icc 1 ((n-1)/R), if d ∣ n then (μ d : ℝ) else 0)^2 := by
  have hm : (μ n : ℝ)^2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn
  rw [sharp_reflection hn hn1 hR,mul_pow,neg_sq,hm,one_mul]

private theorem mean_by_quotient {E : ℝ} (hmean : ∀ X Y R : ℕ, Y ≤ X →
    (∑ n ∈ Finset.Ioc Y X,
      (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤
        E*((X : ℝ)-Y)+R^2) {R : ℕ} (hR : 0 < R) (Q : ℕ) :
    ∀ (X : ℕ) (S : Finset ℕ), X ≤ Q*R → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤
        E*X+∑ q ∈ Finset.range Q, (q : ℝ)^2 := by
  induction Q with
  | zero =>
    intro X S hX hS _
    have hX0 : X = 0 := by simpa using hX
    have hs : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have := Finset.mem_Ioc.mp (hS hn)
      omega
    simp [hs,hX0]
  | succ Q ih =>
    intro X S hX hS hSF
    by_cases hsmall : X ≤ Q*R
    · have hb := ih X S hsmall hS hSF
      rw [Finset.sum_range_succ]
      linarith only [hb,sq_nonneg (Q : ℝ)]
    · have hQX : Q*R < X := Nat.lt_of_not_ge hsmall
      let T := S.filter (fun n => n ≤ Q*R)
      let U := S.filter (fun n => Q*R < n)
      have hT : T ⊆ Finset.Ioc 1 (Q*R) := by
        intro n hn
        exact Finset.mem_Ioc.mpr
          ⟨(Finset.mem_Ioc.mp (hS (Finset.mem_filter.mp hn).1)).1,(Finset.mem_filter.mp hn).2⟩
      have hU : U ⊆ Finset.Ioc (Q*R) X := by
        intro n hn
        exact Finset.mem_Ioc.mpr
          ⟨(Finset.mem_filter.mp hn).2,(Finset.mem_Ioc.mp (hS (Finset.mem_filter.mp hn).1)).2⟩
      have hp := ih (Q*R) T le_rfl hT (fun n hn => hSF n (Finset.mem_filter.mp hn).1)
      have he n (hn : n ∈ U) :
          (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2 =
            (∑ d ∈ Finset.Icc 1 Q, if d ∣ n then (μ d : ℝ) else 0)^2 := by
        have hnS := (Finset.mem_filter.mp hn).1
        have hnlo := (Finset.mem_filter.mp hn).2
        have hnhi := (Finset.mem_Ioc.mp (hS hnS)).2
        have hn1 := (Finset.mem_Ioc.mp (hS hnS)).1
        have hq : (n-1)/R = Q := by
          have hl : Q ≤ (n-1)/R := (Nat.le_div_iff_mul_le hR).mpr (by omega)
          have hu : (n-1)/R < Q+1 := (Nat.div_lt_iff_lt_mul hR).mpr (by omega)
          omega
        rw [square_reflection (hSF n hnS) (by omega) hR,hq]
      have ht : (∑ n ∈ U,
          (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤
            E*((X : ℝ)-(Q*R : ℕ))+(Q : ℝ)^2 := by
        rw [Finset.sum_congr rfl he]
        exact (Finset.sum_le_sum_of_subset_of_nonneg hU (fun _ _ _ => sq_nonneg _)).trans
          (hmean X (Q*R) Q hQX.le)
      have hs : (∑ n ∈ S,
          (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) =
          (∑ n ∈ T, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2)+
          (∑ n ∈ U, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) := by
        simpa only [T,U,not_le] using
          (Finset.sum_filter_add_sum_filter_not S (fun n => n ≤ Q*R)
            (fun n => (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2)).symm
      rw [hs,Finset.sum_range_succ]
      linarith only [hp,ht]

/-- The large-cutoff counting error is paid at the COMPLEMENTARY
cutoffs, after exact squarefree reflection. Every selected label remains. -/
theorem exists_dual_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ), 0 < R →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤
        E*X+∑ q ∈ Finset.range (X/R+1), (q : ℝ)^2 := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSharpSieve.exists_sharp_interval_bound
  refine ⟨E,hE,fun X R S hR hS hSF => ?_⟩
  exact mean_by_quotient hmean hR (X/R+1) X S
    (by simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ X hR).le) hS hSF

private theorem sum_squares_le_cube (Q : ℕ) :
    (∑ q ∈ Finset.range (Q+1), (q : ℝ)^2) ≤ (Q : ℝ)^3 := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith [sq_nonneg (Q : ℝ),Nat.cast_nonneg (α := ℝ) Q]

/-- Cubic complementary error instead of the original large `R^2`.
The stronger exact sum of complementary squares remains available above. -/
theorem exists_dual_cubic_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ), 0 < R →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤
        E*X+(X/R : ℕ)^3 := by
  obtain ⟨E,hE,hmean⟩ := exists_dual_mean_bound
  exact ⟨E,hE,fun X R S hR hS hSF =>
    (hmean X R S hR hS hSF).trans (by linarith only [sum_squares_le_cube (X/R)])⟩

/-- Both complementary estimates hold with the SAME constant and for
every original squarefree selection. The finite error is their minimum. -/
theorem exists_min_error_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ), 0 < R →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤
        E*X+min ((R : ℝ)^2) (((X/R : ℕ) : ℝ)^3) := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSharpSieve.exists_sharp_interval_bound
  refine ⟨E,hE,fun X R S hR hS hSF => ?_⟩
  have hs : S ⊆ Finset.Ioc 0 X := by
    intro n hn
    have h := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Ioc.mpr ⟨by omega,h.2⟩
  have hfirst := (Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun _ _ _ => sq_nonneg _)).trans (hmean X 0 R (Nat.zero_le X))
  simp only [Nat.cast_zero,sub_zero] at hfirst
  have hsecond := mean_by_quotient hmean hR (X/R+1) X S
    (by simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ X hR).le) hS hSF
  have hsecond' := hsecond.trans (add_le_add_right (sum_squares_le_cube (X/R)) (E*X))
  rw [add_min]
  exact le_min hfirst hsecond'

private theorem quotient_cube_le {X R : ℕ} (h : X^2 ≤ R^3) : (X/R)^3 ≤ X := by
  by_cases hX : X = 0
  · simp [hX]
  have hX0 : 0 < X := Nat.pos_of_ne_zero hX
  have hp : (X/R)^3*R^3 ≤ X^3 := by
    simpa only [← mul_pow] using Nat.pow_le_pow_left (Nat.div_mul_le_self X R) 3
  have hq := (Nat.mul_le_mul_left ((X/R)^3) h).trans hp
  have he : X^3 = X*X^2 := by ring
  rw [he] at hq
  exact Nat.le_of_mul_le_mul_right hq (show 0 < X^2 by positivity)

/-- The finite counting error is linear in the population throughout
BOTH regimes: small cutoffs R^2<=X, and large cutoffs X^2<=R^3.
The intervening range is not claimed here. -/
theorem exists_two_regime_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ), 0 < R →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (R^2 ≤ X ∨ X^2 ≤ R^3) →
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤ E*X := by
  obtain ⟨E,hE,hmean⟩ := exists_min_error_mean_bound
  refine ⟨E+1,by linarith,fun X R S hR hS hSF hreg => ?_⟩
  have ht := hmean X R S hR hS hSF
  have he : min ((R : ℝ)^2) (((X/R : ℕ) : ℝ)^3) ≤ X := by
    rcases hreg with hlo | hhi
    · exact (min_le_left _ _).trans (by exact_mod_cast hlo)
    · exact (min_le_right _ _).trans (by exact_mod_cast quotient_cube_le hhi)
  nlinarith only [ht,he]

/-- Arbitrary correlated real weights retain BOTH signed sides. In
particular they may contain the exact prime-period coefficients. Their
weight energy remains explicit and is not assumed small. -/
theorem exists_weighted_signed_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ) (w : ℕ → ℝ), 0 < R →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      let J := ∑ n ∈ S, w n*(∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0);
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*
        (E*X+min ((R : ℝ)^2) (((X/R : ℕ) : ℝ)^3)));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_min_error_mean_bound
  refine ⟨E,hE,fun X R S w hR hS hSF => ?_⟩
  dsimp only
  have hw : 0 ≤ ∑ n ∈ S, (w n)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => ∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)).trans
      (mul_le_mul_of_nonneg_left (hmean X R S hR hS hSF) hw)
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  exact hs

/-- An exact integer interpolation pays EVERY cutoff with error Q^6
whenever X<=Q^5. It does not assert the stronger uniform linear mean in
the intermediate cutoff range. -/
theorem exists_uniform_cutoff_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X Q R : ℕ) (S : Finset ℕ), 0 < Q → X ≤ Q^5 → 0 < R →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤
        E*X+(Q : ℝ)^6 := by
  obtain ⟨E,hE,hmean⟩ := exists_min_error_mean_bound
  refine ⟨E,hE,fun X Q R S hQ hX hR hS hSF => ?_⟩
  apply (hmean X R S hR hS hSF).trans
  apply add_le_add_right
  by_cases hsmall : R ≤ Q^3
  · apply (min_le_left _ _).trans
    have hp := Nat.pow_le_pow_left hsmall 2
    have he : (Q^3)^2 = Q^6 := by ring
    rw [he] at hp
    exact_mod_cast hp
  · have hQR : Q^3 ≤ R := Nat.le_of_lt (Nat.lt_of_not_ge hsmall)
    have hp := (Nat.mul_le_mul_left (X/R) hQR).trans
      ((Nat.div_mul_le_self X R).trans hX)
    have he : Q^5 = Q^2*Q^3 := by ring
    rw [he] at hp
    have hquot : X/R ≤ Q^2 := Nat.le_of_mul_le_mul_right hp (by positivity)
    have hcube := Nat.pow_le_pow_left hquot 3
    have hc : (Q^2)^3 = Q^6 := by ring
    rw [hc] at hcube
    exact (min_le_right _ _).trans (by exact_mod_cast hcube)

/-- The original two-cutoff response now has a budget independent of
its upper physical cutoff. All signed divisor cross terms are retained
before the finite positive-mixture inequality is applied. -/
theorem exists_riesz_difference_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X Q R : ℕ) (S : Finset ℕ) (A B : ℝ),
      0 < Q → X ≤ Q^5 → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      A ≤ B → Real.exp B < R+1 →
      (∑ n ∈ S, (VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)^2) ≤
        (B-A)^2*(E*X+(Q : ℝ)^6) := by
  obtain ⟨E,hE,hmean⟩ := exists_uniform_cutoff_mean_bound
  refine ⟨E,hE,fun X Q R S A B hQ hX hS hSF hAB hBR => ?_⟩
  apply ZetaRieszCutoffMean.riesz_difference_mean_le S R (E*X+(Q : ℝ)^6) A B
    (fun n hn => by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)
    (by positivity) hAB hBR
  intro k hk
  exact hmean X Q k S hQ hX (Finset.mem_Icc.mp hk).1 hS hSF

/-- A numerical upper/lower inequality for the actual signed Riesz
difference. Arbitrary retained phase/allocation/prime-moment weights are
allowed; their energy is displayed rather than postulated to vanish. -/
theorem exists_joint_riesz_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X Q R : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) (A B : ℝ),
      0 < Q → X ≤ Q^5 → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      A ≤ B → Real.exp B < R+1 →
      let J := ∑ n ∈ S, w n*(VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n);
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*(B-A)^2*(E*X+(Q : ℝ)^6));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_riesz_difference_mean_bound
  refine ⟨E,hE,fun X Q R S w A B hQ hX hS hSF hAB hBR => ?_⟩
  dsimp only
  have hw : 0 ≤ ∑ n ∈ S, (w n)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)).trans
      (mul_le_mul_of_nonneg_left (hmean X Q R S A B hQ hX hS hSF hAB hBR) hw)
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  simpa only [mul_assoc] using hs

/-- Exact application to the retained strict-cutoff slopes. The two
complementary arithmetic error bounds improve both signed sides without
changing a prime, factorial, owner or phase weight. -/
theorem exists_slope_signed_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) (D : ℝ),
      0 < R → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (R : ℝ) < Real.exp D → Real.exp D ≤ R+1 →
      let J := ∑ n ∈ S, w n*ZetaRieszGlobalCurvature.cutoffSlope D n;
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*
        (E*X+min ((R : ℝ)^2) (((X/R : ℕ) : ℝ)^3)));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_weighted_signed_bounds
  refine ⟨E,hE,fun X R S w D hR hS hSF hlo hhi => ?_⟩
  have hs := hmean X R S w hR hS hSF
  dsimp only at hs ⊢
  have he : (∑ n ∈ S, w n*ZetaRieszGlobalCurvature.cutoffSlope D n) =
      ∑ n ∈ S, w n*(∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ZetaRieszCrossCutoff.cutoffSlope_eq_prefix R D hlo hhi
      (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)]
  rw [he]
  exact hs

/-- Reflection fixes both endpoints across the cofactor population for
one marked-prime logarithm. The sign is kept; it is not a completion. -/
theorem response_reflection (L v : ℝ) {n : ℕ} (hs : Squarefree n)
    (hn : n ≠ 1) (hp : ¬n.Prime) :
    ZetaRieszFixedCountPeriod.response L (v+Real.log n) n =
      -(μ n : ℝ)*(VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-v) n) := by
  unfold ZetaRieszFixedCountPeriod.response
  rw [show v+Real.log n-L = Real.log n-(L-v) by ring,
    VaughanLogAverage.riesz_reflection (L-v) hs hn hp,
    VaughanLogAverage.riesz_reflection L hs hn hp]
  ring

/-- A bound on the literal residual coefficient times the original
factorial/phase kernel, for an arbitrary squarefree cofactor selection.
The moving cofactor endpoints are paid by exact reflection. Prime weight
energy remains explicit; no source-scale smallness is asserted. -/
theorem exists_literal_prime_fibre_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X Q R N p : ℕ) (A S : Finset ℕ) (L y : ℝ),
      0 < Q → X ≤ Q^5 → S ⊆ Finset.Ioc 1 X →
      (∀ a ∈ S, Squarefree a ∧ 2 ≤ a.primeFactors.card) →
      p.Prime → (∀ a ∈ S, ¬p ∣ a) → Real.exp L < R+1 →
      let K := Real.sqrt ((∑ a ∈ S,
        (ZetaRieszGlobalPrimePeriod.signedPrimeWeight A L N y a p/a)^2)*
        (Real.log p)^2*(E*X+(Q : ℝ)^6));
      let J := (∑ a ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re;
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_joint_riesz_bounds
  refine ⟨E,hE,fun X Q R N p A S L y hQ hX hS hSF hp hpd hR => ?_⟩
  let g := fun a => ZetaRieszGlobalPrimePeriod.signedPrimeWeight A L N y a p/a
  let w := fun a => -(μ a : ℝ)*g a
  have he a (ha : a ∈ S) :
      (ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      w a*(VaughanLogAverage.riesz L a-VaughanLogAverage.riesz (L-Real.log p) a) := by
    rw [ZetaRieszGlobalPrimePeriod.re_residual_atom
      (hSF a ha).1 (hSF a ha).2 hp (hpd a ha) A L y N,
      response_reflection L (Real.log p) (hSF a ha).1
        (by have := (Finset.mem_Ioc.mp (hS ha)).1; omega)
        (by intro h; have hc := (hSF a ha).2; rw [h.primeFactors] at hc; simp at hc)]
    dsimp [w,g]
    ring
  have hw : (∑ a ∈ S, (w a)^2) = ∑ a ∈ S, (g a)^2 := by
    apply Finset.sum_congr rfl
    intro a ha
    have hm : (μ a : ℝ)^2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hSF a ha).1
    dsimp [w]
    rw [mul_pow,neg_sq,hm,one_mul]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hb := hbound X Q R S w (L-Real.log p) L hQ hX hS
    (fun a ha => (hSF a ha).1) (by linarith) hR
  dsimp only at hb ⊢
  rw [hw,show L-(L-Real.log p) = Real.log p by ring] at hb
  rw [Complex.re_sum,Finset.sum_congr rfl he]
  exact hb

end RiemannGaussian.ZetaRieszSquarefreeDualMean
