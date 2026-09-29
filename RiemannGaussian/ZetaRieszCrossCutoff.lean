/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCutoffMean
import RiemannGaussian.RiemannXiSuzukiGramSchur

/-!
# Joint bounds for different sharp Möbius cutoffs

The signed common-divisor rows are summed before any prime-count split.
Inverse-square decay in logarithmic cutoff separation is intended to bound
many radial periods together. Finite integer-counting errors stay explicit.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCrossCutoff
open ZetaRieszSharpSieve

/-- The square logarithmic row weight is integrable uniformly over every
physical cutoff. This exponent retains the second cutoff's decay. -/
theorem logarithmic_square_row_sum_le_two (M : ℕ) {x : ℝ} (hx : 0 < x)
    (hMx : (M : ℝ) ≤ x) :
    (∑ n ∈ Finset.Icc 1 M, 1/((n : ℝ)*(4+Real.log (x/n))^2)) ≤ 2 := by
  rcases M.eq_zero_or_pos with rfl | hM
  · simp
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  let H := fun t : ℝ => 4+Real.log x-Real.log t
  let f := fun t : ℝ => t⁻¹*(H t^2)⁻¹
  let F := fun t : ℝ => (H t)⁻¹
  have hH t (ht : t ∈ Set.Icc (1 : ℝ) M) : 4 ≤ H t := by
    have ht0 : 0 < t := by linarith [ht.1]
    have hl := Real.log_le_log ht0 (ht.2.trans hMx)
    dsimp [H]
    linarith
  have hder t (ht : t ∈ Set.Icc (1 : ℝ) M) :
      HasDerivAt f ((2-H t)/(t^2*H t^3)) t := by
    have ht0 : 0 < t := by linarith [ht.1]
    have hHt : 0 < H t := by linarith [hH t ht]
    have hh : HasDerivAt H (-t⁻¹) t := by
      simpa only [H,Pi.sub_apply,zero_sub] using!
        (hasDerivAt_const t (4+Real.log x)).sub (Real.hasDerivAt_log ht0.ne')
    have hd := ((hasDerivAt_id t).inv ht0.ne').mul ((hh.pow 2).inv (pow_ne_zero 2 hHt.ne'))
    apply hd.congr_deriv
    dsimp only [Pi.inv_apply,Pi.pow_apply,id_eq]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    change -1/t^2*(H t^2)⁻¹+t⁻¹*(-(2*H t*(-t⁻¹))/(H t^2)^2) = _
    field_simp [ht0.ne',hHt.ne']
    ring
  have hc : ContinuousOn f (Set.Icc (1 : ℝ) M) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hanti : AntitoneOn f (Set.Icc (1 : ℝ) M) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc
    · intro t ht
      exact (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hder t (interior_subset ht)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hH t (interior_subset ht)])
        (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith [hH t (interior_subset ht)]) _))
  have hprim t (ht : t ∈ Set.Icc (1 : ℝ) M) : HasDerivAt F (f t) t := by
    have ht0 : 0 < t := by linarith [ht.1]
    have hHt : 0 < H t := by linarith [hH t ht]
    have hh : HasDerivAt H (-t⁻¹) t := by
      simpa only [H,Pi.sub_apply,zero_sub] using!
        (hasDerivAt_const t (4+Real.log x)).sub (Real.hasDerivAt_log ht0.ne')
    have hd := hh.inv hHt.ne'
    apply hd.congr_deriv
    dsimp only [f,Pi.inv_apply,Pi.pow_apply]
    field_simp [ht0.ne',hHt.ne']
  have hint : IntervalIntegrable f MeasureTheory.volume 1 M := hc.intervalIntegrable_of_Icc hM1
  have hi : (∫ t in (1 : ℝ)..M, f t) = F M-F 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hprim t
      (by simpa only [Set.uIcc_of_le hM1] using ht)) hint
  have hF0 : 0 ≤ F 1 := by
    dsimp [F]
    positivity [show 0 ≤ H 1 by linarith [hH 1 ⟨le_rfl,hM1⟩]]
  have hFM : F M ≤ 1 := by
    have hHp : 0 < H M := by linarith [hH M ⟨hM1,le_rfl⟩]
    have hb : (H M)⁻¹ ≤ 1 := (inv_le_one₀ hHp).mpr
      (by linarith [hH M ⟨hM1,le_rfl⟩])
    dsimp [F]
    linarith
  have hf1 : f 1 ≤ 1 := by
    have hHp : 0 < H 1 := by linarith [hH 1 ⟨le_rfl,hM1⟩]
    dsimp only [f]
    rw [inv_one,one_mul]
    exact (inv_le_one₀ (pow_pos hHp _)).mpr (one_le_pow₀ (by linarith [hH 1 ⟨le_rfl,hM1⟩]))
  have hsum := AntitoneOn.sum_le_integral_Ico (f := f) (a := 1) (b := M)
    (by omega) (by simpa only [Nat.cast_one] using hanti)
  rw [Finset.sum_Ico_add' (fun n : ℕ => f n) 1 M 1] at hsum
  have hset : Finset.Ico (1+1) (M+1) = Finset.Icc 2 M := by
    ext n
    simp only [Finset.mem_Ico,Finset.mem_Icc]
    omega
  rw [hset] at hsum
  simp only [Nat.cast_one] at hsum
  have he : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext n
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hs : (∑ n ∈ Finset.Icc 1 M, f n) ≤ 2 := by
    rw [he,Finset.sum_insert (by simp)]
    simp only [Nat.cast_one]
    linarith only [hsum,hi,hF0,hFM,hf1]
  convert hs using 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  dsimp [f,H]
  rw [Real.log_div hx.ne' hn0.ne',show 4+(Real.log x-Real.log n) =
    4+Real.log x-Real.log n by ring]
  simp only [one_div,mul_inv_rev]
  ring


/-- The averaged prime-exclusion cost with inverse-square logarithmic decay. -/
theorem excluded_row_log_square_sum_bound (R : ℕ) :
    (∑ g ∈ Finset.Icc 1 R, (halfExclusionCost g.primeFactors)^2/
      ((g : ℝ)*(4+Real.log ((R : ℝ)/g))^2)) ≤
        2*smallPrimeCost*divisorSquareDirichletMass (3/2) := by
  rcases R.eq_zero_or_pos with rfl | hR
  · simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),Finset.sum_empty]
    positivity [smallPrimeCost_one_le,divisorSquareDirichletMass_nonneg (3/2)]
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  let a := fun d : ℕ => (d.divisors.card : ℝ)^2/Real.sqrt d
  let w := fun g : ℕ => 1/((g : ℝ)*(4+Real.log ((R : ℝ)/g))^2)
  have hw g : 0 ≤ w g := by dsimp [w]; positivity
  have hmain : (∑ g ∈ Finset.Icc 1 R, ∑ d ∈ g.divisors, a d*w g) =
      ∑ d ∈ Finset.Icc 1 R, (a d/d)*
        ∑ n ∈ Finset.Icc 1 (R/d), 1/((n : ℝ)*(4+Real.log (((R : ℝ)/d)/n))^2) := by
    have he g : (∑ d ∈ g.divisors, a d*w g) =
        ∑ ab ∈ g.divisorsAntidiagonal, a ab.1*w (ab.1*ab.2) := by
      rw [Nat.sum_divisorsAntidiagonal (fun d n => a d*w (d*n))]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    simp_rw [he]
    rw [ZetaRieszGlobalCurvature.weighted_hyperbola (fun d n => a d*w (d*n))]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [w]
    simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
    ring
  have hmass : (∑ d ∈ Finset.Icc 1 R, a d/d) ≤ divisorSquareDirichletMass (3/2) := by
    have he d (hd : d ∈ Finset.Icc 1 R) : a d/d =
        (d.divisors.card : ℝ)^2*(d : ℝ)^(-(3/2 : ℝ)) := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      dsimp [a]
      rw [Real.sqrt_eq_rpow,show -(3/2 : ℝ) = -(1/2+1) by ring,
        Real.rpow_neg hd0.le,Real.rpow_add hd0,Real.rpow_one]
      ring
    rw [Finset.sum_congr rfl he]
    exact (summable_card_divisors_sq_mul_rpow_neg (by norm_num : (1 : ℝ) < 3/2)).sum_le_tsum
      _ (fun _ _ => by positivity)
  calc
    _ = ∑ g ∈ Finset.Icc 1 R, (halfExclusionCost g.primeFactors)^2*w g := by
      simp only [w,div_eq_mul_inv,one_mul]
    _ ≤ ∑ g ∈ Finset.Icc 1 R, smallPrimeCost*(∑ d ∈ g.divisors, a d)*w g := by
      apply Finset.sum_le_sum
      intro g hg
      exact mul_le_mul_of_nonneg_right
        (halfExclusionCost_sq_le_divisors (Nat.ne_of_gt (Finset.mem_Icc.mp hg).1)) (hw g)
    _ = smallPrimeCost*(∑ g ∈ Finset.Icc 1 R, ∑ d ∈ g.divisors, a d*w g) := by
      simp only [← Finset.mul_sum,Finset.sum_mul,mul_assoc]
    _ ≤ smallPrimeCost*(2*∑ d ∈ Finset.Icc 1 R, a d/d) := by
      apply mul_le_mul_of_nonneg_left ?_ (by linarith [smallPrimeCost_one_le])
      rw [hmain,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hfloor : ((R/d : ℕ) : ℝ) ≤ (R : ℝ)/d := (le_div_iff₀ hd0).mpr
        (by exact_mod_cast Nat.div_mul_le_self R d)
      have hb := logarithmic_square_row_sum_le_two (R/d) (div_pos hRR hd0) hfloor
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb
        (show 0 ≤ a d/d by dsimp [a]; positivity)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 2*smallPrimeCost by linarith [smallPrimeCost_one_le])
      nlinarith only [h]


/-- Exact signed cross-cutoff diagonalization; the common divisor cannot
exceed the smaller indexed cutoff. -/
theorem cross_eq_diagonal (R S : ℕ) (f h : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 S, f d*h e/(Nat.lcm d e : ℝ)) =
      ∑ g ∈ Finset.Icc 1 S, (g.totient : ℝ)*
        (∑ d ∈ Finset.Icc 1 R, if g ∣ d then f d/d else 0)*
        (∑ e ∈ Finset.Icc 1 S, if g ∣ e then h e/e else 0) := by
  have hcommon d e (he : e ∈ Finset.Icc 1 S) :
      (∑ g ∈ Finset.Icc 1 S, if g ∣ Nat.gcd d e then (g.totient : ℝ) else 0) =
        Nat.gcd d e := by
    have he0 := (Finset.mem_Icc.mp he).1
    have hg0 : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_right d he0
    have hset : (Finset.Icc 1 S).filter (fun g => g ∣ Nat.gcd d e) =
        (Nat.gcd d e).divisors := by
      ext g
      simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_,_⟩,hgd⟩
        exact ⟨hgd,hg0.ne'⟩
      · rintro ⟨hgd,_⟩
        have hg : 0 < g := Nat.pos_of_dvd_of_pos hgd hg0
        exact ⟨⟨hg,(Nat.le_of_dvd he0 (hgd.trans (Nat.gcd_dvd_right d e))).trans
          (Finset.mem_Icc.mp he).2⟩,hgd⟩
    rw [← Finset.sum_filter,hset,← Nat.cast_sum,Nat.sum_totient]
  have hentry d (hd : d ∈ Finset.Icc 1 R) e (he : e ∈ Finset.Icc 1 S) :
      f d*h e/(Nat.lcm d e : ℝ) =
        ∑ g ∈ Finset.Icc 1 S, (g.totient : ℝ)*
          (if g ∣ d then f d/d else 0)*(if g ∣ e then h e/e else 0) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have heR : (0 : ℝ) < e := by exact_mod_cast (Finset.mem_Icc.mp he).1
    have hlR : (0 : ℝ) < Nat.lcm d e := by
      exact_mod_cast Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    have hprod : (Nat.gcd d e : ℝ)*Nat.lcm d e = (d : ℝ)*e := by
      exact_mod_cast Nat.gcd_mul_lcm d e
    calc
      _ = (f d/d)*(h e/e)*(Nat.gcd d e : ℝ) := by
        field_simp
        linear_combination -(f d*h e)*hprod
      _ = (f d/d)*(h e/e)*∑ g ∈ Finset.Icc 1 S,
          if g ∣ Nat.gcd d e then (g.totient : ℝ) else 0 := by rw [hcommon d e he]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        simp only [Nat.dvd_gcd_iff]
        by_cases hgd : g ∣ d <;> by_cases hge : g ∣ e <;> simp [hgd,hge]
        ring
  calc
    _ = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 S, ∑ g ∈ Finset.Icc 1 S,
        (g.totient : ℝ)*(if g ∣ d then f d/d else 0)*(if g ∣ e then h e/e else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_congr rfl (fun e he => hentry d hd e he)
    _ = ∑ d ∈ Finset.Icc 1 R, ∑ g ∈ Finset.Icc 1 S, ∑ e ∈ Finset.Icc 1 S,
        (g.totient : ℝ)*(if g ∣ d then f d/d else 0)*(if g ∣ e then h e/e else 0) := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ g ∈ Finset.Icc 1 S, ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 S,
        (g.totient : ℝ)*(if g ∣ d then f d/d else 0)*(if g ∣ e then h e/e else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      simp only [← Finset.mul_sum,← Finset.sum_mul]

/-- Both cutoff rows share the same uniform harmonic cancellation
constant, with the actual coprimality exclusions retained. -/
theorem exists_common_row_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ R g : ℕ, 0 < g → g ≤ R →
      |∑ d ∈ Finset.Icc 1 R, if g ∣ d then (μ d : ℝ)/d else 0| ≤
        C*halfExclusionCost g.primeFactors/((g : ℝ)*(4+Real.log ((R : ℝ)/g))^2) := by
  obtain ⟨C,hC,hbound⟩ := exists_excluded_log_weight_bound
  refine ⟨C,hC,fun R g hg hgR => ?_⟩
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hx : 1 ≤ (R : ℝ)/g := (one_le_div hg0).mpr (by exact_mod_cast hgR)
  have hl : 0 < 4+Real.log ((R : ℝ)/g) := by positivity [Real.log_nonneg hx]
  have hb := hbound g.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    (R/g) ((R : ℝ)/g) hx
    ((le_div_iff₀ hg0).mpr (by exact_mod_cast Nat.div_mul_le_self R g)) (by
      apply (div_lt_iff₀ hg0).mpr
      exact_mod_cast (show R < (R/g+1)*g by
        simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ R hg))
  have hh : |harmonicPrefix g.primeFactors (R/g)| ≤
      C*halfExclusionCost g.primeFactors/(4+Real.log ((R : ℝ)/g))^2 :=
    (le_div_iff₀ (sq_pos_of_pos hl)).mpr (by simpa only [mul_comm] using hb)
  rw [harmonic_row_eq R g hg,abs_mul,abs_div,abs_of_pos hg0]
  calc
    _ ≤ (1/(g : ℝ))*(C*halfExclusionCost g.primeFactors/(4+Real.log ((R : ℝ)/g))^2) :=
      mul_le_mul (div_le_div_of_nonneg_right (abs_real_moebius_le_one g) hg0.le)
        hh (abs_nonneg _) (by positivity)
    _ = _ := by field_simp

/-- The actual signed sharp cross quadratic decays with logarithmic
cutoff separation. One constant covers all counts and all two-cutoff pairs. -/
theorem exists_cross_quadratic_decay :
    ∃ E : ℝ, 0 < E ∧ ∀ R S : ℕ, 0 < S → S ≤ R →
      (4+Real.log ((R : ℝ)/S))^2*
        |∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 S,
          (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)| ≤ E := by
  obtain ⟨C,hC,hrow⟩ := exists_common_row_bound
  let E := 1+2*C^2*smallPrimeCost*divisorSquareDirichletMass (3/2)
  have hsmall : 0 ≤ smallPrimeCost := by linarith [smallPrimeCost_one_le]
  have hmass := divisorSquareDirichletMass_nonneg (3/2)
  refine ⟨E,by dsimp [E]; positivity,fun R S hS hSR => ?_⟩
  have hS0 : (0 : ℝ) < S := by exact_mod_cast hS
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hS.trans_le hSR
  have hD : 0 < 4+Real.log ((R : ℝ)/S) := by
    have hr : 1 ≤ (R : ℝ)/S := (one_le_div hS0).mpr (by exact_mod_cast hSR)
    positivity [Real.log_nonneg hr]
  rw [cross_eq_diagonal]
  have hb g (hg : g ∈ Finset.Icc 1 S) :
      (4+Real.log ((R : ℝ)/S))^2*
        |(g.totient : ℝ)*(∑ d ∈ Finset.Icc 1 R, if g ∣ d then (μ d : ℝ)/d else 0)*
          (∑ e ∈ Finset.Icc 1 S, if g ∣ e then (μ e : ℝ)/e else 0)| ≤
        C^2*(halfExclusionCost g.primeFactors)^2/
          ((g : ℝ)*(4+Real.log ((S : ℝ)/g))^2) := by
    have hgN := (Finset.mem_Icc.mp hg).1
    have hgS := (Finset.mem_Icc.mp hg).2
    have hg0 : (0 : ℝ) < g := by exact_mod_cast hgN
    have hgS0 : (g : ℝ) ≤ S := by exact_mod_cast hgS
    have hRS : 4+Real.log ((R : ℝ)/S) ≤ 4+Real.log ((R : ℝ)/g) := by
      gcongr
    have hRg : 0 < 4+Real.log ((R : ℝ)/g) := hD.trans_le hRS
    have hSg : 0 < 4+Real.log ((S : ℝ)/g) := by
      positivity [Real.log_nonneg ((one_le_div hg0).mpr hgS0)]
    have hr := hrow R g hgN (hgS.trans hSR)
    have hs := hrow S g hgN hgS
    have hc0 : 0 ≤ C*halfExclusionCost g.primeFactors :=
      mul_nonneg hC.le (halfExclusionCost_pos _ (fun _ hp => Nat.prime_of_mem_primeFactors hp)).le
    have hrd : |∑ d ∈ Finset.Icc 1 R, if g ∣ d then (μ d : ℝ)/d else 0| ≤
        C*halfExclusionCost g.primeFactors/((g : ℝ)*(4+Real.log ((R : ℝ)/S))^2) := by
      apply hr.trans
      exact div_le_div_of_nonneg_left hc0 (mul_pos hg0 (sq_pos_of_pos hD))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD.le hRS 2) hg0.le)
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg g.totient)]
    calc
      _ ≤ (4+Real.log ((R : ℝ)/S))^2*
          ((g : ℝ)*(C*halfExclusionCost g.primeFactors/
              ((g : ℝ)*(4+Real.log ((R : ℝ)/S))^2))*
            (C*halfExclusionCost g.primeFactors/((g : ℝ)*(4+Real.log ((S : ℝ)/g))^2))) := by
        apply mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact mul_le_mul
          (mul_le_mul (by exact_mod_cast Nat.totient_le g) hrd (abs_nonneg _) hg0.le)
          hs (abs_nonneg _) (by positivity)
      _ = _ := by field_simp [hg0.ne',hD.ne',hSg.ne']
  calc
    _ ≤ (4+Real.log ((R : ℝ)/S))^2*
        (∑ g ∈ Finset.Icc 1 S,
          |(g.totient : ℝ)*(∑ d ∈ Finset.Icc 1 R, if g ∣ d then (μ d : ℝ)/d else 0)*
            (∑ e ∈ Finset.Icc 1 S, if g ∣ e then (μ e : ℝ)/e else 0)|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (sq_nonneg _)
    _ ≤ ∑ g ∈ Finset.Icc 1 S, C^2*(halfExclusionCost g.primeFactors)^2/
        ((g : ℝ)*(4+Real.log ((S : ℝ)/g))^2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hb
    _ = C^2*(∑ g ∈ Finset.Icc 1 S, (halfExclusionCost g.primeFactors)^2/
        ((g : ℝ)*(4+Real.log ((S : ℝ)/g))^2)) := by
      simp only [Finset.mul_sum,mul_div_assoc]
    _ ≤ C^2*(2*smallPrimeCost*divisorSquareDirichletMass (3/2)) :=
      mul_le_mul_of_nonneg_left (excluded_row_log_square_sum_bound S) (sq_nonneg _)
    _ ≤ E := by dsimp [E]; linarith

/-- Interchanging the two literal cutoffs preserves the signed quadratic. -/
theorem cross_symm (R S : ℕ) :
    (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 S,
      (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)) =
    ∑ e ∈ Finset.Icc 1 S, ∑ d ∈ Finset.Icc 1 R,
      (μ e : ℝ)*(μ d : ℝ)/(Nat.lcm e d : ℝ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.lcm_comm,mul_comm (μ d : ℝ)]

/-- Symmetric inverse-square separation bound for every positive pair
of sharp cutoffs. -/
theorem exists_symmetric_cross_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ R S : ℕ, 0 < R → 0 < S →
      |∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 S,
        (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)| ≤
          E/(4+|Real.log R-Real.log S|)^2 := by
  obtain ⟨E,hE,hbound⟩ := exists_cross_quadratic_decay
  refine ⟨E,hE,fun R S hR hS => ?_⟩
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hS0 : (0 : ℝ) < S := by exact_mod_cast hS
  apply (le_div_iff₀ (by positivity : 0 < (4+|Real.log R-Real.log S|)^2)).mpr
  rcases le_total S R with h | h
  · have hl : 0 ≤ Real.log R-Real.log S :=
      sub_nonneg.mpr (Real.log_le_log hS0 (by exact_mod_cast h))
    rw [abs_of_nonneg hl]
    simpa only [Real.log_div hR0.ne' hS0.ne',mul_comm] using hbound R S hS h
  · have hl : Real.log R-Real.log S ≤ 0 :=
      sub_nonpos.mpr (Real.log_le_log hR0 (by exact_mod_cast h))
    rw [abs_of_nonpos hl,neg_sub,cross_symm R S]
    simpa only [Real.log_div hS0.ne' hR0.ne',mul_comm] using hbound S R hR h

/-- A positive logarithmic spacing has finite total inverse-square cost. -/
theorem summable_separation_kernel {h : ℝ} (hh : 0 < h) :
    Summable (fun k : ℤ => 1/(4+h*|(k : ℝ)|)^2) := by
  have hs : Summable (fun n : ℕ => 1/((n : ℝ)+4/h)^2) := by
    have hb := (Real.summable_one_div_nat_add_rpow (4/h) 2).mpr (by norm_num)
    simpa only [Real.rpow_two,sq_abs] using hb
  have ht : Summable (fun n : ℕ => 1/(4+h*(n : ℝ))^2) := by
    apply (hs.mul_left (1/h^2)).congr
    intro n
    field_simp [hh.ne']
    ring
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa only [Int.cast_natCast,Int.cast_neg,abs_neg,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using ht

/-- The spacing-kernel row bound is independent of the number or
location of retained periods. -/
theorem separation_row_le (I : Finset ℕ) (i : ℕ) {h : ℝ} (hh : 0 < h) :
    (∑ j ∈ I, 1/(4+h*|(i : ℝ)-j|)^2) ≤
      ∑' k : ℤ, 1/(4+h*|(k : ℝ)|)^2 := by
  have hinj : Set.InjOn (fun j : ℕ => (i : ℤ)-j) (I : Set ℕ) := by
    intro j _ k _ hjk
    exact_mod_cast (sub_right_inj.mp hjk)
  have he : (∑ j ∈ I, 1/(4+h*|(i : ℝ)-j|)^2) =
      ∑ k ∈ I.image (fun j : ℕ => (i : ℤ)-j), 1/(4+h*|(k : ℝ)|)^2 := by
    rw [Finset.sum_image hinj]
    simp only [Int.cast_sub,Int.cast_natCast]
  rw [he]
  exact (summable_separation_kernel hh).sum_le_tsum _ (fun _ _ => by positivity)

/-- Joint control of an arbitrary signed family of separated cutoffs.
The cost depends on spacing but not the number of periods or prime counts.
Signed cross terms are summed before the finite Schur estimate. -/
theorem exists_separated_quadratic_bound {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (R : ℕ → ℕ) (a : ℕ → ℝ),
      (∀ i ∈ I, 0 < R i) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      |∑ i ∈ I, ∑ j ∈ I, a i*a j*
        (∑ d ∈ Finset.Icc 1 (R i), ∑ e ∈ Finset.Icc 1 (R j),
          (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ))| ≤ E*∑ i ∈ I, (a i)^2 := by
  obtain ⟨C,hC,hcross⟩ := exists_symmetric_cross_bound
  let B := ∑' k : ℤ, 1/(4+h*|(k : ℝ)|)^2
  have hB : 0 ≤ B := tsum_nonneg (fun _ => by positivity)
  refine ⟨1+C*B,by positivity,fun I R a hR hsep => ?_⟩
  let Q := fun i j => ∑ d ∈ Finset.Icc 1 (R i), ∑ e ∈ Finset.Icc 1 (R j),
    (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)
  have hpair i (hi : i ∈ I) j (hj : j ∈ I) :
      |Q i j| ≤ C/(4+h*|(i : ℝ)-j|)^2 := by
    apply (hcross (R i) (R j) (hR i hi) (hR j hj)).trans
    exact div_le_div_of_nonneg_left hC.le (by positivity)
      (pow_le_pow_left₀ (by positivity) (by linarith [hsep i hi j hj]) 2)
  have hrows i (hi : i ∈ I) : (∑ j ∈ I, |Q i j|) ≤ C*B := by
    calc
      _ ≤ ∑ j ∈ I, C/(4+h*|(i : ℝ)-j|)^2 := Finset.sum_le_sum (hpair i hi)
      _ = C*(∑ j ∈ I, 1/(4+h*|(i : ℝ)-j|)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ C*B := mul_le_mul_of_nonneg_left (separation_row_le I i hh) hC.le
  have hschur := finset_symmetric_schur_quadratic_le I (fun i => |a i|)
    (fun i j => |Q i j|) (C*B) (fun _ _ => abs_nonneg _)
    (fun i j => congrArg abs (cross_symm (R i) (R j))) hrows
  simp only [sq_abs] at hschur
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, |a i| * |a j| * |Q i j| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => a i*a j*Q i j) I
    _ ≤ C*B*∑ i ∈ I, (a i)^2 := hschur
    _ ≤ (1+C*B)*∑ i ∈ I, (a i)^2 := by
      nlinarith [Finset.sum_nonneg (s := I) (fun i _ => sq_nonneg (a i))]

private theorem restrict_prefix (M R : ℕ) (hRM : R ≤ M) (f : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 M, if d ≤ R then f d else 0) = ∑ d ∈ Finset.Icc 1 R, f d := by
  rw [← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter,Finset.mem_Icc]
  omega

private theorem mixture_sum (I : Finset ℕ) (R : ℕ → ℕ) (a : ℕ → ℝ) (M : ℕ)
    (hR : ∀ i ∈ I, R i ≤ M) (t : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 M, (∑ i ∈ I, if d ≤ R i then a i*(μ d : ℝ) else 0)*t d) =
      ∑ i ∈ I, a i*(∑ d ∈ Finset.Icc 1 (R i), (μ d : ℝ)*t d) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ite_mul,zero_mul,mul_assoc]
  rw [← restrict_prefix M (R i) (hR i hi)]
  simp only [Finset.mul_sum,mul_ite,mul_zero]

/-- The literal integer second moment of a whole signed cutoff family.
Cutoff coefficients are summed with their signs BEFORE the finite counting
error is charged. No factor counts the number of retained periods. -/
theorem exists_separated_cancellation_mean_bound {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (R : ℕ → ℕ) (a : ℕ → ℝ) (X Y : ℕ),
      Y ≤ X → (∀ i ∈ I, 0 < R i) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∑ n ∈ Finset.Ioc Y X,
        (∑ i ∈ I, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2) ≤
          E*((X : ℝ)-Y)*(∑ i ∈ I, (a i)^2)+(∑ d ∈ Finset.Icc 1 (I.sup R),
            |∑ i ∈ I, if d ≤ R i then a i*(μ d : ℝ) else 0|)^2 := by
  obtain ⟨E,hE,hbound⟩ := exists_separated_quadratic_bound hh
  refine ⟨E,hE,fun I R a X Y hYX hR hsep => ?_⟩
  let M := I.sup R
  let f := fun d : ℕ => ∑ i ∈ I, if d ≤ R i then a i*(μ d : ℝ) else 0
  have hRM i (hi : i ∈ I) : R i ≤ M := Finset.le_sup hi
  have hmix (t : ℕ → ℝ) : (∑ d ∈ Finset.Icc 1 M, f d*t d) =
      ∑ i ∈ I, a i*(∑ d ∈ Finset.Icc 1 (R i), (μ d : ℝ)*t d) :=
    mixture_sum I R a M hRM t
  have hprefix n : (∑ d ∈ Finset.Icc 1 M, if d ∣ n then f d else 0) =
      ∑ i ∈ I, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0) := by
    simpa only [mul_ite,mul_one,mul_zero] using hmix (fun d => if d ∣ n then 1 else 0)
  have hquad : (∑ d ∈ Finset.Icc 1 M, ∑ e ∈ Finset.Icc 1 M,
      f d*f e/(Nat.lcm d e : ℝ)) =
        ∑ i ∈ I, ∑ j ∈ I, a i*a j*
          (∑ d ∈ Finset.Icc 1 (R i), ∑ e ∈ Finset.Icc 1 (R j),
            (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)) := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 M, f d*
          (∑ e ∈ Finset.Icc 1 M, f e*(1/(Nat.lcm d e : ℝ))) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = ∑ d ∈ Finset.Icc 1 M, f d*
          (∑ j ∈ I, a j*(∑ e ∈ Finset.Icc 1 (R j), (μ e : ℝ)*(1/(Nat.lcm d e : ℝ)))) := by
        simp_rw [hmix]
      _ = ∑ j ∈ I, a j*(∑ d ∈ Finset.Icc 1 M, f d*
          (∑ e ∈ Finset.Icc 1 (R j), (μ e : ℝ)*(1/(Nat.lcm d e : ℝ)))) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = ∑ j ∈ I, a j*(∑ i ∈ I, a i*(∑ d ∈ Finset.Icc 1 (R i), (μ d : ℝ)*
          (∑ e ∈ Finset.Icc 1 (R j), (μ e : ℝ)*(1/(Nat.lcm d e : ℝ))))) := by
        simp_rw [hmix]
      _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro e _
        ring
  have he := interval_mean_square_le X Y M hYX f
  simp_rw [hprefix] at he
  rw [hquad] at he
  have hq := (le_abs_self _).trans (hbound I R a hR hsep)
  have hl : 0 ≤ (X : ℝ)-Y := sub_nonneg.mpr (by exact_mod_cast hYX)
  have hmain := mul_le_mul_of_nonneg_left hq hl
  change _ ≤ E*((X : ℝ)-Y)*(∑ i ∈ I, (a i)^2)+(∑ d ∈ Finset.Icc 1 M, |f d|)^2
  nlinarith only [he,hmain]

/-- The literal integer second moment of a whole signed cutoff family.
The main term is proportional to the squared coefficient energy, with no
period-count factor. The combined finite floor error is not discarded. -/
theorem exists_separated_mean_bound {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (R : ℕ → ℕ) (a : ℕ → ℝ) (X Y : ℕ),
      Y ≤ X → (∀ i ∈ I, 0 < R i) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∑ n ∈ Finset.Ioc Y X,
        (∑ i ∈ I, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2) ≤
          E*((X : ℝ)-Y)*(∑ i ∈ I, (a i)^2)+(∑ i ∈ I, |a i| * (R i : ℝ))^2 := by
  obtain ⟨E,hE,hbound⟩ := exists_separated_cancellation_mean_bound hh
  refine ⟨E,hE,fun I R a X Y hYX hR hsep => ?_⟩
  let M := I.sup R
  let f := fun d : ℕ => ∑ i ∈ I, if d ≤ R i then a i*(μ d : ℝ) else 0
  have hRM i (hi : i ∈ I) : R i ≤ M := Finset.le_sup hi
  have hmass : (∑ d ∈ Finset.Icc 1 M, |f d|) ≤ ∑ i ∈ I, |a i| * (R i : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 M, ∑ i ∈ I, if d ≤ R i then |a i| else 0 := by
        apply Finset.sum_le_sum
        intro d _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i _
        by_cases hd : d ≤ R i
        · simp only [if_pos hd,abs_mul]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (abs_real_moebius_le_one d) (abs_nonneg (a i))
        · simp [hd]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [restrict_prefix M (R i) (hRM i hi)]
        simp [mul_comm]
  have he := hbound I R a X Y hYX hR hsep
  have herror := pow_le_pow_left₀ (Finset.sum_nonneg (fun d _ => abs_nonneg (f d))) hmass 2
  exact he.trans (add_le_add_right herror _)

/-- Both signed sides after coupling all retained cutoffs. The final
selection and real weights stay inside the actual integer sum; the
coefficient family is fixed on that selection, not label-dependent. -/
theorem exists_joint_signed_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I S : Finset ℕ) (R : ℕ → ℕ) (a w : ℕ → ℝ) (X Y : ℕ),
      S ⊆ Finset.Ioc Y X → Y ≤ X → (∀ i ∈ I, 0 < R i) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ I, a i*
        (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0));
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*
        (E*((X : ℝ)-Y)*(∑ i ∈ I, (a i)^2)+(∑ i ∈ I, |a i| * (R i : ℝ))^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_separated_mean_bound hh
  refine ⟨E,hE,fun I S R a w X Y hS hYX hR hsep => ?_⟩
  dsimp only
  let F := fun n => ∑ i ∈ I, a i*
    (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)
  have hs : (∑ n ∈ S, (F n)^2) ≤
      E*((X : ℝ)-Y)*(∑ i ∈ I, (a i)^2)+(∑ i ∈ I, |a i| * (R i : ℝ))^2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)).trans
      (hmean I R a X Y hYX hR hsep)
  have hsq := (Finset.sum_mul_sq_le_sq_mul_sq S w F).trans
    (mul_le_mul_of_nonneg_left hs (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hl : 0 ≤ (X : ℝ)-Y := sub_nonneg.mpr (by exact_mod_cast hYX)
  have hcost : 0 ≤ (∑ n ∈ S, (w n)^2)*
      (E*((X : ℝ)-Y)*(∑ i ∈ I, (a i)^2)+(∑ i ∈ I, |a i| * (R i : ℝ))^2) := by positivity
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt hcost]
  exact hsq

/-- Both signed sides retain the cancellation among cutoff coefficients
inside the finite counting error as well as the main quadratic. The final
selection and real weights stay inside the actual integer sum; the
coefficient family is fixed on that selection, not label-dependent. -/
theorem exists_joint_cancellation_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I S : Finset ℕ) (R : ℕ → ℕ) (a w : ℕ → ℝ) (X Y : ℕ),
      S ⊆ Finset.Ioc Y X → Y ≤ X → (∀ i ∈ I, 0 < R i) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ I, a i*
        (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0));
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*
        (E*((X : ℝ)-Y)*(∑ i ∈ I, (a i)^2)+(∑ d ∈ Finset.Icc 1 (I.sup R),
            |∑ i ∈ I, if d ≤ R i then a i*(μ d : ℝ) else 0|)^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_separated_cancellation_mean_bound hh
  refine ⟨E,hE,fun I S R a w X Y hS hYX hR hsep => ?_⟩
  dsimp only
  let F := fun n => ∑ i ∈ I, a i*
    (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)
  have hs : (∑ n ∈ S, (F n)^2) ≤
      E*((X : ℝ)-Y)*(∑ i ∈ I, (a i)^2)+(∑ d ∈ Finset.Icc 1 (I.sup R),
            |∑ i ∈ I, if d ≤ R i then a i*(μ d : ℝ) else 0|)^2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)).trans
      (hmean I R a X Y hYX hR hsep)
  have hsq := (Finset.sum_mul_sq_le_sq_mul_sq S w F).trans
    (mul_le_mul_of_nonneg_left hs (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hl : 0 ≤ (X : ℝ)-Y := sub_nonneg.mpr (by exact_mod_cast hYX)
  have hcost : 0 ≤ (∑ n ∈ S, (w n)^2)*
      (E*((X : ℝ)-Y)*(∑ i ∈ I, (a i)^2)+(∑ d ∈ Finset.Icc 1 (I.sup R),
            |∑ i ∈ I, if d ≤ R i then a i*(μ d : ℝ) else 0|)^2) := by positivity
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt hcost]
  exact hsq

/-- Exact bridge to the strict-cutoff slope already used in the prime
period theorem. Integer endpoints are retained with their original side. -/
theorem cutoffSlope_eq_prefix (R : ℕ) (D : ℝ)
    (hlo : (R : ℝ) < Real.exp D) (hhi : Real.exp D ≤ R+1)
    {n : ℕ} (hn : 0 < n) :
    ZetaRieszGlobalCurvature.cutoffSlope D n =
      ∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0 := by
  have hset : (Finset.Icc 1 R).filter (fun d => d ∣ n) =
      n.divisors.filter (fun d => d ≤ R) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_,hdR⟩,hdn⟩
      exact ⟨⟨hdn,hn.ne'⟩,hdR⟩
    · rintro ⟨⟨hdn,_⟩,hdR⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn,hdR⟩,hdn⟩
  rw [← Finset.sum_filter,hset,Finset.sum_filter,ZetaRieszGlobalCurvature.cutoffSlope]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  by_cases hdR : d ≤ R
  · have hdx : (d : ℝ) < Real.exp D := (by exact_mod_cast hdR : (d : ℝ) ≤ R).trans_lt hlo
    have hlog : Real.log d < D := by
      simpa only [Real.log_exp] using Real.log_lt_log hd0 hdx
    rw [if_pos hdR,if_pos (sub_pos.mpr hlog),mul_one]
  · have hdx : Real.exp D ≤ d := hhi.trans (by exact_mod_cast (by omega : R+1 ≤ d))
    have hlog : D ≤ Real.log d := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos D) hdx
    rw [if_neg hdR,if_neg (not_lt.mpr (sub_nonpos.mpr hlog)),mul_zero]

/-- The joint signed estimate applies directly to the original retained
cutoff slopes, with strict endpoints and arbitrary population masks. It
does not assume a bound for the remaining affine moments or their correction. -/
theorem exists_joint_slope_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I S : Finset ℕ) (R : ℕ → ℕ)
      (D a w : ℕ → ℝ) (X Y : ℕ),
      S ⊆ Finset.Ioc Y X → Y ≤ X → (∀ i ∈ I, 0 < R i) →
      (∀ i ∈ I, (R i : ℝ) < Real.exp (D i) ∧ Real.exp (D i) ≤ R i+1) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ I, a i*ZetaRieszGlobalCurvature.cutoffSlope (D i) n);
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*
        (E*((X : ℝ)-Y)*(∑ i ∈ I, (a i)^2)+(∑ i ∈ I, |a i| * (R i : ℝ))^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_joint_signed_bounds hh
  refine ⟨E,hE,fun I S R D a w X Y hS hYX hR hD hsep => ?_⟩
  dsimp only
  have he : (∑ n ∈ S, w n*(∑ i ∈ I, a i*ZetaRieszGlobalCurvature.cutoffSlope (D i) n)) =
      ∑ n ∈ S, w n*(∑ i ∈ I, a i*
        (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [cutoffSlope_eq_prefix (R i) (D i) (hD i hi).1 (hD i hi).2
      (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)]
  rw [he]
  exact hbound I S R a w X Y hS hYX hR hsep
/-- The stronger literal slope bound preserves cancellation in the
counting-error coefficient. All original endpoint and population masks remain;
no source-small bound for this error or the actual weight variation is assumed. -/
theorem exists_joint_cancellation_slope_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I S : Finset ℕ) (R : ℕ → ℕ)
      (D a w : ℕ → ℝ) (X Y : ℕ),
      S ⊆ Finset.Ioc Y X → Y ≤ X → (∀ i ∈ I, 0 < R i) →
      (∀ i ∈ I, (R i : ℝ) < Real.exp (D i) ∧ Real.exp (D i) ≤ R i+1) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ I, a i*ZetaRieszGlobalCurvature.cutoffSlope (D i) n);
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*
        (E*((X : ℝ)-Y)*(∑ i ∈ I, (a i)^2)+(∑ d ∈ Finset.Icc 1 (I.sup R),
            |∑ i ∈ I, if d ≤ R i then a i*(μ d : ℝ) else 0|)^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_joint_cancellation_bounds hh
  refine ⟨E,hE,fun I S R D a w X Y hS hYX hR hD hsep => ?_⟩
  dsimp only
  have he : (∑ n ∈ S, w n*(∑ i ∈ I, a i*ZetaRieszGlobalCurvature.cutoffSlope (D i) n)) =
      ∑ n ∈ S, w n*(∑ i ∈ I, a i*
        (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [cutoffSlope_eq_prefix (R i) (D i) (hD i hi).1 (hD i hi).2
      (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)]
  rw [he]
  exact hbound I S R a w X Y hS hYX hR hsep

end RiemannGaussian.ZetaRieszCrossCutoff
