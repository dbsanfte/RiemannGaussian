/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSquarefreeDualMean

/-!
# A uniform squarefree mean bound for every cutoff

Exact complementary divisor pairs are combined before their single integer
rounding error is charged. The reflected error is quadratic, and combines
with the direct quadratic error to give a linear population mean at every
cutoff. The resulting two-sided inequalities apply to the original Riesz
difference, strict slope, and literal marked-prime fibre. Correlated weight
energy is retained explicitly; no whole source floor or ceiling is assumed.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSquarefreeUniformMean

private theorem floor_error {l : ℕ} (hl : 0 < l) (X Y : ℕ) :
    |((X/l : ℕ) : ℝ)-(Y/l : ℕ)-((X : ℝ)-Y)/l| ≤ 1 := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hlo (T : ℕ) : ((T/l : ℕ) : ℝ) ≤ (T : ℝ)/l := by
    apply (le_div_iff₀ hlR).mpr
    exact_mod_cast Nat.div_mul_le_self T l
  have hhi (T : ℕ) : (T : ℝ)/l ≤ (T/l : ℕ)+1 := by
    apply (div_le_iff₀ hlR).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ T hl).le)
  rw [sub_div]
  exact abs_le.mpr (by constructor <;> linarith only [hlo X,hlo Y,hhi X,hhi Y])

private theorem interval_count (X Y l : ℕ) (hYX : Y ≤ X) (hl : 0 < l) (c : ℝ) :
    (∑ n ∈ Finset.Ioc Y X, if l ∣ n then c else 0) =
      c*(((X/l : ℕ) : ℝ)-(Y/l : ℕ)) := by
  have hset : Finset.Icc 1 X \ Finset.Icc 1 Y = Finset.Ioc Y X := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have h := Finset.sum_sdiff (f := fun n => if l ∣ n then c else 0)
    (Finset.Icc_subset_Icc (show (1 : ℕ) ≤ 1 from le_rfl) hYX)
  rw [hset,sum_Icc_dvd_eq hl,sum_Icc_dvd_eq hl] at h
  simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul] at h
  nlinarith only [h]

private theorem moving_pair (X R Q d e : ℕ) (hRX : R*Q ≤ X)
    (hd : d ∈ Finset.Icc 1 Q) (he : e ∈ Finset.Icc 1 Q) :
    (∑ n ∈ Finset.Icc 1 X, if R*max d e < n ∧ Nat.lcm d e ∣ n
      then (μ d : ℝ)*(μ e : ℝ) else 0) =
      (μ d : ℝ)*(μ e : ℝ)*(((X/Nat.lcm d e : ℕ) : ℝ)-
        (R*max d e/Nat.lcm d e : ℕ)) := by
  have hY : R*max d e ≤ X := (Nat.mul_le_mul_left R
    (max_le (Finset.mem_Icc.mp hd).2 (Finset.mem_Icc.mp he).2)).trans hRX
  have hset : (Finset.Icc 1 X).filter (fun n => R*max d e < n) =
      Finset.Ioc (R*max d e) X := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  simp_rw [ite_and]
  rw [← Finset.sum_filter,hset]
  exact interval_count X (R*max d e) (Nat.lcm d e) hY
    (Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1) _

private theorem moving_mean_le (X R Q : ℕ) (hRX : R*Q ≤ X) :
    (∑ n ∈ Finset.Icc 1 X,
      (∑ d ∈ Finset.Icc 1 Q, if R*d < n ∧ d ∣ n then (μ d : ℝ) else 0)^2) ≤
      (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 Q, ∑ e ∈ Finset.Icc 1 Q,
        if R*max d e < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0)+
      (Q : ℝ)^2 := by
  have hex n :
      (∑ d ∈ Finset.Icc 1 Q, if R*d < n ∧ d ∣ n then (μ d : ℝ) else 0)^2 =
        ∑ d ∈ Finset.Icc 1 Q, ∑ e ∈ Finset.Icc 1 Q,
          if R*max d e < n ∧ Nat.lcm d e ∣ n then (μ d : ℝ)*(μ e : ℝ) else 0 := by
    rw [sq,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    have ht : R*max d e < n ↔ R*d < n ∧ R*e < n := by
      rw [mul_max,max_lt_iff]
    simp only [ht,Nat.lcm_dvd_iff]
    split_ifs <;> simp_all
  have hmain d (hd : d ∈ Finset.Icc 1 Q) e (he : e ∈ Finset.Icc 1 Q) :
      (∑ n ∈ Finset.Icc 1 X,
        if R*max d e < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0) =
      ((X : ℝ)-(R*max d e : ℕ))*((μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)) := by
    have hY : R*max d e ≤ X := (Nat.mul_le_mul_left R
      (max_le (Finset.mem_Icc.mp hd).2 (Finset.mem_Icc.mp he).2)).trans hRX
    have hset : (Finset.Icc 1 X).filter (fun n => R*max d e < n) =
        Finset.Ioc (R*max d e) X := by
      ext n
      simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
      omega
    rw [← Finset.sum_filter,hset,Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul,
      Nat.cast_sub hY]
  have hp d (hd : d ∈ Finset.Icc 1 Q) e (he : e ∈ Finset.Icc 1 Q) :
      (∑ n ∈ Finset.Icc 1 X, if R*max d e < n ∧ Nat.lcm d e ∣ n
        then (μ d : ℝ)*(μ e : ℝ) else 0) ≤
      (∑ n ∈ Finset.Icc 1 X,
        if R*max d e < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0)+1 := by
    rw [moving_pair X R Q d e hRX hd he,hmain d hd e he]
    have hf := floor_error (Nat.lcm_pos (Finset.mem_Icc.mp hd).1
      (Finset.mem_Icc.mp he).1) X (R*max d e)
    have hm : |(μ d : ℝ)*(μ e : ℝ)| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_real_moebius_le_one d,abs_real_moebius_le_one e,
        abs_nonneg (μ d : ℝ),abs_nonneg (μ e : ℝ)]
    have h := (abs_le.mp ((by
      rw [abs_mul]
      exact (mul_le_mul hf hm (abs_nonneg _) (by norm_num)).trans (by norm_num)
      : |(((X/Nat.lcm d e : ℕ) : ℝ)-(R*max d e/Nat.lcm d e : ℕ)-
          ((X : ℝ)-(R*max d e : ℕ))/(Nat.lcm d e : ℝ))*
          ((μ d : ℝ)*(μ e : ℝ))| ≤ 1))).2
    calc
      _ = ((X : ℝ)-(R*max d e : ℕ))*((μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ))+
          ((((X/Nat.lcm d e : ℕ) : ℝ)-(R*max d e/Nat.lcm d e : ℕ)-
            ((X : ℝ)-(R*max d e : ℕ))/(Nat.lcm d e : ℝ))*((μ d : ℝ)*(μ e : ℝ))) := by ring
      _ ≤ _ := by linarith only [h]
  simp_rw [hex]
  rw [Finset.sum_comm]
  conv_rhs => lhs; rw [Finset.sum_comm]
  calc
    _ = ∑ d ∈ Finset.Icc 1 Q, ∑ e ∈ Finset.Icc 1 Q,
        ∑ n ∈ Finset.Icc 1 X, if R*max d e < n ∧ Nat.lcm d e ∣ n
          then (μ d : ℝ)*(μ e : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
    _ ≤ ∑ d ∈ Finset.Icc 1 Q, ∑ e ∈ Finset.Icc 1 Q,
        ((∑ n ∈ Finset.Icc 1 X,
          if R*max d e < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0)+1) :=
      Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hp d hd e he))
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Nat.card_Icc,
        Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
      rw [← sq]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]

private theorem moving_prefix_eq (R Q n : ℕ) (hR : 0 < R) (hn : 0 < n)
    (hQ : (n-1)/R ≤ Q) (f : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 Q, if R*d < n then f d else 0) =
      ∑ d ∈ Finset.Icc 1 ((n-1)/R), f d := by
  have hcond d : R*d < n ↔ d ≤ (n-1)/R := by
    rw [Nat.le_div_iff_mul_le hR]
    rw [Nat.mul_comm d R]
    omega
  have hset : (Finset.Icc 1 Q).filter (fun d => R*d < n) =
      Finset.Icc 1 ((n-1)/R) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,hcond]
    omega
  rw [← Finset.sum_filter,hset]

private theorem moving_main_le (E : ℝ)
    (hE : ∀ Q : ℕ, (∑ d ∈ Finset.Icc 1 Q, ∑ e ∈ Finset.Icc 1 Q,
      (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)) ≤ E)
    (X R : ℕ) (hR : 0 < R) :
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 (X/R),
      ∑ e ∈ Finset.Icc 1 (X/R),
        if R*max d e < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0) ≤ E*X := by
  have hp n (hn : n ∈ Finset.Icc 1 X) :
      (∑ d ∈ Finset.Icc 1 (X/R), ∑ e ∈ Finset.Icc 1 (X/R),
        if R*max d e < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0) ≤ E := by
    have hn0 := (Finset.mem_Icc.mp hn).1
    have hk : (n-1)/R ≤ X/R := Nat.div_le_div_right (by have := (Finset.mem_Icc.mp hn).2; omega)
    calc
      _ = ∑ d ∈ Finset.Icc 1 (X/R), if R*d < n then
          (∑ e ∈ Finset.Icc 1 (X/R),
            if R*e < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : R*d < n <;> simp only [mul_max,max_lt_iff,ite_and,hd,
          if_true,if_false,Finset.sum_const_zero]
      _ = ∑ d ∈ Finset.Icc 1 ((n-1)/R), ∑ e ∈ Finset.Icc 1 ((n-1)/R),
          (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) := by
        rw [moving_prefix_eq R (X/R) n hR hn0 hk]
        apply Finset.sum_congr rfl
        intro d _
        exact moving_prefix_eq R (X/R) n hR hn0 hk _
      _ ≤ E := hE _
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 X, E := Finset.sum_le_sum hp
    _ = _ := by simp [mul_comm]

/-- Keeping all moving cutoff blocks together pays just one rounding
error per divisor pair, hence a square rather than a cubic error. -/
theorem exists_dual_square_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ), 0 < R →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤
        E*X+((X/R : ℕ) : ℝ)^2 := by
  obtain ⟨E,hE,hquad⟩ := ZetaRieszSharpSieve.exists_sharp_quadratic_bound
  refine ⟨E,hE,fun X R S hR hS hSF => ?_⟩
  have he n (hn : n ∈ S) :
      (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2 =
        (∑ d ∈ Finset.Icc 1 (X/R), if R*d < n ∧ d ∣ n then (μ d : ℝ) else 0)^2 := by
    have hn1 := (Finset.mem_Ioc.mp (hS hn)).1
    have hk : (n-1)/R ≤ X/R := Nat.div_le_div_right (by have := (Finset.mem_Ioc.mp (hS hn)).2; omega)
    simp_rw [ite_and]
    rw [moving_prefix_eq R (X/R) n hR (by omega) hk,
      ZetaRieszSquarefreeDualMean.sharp_reflection (hSF n hn) (by omega) hR,
      mul_pow,neg_sq]
    have hm : (μ n : ℝ)^2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hSF n hn)
    rw [hm,one_mul]
  rw [Finset.sum_congr rfl he]
  have hs : S ⊆ Finset.Icc 1 X := by
    intro n hn
    have h := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Icc.mpr ⟨by omega,h.2⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)).trans
    ((moving_mean_le X R (X/R) (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self X R)).trans
      (add_le_add_left (moving_main_le E hquad X R hR) _))

/-- Every positive cutoff now has a LINEAR squarefree population mean.
The direct and reflected square errors cover complementary ranges. -/
theorem exists_uniform_linear_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ), 0 < R →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤ E*X := by
  obtain ⟨E,hE,hfirst⟩ := ZetaRieszSharpSieve.exists_sharp_mean_bound
  obtain ⟨F,hF,hsecond⟩ := exists_dual_square_mean_bound
  refine ⟨E+F+1,by linarith,fun X R S hR hS hSF => ?_⟩
  have hx : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  by_cases hsmall : R^2 ≤ X
  · have hs : S ⊆ Finset.Icc 1 X := by
      intro n hn
      have h := Finset.mem_Ioc.mp (hS hn)
      exact Finset.mem_Icc.mpr ⟨by omega,h.2⟩
    have h := (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)).trans
      (hfirst X R)
    have he : (R : ℝ)^2 ≤ X := by exact_mod_cast hsmall
    nlinarith only [h,he,mul_nonneg hF.le hx]
  · have hR2 : X ≤ R^2 := Nat.le_of_lt (Nat.lt_of_not_ge hsmall)
    have hq : (X/R)^2 ≤ X := by
      have hp := Nat.pow_le_pow_left (Nat.div_mul_le_self X R) 2
      rw [mul_pow] at hp
      have hc := (Nat.mul_le_mul_left ((X/R)^2) hR2).trans hp
      by_cases hX : X = 0
      · simp [hX]
      have hx0 := Nat.pos_of_ne_zero hX
      rw [pow_two X] at hc
      exact Nat.le_of_mul_le_mul_right hc hx0
    have he : (((X/R : ℕ) : ℝ)^2) ≤ X := by exact_mod_cast hq
    have h := hsecond X R S hR hS hSF
    nlinarith only [h,he,mul_nonneg hE.le hx]

/-- Both original Riesz endpoints are combined before estimating. The
mean is linear in the population for EVERY real cutoff pair. -/
theorem exists_riesz_difference_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S : Finset ℕ) (A B : ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) → A ≤ B →
      (∑ n ∈ S, (VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)^2) ≤
        (B-A)^2*(E*X) := by
  obtain ⟨E,hE,hmean⟩ := exists_uniform_linear_mean_bound
  refine ⟨E,hE,fun X S A B hS hSF hAB => ?_⟩
  obtain ⟨R,hR⟩ := exists_nat_gt (Real.exp B)
  apply ZetaRieszCutoffMean.riesz_difference_mean_le S R (E*X) A B
    (fun n hn => by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)
    (by positivity) hAB (by linarith)
  intro k hk
  exact hmean X k S (Finset.mem_Icc.mp hk).1 hS hSF

/-- Both signed sides have one all-cutoff/all-count linear mean budget.
Only the actual correlated weight energy remains on the right. -/
theorem exists_joint_riesz_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) (A B : ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) → A ≤ B →
      let J := ∑ n ∈ S, w n*(VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n);
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*(B-A)^2*(E*X));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_riesz_difference_mean_bound
  refine ⟨E,hE,fun X S w A B hS hSF hAB => ?_⟩
  dsimp only
  have hw : 0 ≤ ∑ n ∈ S, (w n)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => VaughanLogAverage.riesz B n-VaughanLogAverage.riesz A n)).trans
      (mul_le_mul_of_nonneg_left (hmean X S A B hS hSF hAB) hw)
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  simpa only [mul_assoc] using hs

/-- The linear mean bound applies to the literal arithmetic prime fibre,
including every cofactor count, original finite mask and oscillating weight.
Its remaining energy is explicit; it is not a source-normalized floor. -/
theorem exists_literal_prime_fibre_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X N p : ℕ) (A S : Finset ℕ) (L y : ℝ),
      S ⊆ Finset.Ioc 1 X →
      (∀ a ∈ S, Squarefree a ∧ 2 ≤ a.primeFactors.card) →
      p.Prime → (∀ a ∈ S, ¬p ∣ a) →
      let K := Real.sqrt ((∑ a ∈ S,
        (ZetaRieszGlobalPrimePeriod.signedPrimeWeight A L N y a p/a)^2)*
        (Real.log p)^2*(E*X));
      let J := (∑ a ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re;
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_joint_riesz_bounds
  refine ⟨E,hE,fun X N p A S L y hS hSF hp hpd => ?_⟩
  let g := fun a => ZetaRieszGlobalPrimePeriod.signedPrimeWeight A L N y a p/a
  let w := fun a => -(μ a : ℝ)*g a
  have he a (ha : a ∈ S) :
      (ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      w a*(VaughanLogAverage.riesz L a-VaughanLogAverage.riesz (L-Real.log p) a) := by
    rw [ZetaRieszGlobalPrimePeriod.re_residual_atom
      (hSF a ha).1 (hSF a ha).2 hp (hpd a ha) A L y N,
      ZetaRieszSquarefreeDualMean.response_reflection L (Real.log p) (hSF a ha).1
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
  have hb := hbound X S w (L-Real.log p) L hS
    (fun a ha => (hSF a ha).1) (by linarith)
  dsimp only at hb ⊢
  rw [hw,show L-(L-Real.log p) = Real.log p by ring] at hb
  rw [Complex.re_sum,Finset.sum_congr rfl he]
  exact hb

/-- The all-cutoff linear budget also controls the original strict
cutoff slope with arbitrary real correlated weights, on both signed sides. -/
theorem exists_slope_signed_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) (D : ℝ),
      0 < R → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (R : ℝ) < Real.exp D → Real.exp D ≤ R+1 →
      let J := ∑ n ∈ S, w n*ZetaRieszGlobalCurvature.cutoffSlope D n;
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*(E*X));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_uniform_linear_mean_bound
  refine ⟨E,hE,fun X R S w D hR hS hSF hlo hhi => ?_⟩
  dsimp only
  have he n (hn : n ∈ S) : ZetaRieszGlobalCurvature.cutoffSlope D n =
      ∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0 :=
    ZetaRieszCrossCutoff.cutoffSlope_eq_prefix R D hlo hhi
      (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)
  have hm : (∑ n ∈ S, (ZetaRieszGlobalCurvature.cutoffSlope D n)^2) ≤ E*X := by
    calc
      _ = ∑ n ∈ S, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2 :=
        Finset.sum_congr rfl (fun n hn => by rw [he n hn])
      _ ≤ _ := hmean X R S hR hS hSF
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => ZetaRieszGlobalCurvature.cutoffSlope D n)).trans
      (mul_le_mul_of_nonneg_left hm (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  exact hs

end RiemannGaussian.ZetaRieszSquarefreeUniformMean
