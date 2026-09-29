/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSieveQuadratic

/-!
# Finite mean-square bounds for the literal Riesz response

The response is unchanged. Its signed divisor quadratic form is bounded
before the finite integer-counting error is paid. Arbitrary finite masks
and signed weights may then be retained in Cauchy--Schwarz. No prime-count
cutoff, density approximation or zero hypothesis enters these estimates.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSieveMean
open ZetaRieszSieveQuadratic

/-- The physical cutoff is literal, including its fractional endpoint. -/
theorem riesz_eq_log_prefix (R : ℕ) {x : ℝ} (hx : 0 < x)
    (hlo : (R : ℝ) ≤ x) (hhi : x < R+1) {n : ℕ} (hn : 0 < n) :
    VaughanLogAverage.riesz (Real.log x) n =
      ∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ)*Real.log (x/d) else 0 := by
  have hset : (Finset.Icc 1 R).filter (fun d => d ∣ n) =
      n.divisors.filter (fun d => d ≤ R) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_,hdR⟩,hdn⟩
      exact ⟨⟨hdn,hn.ne'⟩,hdR⟩
    · rintro ⟨⟨hdn,_⟩,hdR⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn,hdR⟩,hdn⟩
  rw [← Finset.sum_filter,hset,Finset.sum_filter,VaughanLogAverage.riesz]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  by_cases hdM : d ≤ R
  · have hdx : (d : ℝ) ≤ x := (by exact_mod_cast hdM : (d : ℝ) ≤ R).trans hlo
    rw [if_pos hdM,Real.log_div hx.ne' hdR.ne',max_eq_right
      (sub_nonneg.mpr (Real.log_le_log hdR hdx))]
  · have hdx : x < d := hhi.trans_le (by exact_mod_cast (by omega : R+1 ≤ d))
    rw [if_neg hdM,max_eq_left (sub_nonpos.mpr (Real.log_le_log hx hdx.le)),mul_zero]

/-- Exact second moment of a finite divisor sum, with the integer
least-common-multiple quotient retained. -/
theorem mean_square_eq (X R : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 X, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then f d else 0)^2) =
      ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        f d*f e*(X/Nat.lcm d e : ℕ) := by
  have he n : (∑ d ∈ Finset.Icc 1 R, if d ∣ n then f d else 0)^2 =
      ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        if Nat.lcm d e ∣ n then f d*f e else 0 := by
    rw [sq,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [Nat.lcm_dvd_iff]
    by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [hd,he]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hL : 0 < Nat.lcm d e :=
    Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
  rw [sum_Icc_dvd_eq hL]
  simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
  ring

/-- The floor error is paid after all divisor cross terms are summed.
It costs the square of the coefficient mass, with no extra log factor. -/
theorem mean_square_le (X R : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 X, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then f d else 0)^2) ≤
      (X : ℝ)*(∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        f d*f e/(Nat.lcm d e : ℝ))+(∑ d ∈ Finset.Icc 1 R, |f d|)^2 := by
  rw [mean_square_eq]
  have hp d (hd : d ∈ Finset.Icc 1 R) e (he : e ∈ Finset.Icc 1 R) :
      f d*f e*(X/Nat.lcm d e : ℕ) ≤
        (X : ℝ)*(f d*f e/(Nat.lcm d e : ℝ))+|f d| * |f e| := by
    let l := Nat.lcm d e
    have hl : 0 < l := Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    have hlR : (0 : ℝ) < l := by exact_mod_cast hl
    have hlo : ((X/l : ℕ) : ℝ) ≤ (X : ℝ)/l := by
      apply (le_div_iff₀ hlR).mpr
      exact_mod_cast Nat.div_mul_le_self X l
    have hhi : (X : ℝ)/l ≤ (X/l : ℕ)+1 := by
      apply (div_le_iff₀ hlR).mpr
      exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ X hl).le)
    have hb : |((X/l : ℕ) : ℝ)-(X : ℝ)/l| ≤ 1 := abs_le.mpr (by constructor <;> linarith)
    have hh := mul_le_mul_of_nonneg_left hb (abs_nonneg (f d*f e))
    rw [← abs_mul,mul_one] at hh
    have hu := (abs_le.mp hh).2
    rw [abs_mul] at hu
    dsimp only [l] at hu
    calc
      _ = f d*f e*((X/Nat.lcm d e : ℕ)-(X : ℝ)/(Nat.lcm d e : ℝ))+
          (X : ℝ)*(f d*f e/(Nat.lcm d e : ℝ)) := by ring
      _ ≤ |f d| * |f e|+(X : ℝ)*(f d*f e/(Nat.lcm d e : ℝ)) := by linarith only [hu]
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        ((X : ℝ)*(f d*f e/(Nat.lcm d e : ℝ))+|f d| * |f e|) :=
      Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hp d hd e he))
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
      ring

/-- The actual logarithmic coefficients have linear total mass. This
elementary estimate is used only for the finite integer-rounding error. -/
theorem logarithmic_mass_le (R : ℕ) {x : ℝ} (hx : 0 < x) (hlo : (R : ℝ) ≤ x) :
    (∑ d ∈ Finset.Icc 1 R, |(μ d : ℝ)*Real.log (x/d)|) ≤ 4*x := by
  have hb d (hd : d ∈ Finset.Icc 1 R) :
      |(μ d : ℝ)*Real.log (x/d)| ≤ 2*Real.sqrt x*(1/Real.sqrt (d : ℝ)) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hdx : (d : ℝ) ≤ x := (by exact_mod_cast (Finset.mem_Icc.mp hd).2 : (d : ℝ) ≤ R).trans hlo
    have hl : 0 ≤ Real.log (x/d) := Real.log_nonneg ((one_le_div hdR).mpr hdx)
    rw [abs_mul,abs_of_nonneg hl]
    calc
      _ ≤ Real.log (x/d) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (abs_real_moebius_le_one d) hl
      _ ≤ (x/d)^(1/2 : ℝ)/(1/2) :=
        Real.log_le_rpow_div (div_nonneg hx.le hdR.le) (by norm_num)
      _ = _ := by
        rw [← Real.sqrt_eq_rpow,Real.sqrt_div hx.le]
        ring
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 R, 2*Real.sqrt x*(1/Real.sqrt (d : ℝ)) := Finset.sum_le_sum hb
    _ = 2*Real.sqrt x*(∑ d ∈ Finset.Icc 1 R, 1/Real.sqrt (d : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 2*Real.sqrt x*(2*Real.sqrt R) :=
      mul_le_mul_of_nonneg_left (sum_inv_sqrt_Icc_le R) (by positivity)
    _ ≤ 2*Real.sqrt x*(2*Real.sqrt x) := by gcongr
    _ = _ := by nlinarith [Real.sq_sqrt hx.le]

/-- A numerical, all-count second-moment bound for the original Riesz
response. The physical cutoff may be any positive real number. -/
theorem riesz_mean_square_le (X R : ℕ) {x : ℝ} (hx : 0 < x)
    (hlo : (R : ℝ) ≤ x) (hhi : x < R+1) :
    (∑ n ∈ Finset.Icc 1 X, (VaughanLogAverage.riesz (Real.log x) n)^2) ≤
      196*X*(1+Real.log R)+16*x^2 := by
  have he : (∑ n ∈ Finset.Icc 1 X, (VaughanLogAverage.riesz (Real.log x) n)^2) =
      ∑ n ∈ Finset.Icc 1 X, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then
        (μ d : ℝ)*Real.log (x/d) else 0)^2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [riesz_eq_log_prefix R hx hlo hhi (Finset.mem_Icc.mp hn).1]
  rw [he]
  apply (mean_square_le X R (fun d => (μ d : ℝ)*Real.log (x/d))).trans
  have hq := mul_le_mul_of_nonneg_left (logarithmic_quadratic_bound R hlo hhi)
    (Nat.cast_nonneg (α := ℝ) X)
  have hm := (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)).mpr
    (logarithmic_mass_le R hx hlo)
  nlinarith only [hq,hm]

/-- The finite counting error is linear once the actual physical cutoff
is at most the square root of the population length. -/
theorem riesz_mean_square_le_of_cutoff_sq (X R : ℕ) {x : ℝ} (hx : 0 < x)
    (hlo : (R : ℝ) ≤ x) (hhi : x < R+1) (hsize : x^2 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, (VaughanLogAverage.riesz (Real.log x) n)^2) ≤
      (212+196*Real.log R)*X := by
  have h := riesz_mean_square_le X R hx hlo hhi
  nlinarith only [h,hsize]

/-- Any signed finite test keeps its original weights and masks. The
Riesz cross terms have already been bounded jointly over all prime counts. -/
theorem masked_signed_square_le (S : Finset ℕ) (w : ℕ → ℝ) (X R : ℕ)
    (hS : S ⊆ Finset.Icc 1 X) {x : ℝ} (hx : 0 < x)
    (hlo : (R : ℝ) ≤ x) (hhi : x < R+1) :
    (∑ n ∈ S, w n*VaughanLogAverage.riesz (Real.log x) n)^2 ≤
      (∑ n ∈ S, (w n)^2)*(196*X*(1+Real.log R)+16*x^2) := by
  have hmean : (∑ n ∈ S, (VaughanLogAverage.riesz (Real.log x) n)^2) ≤
      196*X*(1+Real.log R)+16*x^2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)).trans
      (riesz_mean_square_le X R hx hlo hhi)
  exact (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => VaughanLogAverage.riesz (Real.log x) n)).trans
      (mul_le_mul_of_nonneg_left hmean (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- The weight of the original real residual; allocation, factorial
order and the complete complex phase are retained exactly. -/
def literalWeight (A : Finset ℕ) (L y : ℝ) (N n : ℕ) : ℝ :=
  (1-ZetaRieszJointAllocation.boundedShare A N n)*(-Real.log n/L)*
    (zetaPrimeLogKernel N (3/2+Complex.I*y) n).re

/-- This is the existing residual coefficient, not a completed surrogate. -/
theorem re_residual_eq_weight (A : Finset ℕ) (L y : ℝ) (N n : ℕ)
    (hs : Squarefree n) (hn : ¬n.Prime) :
    (ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re =
      literalWeight A L y N n*VaughanLogAverage.riesz L n := by
  rw [ZetaRieszJointAllocation.residualCoefficient,
    SquarefreeVaughanLogSource.coefficient,if_pos ⟨hs,hn⟩,← Complex.ofReal_mul,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,literalWeight]
  ring

/-- A numerical two-sided estimate for the original masked residual sum,
with no count or share restriction. Its displayed weight energy and finite
cutoff term must still be paid at source scale; no whole floor is assumed. -/
theorem literal_residual_square_le (A S : Finset ℕ) (X R N : ℕ) (y : ℝ)
    (hS : S ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S, Squarefree n ∧ ¬n.Prime)
    {x : ℝ} (hx : 0 < x) (hlo : (R : ℝ) ≤ x) (hhi : x < R+1) :
    ((∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A (Real.log x) N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)^2 ≤
      (∑ n ∈ S, (literalWeight A (Real.log x) y N n)^2)*
        (196*X*(1+Real.log R)+16*x^2) := by
  rw [Complex.re_sum]
  have he : (∑ n ∈ S, (ZetaRieszJointAllocation.residualCoefficient A (Real.log x) N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) =
      ∑ n ∈ S, literalWeight A (Real.log x) y N n*VaughanLogAverage.riesz (Real.log x) n :=
    Finset.sum_congr rfl (fun n hn => re_residual_eq_weight A (Real.log x) y N n
      (hSF n hn).1 (hSF n hn).2)
  rw [he]
  exact masked_signed_square_le S (literalWeight A (Real.log x) y N) X R hS hx hlo hhi

/-- Both signed sides follow from the same all-count arithmetic budget.
The prime-period weight energy remains explicit, so this is not the final
source-normalized numerical floor or ceiling. -/
theorem literal_residual_bounds (A S : Finset ℕ) (X R N : ℕ) (y : ℝ)
    (hS : S ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S, Squarefree n ∧ ¬n.Prime)
    {x : ℝ} (hx : 0 < x) (hlo : (R : ℝ) ≤ x) (hhi : x < R+1) :
    let B := Real.sqrt ((∑ n ∈ S, (literalWeight A (Real.log x) y N n)^2)*
      (196*X*(1+Real.log R)+16*x^2))
    let J := (∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A (Real.log x) N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re;
    -B ≤ J ∧ J ≤ B := by
  dsimp only
  have hE : 0 ≤ (∑ n ∈ S, (literalWeight A (Real.log x) y N n)^2)*
      (196*X*(1+Real.log R)+16*x^2) := by
    have hlog := Real.log_natCast_nonneg R
    positivity
  have hsq := literal_residual_square_le A S X R N y hS hSF hx hlo hhi
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rwa [sq_abs,Real.sq_sqrt hE]

end RiemannGaussian.ZetaRieszSieveMean
