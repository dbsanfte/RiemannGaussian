/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSquarefreeUniformMean

/-!
# Joint squarefree means with every finite counting error paid

Small direct cutoffs and large complementary cutoffs share the same
inverse-square logarithmic separation bound, including their literal
integer rounding errors. One Schur estimate controls the complete signed
family independently of its size. The squarefree mean is linear in X,
with no residual counting-error term. Common correlated weights remain
explicit; no source-small prime-energy bound is assumed.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSquarefreeSeparatedMean

private theorem log_square_le {x : ℝ} (hx : 1 ≤ x) :
    (4+Real.log x)^2 ≤ 16*x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have he := Real.add_one_le_exp (Real.log x/2)
  have hb : 4+Real.log x ≤ 4*Real.exp (Real.log x/2) := by linarith
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 4+Real.log x) hb 2
  have heq : (Real.exp (Real.log x/2))^2 = x := by
    rw [pow_two,← Real.exp_add,show Real.log x/2+Real.log x/2 = Real.log x by ring,
      Real.exp_log hx0]
  simpa only [mul_pow,show (4 : ℝ)^2 = 16 by norm_num,heq] using hp

private theorem quotient_log_error {T R : ℕ} (hR : 0 < R) (hq : 0 < T/R) :
    0 ≤ Real.log T-Real.log R-Real.log (T/R : ℕ) ∧
      Real.log T-Real.log R-Real.log (T/R : ℕ) ≤ 1 := by
  have hT : 0 < T := by
    by_contra h
    have hz : T = 0 := by omega
    simp [hz] at hq
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hqr : (0 : ℝ) < (T/R : ℕ) := by exact_mod_cast hq
  have hlo : ((T/R : ℕ) : ℝ) ≤ (T : ℝ)/R := by
    apply (le_div_iff₀ hRR).mpr
    exact_mod_cast Nat.div_mul_le_self T R
  have hhi : (T : ℝ)/R ≤ 2*(T/R : ℕ) := by
    apply (div_le_iff₀ hRR).mpr
    have hh := Nat.lt_mul_div_succ T hR
    have hq1 : (T/R+1) ≤ 2*(T/R) := by omega
    exact_mod_cast hh.le.trans (by
      simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left R hq1)
  have hx : 0 < ((T : ℝ)/R)/((T/R : ℕ) : ℝ) := by positivity
  have hx1 : 1 ≤ ((T : ℝ)/R)/((T/R : ℕ) : ℝ) := (one_le_div hqr).mpr hlo
  have hx2 : ((T : ℝ)/R)/((T/R : ℕ) : ℝ) ≤ 2 := (div_le_iff₀ hqr).mpr hhi
  have hl := Real.log_nonneg hx1
  have hu := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (div_pos hTR hRR).ne' hqr.ne',Real.log_div hTR.ne' hRR.ne'] at hl hu
  exact ⟨hl,by linarith⟩

/-- Complementary integer rounding changes logarithmic separation by
at most one, whenever the two complementary cutoffs are nonzero. -/
theorem quotient_log_separation {T R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (hqR : 0 < T/R) (hqS : 0 < T/S) :
    |Real.log R-Real.log S| ≤
      |Real.log (T/R : ℕ)-Real.log (T/S : ℕ)|+1 := by
  have heR := quotient_log_error hR hqR
  have heS := quotient_log_error hS hqS
  have he : |(Real.log T-Real.log S-Real.log (T/S : ℕ))-
      (Real.log T-Real.log R-Real.log (T/R : ℕ))| ≤ 1 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    _ = |(Real.log (T/S : ℕ)-Real.log (T/R : ℕ))+
        ((Real.log T-Real.log S-Real.log (T/S : ℕ))-
          (Real.log T-Real.log R-Real.log (T/R : ℕ)))| := by congr 1; ring
    _ ≤ |Real.log (T/S : ℕ)-Real.log (T/R : ℕ)|+1 :=
      (abs_add_le _ _).trans (add_le_add_right he _)
    _ = _ := by rw [abs_sub_comm]

/-- The actual complementary cross quadratic retains inverse-square
separation uniformly in the moving numerator. Zero cutoffs are retained. -/
theorem exists_reflected_cross_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T R S : ℕ, 0 < R → 0 < S →
      |∑ d ∈ Finset.Icc 1 (T/R), ∑ e ∈ Finset.Icc 1 (T/S),
        (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)| ≤
      C/(4+|Real.log R-Real.log S|)^2 := by
  obtain ⟨C,hC,hbound⟩ := ZetaRieszCrossCutoff.exists_symmetric_cross_bound
  refine ⟨4*C,by positivity,fun T R S hR hS => ?_⟩
  rcases (T/R).eq_zero_or_pos with hz | hp
  · simp only [hz,Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),Finset.sum_empty,abs_zero]
    positivity
  rcases (T/S).eq_zero_or_pos with hz | hq
  · simp only [hz,Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),Finset.sum_empty,
      Finset.sum_const_zero,abs_zero]
    positivity
  have he := quotient_log_separation hR hS hp hq
  have hbase := (le_div_iff₀ (by positivity)).mp (hbound (T/R) (T/S) hp hq)
  have hsep : (4+|Real.log R-Real.log S|)^2 ≤
      4*(4+|Real.log (T/R : ℕ)-Real.log (T/S : ℕ)|)^2 := by
    have hh : 4+|Real.log R-Real.log S| ≤
        2*(4+|Real.log (T/R : ℕ)-Real.log (T/S : ℕ)|) := by linarith [abs_nonneg (Real.log (T/R : ℕ)-Real.log (T/S : ℕ))]
    have hh' := pow_le_pow_left₀ (by positivity : 0 ≤ 4+|Real.log R-Real.log S|) hh 2
    nlinarith only [hh']
  apply (le_div_iff₀ (by positivity)).mpr
  have hs := mul_le_mul_of_nonneg_left hsep (abs_nonneg
    (∑ d ∈ Finset.Icc 1 (T/R), ∑ e ∈ Finset.Icc 1 (T/S),
      (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)))
  nlinarith only [hs,hbase]

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

private theorem reorder (X D E : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 E, f n d e) =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 E, ∑ n ∈ Finset.Icc 1 X, f n d e := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]

private theorem incidence_cross_error (X D E : ℕ) (a b : ℕ → ℕ)
    (ha : ∀ d ∈ Finset.Icc 1 D, a d ≤ X)
    (hb : ∀ e ∈ Finset.Icc 1 E, b e ≤ X) :
    |(∑ n ∈ Finset.Icc 1 X,
       (∑ d ∈ Finset.Icc 1 D, if a d < n ∧ d ∣ n then (μ d : ℝ) else 0)*
       (∑ e ∈ Finset.Icc 1 E, if b e < n ∧ e ∣ n then (μ e : ℝ) else 0))-
      ∑ n ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 E,
        if max (a d) (b e) < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0| ≤
      (D : ℝ)*E := by
  have hex n :
      (∑ d ∈ Finset.Icc 1 D, if a d < n ∧ d ∣ n then (μ d : ℝ) else 0)*
      (∑ e ∈ Finset.Icc 1 E, if b e < n ∧ e ∣ n then (μ e : ℝ) else 0) =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 E,
        if max (a d) (b e) < n ∧ Nat.lcm d e ∣ n then (μ d : ℝ)*(μ e : ℝ) else 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [max_lt_iff,Nat.lcm_dvd_iff]
    split_ifs <;> simp_all
  have hp d (hd : d ∈ Finset.Icc 1 D) e (he : e ∈ Finset.Icc 1 E) :
      |(∑ n ∈ Finset.Icc 1 X,
          if max (a d) (b e) < n ∧ Nat.lcm d e ∣ n then (μ d : ℝ)*(μ e : ℝ) else 0)-
        ∑ n ∈ Finset.Icc 1 X,
          if max (a d) (b e) < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0| ≤ 1 := by
    let Y := max (a d) (b e)
    have hY : Y ≤ X := max_le (ha d hd) (hb e he)
    have hset : (Finset.Icc 1 X).filter (fun n => Y < n) = Finset.Ioc Y X := by
      ext n
      simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
      omega
    have hl : 0 < Nat.lcm d e := Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    change |(∑ n ∈ Finset.Icc 1 X, if Y < n ∧ _ then _ else _)-
      ∑ n ∈ Finset.Icc 1 X, if Y < n then _ else _| ≤ 1
    simp_rw [ite_and]
    rw [← Finset.sum_filter,hset,interval_count X Y (Nat.lcm d e) hY hl,
      ← Finset.sum_filter,hset,Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul,Nat.cast_sub hY]
    have hm : |(μ d : ℝ)*(μ e : ℝ)| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_real_moebius_le_one d,abs_real_moebius_le_one e,
        abs_nonneg (μ d : ℝ),abs_nonneg (μ e : ℝ)]
    calc
      _ = |((μ d : ℝ)*(μ e : ℝ))*
          (((X/Nat.lcm d e : ℕ) : ℝ)-(Y/Nat.lcm d e : ℕ)-
            ((X : ℝ)-Y)/(Nat.lcm d e : ℝ))| := by congr 1; ring
      _ ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul hm (floor_error hl X Y) (abs_nonneg _) (by norm_num)).trans (by norm_num)
  simp_rw [hex]
  rw [reorder X D E,reorder X D E]
  calc
    _ = |∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 E,
        ((∑ n ∈ Finset.Icc 1 X, if max (a d) (b e) < n ∧ Nat.lcm d e ∣ n
          then (μ d : ℝ)*(μ e : ℝ) else 0)-
          ∑ n ∈ Finset.Icc 1 X, if max (a d) (b e) < n
            then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0)| := by
      simp only [Finset.sum_sub_distrib]
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 E,
        |(∑ n ∈ Finset.Icc 1 X, if max (a d) (b e) < n ∧ Nat.lcm d e ∣ n
          then (μ d : ℝ)*(μ e : ℝ) else 0)-
          ∑ n ∈ Finset.Icc 1 X, if max (a d) (b e) < n
            then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun d _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, ∑ _e ∈ Finset.Icc 1 E, (1 : ℝ) :=
      Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hp d hd e he))
    _ = _ := by simp

private theorem small_pair_cost {X R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (hRX : R^2 ≤ X) (hSX : S^2 ≤ X) :
    (R : ℝ)*S ≤ 16*(X : ℝ)/(4+|Real.log R-Real.log S|)^2 := by
  suffices h : ∀ r s : ℝ, 0 < r → r ≤ s → s^2 ≤ X →
      r*s*(4+|Real.log r-Real.log s|)^2 ≤ 16*X by
    apply (le_div_iff₀ (by positivity)).mpr
    rcases le_total R S with hrs | hsr
    · exact h R S (by exact_mod_cast hR) (by exact_mod_cast hrs) (by exact_mod_cast hSX)
    · simpa only [mul_comm (S : ℝ) R,abs_sub_comm (Real.log S) (Real.log R)] using
        h S R (by exact_mod_cast hS) (by exact_mod_cast hsr) (by exact_mod_cast hRX)
  intro r s hr hrs hsX
  have hs : 0 < s := hr.trans_le hrs
  have hlog : |Real.log r-Real.log s| = Real.log (s/r) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hr hrs)),neg_sub,
      Real.log_div hs.ne' hr.ne']
  have hb := mul_le_mul_of_nonneg_left (log_square_le ((one_le_div hr).mpr hrs))
    (mul_nonneg hr.le hs.le)
  rw [hlog]
  have he : r*s*(16*(s/r)) = 16*s^2 := by field_simp
  rw [he] at hb
  linarith only [hb,hsX]

private theorem large_pair_cost {X R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (hRX : X ≤ R^2) (hSX : X ≤ S^2) :
    ((X/R : ℕ) : ℝ)*(X/S : ℕ) ≤ 16*(X : ℝ)/(4+|Real.log R-Real.log S|)^2 := by
  have one_side : ∀ r s : ℕ, 0 < r → r ≤ s → X ≤ r^2 →
      ((X/r : ℕ) : ℝ)*(X/s : ℕ)*(4+|Real.log r-Real.log s|)^2 ≤ 16*X := by
    intro r s hr hrs hrX
    have hs : 0 < s := hr.trans_le hrs
    have hrr : (0 : ℝ) < r := by exact_mod_cast hr
    have hss : (0 : ℝ) < s := by exact_mod_cast hs
    have hrs' : (r : ℝ) ≤ s := by exact_mod_cast hrs
    have hlog : |Real.log r-Real.log s| = Real.log ((s : ℝ)/r) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hrr hrs')),neg_sub,
        Real.log_div hss.ne' hrr.ne']
    have hb := mul_le_mul_of_nonneg_left (log_square_le ((one_le_div hrr).mpr hrs'))
      (show 0 ≤ ((X/r : ℕ) : ℝ)*(X/s : ℕ) by positivity)
    have hpR : ((X/r : ℕ) : ℝ)*r ≤ X := by exact_mod_cast Nat.div_mul_le_self X r
    have hpS : ((X/s : ℕ) : ℝ)*s ≤ X := by exact_mod_cast Nat.div_mul_le_self X s
    have hrX' : (X : ℝ) ≤ (r : ℝ)^2 := by exact_mod_cast hrX
    have hx : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    have hprod := mul_le_mul hpR hpS (by positivity) hx
    have hp : ((X/r : ℕ) : ℝ)*(X/s : ℕ)*s ≤ (X : ℝ)*r := by
      have hh : (((X/r : ℕ) : ℝ)*(X/s : ℕ)*s)*(r : ℝ) ≤ ((X : ℝ)*r)*r := by
        nlinarith only [hprod,mul_le_mul_of_nonneg_left hrX' hx]
      exact (mul_le_mul_iff_left₀ hrr).mp hh
    have hquot : ((X/r : ℕ) : ℝ)*(X/s : ℕ)*((s : ℝ)/r) ≤ X := by
      rw [← mul_div_assoc]
      exact (div_le_iff₀ hrr).mpr hp
    rw [hlog]
    nlinarith only [hb,hquot]
  apply (le_div_iff₀ (by positivity)).mpr
  rcases le_total R S with hrs | hsr
  · exact one_side R S hR hrs hRX
  · simpa only [mul_comm (((X/S : ℕ) : ℝ)) ((X/R : ℕ) : ℝ),
      abs_sub_comm (Real.log S) (Real.log R)] using one_side S R hS hsr hSX

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

/-- The finite direct Gram kernel keeps its logarithmic decay when
both cutoffs are below the square-root transition. -/
theorem exists_small_gram_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X R S : ℕ, 0 < R → 0 < S → R^2 ≤ X → S^2 ≤ X →
      |∑ n ∈ Finset.Icc 1 X,
        (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)*
        (∑ e ∈ Finset.Icc 1 S, if e ∣ n then (μ e : ℝ) else 0)| ≤
        C*X/(4+|Real.log R-Real.log S|)^2 := by
  obtain ⟨C,hC,hbound⟩ := ZetaRieszCrossCutoff.exists_symmetric_cross_bound
  refine ⟨C+16,by linarith,fun X R S hR hS hRX hSX => ?_⟩
  let G := ∑ n ∈ Finset.Icc 1 X,
    (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)*
    (∑ e ∈ Finset.Icc 1 S, if e ∣ n then (μ e : ℝ) else 0)
  let Q := ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 S,
    (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)
  have hc := incidence_cross_error X R S (fun _ => 0) (fun _ => 0)
    (fun _ _ => Nat.zero_le X) (fun _ _ => Nat.zero_le X)
  have he : (∑ n ∈ Finset.Icc 1 X,
      (∑ d ∈ Finset.Icc 1 R, if 0 < n ∧ d ∣ n then (μ d : ℝ) else 0)*
      (∑ e ∈ Finset.Icc 1 S, if 0 < n ∧ e ∣ n then (μ e : ℝ) else 0)) = G := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    simp only [hn0,true_and]
  have hm : (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 S,
      if max 0 0 < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0) = (X : ℝ)*Q := by
    calc
      _ = ∑ _n ∈ Finset.Icc 1 X, Q := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
        simp only [max_self,hn0,if_true,Q]
      _ = _ := by simp
  rw [he,hm] at hc
  have hq : |(X : ℝ)*Q| ≤ (X : ℝ)*(C/(4+|Real.log R-Real.log S|)^2) := by
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg X)]
    exact mul_le_mul_of_nonneg_left (hbound R S hR hS) (Nat.cast_nonneg X)
  change |G| ≤ _
  calc
    _ = |(G-(X : ℝ)*Q)+(X : ℝ)*Q| := by congr 1; ring
    _ ≤ |G-(X : ℝ)*Q|+|(X : ℝ)*Q| := abs_add_le _ _
    _ ≤ 16*(X : ℝ)/(4+|Real.log R-Real.log S|)^2+
        (X : ℝ)*(C/(4+|Real.log R-Real.log S|)^2) :=
      add_le_add (hc.trans (small_pair_cost hR hS hRX hSX)) hq
    _ = _ := by ring

/-- The finite complementary Gram kernel has the SAME separation
budget above the square-root transition. All moving cutoffs remain exact. -/
theorem exists_large_gram_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X R S : ℕ, 0 < R → 0 < S → X ≤ R^2 → X ≤ S^2 →
      |∑ n ∈ Finset.Icc 1 X,
        (∑ d ∈ Finset.Icc 1 ((n-1)/R), if d ∣ n then (μ d : ℝ) else 0)*
        (∑ e ∈ Finset.Icc 1 ((n-1)/S), if e ∣ n then (μ e : ℝ) else 0)| ≤
        C*X/(4+|Real.log R-Real.log S|)^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_reflected_cross_bound
  refine ⟨C+16,by linarith,fun X R S hR hS hRX hSX => ?_⟩
  let G := ∑ n ∈ Finset.Icc 1 X,
    (∑ d ∈ Finset.Icc 1 ((n-1)/R), if d ∣ n then (μ d : ℝ) else 0)*
    (∑ e ∈ Finset.Icc 1 ((n-1)/S), if e ∣ n then (μ e : ℝ) else 0)
  let Q := fun n => ∑ d ∈ Finset.Icc 1 ((n-1)/R), ∑ e ∈ Finset.Icc 1 ((n-1)/S),
    (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)
  have hc := incidence_cross_error X (X/R) (X/S) (fun d => R*d) (fun e => S*e)
    (fun d hd => (Nat.mul_le_mul_left R (Finset.mem_Icc.mp hd).2).trans
      (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self X R))
    (fun e he => (Nat.mul_le_mul_left S (Finset.mem_Icc.mp he).2).trans
      (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self X S))
  have he : (∑ n ∈ Finset.Icc 1 X,
      (∑ d ∈ Finset.Icc 1 (X/R), if R*d < n ∧ d ∣ n then (μ d : ℝ) else 0)*
      (∑ e ∈ Finset.Icc 1 (X/S), if S*e < n ∧ e ∣ n then (μ e : ℝ) else 0)) = G := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 := (Finset.mem_Icc.mp hn).1
    have hnX : n-1 ≤ X := by have := (Finset.mem_Icc.mp hn).2; omega
    simp_rw [ite_and]
    rw [moving_prefix_eq R (X/R) n hR hn0 (Nat.div_le_div_right hnX),
      moving_prefix_eq S (X/S) n hS hn0 (Nat.div_le_div_right hnX)]
  have hpoint n (hn : n ∈ Finset.Icc 1 X) :
      (∑ d ∈ Finset.Icc 1 (X/R), ∑ e ∈ Finset.Icc 1 (X/S),
        if max (R*d) (S*e) < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0) = Q n := by
    have hn0 := (Finset.mem_Icc.mp hn).1
    have hnX : n-1 ≤ X := by have := (Finset.mem_Icc.mp hn).2; omega
    calc
      _ = ∑ d ∈ Finset.Icc 1 (X/R), if R*d < n then
          (∑ e ∈ Finset.Icc 1 (X/S),
            if S*e < n then (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : R*d < n <;> simp only [max_lt_iff,ite_and,hd,
          if_true,if_false,Finset.sum_const_zero]
      _ = _ := by
        rw [moving_prefix_eq R (X/R) n hR hn0 (Nat.div_le_div_right hnX)]
        apply Finset.sum_congr rfl
        intro d _
        exact moving_prefix_eq S (X/S) n hS hn0 (Nat.div_le_div_right hnX) _
  rw [he,Finset.sum_congr rfl hpoint] at hc
  have hmain : |∑ n ∈ Finset.Icc 1 X, Q n| ≤ (X : ℝ)*(C/(4+|Real.log R-Real.log S|)^2) := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 X, |Q n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Icc 1 X, C/(4+|Real.log R-Real.log S|)^2 :=
        Finset.sum_le_sum (fun n _ => hbound (n-1) R S hR hS)
      _ = _ := by simp
  change |G| ≤ _
  calc
    _ = |(G-∑ n ∈ Finset.Icc 1 X, Q n)+∑ n ∈ Finset.Icc 1 X, Q n| := by congr 1; ring
    _ ≤ |G-∑ n ∈ Finset.Icc 1 X, Q n|+|∑ n ∈ Finset.Icc 1 X, Q n| := abs_add_le _ _
    _ ≤ 16*(X : ℝ)/(4+|Real.log R-Real.log S|)^2+
        (X : ℝ)*(C/(4+|Real.log R-Real.log S|)^2) :=
      add_le_add (hc.trans (large_pair_cost hR hS hRX hSX)) hmain
    _ = _ := by ring

private theorem schur_mean_le (I T : Finset ℕ) (a : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    {C h : ℝ} (hC : 0 ≤ C) (hh : 0 < h)
    (hpair : ∀ i ∈ I, ∀ j ∈ I,
      |∑ n ∈ T, f i n*f j n| ≤ C/(4+h*|(i : ℝ)-j|)^2) :
    (∑ n ∈ T, (∑ i ∈ I, a i*f i n)^2) ≤
      C*(∑' k : ℤ, 1/(4+h*|(k : ℝ)|)^2)*(∑ i ∈ I, (a i)^2) := by
  let G := fun i j => ∑ n ∈ T, f i n*f j n
  let B := ∑' k : ℤ, 1/(4+h*|(k : ℝ)|)^2
  have hrows i (hi : i ∈ I) : (∑ j ∈ I, |G i j|) ≤ C*B := by
    calc
      _ ≤ ∑ j ∈ I, C/(4+h*|(i : ℝ)-j|)^2 := Finset.sum_le_sum (hpair i hi)
      _ = C*(∑ j ∈ I, 1/(4+h*|(i : ℝ)-j|)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ C*B := mul_le_mul_of_nonneg_left (ZetaRieszCrossCutoff.separation_row_le I i hh) hC
  have hsym i j : |G i j| = |G j i| := by
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hschur := finset_symmetric_schur_quadratic_le I (fun i => |a i|)
    (fun i j => |G i j|) (C*B) (fun _ _ => abs_nonneg _) hsym hrows
  simp only [sq_abs] at hschur
  have he : (∑ n ∈ T, (∑ i ∈ I, a i*f i n)^2) =
      ∑ i ∈ I, ∑ j ∈ I, a i*a j*G i j := by
    calc
      _ = ∑ n ∈ T, ∑ i ∈ I, ∑ j ∈ I, (a i*f i n)*(a j*f j n) := by
        simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_comm]
      _ = ∑ i ∈ I, ∑ j ∈ I, ∑ n ∈ T, (a i*f i n)*(a j*f j n) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        simp only [G,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro n _
        ring
  rw [he]
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, |a i| * |a j| * |G i j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_mul] using le_abs_self (a i*a j*G i j)
    _ ≤ _ := hschur

private theorem small_family_mean {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (R : ℕ → ℕ) (a : ℕ → ℝ) (X : ℕ),
      (∀ i ∈ I, 0 < R i) → (∀ i ∈ I, (R i)^2 ≤ X) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∑ n ∈ Finset.Icc 1 X,
        (∑ i ∈ I, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      E*X*(∑ i ∈ I, (a i)^2) := by
  obtain ⟨C,hC,hbound⟩ := exists_small_gram_bound
  let B := ∑' k : ℤ, 1/(4+h*|(k : ℝ)|)^2
  have hB : 0 ≤ B := tsum_nonneg (fun _ => by positivity)
  refine ⟨1+C*B,by positivity,fun I R a X hR hRX hsep => ?_⟩
  have hs := schur_mean_le I (Finset.Icc 1 X) a
    (fun i n => ∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)
    (C := C*X) (by positivity) hh (fun i hi j hj =>
      (hbound X (R i) (R j) (hR i hi) (hR j hj) (hRX i hi) (hRX j hj)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by positivity) (by linarith [hsep i hi j hj]) 2)))
  change _ ≤ C*X*B*(∑ i ∈ I, (a i)^2) at hs
  have he : 0 ≤ (X : ℝ)*(∑ i ∈ I, (a i)^2) :=
    mul_nonneg (Nat.cast_nonneg X) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  nlinarith only [hs,he]

private theorem large_family_mean {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (R : ℕ → ℕ) (a : ℕ → ℝ) (X : ℕ),
      (∀ i ∈ I, 0 < R i) → (∀ i ∈ I, X ≤ (R i)^2) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∑ n ∈ Finset.Icc 1 X,
        (∑ i ∈ I, a i*(∑ d ∈ Finset.Icc 1 ((n-1)/R i), if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      E*X*(∑ i ∈ I, (a i)^2) := by
  obtain ⟨C,hC,hbound⟩ := exists_large_gram_bound
  let B := ∑' k : ℤ, 1/(4+h*|(k : ℝ)|)^2
  have hB : 0 ≤ B := tsum_nonneg (fun _ => by positivity)
  refine ⟨1+C*B,by positivity,fun I R a X hR hRX hsep => ?_⟩
  have hs := schur_mean_le I (Finset.Icc 1 X) a
    (fun i n => ∑ d ∈ Finset.Icc 1 ((n-1)/R i), if d ∣ n then (μ d : ℝ) else 0)
    (C := C*X) (by positivity) hh (fun i hi j hj =>
      (hbound X (R i) (R j) (hR i hi) (hR j hj) (hRX i hi) (hRX j hj)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by positivity) (by linarith [hsep i hi j hj]) 2)))
  change _ ≤ C*X*B*(∑ i ∈ I, (a i)^2) at hs
  have he : 0 ≤ (X : ℝ)*(∑ i ∈ I, (a i)^2) :=
    mul_nonneg (Nat.cast_nonneg X) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  nlinarith only [hs,he]

/-- One joint LINEAR population bound for an arbitrary signed family
of separated cutoffs, with neither a floor error nor a period-count factor.
All selected squarefree labels and all cofactor counts are retained. -/
theorem exists_separated_mean_bound {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (R : ℕ → ℕ) (a : ℕ → ℝ)
      (X : ℕ) (S : Finset ℕ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) → (∀ i ∈ I, 0 < R i) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      (∑ n ∈ S,
        (∑ i ∈ I, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      E*X*(∑ i ∈ I, (a i)^2) := by
  obtain ⟨E,hE,hsmall⟩ := small_family_mean hh
  obtain ⟨F,hF,hlarge⟩ := large_family_mean hh
  refine ⟨2*(E+F),by linarith,fun I R a X S hS hSF hR hsep => ?_⟩
  let U := I.filter (fun i => (R i)^2 ≤ X)
  let V := I.filter (fun i => ¬(R i)^2 ≤ X)
  have hU : U ⊆ I := Finset.filter_subset _ _
  have hV : V ⊆ I := Finset.filter_subset _ _
  have hSI : S ⊆ Finset.Icc 1 X := by
    intro n hn
    have h := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Icc.mpr ⟨by omega,h.2⟩
  have hEU : (∑ i ∈ U, (a i)^2) ≤ ∑ i ∈ I, (a i)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hU (fun _ _ _ => sq_nonneg _)
  have hEV : (∑ i ∈ V, (a i)^2) ≤ ∑ i ∈ I, (a i)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hV (fun _ _ _ => sq_nonneg _)
  have hs := hsmall U R a X (fun i hi => hR i (hU hi))
    (fun _ hi => (Finset.mem_filter.mp hi).2) (fun i hi j hj => hsep i (hU hi) j (hU hj))
  have hl := hlarge V R a X (fun i hi => hR i (hV hi))
    (fun _ hi => Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hi).2))
    (fun i hi j hj => hsep i (hV hi) j (hV hj))
  have hsmallS : (∑ n ∈ S,
      (∑ i ∈ U, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      E*X*(∑ i ∈ I, (a i)^2) :=
    ((Finset.sum_le_sum_of_subset_of_nonneg hSI (fun _ _ _ => sq_nonneg _)).trans hs).trans
      (mul_le_mul_of_nonneg_left hEU (by positivity))
  have href n (hn : n ∈ S) :
      (∑ i ∈ V, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2 =
      (∑ i ∈ V, a i*(∑ d ∈ Finset.Icc 1 ((n-1)/R i), if d ∣ n then (μ d : ℝ) else 0))^2 := by
    have he : (∑ i ∈ V, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)) =
        -(μ n : ℝ)*(∑ i ∈ V, a i*(∑ d ∈ Finset.Icc 1 ((n-1)/R i), if d ∣ n then (μ d : ℝ) else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [ZetaRieszSquarefreeDualMean.sharp_reflection (hSF n hn)
        (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega) (hR i (hV hi))]
      ring
    have hm : (μ n : ℝ)^2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hSF n hn)
    rw [he,mul_pow,neg_sq,hm,one_mul]
  have hlargeS : (∑ n ∈ S,
      (∑ i ∈ V, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2) ≤
      F*X*(∑ i ∈ I, (a i)^2) := by
    rw [Finset.sum_congr rfl href]
    exact ((Finset.sum_le_sum_of_subset_of_nonneg hSI (fun _ _ _ => sq_nonneg _)).trans hl).trans
      (mul_le_mul_of_nonneg_left hEV (by positivity))
  have hp n :
      (∑ i ∈ I, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2 ≤
      2*(∑ i ∈ U, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2+
      2*(∑ i ∈ V, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))^2 := by
    have he := Finset.sum_filter_add_sum_filter_not I (fun i => (R i)^2 ≤ X)
      (fun i => a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))
    change (∑ i ∈ U, _)+(∑ i ∈ V, _) = _ at he
    rw [← he]
    nlinarith only [sq_nonneg ((∑ i ∈ U, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0))-
      (∑ i ∈ V, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)))]
  have ht := Finset.sum_le_sum (fun n (_ : n ∈ S) => hp n)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at ht
  nlinarith only [ht,hsmallS,hlargeS]

/-- Both signed sides retain an arbitrary common correlated real
weight and the whole signed cutoff family. No finite floor budget remains. -/
theorem exists_joint_signed_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (R : ℕ → ℕ) (a w : ℕ → ℝ)
      (X : ℕ) (S : Finset ℕ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) → (∀ i ∈ I, 0 < R i) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ I, a i*
        (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0));
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*(E*X)*(∑ i ∈ I, (a i)^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_separated_mean_bound hh
  refine ⟨E,hE,fun I R a w X S hS hSF hR hsep => ?_⟩
  dsimp only
  let f := fun n => ∑ i ∈ I, a i*
    (∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w f).trans
    (mul_le_mul_of_nonneg_left (hmean I R a X S hS hSF hR hsep)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  simpa only [mul_assoc] using hs

/-- The joint arithmetic bound applies to all retained strict slopes,
with their exact integer endpoints and arbitrary fixed signed coefficients. -/
theorem exists_joint_slope_bounds {h : ℝ} (hh : 0 < h) :
    ∃ E : ℝ, 0 < E ∧ ∀ (I : Finset ℕ) (R : ℕ → ℕ) (D a w : ℕ → ℝ)
      (X : ℕ) (S : Finset ℕ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) → (∀ i ∈ I, 0 < R i) →
      (∀ i ∈ I, (R i : ℝ) < Real.exp (D i) ∧ Real.exp (D i) ≤ R i+1) →
      (∀ i ∈ I, ∀ j ∈ I, h*|(i : ℝ)-j| ≤ |Real.log (R i)-Real.log (R j)|) →
      let J := ∑ n ∈ S, w n*(∑ i ∈ I, a i*ZetaRieszGlobalCurvature.cutoffSlope (D i) n);
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*(E*X)*(∑ i ∈ I, (a i)^2));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_joint_signed_bounds hh
  refine ⟨E,hE,fun I R D a w X S hS hSF hR hD hsep => ?_⟩
  have hs := hbound I R a w X S hS hSF hR hsep
  dsimp only at hs ⊢
  have he : (∑ n ∈ S, w n*(∑ i ∈ I, a i*ZetaRieszGlobalCurvature.cutoffSlope (D i) n)) =
      ∑ n ∈ S, w n*(∑ i ∈ I, a i*(∑ d ∈ Finset.Icc 1 (R i), if d ∣ n then (μ d : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [ZetaRieszCrossCutoff.cutoffSlope_eq_prefix (R i) (D i) (hD i hi).1 (hD i hi).2
      (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)]
  rw [he]
  exact hs

end RiemannGaussian.ZetaRieszSquarefreeSeparatedMean
