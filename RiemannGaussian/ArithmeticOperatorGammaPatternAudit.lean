/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorSuccessorGammaAudit

/-!
# All fixed-degree shifted complete-Gamma products

Different integer endpoints and prime columns are multiplied before
estimating. Each COMPLETE cofactor-phased divisor row then evaluates to
its actual phased integer logarithm. Relative to the common-endpoint
reference, the entire finite product has a cutoff budget
`O(H log(X+H)^(degree+2))`, uniformly in every bounded external row code.
At dyadic cutoffs it is source-small whenever the endpoint shifts grow
with a rational exponent strictly below the proposed source exponent.

This closes a whole nonlinear COMPLETE-Gamma source gate. It does not
estimate a prime-leg-only product, a truncated divisor column, a growing
product degree, or the exact signed commutator left by those changes.
-/

namespace RiemannGaussian.ArithmeticOperatorGammaPatternAudit
noncomputable section
open Complex Filter ArithmeticOperatorGammaTwistAudit
open ArithmeticOperatorFloorInverseAudit SuzukiCarryCorrelation
open scoped BigOperators Topology

/-- Exact full divisor row at one literal shifted endpoint. All actual
prime-power incidences and the compatible cofactor phase are retained. -/
def row (y : ℝ) (n : ℕ) : ℂ := coupledDivisor (primePhase y) n

/-- Fixed finite nonlinear pattern, with arbitrary integer-valued moving
offsets, multiple heights and their original correlated product. -/
def pattern (S : Finset ℕ) (y : ℕ → ℝ) (shift : ℕ → ℕ → ℕ) (n : ℕ) : ℂ :=
  ∏ i ∈ S, row (y i) (n+shift i n)

/-- Whole common-endpoint reference; it is not a prime-by-prime density
approximation. The total height is retained exactly. -/
def reference (S : Finset ℕ) (y : ℕ → ℝ) (n : ℕ) : ℂ :=
  ∏ i ∈ S, row (y i) n

/-- Joined reference subtraction, with any bounded external phase,
Gaussian coefficient or literal integer row mask still inside the cutoff. -/
def centered (S : Finset ℕ) (y : ℕ → ℝ) (shift : ℕ → ℕ → ℕ)
    (code : ℕ → ℂ) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, code n*(pattern S y shift n-reference S y n)

/-- Exact finite integer identity before any estimate or source test. -/
theorem pattern_eq_phased_logs (S : Finset ℕ) (y : ℕ → ℝ)
    (shift : ℕ → ℕ → ℕ) {n : ℕ} (hn : 0<n) :
    pattern S y shift n=
      ∏ i ∈ S, primePhase (y i) (n+shift i n)*(Real.log ((n+shift i n : ℕ) : ℝ) : ℂ) := by
  unfold pattern row
  exact Finset.prod_congr rfl (fun _ _ => coupledDivisor_primePhase _ (by omega))

theorem reference_eq_total_height (S : Finset ℕ) (y : ℕ → ℝ)
    {n : ℕ} (hn : 0<n) :
    reference S y n=primePhase (∑ i ∈ S, y i) n*(Real.log n : ℂ)^S.card := by
  unfold reference row
  simp_rw [coupledDivisor_primePhase _ hn]
  rw [Finset.prod_mul_distrib,Finset.prod_const]
  congr 1
  unfold primePhase
  rw [←Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.sum_mul,Finset.mul_sum,neg_mul,Finset.sum_neg_distrib]

private theorem log_shift_gap {n h : ℕ} (hn : 0<n) :
    0≤Real.log ((n+h : ℕ) : ℝ)-Real.log n ∧
      Real.log ((n+h : ℕ) : ℝ)-Real.log n≤(h : ℝ)/(n : ℝ) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hnR (by exact_mod_cast Nat.le_add_right n h))
  · have hh := Real.log_le_sub_one_of_pos (x := (n+h : ℕ)/(n : ℝ)) (by positivity)
    rw [Real.log_div (by positivity) hnR.ne'] at hh
    have he : ((n+h : ℕ) : ℝ)/(n : ℝ)-1=(h : ℝ)/(n : ℝ) := by
      push_cast
      field_simp
      ring
    exact hh.trans_eq he

private theorem phase_shift_eq (y : ℝ) (n h : ℕ) :
    primePhase y (n+h)=primePhase y n*
      Complex.exp (I*(-y*(Real.log ((n+h : ℕ) : ℝ)-Real.log n) : ℝ)) := by
  unfold primePhase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Lipschitz phase payment uses the exact multiplicative height at the
endpoint, not an untwisted replacement of the prime columns. -/
theorem norm_phase_shift_le (y : ℝ) {n h : ℕ} (hn : 0<n) :
    ‖primePhase y (n+h)-primePhase y n‖≤|y| *(h : ℝ)/(n : ℝ) := by
  rw [phase_shift_eq]
  rw [show primePhase y n*Complex.exp (I*(-y*(Real.log ((n+h : ℕ) : ℝ)-Real.log n) : ℝ))-
      primePhase y n=primePhase y n*(Complex.exp
        (I*(-y*(Real.log ((n+h : ℕ) : ℝ)-Real.log n) : ℝ))-1) by ring,
    norm_mul,norm_primePhase,one_mul]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := -y*(Real.log ((n+h : ℕ) : ℝ)-Real.log n))
  rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg (log_shift_gap hn).1] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left (log_shift_gap hn).2 (abs_nonneg y))).trans_eq
    (by ring)

private theorem norm_row_le {n h X H : ℕ} (hn : 0<n) (hnX : n≤X) (hhH : h≤H)
    (y : ℝ) : ‖row y (n+h)‖≤1+Real.log ((X+H : ℕ) : ℝ) := by
  rw [row,coupledDivisor_primePhase y (by omega),norm_mul,norm_primePhase,one_mul,
    Complex.norm_real,Real.norm_of_nonneg (Real.log_natCast_nonneg _)]
  have hlog : Real.log ((n+h : ℕ) : ℝ)≤Real.log ((X+H : ℕ) : ℝ) :=
    Real.log_le_log (by positivity : (0 : ℝ)<(n+h : ℕ))
    (by exact_mod_cast (show n+h≤X+H by omega))
  linarith

/-- Single complete row estimate, used only AFTER its exact Gamma join. -/
theorem norm_row_shift_sub_le {n h X H : ℕ} {B : ℝ} (hn : 0<n)
    (hnX : n≤X) (hhH : h≤H) (hB : 0≤B) (y : ℝ) (hy : |y|≤B) :
    ‖row y (n+h)-row y n‖≤
      (1+B)*((H : ℝ)/(n : ℝ))*(1+Real.log ((X+H : ℕ) : ℝ)) := by
  have hdelta := log_shift_gap (h := h) hn
  have hlog : Real.log ((n+h : ℕ) : ℝ)≤Real.log ((X+H : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show n+h≤X+H by omega))
  have hhn : (h : ℝ)/(n : ℝ)≤(H : ℝ)/(n : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hhH) (by positivity)
  have hphase : ‖primePhase y (n+h)-primePhase y n‖≤B*((H : ℝ)/(n : ℝ)) := by
    calc
      _ ≤ |y| *((h : ℝ)/(n : ℝ)) := by simpa only [mul_div_assoc] using norm_phase_shift_le y hn
      _ ≤ _ := mul_le_mul hy hhn (by positivity) hB
  rw [row,row,coupledDivisor_primePhase y (by omega),coupledDivisor_primePhase y hn]
  have he : primePhase y (n+h)*(Real.log ((n+h : ℕ) : ℝ) : ℂ)-primePhase y n*(Real.log n : ℂ)=
      (primePhase y (n+h)-primePhase y n)*(Real.log ((n+h : ℕ) : ℝ) : ℂ)+
        primePhase y n*(Real.log ((n+h : ℕ) : ℝ)-Real.log n : ℝ) := by push_cast; ring
  rw [he]
  calc
    _ ≤ ‖(primePhase y (n+h)-primePhase y n)*(Real.log ((n+h : ℕ) : ℝ) : ℂ)‖+
        ‖primePhase y n*(Real.log ((n+h : ℕ) : ℝ)-Real.log n : ℝ)‖ := norm_add_le _ _
    _ ≤ B*((H : ℝ)/(n : ℝ))*Real.log ((X+H : ℕ) : ℝ)+(H : ℝ)/(n : ℝ) := by
      rw [norm_mul,norm_mul,norm_primePhase,one_mul,Complex.norm_real,Complex.norm_real,
        Real.norm_of_nonneg (Real.log_natCast_nonneg _),Real.norm_of_nonneg hdelta.1]
      exact add_le_add (mul_le_mul hphase hlog (Real.log_natCast_nonneg _) (by positivity))
        (hdelta.2.trans hhn)
    _ ≤ _ := by
      have hnR : (0 : ℝ)<n := by exact_mod_cast hn
      have hnon := Real.log_natCast_nonneg (X+H)
      nlinarith [div_nonneg (show (0 : ℝ)≤H by positivity) hnR.le]

/-- A joined finite product bound. No denominator-column estimate is
applied here: the f and g have already been evaluated as complete rows. -/
theorem norm_product_sub_product_le (S : Finset ℕ) (f g : ℕ → ℂ)
    {Q E : ℝ} (hQ : 1≤Q) (hE : 0≤E)
    (hf : ∀ i ∈ S, ‖f i‖≤Q) (hg : ∀ i ∈ S, ‖g i‖≤Q)
    (he : ∀ i ∈ S, ‖f i-g i‖≤E) :
    ‖(∏ i ∈ S, f i)-(∏ i ∈ S, g i)‖≤(S.card : ℝ)*E*Q^S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfS : ∀ j ∈ S, ‖f j‖≤Q := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hgS : ∀ j ∈ S, ‖g j‖≤Q := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have heS : ∀ j ∈ S, ‖f j-g j‖≤E := fun j hj => he j (Finset.mem_insert_of_mem hj)
    have hfi := he i (Finset.mem_insert_self _ _)
    have hgi := hg i (Finset.mem_insert_self _ _)
    have hfp : ‖∏ j ∈ S, f j‖≤Q^S.card := by
      rw [norm_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hfS).trans_eq (by simp)
    have hp : Q^S.card≤Q^(S.card+1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (by positivity) hQ
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.card_insert_of_notMem hi]
    rw [show f i*(∏ j ∈ S, f j)-g i*(∏ j ∈ S, g j)=
      (f i-g i)*(∏ j ∈ S, f j)+g i*((∏ j ∈ S, f j)-(∏ j ∈ S, g j)) by ring]
    calc
      _ ≤ ‖(f i-g i)*(∏ j ∈ S, f j)‖+
          ‖g i*((∏ j ∈ S, f j)-(∏ j ∈ S, g j))‖ := norm_add_le _ _
      _ ≤ E*Q^S.card+Q*((S.card : ℝ)*E*Q^S.card) := by
        rw [norm_mul,norm_mul]
        exact add_le_add (mul_le_mul hfi hfp (norm_nonneg _) hE)
          (mul_le_mul hgi (ih hfS hgS heS) (norm_nonneg _) (by positivity))
      _ ≤ E*Q^(S.card+1)+Q*((S.card : ℝ)*E*Q^S.card) := by gcongr
      _ = _ := by push_cast; rw [pow_succ]; ring

/-- Whole arbitrary-degree finite pattern budget. This controls the
extra shifted interaction, not the original twisted prime-only carrier. -/
theorem norm_centered_le (S : Finset ℕ) (y : ℕ → ℝ) (shift : ℕ → ℕ → ℕ)
    (code : ℕ → ℂ) {X H : ℕ} {B : ℝ} (hB : 0≤B)
    (hy : ∀ i ∈ S, |y i|≤B) (hshift : ∀ n ∈ Finset.Icc 1 X, ∀ i ∈ S, shift i n≤H)
    (hcode : ∀ n ∈ Finset.Icc 1 X, ‖code n‖≤1) :
    ‖centered S y shift code X‖≤
      (S.card : ℝ)*(1+B)*(H : ℝ)*(1+Real.log ((X+H : ℕ) : ℝ))^(S.card+1)*(1+Real.log X) := by
  let Q := 1+Real.log ((X+H : ℕ) : ℝ)
  have hQ : 1≤Q := by dsimp [Q]; have := Real.log_natCast_nonneg (X+H); linarith
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
      ‖code n*(pattern S y shift n-reference S y n)‖≤
        ((S.card : ℝ)*(1+B)*(H : ℝ)*Q^(S.card+1))*(n : ℝ)⁻¹ := by
    obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp hn
    have hbase (i : ℕ) : ‖row (y i) n‖≤Q := by
      have hh : ‖row (y i) (n+0)‖≤1+Real.log ((X+H : ℕ) : ℝ) :=
        norm_row_le (h := 0) hn0 hnX (Nat.zero_le H) (y i)
      simpa only [Nat.add_zero] using hh
    have hh := norm_product_sub_product_le S
      (fun i => row (y i) (n+shift i n)) (fun i => row (y i) n) hQ
      (E := (1+B)*((H : ℝ)/(n : ℝ))*Q) (by positivity)
      (fun i hi => norm_row_le hn0 hnX (hshift n hn i hi) _)
      (fun i _ => hbase i)
      (fun i hi => norm_row_shift_sub_le hn0 hnX (hshift n hn i hi) hB _ (hy i hi))
    rw [norm_mul]
    calc
      _ ≤ 1*((S.card : ℝ)*((1+B)*((H : ℝ)/(n : ℝ))*Q)*Q^S.card) :=
        mul_le_mul (hcode n hn) hh (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  unfold centered
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X,
        ((S.card : ℝ)*(1+B)*(H : ℝ)*Q^(S.card+1))*(n : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = ((S.card : ℝ)*(1+B)*(H : ℝ)*Q^(S.card+1))*(harmonic X : ℝ) := by
      rw [←Finset.mul_sum,harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log X) (by positivity)

/-- Uniform dyadic budget for every bounded physical row code and every
endpoint pattern through a rational sublinear shift exponent. -/
theorem norm_dyadic_centered_le (S : Finset ℕ) (y : ℕ → ℝ)
    (shift : ℕ → ℕ → ℕ) (code : ℕ → ℂ) (A B J : ℕ) (hBA : B≤A)
    {Y : ℝ} (hY : 0≤Y) (hy : ∀ i ∈ S, |y i|≤Y)
    (hshift : ∀ n ∈ Finset.Icc 1 (2^(A*J)), ∀ i ∈ S, shift i n≤2^(B*J))
    (hcode : ∀ n ∈ Finset.Icc 1 (2^(A*J)), ‖code n‖≤1) :
    ‖centered S y shift code (2^(A*J))‖≤
      ((S.card : ℝ)*(1+Y)*(((A+1 : ℕ) : ℝ)*(1+Real.log 2))^(S.card+2))*
        ((J+1 : ℕ) : ℝ)^(S.card+2)*(2 : ℝ)^(B*J) := by
  have hHX : (2 : ℕ)^(B*J)≤2^(A*J) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right J hBA)
  have hsum : (2 : ℕ)^(A*J)+2^(B*J)≤2^(A*J+1) := by rw [pow_succ]; omega
  have hlog : Real.log ((2^(A*J)+2^(B*J) : ℕ) : ℝ)≤
      ((A*J+1 : ℕ) : ℝ)*Real.log 2 := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ)<(2^(A*J)+2^(B*J) : ℕ))
      (show ((2^(A*J)+2^(B*J) : ℕ) : ℝ)≤(2 : ℝ)^(A*J+1) by exact_mod_cast hsum)
    simpa only [Real.log_pow] using hh
  let C := ((A+1 : ℕ) : ℝ)*(1+Real.log 2)
  have hQ : 1+Real.log ((2^(A*J)+2^(B*J) : ℕ) : ℝ)≤C*((J+1 : ℕ) : ℝ) := by
    have hAJ : ((A*J+1 : ℕ) : ℝ)≤((A+1 : ℕ) : ℝ)*((J+1 : ℕ) : ℝ) := by
      exact_mod_cast (by nlinarith : A*J+1≤(A+1)*(J+1))
    have h1 : (1 : ℝ)≤((A+1 : ℕ) : ℝ)*((J+1 : ℕ) : ℝ) := by
      exact_mod_cast (by nlinarith : 1≤(A+1)*(J+1))
    dsimp [C]
    have hl2 := Real.log_pos (by norm_num : (1 : ℝ)<2)
    nlinarith
  have hmono : Real.log ((2^(A*J) : ℕ) : ℝ)≤
      Real.log ((2^(A*J)+2^(B*J) : ℕ) : ℝ) :=
    Real.log_le_log (by positivity : (0 : ℝ)<(2^(A*J) : ℕ))
      (by exact_mod_cast (Nat.le_add_right ((2 : ℕ)^(A*J)) (2^(B*J))))
  have hP : 1+Real.log ((2^(A*J) : ℕ) : ℝ)≤C*((J+1 : ℕ) : ℝ) := by linarith
  have hP0 : 0≤1+Real.log ((2^(A*J) : ℕ) : ℝ) := by
    have := Real.log_natCast_nonneg (2^(A*J))
    linarith
  have hQ0 : 0≤1+Real.log ((2^(A*J)+2^(B*J) : ℕ) : ℝ) := by
    have := Real.log_natCast_nonneg (2^(A*J)+2^(B*J))
    linarith
  calc
    _ ≤ (S.card : ℝ)*(1+Y)*((2^(B*J) : ℕ) : ℝ)*
        (1+Real.log ((2^(A*J)+2^(B*J) : ℕ) : ℝ))^(S.card+1)*
          (1+Real.log ((2^(A*J) : ℕ) : ℝ)) :=
      norm_centered_le S y shift code hY hy hshift hcode
    _ ≤ (S.card : ℝ)*(1+Y)*((2^(B*J) : ℕ) : ℝ)*
        (C*((J+1 : ℕ) : ℝ))^(S.card+1)*(C*((J+1 : ℕ) : ℝ)) := by
      gcongr
    _ = _ := by
      rw [Nat.cast_pow]
      dsimp [C]
      rw [mul_pow]
      simp only [pow_succ]
      ring

/-- ALL rational sub-source endpoint-growth exponents, arbitrary finite
product degree and every moving bounded external row mask. There is
no actual zero or exposure premise, so the extra Gamma interaction
cannot carry any nonzero matched power source in this class. -/
theorem tendsto_scaled_centered (S : Finset ℕ) (y : ℕ → ℝ)
    (shift : ℕ → ℕ → ℕ → ℕ) (code : ℕ → ℕ → ℂ) (A B : ℕ)
    (hBA : B≤A) {Y beta : ℝ} (hY : 0≤Y)
    (hy : ∀ i ∈ S, |y i|≤Y)
    (hshift : ∀ J n, n ∈ Finset.Icc 1 (2^(A*J)) → ∀ i ∈ S, shift J i n≤2^(B*J))
    (hcode : ∀ J n, n ∈ Finset.Icc 1 (2^(A*J)) → ‖code J n‖≤1)
    (hsource : (B : ℝ)<A*beta) :
    Tendsto (fun J : ℕ => (Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*
      centered S y (shift J) (code J) (2^(A*J))) atTop (𝓝 0) := by
  let a := Real.exp (-(A : ℝ)*beta*Real.log 2)
  let r := a*(2 : ℝ)^B
  have ha : 0<a := Real.exp_pos _
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r<1 := by
    have he : r=Real.exp (((B : ℝ)-A*beta)*Real.log 2) := by
      dsimp [r,a]
      calc
        _ = Real.exp (-(A : ℝ)*beta*Real.log 2)*Real.exp (Real.log ((2 : ℝ)^B)) := by
          rw [Real.exp_log (by positivity)]
        _ = _ := by rw [Real.log_pow,←Real.exp_add]; congr 1; ring
    rw [he]
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num))
  let C := (S.card : ℝ)*(1+Y)*(((A+1 : ℕ) : ℝ)*(1+Real.log 2))^(S.card+2)
  have ht : Tendsto (fun J : ℕ => C*((J+1 : ℕ) : ℝ)^(S.card+2)*r^J) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_assoc] using
      (tendsto_shifted_polynomial_geometric (S.card+2) hr hr1).const_mul C
  apply squeeze_zero_norm (fun J => ?_) ht
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ha.le]
  calc
    _ ≤ a^J*(C*((J+1 : ℕ) : ℝ)^(S.card+2)*(2 : ℝ)^(B*J)) :=
      mul_le_mul_of_nonneg_left
        (norm_dyadic_centered_le S y (shift J) (code J) A B J hBA hY hy
          (hshift J) (hcode J)) (pow_nonneg ha.le J)
    _ = _ := by dsimp [r]; rw [mul_pow,pow_mul]; ring

/-- Strict source rejection for the whole finite nonlinear pattern,
not an estimate for any unpaid prime-leg-only commutator. -/
theorem no_nonzero_centered_source (S : Finset ℕ) (y : ℕ → ℝ)
    (shift : ℕ → ℕ → ℕ → ℕ) (code : ℕ → ℕ → ℂ) (A B : ℕ)
    (hBA : B≤A) {Y beta : ℝ} (hY : 0≤Y) (hy : ∀ i ∈ S, |y i|≤Y)
    (hshift : ∀ J n, n ∈ Finset.Icc 1 (2^(A*J)) → ∀ i ∈ S, shift J i n≤2^(B*J))
    (hcode : ∀ J n, n ∈ Finset.Icc 1 (2^(A*J)) → ‖code J n‖≤1)
    (hsource : (B : ℝ)<A*beta) {v : ℂ} (hv : v≠0) :
    ¬Tendsto (fun J : ℕ => (Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*
      centered S y (shift J) (code J) (2^(A*J))) atTop (𝓝 v) := by
  intro hh
  exact hv (tendsto_nhds_unique hh
    (tendsto_scaled_centered S y shift code A B hBA hY hy hshift hcode hsource))

end
end RiemannGaussian.ArithmeticOperatorGammaPatternAudit
