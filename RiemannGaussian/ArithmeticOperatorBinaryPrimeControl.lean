/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorPrimeTowerControl
import RiemannGaussian.FiniteAbelVariation
import RiemannGaussian.ZetaMoebiusResonanceDecay
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Literal binary prime rounding retains the coherent source

The bounded cumulative discrepancy is supplied by the repository's
exact integer rounding construction. Here the FULL complex factorial
test is transported through that discrepancy; a finite binary witness
is never promoted to an asymptotic hypothesis. This is a deliberately
selected prime subset, not the unaltered actual Mangoldt sequence.
-/

namespace RiemannGaussian.ArithmeticOperatorBinaryPrimeControl
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
open ZetaRieszCeilingPrimeThinningAudit

/-- Safe evaluation center of the unchanged factorial prime moments. -/
def center (y : ℝ) : ℂ := 3/2+Complex.I*y

/-- Continuous complex factorial test, including its logarithmic weight. -/
def test (k : ℕ) (y x : ℝ) : ℂ :=
  (Real.log x : ℂ)^(k+1)/(k.factorial : ℂ)*Complex.exp (-center y*(Real.log x : ℂ))

/-- The exact derivative, keeping both height-dependent terms together. -/
def testDerivative (k : ℕ) (y x : ℝ) : ℂ :=
  ((k+1 : ℕ) : ℂ)*(Real.log x : ℂ)^k/(k.factorial : ℂ)/(x : ℂ)*
    Complex.exp (-center y*(Real.log x : ℂ))-center y*test k y x/(x : ℂ)

/-- Exact calculus identity on the positive axis. -/
theorem hasDerivAt_test (k : ℕ) (y : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (test k y) (testDerivative k y x) x := by
  have hl := (Real.hasDerivAt_log hx.ne').ofReal_comp
  have hp := (hl.pow (k+1)).div_const (k.factorial : ℂ)
  have he := (hl.const_mul (-center y)).cexp
  have hd : testDerivative k y x =
      (((k+1 : ℕ) : ℂ)*(Real.log x : ℂ)^(k+1-1)*(↑(x⁻¹) : ℂ)/(k.factorial : ℂ))*
        Complex.exp (-center y*(Real.log x : ℂ))+
      ((Real.log x : ℂ)^(k+1)/(k.factorial : ℂ))*
        (Complex.exp (-center y*(Real.log x : ℂ))*(-center y*(↑(x⁻¹) : ℂ))) := by
    simp only [testDerivative,test,Complex.ofReal_inv,Nat.add_sub_cancel,div_eq_mul_inv]
    ring
  rw [hd]
  exact hp.mul he

private theorem norm_exp_center (y x : ℝ) :
    ‖Complex.exp (-center y*(Real.log x : ℂ))‖ =
      Real.exp (-(3/2)*Real.log x) := by
  have hc : (center y).re = 3/2 := by norm_num [center]
  simp only [Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero,hc]

/-- The positive factorial envelope is uniform in derivative order. -/
private theorem log_test_envelope (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x)^(k+1)/(k.factorial : ℝ) ≤ (k+1 : ℕ)*x := by
  have hh := Real.pow_div_factorial_le_exp (Real.log x)
    (Real.log_nonneg hx) (k+1)
  rw [Real.exp_log (by linarith : 0 < x),Nat.factorial_succ,Nat.cast_mul] at hh
  have hk : (0 : ℝ)<(k+1 : ℕ) := by positivity
  have hf : (0 : ℝ)<(k.factorial : ℝ) := by positivity
  field_simp at hh ⊢
  nlinarith

/-- A summable spatial envelope for the derivative of the complete
complex test. The factorial order costs only its explicit linear factor. -/
theorem norm_testDerivative_le (k : ℕ) (y : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ‖testDerivative k y x‖ ≤
      ((k+1 : ℕ) : ℝ)*(1+‖center y‖)*Real.exp (-(3/2)*Real.log x) := by
  have hx0 : 0<x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hp := Real.pow_div_factorial_le_exp (Real.log x) hlog k
  rw [Real.exp_log hx0] at hp
  have hq := log_test_envelope k hx
  have he := norm_exp_center y x
  have ht : ‖test k y x‖ = (Real.log x)^(k+1)/(k.factorial : ℝ)*
      Real.exp (-(3/2)*Real.log x) := by
    simp only [test,norm_mul,norm_div,norm_pow,he,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hlog,Complex.norm_natCast]
  unfold testDerivative
  apply (norm_sub_le _ _).trans
  simp only [norm_mul,norm_div,norm_pow,Complex.norm_natCast,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog,abs_of_pos hx0,he,ht]
  have hfirst : ((k+1 : ℕ) : ℝ)*(Real.log x)^k/(k.factorial : ℝ)/x ≤ (k+1 : ℕ) := by
    apply (div_le_iff₀ hx0).mpr
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hp
      (by positivity : (0 : ℝ) ≤ (k+1 : ℕ))
  have hsecond : (Real.log x)^(k+1)/(k.factorial : ℝ)/x ≤ (k+1 : ℕ) :=
    (div_le_iff₀ hx0).mpr (by simpa [mul_comm] using hq)
  calc
    _ ≤ ((k+1 : ℕ) : ℝ)*Real.exp (-(3/2)*Real.log x)+
        ‖center y‖*(((k+1 : ℕ) : ℝ)*Real.exp (-(3/2)*Real.log x)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hfirst (Real.exp_pos _).le
      · have hh := mul_le_mul_of_nonneg_right hsecond (Real.exp_pos (-(3/2)*Real.log x)).le
        convert mul_le_mul_of_nonneg_left hh (norm_nonneg (center y)) using 1
        ring
    _ = _ := by ring

/-- Exact logarithmic prime test at literal integer labels. -/
theorem test_nat (k : ℕ) (y : ℝ) (n : ℕ) :
    test k y n = (Real.log n : ℂ)*zetaPrimeLogKernel k (center y) n := by
  unfold test zetaPrimeLogKernel zetaPrimeFeature
  rw [pow_succ]
  ring

/-- The endpoint norm has the same polynomial order cost. -/
theorem norm_test_nat_le (k : ℕ) (y : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖test k y n‖ ≤ (k+1 : ℕ) := by
  have hx : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hh := log_test_envelope k hx
  have he := norm_exp_center y (n : ℝ)
  have hs : (n : ℝ)*Real.exp (-(3/2)*Real.log n) =
      Real.exp (-(1/2)*Real.log n) := by
    conv_lhs => lhs; rw [←Real.exp_log (by positivity : (0 : ℝ)<n)]
    rw [←Real.exp_add]
    congr 1
    ring
  have hle : Real.exp (-(1/2)*Real.log n) ≤ 1 :=
    (Real.exp_le_one_iff).mpr (by nlinarith [Real.log_natCast_nonneg n])
  rw [test,norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg _),Complex.norm_natCast,he]
  calc
    _ ≤ ((k+1 : ℕ) : ℝ)*n*Real.exp (-(3/2)*Real.log n) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = ((k+1 : ℕ) : ℝ)*Real.exp (-(1/2)*Real.log n) := by rw [mul_assoc,hs]
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hle

/-- The FULL complex variation across each unit interval is summable. -/
theorem norm_test_step_le (k : ℕ) (y : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖test k y (n+1)-test k y n‖ ≤
      ((k+1 : ℕ) : ℝ)*(1+‖center y‖)*zetaPrimeExpWeight (3/2) n := by
  have hx : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (n : ℝ)) (b := (n : ℝ)+1)
    (f := test k y) (f' := testDerivative k y)
    (C := ((k+1 : ℕ) : ℝ)*(1+‖center y‖)*zetaPrimeExpWeight (3/2) n)
    (fun x hx' => (hasDerivAt_test k y (by linarith [hx'.1])).hasDerivWithinAt)
    (by
      intro x hx'
      apply (norm_testDerivative_le k y (hx.trans hx'.1)).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold zetaPrimeExpWeight
      apply Real.exp_le_exp.mpr
      have hlog := Real.log_le_log (by linarith : (0 : ℝ)<n) hx'.1
      linarith)
    ((n : ℝ)+1) ⟨by linarith,le_rfl⟩
  simpa using hh

/-- Literal binary-minus-fractional rounding discrepancy. -/
def roundingError (u y : ℝ) (n : ℕ) : ℝ :=
  (binaryPrimeAtom u y n : ℝ)-(if n.Prime then clippedWeight u y n else 0)

/-- No composite is created by rounding. -/
theorem roundingError_composite (u y : ℝ) {n : ℕ} (hn : ¬n.Prime) :
    roundingError u y n = 0 := by
  simp [roundingError,binaryPrimeAtom_composite u y hn,hn]

/-- Each atom has norm at most one, including the finite clipped head. -/
theorem roundingError_abs_le (u y : ℝ) (n : ℕ) : |roundingError u y n| ≤ 1 := by
  by_cases hn : n.Prime
  · have hb := clippedWeight_bounds u y n
    rcases binaryPrimeAtom_zero_or_one u y n with hh | hh
    · simp only [roundingError,hn,ite_true,hh,Nat.cast_zero,zero_sub,abs_neg]
      exact (abs_of_nonneg hb.1).le.trans hb.2
    · simp only [roundingError,hn,ite_true,hh,Nat.cast_one]
      rw [abs_of_nonneg (by linarith only [hb.2])]
      linarith only [hb.1]
  · simp [roundingError_composite u y hn]

/-- Exact cumulative error, before any weighted estimate. -/
theorem roundingError_prefix (u y : ℝ) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, (roundingError u y n : ℂ)‖ < 1 := by
  have he : (∑ n ∈ Finset.range M, (roundingError u y n : ℂ)) =
      (((∑ n ∈ Finset.range M, (binaryPrimeAtom u y n : ℝ))-primePrefix u y M : ℝ) : ℂ) := by
    simp only [roundingError,primePrefix,Complex.ofReal_sub,Complex.ofReal_sum,
      Finset.sum_sub_distrib]
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  exact binaryPrimeAtom_prefix_error u y M

/-- Fixed summable spatial budget; it has no dependence on order or height. -/
def spatialMass : ℝ := ∑' n : ℕ, zetaPrimeExpWeight (3/2) n

/-- The exact complex rounding error costs only a linear factor in order. -/
theorem finite_rounding_bound (u y : ℝ) (k M : ℕ) :
    ‖∑ n ∈ Finset.range M, test k y n*(roundingError u y n : ℂ)‖ ≤
      ((k+1 : ℕ) : ℝ)*(1+(1+‖center y‖)*spatialMass) := by
  cases M with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,norm_zero]
    have hm : 0 ≤ spatialMass := tsum_nonneg (fun n => (Real.exp_pos _).le)
    positivity
  | succ M =>
    have hh := FiniteAbelVariation.weighted_bound (fun n => test k y n)
      (fun n => (roundingError u y n : ℂ)) M
      (B := 1) (fun n _ => (roundingError_prefix u y (n+1)).le)
    have hs : Summable (fun n : ℕ => zetaPrimeExpWeight (3/2) n) :=
      summable_zetaPrimeExpWeight (by norm_num)
    have he : ‖test k y M‖ ≤ (k+1 : ℕ) := by
      by_cases hM : M=0
      · simp only [hM,Nat.cast_zero,test,Real.log_zero,Complex.ofReal_zero,
          zero_pow (Nat.succ_ne_zero _),zero_div,zero_mul,norm_zero]
        positivity
      · exact norm_test_nat_le k y (Nat.pos_of_ne_zero hM)
    have hv : (∑ n ∈ Finset.range M, ‖test k y n-test k y ((n+1 : ℕ) : ℝ)‖) ≤
        ((k+1 : ℕ) : ℝ)*(1+‖center y‖)*spatialMass := by
      calc
        _ ≤ ∑ n ∈ Finset.range M,
            ((k+1 : ℕ) : ℝ)*(1+‖center y‖)*zetaPrimeExpWeight (3/2) n := by
          apply Finset.sum_le_sum
          intro n _
          by_cases hn : n=0
          · simp only [hn,Nat.cast_zero,Nat.zero_add,Nat.cast_one,test,Real.log_zero,
              Real.log_one,Complex.ofReal_zero,zero_pow (Nat.succ_ne_zero _),zero_div,
              zero_mul,sub_zero,norm_zero,zetaPrimeExpWeight, mul_zero,
              Real.exp_zero,mul_one]
            positivity
          · rw [norm_sub_rev]
            simpa only [Nat.cast_add,Nat.cast_one] using
              norm_test_step_le k y (Nat.pos_of_ne_zero hn)
        _ = ((k+1 : ℕ) : ℝ)*(1+‖center y‖)*
            ∑ n ∈ Finset.range M, zetaPrimeExpWeight (3/2) n := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (hs.sum_le_tsum (Finset.range M) (fun _ _ => (Real.exp_pos _).le)) (by positivity)
    exact hh.trans (by
      rw [one_mul]
      exact (add_le_add he hv).trans_eq (by ring))

/-- Absolute convergence of the true integer rounding error series. -/
theorem summable_rounding_test (u y : ℝ) (k : ℕ) :
    Summable (fun n : ℕ => test k y n*(roundingError u y n : ℂ)) := by
  apply (summable_zetaOrdinaryPrimeLogMoment k
    (by norm_num [center] : 1<(center y).re)).norm.of_norm_bounded
  intro n
  by_cases hn : n.Prime
  · rw [test_nat,norm_mul]
    simp only [hn,ite_true,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.log_natCast_nonneg n),
      ArithmeticFunction.vonMangoldt_apply_prime hn]
    exact mul_le_of_le_one_right (by positivity) (roundingError_abs_le u y n)
  · simp [hn,roundingError_composite u y hn]

/-- The finite signed Abel bound passes to the convergent infinite series. -/
theorem rounding_bound (u y : ℝ) (k : ℕ) :
    ‖∑' n : ℕ, test k y n*(roundingError u y n : ℂ)‖ ≤
      ((k+1 : ℕ) : ℝ)*(1+(1+‖center y‖)*spatialMass) := by
  exact le_of_tendsto (summable_rounding_test u y k).hasSum.tendsto_sum_nat.norm
    (Filter.Eventually.of_forall (finite_rounding_bound u y k))

/-- Exact source normalization makes the actual rounding error vanish. -/
theorem tendsto_scaled_rounding {u : ℝ} (hu : 0 ≤ u) (hU : u<1) (y : ℝ) :
    Tendsto (fun k => (u : ℂ)^(k+1)*∑' n : ℕ,
      test k y n*(roundingError u y n : ℂ)) atTop (𝓝 0) := by
  have ht := ((tendsto_self_mul_const_pow_of_lt_one hu hU).comp
    (tendsto_add_atTop_nat 1)).mul_const (1+(1+‖center y‖)*spatialMass)
  apply squeeze_zero_norm (a := fun k : ℕ =>
    ((k+1 : ℕ) : ℝ)*u^(k+1)*(1+(1+‖center y‖)*spatialMass)) _ (by simpa using ht)
  intro k
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  exact (mul_le_mul_of_nonneg_left (rounding_bound u y k)
    (pow_nonneg hu _)).trans_eq (by ring)

/-- The removed prime flag takes only the literal integer values zero and one. -/
def removedBase (u y : ℝ) (p : ℕ) : ℝ := binaryPrimeAtom u y p

/-- The retained prime flag also takes only zero and one. -/
def retainedBase (u y : ℝ) (p : ℕ) : ℝ := 1-removedBase u y p

/-- Unit weights, not fractional prime valuations. -/
theorem removedBase_binary (u y : ℝ) (p : ℕ) :
    removedBase u y p=0 ∨ removedBase u y p=1 := by
  rcases binaryPrimeAtom_zero_or_one u y p with hh | hh
  · left; simp [removedBase,hh]
  · right; simp [removedBase,hh]

/-- Both binary prime systems have nonnegative weights bounded by one. -/
theorem binaryBase_bounds (u y : ℝ) (p : ℕ) :
    (0 ≤ removedBase u y p ∧ removedBase u y p ≤ 1) ∧
    (0 ≤ retainedBase u y p ∧ retainedBase u y p ≤ 1) := by
  rcases removedBase_binary u y p with hh | hh <;>
    norm_num [retainedBase,hh]

private theorem bounded_prime_summable (b : ℕ → ℝ)
    (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1) (y : ℝ) (k : ℕ) :
    Summable (fun n : ℕ => if n.Prime then
      (b n : ℂ)*(ArithmeticFunction.vonMangoldt n : ℂ)*
        zetaPrimeLogKernel k (center y) n else 0) := by
  apply (summable_zetaOrdinaryPrimeLogMoment k
    (by norm_num [center] : 1<(center y).re)).norm.of_norm_bounded
  intro n
  by_cases hn : n.Prime
  · simp only [hn,ite_true,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hb _).1]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hb n).2 (norm_nonneg _))
      (norm_nonneg _)).trans_eq (by ring)
  · simp [hn]

private theorem ordinaryMoment_series (b : ℕ → ℝ) (u y : ℝ) (k : ℕ) :
    ArithmeticOperatorPrimeTowerControl.ordinaryMoment b u y k =
      (u : ℂ)^(k+1)*∑' n : ℕ, if n.Prime then
        (b n : ℂ)*(ArithmeticFunction.vonMangoldt n : ℂ)*
          zetaPrimeLogKernel k (center y) n else 0 := by
  unfold ArithmeticOperatorPrimeTowerControl.ordinaryMoment
  apply congrArg ((u : ℂ)^(k+1)*·)
  apply tsum_congr
  intro n
  by_cases hn : n.Prime
  · simp only [hn,ite_true,ArithmeticOperatorPrimeTowerControl.towerCoefficient,
      hn.minFac_eq,Complex.ofReal_mul,center]
  · simp [hn]

/-- Exact infinite-series rounding ledger, with the entire phase retained. -/
theorem removed_sub_fractional_eq (u y : ℝ) (k : ℕ) :
    ArithmeticOperatorPrimeTowerControl.ordinaryMoment (removedBase u y) u y k-
      clippedRemovedMoment u y k =
    (u : ℂ)^(k+1)*∑' n : ℕ, test k y n*(roundingError u y n : ℂ) := by
  rw [ordinaryMoment_series]
  unfold clippedRemovedMoment
  have h0 := bounded_prime_summable (removedBase u y)
    (fun p => (binaryBase_bounds u y p).1) y k
  have h1 := bounded_prime_summable (clippedWeight u y) (fun p => clippedWeight_bounds u y p) y k
  unfold center at h0 h1 ⊢
  rw [←mul_sub,←h0.tsum_sub h1]
  apply congrArg ((u : ℂ)^(k+1)*·)
  apply tsum_congr
  intro n
  by_cases hn : n.Prime
  · simp only [hn,ite_true,test_nat,roundingError,removedBase,Complex.ofReal_sub,
      Complex.ofReal_natCast,ArithmeticFunction.vonMangoldt_apply_prime hn,center]
    ring
  · simp [hn,roundingError_composite u y hn]

/-- Integer rounding preserves the complete positive removed source. -/
theorem removedMoment_tendsto (u y : ℝ) (hu : 1/2<u) (hU : u<1) (hy : y≠0) :
    Tendsto (ArithmeticOperatorPrimeTowerControl.ordinaryMoment (removedBase u y) u y)
      atTop (𝓝 2) := by
  have hh := (tendsto_scaled_rounding (by linarith : 0≤u) hU y).congr
    (fun k => (removed_sub_fractional_eq u y k).symm)
  simpa only [zero_add] using (hh.add (clippedRemovedMoment_tendsto u y hu hU hy)).congr
    (fun k => sub_add_cancel _ _)

/-- Complementary ordinary-prime systems add to the original actual array. -/
theorem binary_ordinary_ledger (u y : ℝ) (k : ℕ) :
    ArithmeticOperatorPrimeTowerControl.ordinaryMoment (retainedBase u y) u y k+
      ArithmeticOperatorPrimeTowerControl.ordinaryMoment (removedBase u y) u y k =
      ZetaRieszPairPrimePowerPayment.ordinaryArray u y k := by
  rw [ordinaryMoment_series,ordinaryMoment_series,←mul_add,
    ←(bounded_prime_summable (retainedBase u y)
      (fun p => (binaryBase_bounds u y p).2) y k).tsum_add
      (bounded_prime_summable (removedBase u y)
        (fun p => (binaryBase_bounds u y p).1) y k)]
  unfold ZetaRieszPairPrimePowerPayment.ordinaryArray zetaOrdinaryPrimeLogMoment
  apply congrArg ((u : ℂ)^(k+1)*·)
  apply tsum_congr
  intro n
  by_cases hn : n.Prime
  · simp only [hn,ite_true,retainedBase,Complex.ofReal_sub,Complex.ofReal_one,center]
    ring
  · simp [hn]

/-- Literal retained-prime rounding is source-equivalent to fractional thinning. -/
theorem retained_sub_fractional_eq (u y : ℝ) (k : ℕ) :
    ArithmeticOperatorPrimeTowerControl.ordinaryMoment (retainedBase u y) u y k-
      retainedMoment u y k =
    -((u : ℂ)^(k+1)*∑' n : ℕ, test k y n*(roundingError u y n : ℂ)) := by
  have h0 := binary_ordinary_ledger u y k
  have h1 := retainedMoment_add_removed u y k
  have h2 := removed_sub_fractional_eq u y k
  linear_combination h0-h1-h2

/-- A LITERAL subset of ordinary primes has coherent source -2 at the
campaign radius and a permitted fixed height, without any zero hypothesis. -/
theorem retainedMoment_target_tendsto :
    Tendsto (ArithmeticOperatorPrimeTowerControl.ordinaryMoment
      (retainedBase (10001/20000) 54) (10001/20000) 54) atTop (𝓝 (-2)) := by
  have hh := (tendsto_scaled_rounding (u := 10001/20000) (by norm_num) (by norm_num) 54).neg.congr
    (fun k => (retained_sub_fractional_eq (10001/20000) 54 k).symm)
  simpa only [neg_zero,zero_add] using
    (hh.add ZetaRieszCeilingPrimeThinningAudit.retainedMoment_target_tendsto).congr
      (fun k => sub_add_cancel _ _)

/-- Every prime power of the SAME unit-weight prime subset is retained;
the proper-power error is independently geometrically paid. -/
theorem fullMoment_target_tendsto :
    Tendsto (ArithmeticOperatorPrimeTowerControl.fullMoment
      (retainedBase (10001/20000) 54) (10001/20000) 54) atTop (𝓝 (-2)) := by
  have hh := ArithmeticOperatorPrimeTowerControl.tendsto_full_sub_ordinary
    (retainedBase (10001/20000) 54) (fun p => (binaryBase_bounds _ _ p).2)
    (u := 10001/20000) (by norm_num) (by norm_num) 54
  simpa only [zero_add] using (hh.add retainedMoment_target_tendsto).congr
    (fun k => sub_add_cancel _ _)

end
end RiemannGaussian.ArithmeticOperatorBinaryPrimeControl
