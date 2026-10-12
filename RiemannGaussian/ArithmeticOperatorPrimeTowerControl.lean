/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFactorialUniqueness
import RiemannGaussian.ArithmeticOperatorGramAudit
import RiemannGaussian.ZetaRieszCeilingPrimeThinningAudit

/-!
# Positive actual-prime towers do not by themselves prevent coherence

Extend the existing bounded fractional thinning of GENUINE primes to
every proper power of the same base. The extension preserves the full
complex factorial source, literal prime-power support, positivity and
all free feature Grams. Its Gamma observations are bounded by the true
integer observations but cannot equal all of them. This is a collapse
control for support/positivity/power-consistency arguments, not the
actual Mangoldt sequence or a generalized-prime Euler product.
-/

namespace RiemannGaussian.ArithmeticOperatorPrimeTowerControl
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
open ZetaRieszCeilingPrimeThinningAudit

/-- One weight is shared by EVERY power of the same literal prime base. -/
def towerCoefficient (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  b n.minFac*ArithmeticFunction.vonMangoldt n

/-- Full factorial moment, retaining all proper powers and the height. -/
def fullMoment (b : ℕ → ℝ) (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+1)*∑' n, (towerCoefficient b n : ℂ)*
    zetaPrimeLogKernel k (3/2+Complex.I*y) n

/-- Ordinary-prime restriction of the SAME coefficient array. -/
def ordinaryMoment (b : ℕ → ℝ) (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+1)*∑' n, if n.Prime then
    (towerCoefficient b n : ℂ)*zetaPrimeLogKernel k (3/2+Complex.I*y) n else 0

/-- The full proper-prime-power leg with unchanged base weights. -/
def properMoment (b : ℕ → ℝ) (y : ℝ) (k : ℕ) : ℂ :=
  ∑' n, ((b n.minFac*zetaProperPrimePowerCoefficient n : ℝ) : ℂ)*
    zetaPrimeLogKernel k (3/2+Complex.I*y) n

/-- Pointwise arithmetic bounds, not a spectral or exposure assumption. -/
theorem towerCoefficient_bounds (b : ℕ → ℝ) (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1) (n : ℕ) :
    0 ≤ towerCoefficient b n ∧ towerCoefficient b n ≤ ArithmeticFunction.vonMangoldt n := by
  unfold towerCoefficient
  constructor
  · exact mul_nonneg (hb _).1 ArithmeticFunction.vonMangoldt_nonneg
  · exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (hb _).2

/-- Composite labels outside the genuine prime powers have zero weight. -/
theorem towerCoefficient_not_primePow (b : ℕ → ℝ) {n : ℕ} (hn : ¬IsPrimePow n) :
    towerCoefficient b n = 0 := by
  simp [towerCoefficient,ArithmeticFunction.vonMangoldt_apply,hn]

/-- No exponent is truncated or reweighted along a prime-power tower. -/
theorem towerCoefficient_pow (b : ℕ → ℝ) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    towerCoefficient b (p^k) = b p*Real.log p := by
  simp [towerCoefficient,Nat.pow_minFac hk.ne',hp.minFac_eq,
    ArithmeticFunction.vonMangoldt_apply_pow hk.ne',ArithmeticFunction.vonMangoldt_apply_prime hp]

private theorem proper_summable (b : ℕ → ℝ) (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1)
    (y : ℝ) (k : ℕ) :
    Summable (fun n => ((b n.minFac*zetaProperPrimePowerCoefficient n : ℝ) : ℂ)*
      zetaPrimeLogKernel k (3/2+Complex.I*y) n) := by
  apply (summable_zetaProperPrimePowerMoment k (by norm_num :
    1/2 < (3/2+Complex.I*(y : ℂ)).re)).norm.of_norm_bounded
  intro n
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg
    (mul_nonneg (hb _).1 (zetaProperPrimePowerCoefficient_nonneg _)),
    norm_mul,Complex.norm_real,Real.norm_of_nonneg (zetaProperPrimePowerCoefficient_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (zetaProperPrimePowerCoefficient_nonneg _) (hb _).2)
    (norm_nonneg _)

private theorem ordinary_summable (b : ℕ → ℝ) (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1)
    (y : ℝ) (k : ℕ) :
    Summable (fun n => if n.Prime then
      (towerCoefficient b n : ℂ)*zetaPrimeLogKernel k (3/2+Complex.I*y) n else 0) := by
  apply (summable_zetaOrdinaryPrimeLogMoment k (by norm_num :
    1 < (3/2+Complex.I*(y : ℂ)).re)).norm.of_norm_bounded
  intro n
  by_cases hn : n.Prime
  · simp only [hn,ite_true,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (towerCoefficient_bounds b hb n).1,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul_of_nonneg_right (towerCoefficient_bounds b hb n).2 (norm_nonneg _)
  · simp [hn]

/-- Exact full/ordinary/proper splitting with the original phase. -/
theorem fullMoment_eq_ordinary_add_proper (b : ℕ → ℝ) (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1)
    (u y : ℝ) (k : ℕ) :
    fullMoment b u y k = ordinaryMoment b u y k+(u : ℂ)^(k+1)*properMoment b y k := by
  unfold fullMoment ordinaryMoment properMoment
  rw [←mul_add,←(ordinary_summable b hb y k).tsum_add (proper_summable b hb y k)]
  apply congrArg ((u : ℂ)^(k+1)*·)
  apply tsum_congr
  intro n
  by_cases hn : n.Prime <;> simp [hn,towerCoefficient,zetaProperPrimePowerCoefficient]

/-- Bounded base weights preserve the independent geometric proper-power
payment; no linear source or hypothetical zero is assumed. -/
theorem norm_properMoment_le (b : ℕ → ℝ) (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1)
    (y : ℝ) (k : ℕ) :
    ‖properMoment b y k‖ ≤ (4/3 : ℝ)^k*zetaProperPrimePowerExpMass (3/4) := by
  have hs := summable_zetaProperPrimePowerExpMass (by norm_num : (1/2 : ℝ)<3/4)
  have hmajor := hs.mul_left ((4/3 : ℝ)^k)
  unfold properMoment
  apply (norm_tsum_le_tsum_norm (proper_summable b hb y k).norm).trans
  calc
    _ ≤ ∑' n, (4/3 : ℝ)^k*
        (zetaProperPrimePowerCoefficient n*zetaPrimeExpWeight (3/4) n) := by
      apply Summable.tsum_le_tsum _ (proper_summable b hb y k).norm hmajor
      intro n
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg
        (mul_nonneg (hb _).1 (zetaProperPrimePowerCoefficient_nonneg _))]
      have hk := norm_zetaPrimeLogKernel_le k (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ)<3/4)
      norm_num at hk
      exact (mul_le_mul
        (mul_le_of_le_one_left (zetaProperPrimePowerCoefficient_nonneg _) (hb _).2)
        hk (norm_nonneg _) (zetaProperPrimePowerCoefficient_nonneg _)).trans_eq (by ring)
    _ = _ := by rw [tsum_mul_left]; rfl

/-- EVERY bounded prime-tower reweighting has negligible proper powers
at this source scale; positivity has not been used to discard the phase. -/
theorem tendsto_full_sub_ordinary (b : ℕ → ℝ) (hb : ∀ p, 0 ≤ b p ∧ b p ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) (hU : u < 3/4) (y : ℝ) :
    Tendsto (fun k => fullMoment b u y k-ordinaryMoment b u y k) atTop (𝓝 0) := by
  have hrate : 4*u/3 < 1 := by linarith
  have ht : Tendsto (fun k : ℕ => u*zetaProperPrimePowerExpMass (3/4)*(4*u/3)^k)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : (0 : ℝ) ≤ 4*u/3) hrate).const_mul
        (u*zetaProperPrimePowerExpMass (3/4))
  apply squeeze_zero_norm (a := fun k => u*zetaProperPrimePowerExpMass (3/4)*(4*u/3)^k) _ ht
  intro k
  rw [fullMoment_eq_ordinary_add_proper b hb,add_sub_cancel_left,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_of_nonneg hu]
  exact (mul_le_mul_of_nonneg_left (norm_properMoment_le b hb y k)
    (pow_nonneg hu _)).trans_eq (by simp only [pow_succ,div_pow,mul_pow]; ring)

/-- The established bounded thinning profile, now used on ALL actual
prime-power towers rather than only on ordinary primes. -/
def profile (u y : ℝ) (p : ℕ) : ℝ := 1-clippedWeight u y p

/-- Exact agreement on the ordinary-prime leg of the prior control. -/
theorem ordinaryMoment_profile (u y : ℝ) (k : ℕ) :
    ordinaryMoment (profile u y) u y k = retainedMoment u y k := by
  unfold ordinaryMoment retainedMoment
  apply congrArg ((u : ℂ)^(k+1)*·)
  apply tsum_congr
  intro p
  by_cases hp : p.Prime
  · simp [hp,towerCoefficient,profile]
  · simp [hp]

/-- Unconditional coherent control on GENUINE integer prime powers,
with the complete factorial kernel at a permitted campaign height. -/
theorem fullMoment_target_tendsto :
    Tendsto (fullMoment (profile (10001/20000) 54) (10001/20000) 54)
      atTop (𝓝 (-2)) := by
  have hh := tendsto_full_sub_ordinary (profile (10001/20000) 54)
    (fun _ => retainedWeight_bounds _ _ _) (u := 10001/20000) (y := 54)
      (by norm_num) (by norm_num)
  have ht : Tendsto (ordinaryMoment (profile (10001/20000) 54) (10001/20000) 54)
      atTop (𝓝 (-2)) := by
    exact retainedMoment_target_tendsto.congr (fun k => (ordinaryMoment_profile _ _ k).symm)
  simpa only [zero_add] using (hh.add ht).congr (fun k => sub_add_cancel _ _)

/-- Every finite divisor/quotient/Gaussian feature Gram remains PSD for
the SAME full tower control, even though its factorial moments cohere. -/
theorem control_free_Gram_nonnegative {ι : Type*} (S : Finset ι) (D : Finset ℕ)
    (alpha : ι → ℂ) (feature : ι → ℕ → ℂ) (u y : ℝ) :
    0 ≤ (ArithmeticOperatorGramAudit.joinedGram S D alpha feature
      (fun n => (towerCoefficient (profile u y) n : ℂ))).re :=
  ArithmeticOperatorGramAudit.joinedGram_nonnegative_for_arbitrary_weights S D alpha feature
    (towerCoefficient (profile u y)) (fun n _ =>
      (towerCoefficient_bounds _ (fun _ => retainedWeight_bounds _ _ _) n).1)

/-- The literal Gamma inequality also holds for this control; only
equality of ALL exact observations singles out the true sequence. -/
theorem control_factorialPrefix_le (u y : ℝ) (N : ℕ) :
    (ArithmeticOperatorFactorialUniqueness.factorialPrefix
      (fun n => (towerCoefficient (profile u y) n : ℂ)) N).re ≤
      Real.log (N.factorial : ℝ) := by
  have he := congrArg Complex.re (ArithmeticOperatorFactorialUniqueness.factorialPrefix_mangoldt N)
  simp only [ArithmeticOperatorFactorialUniqueness.factorialPrefix,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,
    Complex.natCast_im,mul_zero,sub_zero] at he ⊢
  rw [←he]
  apply Finset.sum_le_sum
  intro n _
  exact mul_le_mul_of_nonneg_left
    (towerCoefficient_bounds _ (fun _ => retainedWeight_bounds _ _ _) n).2 (by positivity)

private theorem actual_target_tendsto :
    Tendsto (ZetaRieszPairPrimePowerPayment.ordinaryArray (10001/20000) 54) atTop (𝓝 0) := by
  have hlog : Real.log (|(54 : ℝ)|+3) ≤ 1800 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<57)
    norm_num at hh ⊢
    linarith only [hh]
  obtain ⟨C,_,hbound⟩ := ZetaRieszJoinedPhaseRadius.exists_ordinary_bound_concrete_height
    (y := 54) (by norm_num) hlog
  apply squeeze_zero_norm (a := fun k => (10001/20000 : ℝ)*C*(100010/100011 : ℝ)^k) _
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ)≤100010/100011)
      (by norm_num : (100010/100011 : ℝ)<1)).const_mul ((10001/20000 : ℝ)*C))
  intro k
  unfold ZetaRieszPairPrimePowerPayment.ordinaryArray
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤10001/20000)]
  calc
    _ ≤ (10001/20000 : ℝ)^(k+1)*(C/(100011/200000)^k) :=
      mul_le_mul_of_nonneg_left (hbound k) (by positivity)
    _ = (10001/20000 : ℝ)*C*((10001/20000)^k/(100011/200000)^k) := by
      rw [pow_succ]
      ring
    _ = (10001/20000 : ℝ)*C*((10001/20000)/(100011/200000))^k :=
      congrArg (fun x : ℝ => (10001/20000 : ℝ)*C*x)
        (div_pow (10001/20000 : ℝ) (100011/200000 : ℝ) k).symm
    _ = _ := by norm_num

/-- Halving the removed mass produces a SIMPLE source while keeping
all base weights between one half and one, on the same genuine towers. -/
def halfProfile (u y : ℝ) (p : ℕ) : ℝ := (1+profile u y p)/2

/-- The simple-source control is positive even on its finite clipped head. -/
theorem halfProfile_bounds (u y : ℝ) (p : ℕ) :
    1/2 ≤ halfProfile u y p ∧ halfProfile u y p ≤ 1 := by
  have hb := retainedWeight_bounds u y p
  unfold halfProfile profile
  constructor <;> linarith only [hb.1,hb.2]

/-- Exact affine ledger on complete convergent prime series. -/
theorem ordinaryMoment_halfProfile_eq (u y : ℝ) (k : ℕ) :
    ordinaryMoment (halfProfile u y) u y k =
      (1/2 : ℂ)*ZetaRieszPairPrimePowerPayment.ordinaryArray u y k+
      (1/2 : ℂ)*retainedMoment u y k := by
  have h0 := summable_zetaOrdinaryPrimeLogMoment k
    (by norm_num : 1 < (3/2+Complex.I*(y : ℂ)).re)
  have h1 := ordinary_summable (profile u y) (fun _ => retainedWeight_bounds _ _ _) y k
  have he : (∑' n, if n.Prime then
      (towerCoefficient (halfProfile u y) n : ℂ)*zetaPrimeLogKernel k (3/2+Complex.I*y) n else 0) =
      (1/2 : ℂ)*((∑' n, if n.Prime then (ArithmeticFunction.vonMangoldt n : ℂ)*
        zetaPrimeLogKernel k (3/2+Complex.I*y) n else 0)+
      ∑' n, if n.Prime then (towerCoefficient (profile u y) n : ℂ)*
        zetaPrimeLogKernel k (3/2+Complex.I*y) n else 0) := by
    rw [←h0.tsum_add h1,←tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn : n.Prime
    · simp only [hn,ite_true,towerCoefficient,halfProfile,Complex.ofReal_mul,
        Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_ofNat]
      ring
    · simp [hn]
  unfold ordinaryMoment ZetaRieszPairPrimePowerPayment.ordinaryArray zetaOrdinaryPrimeLogMoment
  rw [he]
  have hh := ordinaryMoment_profile u y k
  unfold ordinaryMoment at hh
  rw [←hh]
  ring

/-- Source -1 is also compatible with bounded POSITIVE actual-prime
towers and every proper-power incidence, unconditionally. -/
theorem fullMoment_simple_target_tendsto :
    Tendsto (fullMoment (halfProfile (10001/20000) 54) (10001/20000) 54)
      atTop (𝓝 (-1)) := by
  have hb : ∀ p, 0 ≤ halfProfile (10001/20000) 54 p ∧
      halfProfile (10001/20000) 54 p ≤ 1 := by
    intro p
    have hh := halfProfile_bounds (10001/20000) 54 p
    constructor <;> linarith only [hh.1,hh.2]
  have ht : Tendsto (ordinaryMoment (halfProfile (10001/20000) 54) (10001/20000) 54)
      atTop (𝓝 (-1)) := by
    have hh := (actual_target_tendsto.const_mul (1/2 : ℂ)).add
      (retainedMoment_target_tendsto.const_mul (1/2 : ℂ))
    convert hh.congr (fun k => (ordinaryMoment_halfProfile_eq _ _ k).symm) using 1
    norm_num
  have hh := tendsto_full_sub_ordinary (halfProfile (10001/20000) 54) hb
    (u := 10001/20000) (y := 54) (by norm_num) (by norm_num)
  simpa only [zero_add] using (hh.add ht).congr (fun k => sub_add_cancel _ _)

/-- The control is NOT a substitute for all exact integer Gamma data.
This gate is certified by two distinct moment limits, not a floating
prime sample or a hypothetical off-line zero. -/
theorem control_fails_complete_Gamma :
    ∃ N, ArithmeticOperatorFactorialUniqueness.factorialPrefix
      (fun n => (towerCoefficient (profile (10001/20000) 54) n : ℂ)) N ≠
        (Real.log (N.factorial : ℝ) : ℂ) := by
  by_contra hh
  push Not at hh
  have hcoeff := ArithmeticOperatorFactorialUniqueness.mangoldt_unique hh
  have he (k : ℕ) : ordinaryMoment (profile (10001/20000) 54) (10001/20000) 54 k =
      ZetaRieszPairPrimePowerPayment.ordinaryArray (10001/20000) 54 k := by
    unfold ordinaryMoment ZetaRieszPairPrimePowerPayment.ordinaryArray zetaOrdinaryPrimeLogMoment
    apply congrArg (((10001/20000 : ℝ) : ℂ)^(k+1)*·)
    apply tsum_congr
    intro n
    by_cases hn : n.Prime
    · simp only [hn,ite_true,hcoeff n hn.pos]
    · simp [hn]
  have ht : Tendsto (ZetaRieszPairPrimePowerPayment.ordinaryArray (10001/20000) 54)
      atTop (𝓝 (-2)) := by
    have hh' : Tendsto (ordinaryMoment (profile (10001/20000) 54) (10001/20000) 54)
        atTop (𝓝 (-2)) := by
      exact retainedMoment_target_tendsto.congr (fun k => (ordinaryMoment_profile _ _ k).symm)
    exact hh'.congr he
  have heq := tendsto_nhds_unique actual_target_tendsto ht
  norm_num at heq

end
end RiemannGaussian.ArithmeticOperatorPrimeTowerControl
