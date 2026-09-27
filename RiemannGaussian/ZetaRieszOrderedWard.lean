/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMarkedLogDerivative

/-!
# Exact joint logarithmic-derivative cancellation and its order boundary

The Euler logarithmic derivative and its own quotient satisfy a signed
convolution law. An arbitrary order mask retains an explicit complementary
sum. That complement cannot be silently discarded for the Riesz rectangle.
-/

namespace RiemannGaussian.ZetaRieszOrderedWard
noncomputable section
open scoped BigOperators Classical
open Complex Filter Set Topology
open ZetaRieszMarkedEulerError ZetaRieszMarkedSeparation

/-- The signed derivative is a convolution of the full logarithmic
derivative with the same function. No norm enters this identity. -/
theorem logarithmic_convolution {F : ℂ → ℂ} {s : ℂ}
    (hF : AnalyticAt ℂ F s) (hne : F s ≠ 0) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), signedTaylorMoment j (fun z => -logDeriv F z) s*
      signedTaylorMoment (n-j) F s) = ((n+1 : ℕ) : ℂ)*signedTaylorMoment (n+1) F s := by
  have hlog : AnalyticAt ℂ (fun z => -logDeriv F z) s :=
    (hF.deriv.div hF hne).neg
  have he : (fun z => -logDeriv F z*F z) =ᶠ[nhds s] (fun z => -deriv F z) := by
    filter_upwards [hF.continuousAt.eventually_ne hne] with z hz
    simp [logDeriv_apply,hz]
  rw [← signedTaylorMoment_mul hlog hF,signedTaylorMoment_congr n he]
  have hm := signedTaylorMoment_const_mul n (-1) (deriv F) s
  simp only [neg_one_mul] at hm
  rw [hm,signedTaylorMoment_deriv]
  ring

/-- Exact order-window ledger. The omitted convolution is retained
with its sign, not replaced by a termwise positive allowance. -/
theorem masked_logarithmic_convolution {F : ℂ → ℂ} {s : ℂ}
    (hF : AnalyticAt ℂ F s) (hne : F s ≠ 0) (n : ℕ) (W : Finset ℕ)
    (hW : W ⊆ Finset.range (n+1)) :
    (∑ j ∈ W, signedTaylorMoment j (fun z => -logDeriv F z) s*signedTaylorMoment (n-j) F s) =
      ((n+1 : ℕ) : ℂ)*signedTaylorMoment (n+1) F s-
        ∑ j ∈ Finset.range (n+1) \ W,
          signedTaylorMoment j (fun z => -logDeriv F z) s*signedTaylorMoment (n-j) F s := by
  have h := Finset.sum_sdiff hW
    (f := fun j => signedTaylorMoment j (fun z => -logDeriv F z) s*signedTaylorMoment (n-j) F s)
  rw [logarithmic_convolution hF hne n] at h
  exact eq_sub_iff_add_eq.mpr (by linear_combination h)

/-- If the input is the logarithmic derivative of a DIFFERENT prime
range, its signed mismatch remains in the exact window ledger. -/
theorem masked_input_convolution {F H : ℂ → ℂ} {s : ℂ}
    (hF : AnalyticAt ℂ F s) (hne : F s ≠ 0) (hH : AnalyticAt ℂ H s)
    (n : ℕ) (W : Finset ℕ) (hW : W ⊆ Finset.range (n+1)) :
    (∑ j ∈ W, signedTaylorMoment j H s*signedTaylorMoment (n-j) F s) =
      ((n+1 : ℕ) : ℂ)*signedTaylorMoment (n+1) F s-
        (∑ j ∈ Finset.range (n+1) \ W,
          signedTaylorMoment j (fun z => -logDeriv F z) s*signedTaylorMoment (n-j) F s)+
        ∑ j ∈ W, signedTaylorMoment j (fun z => H z+logDeriv F z) s*
          signedTaylorMoment (n-j) F s := by
  have hlog : AnalyticAt ℂ (logDeriv F) s := hF.deriv.div hF hne
  have he : H = (fun z => -logDeriv F z+(H z+logDeriv F z)) := by funext z; ring
  have hm (j : ℕ) : signedTaylorMoment j H s =
      signedTaylorMoment j (fun z => -logDeriv F z) s+
        signedTaylorMoment j (fun z => H z+logDeriv F z) s := by
    conv_lhs => rw [he]
    exact signedTaylorMoment_add j hlog.neg (hH.add hlog)
  simp_rw [hm,add_mul,Finset.sum_add_distrib]
  rw [masked_logarithmic_convolution hF hne n W hW]

/-- The actual local Euler logarithmic slope, with both frequencies. -/
def localSlope (p : ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  (Real.log p : ℂ)*(zetaPrimeFeature s p/(1-zetaPrimeFeature s p)-
    (zetaPrimeFeature s p*zetaPrimeFeature (Complex.I*xi) p)/
      (1-zetaPrimeFeature s p*zetaPrimeFeature (Complex.I*xi) p))

/-- The finite slope uses exactly the primes of its own Euler quotient. -/
def eulerSlope (Q : Finset ℕ) (xi : ℝ) (s : ℂ) : ℂ := ∑ p ∈ Q, localSlope p xi s

theorem feature_hasDerivAt (s : ℂ) (p : ℕ) :
    HasDerivAt (fun z => zetaPrimeFeature z p)
      (-(Real.log p : ℂ)*zetaPrimeFeature s p) s := by
  have h := (((hasDerivAt_id s).mul_const (Real.log p : ℂ)).neg).cexp
  convert! h using 1
  all_goals simp only [zetaPrimeFeature,Pi.neg_apply,id_eq,one_mul]
  ring

theorem local_denominators {p : ℕ} (hp : 16 ≤ p) {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) :
    1-zetaPrimeFeature s p ≠ 0 ∧
      1-zetaPrimeFeature s p*zetaPrimeFeature (Complex.I*xi) p ≠ 0 := by
  have hq := ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter hs hp
  constructor
  · simpa using (ZetaRieszEulerQuotient.local_denominator_ne_zero hq
      (show ‖(1 : ℂ)‖ ≤ 1 by norm_num))
  · exact ZetaRieszEulerQuotient.local_denominator_ne_zero hq (norm_character_phase xi p).le

/-- The finite ordered quotient has no zero in its Euler half-plane. -/
theorem quotient_ne_zero (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) : quotient Q xi s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have h := local_denominators (h16 p hp) hs xi
  exact div_ne_zero h.2 h.1

/-- Exact logarithmic differentiation of the retained finite product.
The prime ordering is part of Q and is not completed by this theorem. -/
theorem neg_logDeriv_quotient (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) :
    -logDeriv (quotient Q xi) s = eulerSlope Q xi s := by
  let f (p : ℕ) (z : ℂ) := (1-zetaPrimeFeature z p*zetaPrimeFeature (Complex.I*xi) p)/
    (1-zetaPrimeFeature z p)
  have hd (p : ℕ) (hp : p ∈ Q) : DifferentiableAt ℂ (f p) s := by
    exact (((hasDerivAt_const s 1).sub
      ((feature_hasDerivAt s p).mul_const (zetaPrimeFeature (Complex.I*xi) p))).div
      ((hasDerivAt_const s 1).sub (feature_hasDerivAt s p))
      (local_denominators (h16 p hp) hs xi).1).differentiableAt
  have hn (p : ℕ) (hp : p ∈ Q) : f p s ≠ 0 :=
    div_ne_zero (local_denominators (h16 p hp) hs xi).2 (local_denominators (h16 p hp) hs xi).1
  have hl := logDeriv_prod hn hd
  have he : (fun z => ∏ p ∈ Q, f p z) = quotient Q xi := rfl
  rw [he] at hl
  rw [hl,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hd := ((hasDerivAt_const s 1).sub
    ((feature_hasDerivAt s p).mul_const (zetaPrimeFeature (Complex.I*xi) p))).div
    ((hasDerivAt_const s 1).sub (feature_hasDerivAt s p))
    (local_denominators (h16 p hp) hs xi).1
  have hd' := hd.deriv
  change deriv (f p) s = _ at hd'
  rw [logDeriv_apply,hd']
  dsimp [f,localSlope]
  field_simp [(local_denominators (h16 p hp) hs xi).1,
    (local_denominators (h16 p hp) hs xi).2]
  ring

/-- The exact cancellation law applies to each literal least-prime
tail; it still has a full convolution range. -/
theorem ordered_quotient_convolution (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (r n : ℕ) {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) :
    (∑ j ∈ Finset.range (n+1),
      signedTaylorMoment j (fun z => -logDeriv (quotient (tailPrimes A r) xi) z) s*
        signedTaylorMoment (n-j) (quotient (tailPrimes A r) xi) s) =
      ((n+1 : ℕ) : ℂ)*signedTaylorMoment (n+1) (quotient (tailPrimes A r) xi) s := by
  have htail : ∀ p ∈ tailPrimes A r, 16 ≤ p := fun p hp => h16 p (Finset.mem_filter.mp hp).1
  exact logarithmic_convolution (analyticAt_quotient _ htail hs xi) (quotient_ne_zero _ htail hs xi) n

/-- The exact complete marked slope after the independently paid
proper-power replacement. -/
def completeSlope (xi : ℝ) (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s-(-logDeriv riemannZeta (s+Complex.I*xi))

theorem analyticAt_completeSlope {s : ℂ} (hs : 1 < s.re) (xi : ℝ) :
    AnalyticAt ℂ (completeSlope xi) s := by
  have ht : 1 < (s+Complex.I*xi).re := by simpa using hs
  exact (ZetaRieszShiftedCenter.analyticAt_zeta_logDeriv hs).sub
    ((ZetaRieszShiftedCenter.analyticAt_zeta_logDeriv ht).comp (f := fun z : ℂ => z+Complex.I*xi)
      (analyticAt_id.add analyticAt_const))

/-- The factor j is essential: the marked prime has an unlogged
factorial kernel, whereas the slope includes one prime logarithm. -/
theorem moment_completeSlope (j : ℕ) {s : ℂ} (hs : 1 < s.re) (xi : ℝ) :
    signedTaylorMoment j (completeSlope xi) s =
      ((j+1 : ℕ) : ℂ)*ZetaRieszMarkedLogDerivative.logDifference (j+1) s xi := by
  have ht : 1 < (s+Complex.I*xi).re := by simpa using hs
  have hshift : signedTaylorMoment j (fun z => -logDeriv riemannZeta (z+Complex.I*xi)) s =
      zetaPrimeLogMoment j (s+Complex.I*xi) := by
    have hd := congrFun (iteratedDeriv_comp_add_const j (fun z => -logDeriv riemannZeta z)
      (Complex.I*xi)) s
    exact congrArg (fun v => (-1 : ℂ)^j/(j.factorial : ℂ)*v) hd
  change signedTaylorMoment j (fun z => -logDeriv riemannZeta z-
    (-logDeriv riemannZeta (z+Complex.I*xi))) s = _
  have ha : AnalyticAt ℂ (fun z => -logDeriv riemannZeta (z+Complex.I*xi)) s :=
    (ZetaRieszShiftedCenter.analyticAt_zeta_logDeriv ht).comp (f := fun z : ℂ => z+Complex.I*xi)
      (analyticAt_id.add analyticAt_const)
  rw [signedTaylorMoment_sub j (ZetaRieszShiftedCenter.analyticAt_zeta_logDeriv hs) ha,
    hshift,ZetaRieszMarkedLogDerivative.logDifference]
  change zetaPrimeLogMoment j s-zetaPrimeLogMoment j (s+Complex.I*xi) = _
  have hj : ((j+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast at hj ⊢
  field_simp

/-- The complete prime range and the literal ordered cofactor have
different logarithmic slopes. This is their exact signed mismatch. -/
def rangeMismatch (Q : Finset ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  completeSlope xi s+logDeriv (quotient Q xi) s

theorem rangeMismatch_eq (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) :
    rangeMismatch Q xi s = completeSlope xi s-eulerSlope Q xi s := by
  rw [← neg_logDeriv_quotient Q h16 hs xi]
  simp only [rangeMismatch,sub_neg_eq_add]

/-- Exact joint ledger for the present complete marked leg and
literal ordered cofactor. Both the omitted orders and prime-range
mismatch survive, with their signs. This is not a bound for either. -/
theorem marked_ordered_ledger (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (r n : ℕ) {s : ℂ} (hs : 1 < s.re) (xi : ℝ) (W : Finset ℕ)
    (hW : W ⊆ Finset.range (n+1)) :
    (∑ j ∈ W, (((j+1 : ℕ) : ℂ)*ZetaRieszMarkedLogDerivative.logDifference (j+1) s xi)*
      signedTaylorMoment (n-j) (quotient (tailPrimes A r) xi) s) =
      ((n+1 : ℕ) : ℂ)*signedTaylorMoment (n+1) (quotient (tailPrimes A r) xi) s-
        (∑ j ∈ Finset.range (n+1) \ W,
          signedTaylorMoment j (fun z => -logDeriv (quotient (tailPrimes A r) xi) z) s*
            signedTaylorMoment (n-j) (quotient (tailPrimes A r) xi) s)+
        ∑ j ∈ W, signedTaylorMoment j (rangeMismatch (tailPrimes A r) xi) s*
          signedTaylorMoment (n-j) (quotient (tailPrimes A r) xi) s := by
  have htail : ∀ p ∈ tailPrimes A r, 16 ≤ p := fun p hp => h16 p (Finset.mem_filter.mp hp).1
  simp_rw [← moment_completeSlope _ hs xi]
  exact masked_input_convolution (analyticAt_quotient _ htail (by linarith) xi)
    (quotient_ne_zero _ htail (by linarith) xi) (analyticAt_completeSlope hs xi) n W hW

end
end RiemannGaussian.ZetaRieszOrderedWard
