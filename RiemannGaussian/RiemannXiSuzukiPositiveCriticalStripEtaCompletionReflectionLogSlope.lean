import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionMultiplier

/-!
# Horizontal logarithmic slope of the eta reflection multiplier

This module differentiates the exact reflection multiplier attached to the
literal positive-measure eta Laplace partition. The apparent endpoint poles
from the spectral factor cancel against the digamma recurrence. The resulting
horizontal logarithmic derivative is expressed as a symmetric shifted-
digamma term plus two explicit dyadic resolvents.

The real part of this pole-free expression is the derivative of the
same-ordinate logarithmic multiplier norm. Proving that its integral has the
strict sign of `sigma - 1 / 2` would establish the still-open horizontal
unit-norm rigidity. No such sign is assumed or claimed here.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The completion-weighted eta Laplace amplitude is differentiable
throughout the open critical strip. -/
theorem differentiableAt_pairedEtaCompletedLaplaceAmplitude
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    DifferentiableAt ℂ pairedEtaCompletedLaplaceAmplitude s := by
  unfold pairedEtaCompletedLaplaceAmplitude
  exact (differentiableAt_pairedEtaXiCompletionFactor hspos hslt).mul
    differentiableAt_id

/-- The eta Laplace reflection multiplier is differentiable throughout the
open critical strip. -/
theorem differentiableAt_pairedEtaLaplaceReflectionMultiplier
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    DifferentiableAt ℂ pairedEtaLaplaceReflectionMultiplier s := by
  have hpartnerPos : 0 < (1 - s).re := by simpa using sub_pos.mpr hslt
  have hpartnerLt : (1 - s).re < 1 := by simpa using sub_lt_self (1 : ℝ) hspos
  have hsDiff :=
    differentiableAt_pairedEtaCompletedLaplaceAmplitude hspos hslt
  have hpartnerDiff :=
    differentiableAt_pairedEtaCompletedLaplaceAmplitude hpartnerPos hpartnerLt
  have hsubDiff : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := by fun_prop
  unfold pairedEtaLaplaceReflectionMultiplier
  exact hsDiff.div (hpartnerDiff.comp s hsubDiff)
    (pairedEtaCompletedLaplaceAmplitude_ne_zero hpartnerPos hpartnerLt)

/-- The logarithmic derivative of the completed Laplace amplitude is its
regular completion correction plus the contribution of the factor `s`. -/
theorem logDeriv_pairedEtaCompletedLaplaceAmplitude
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    logDeriv pairedEtaCompletedLaplaceAmplitude s =
      pairedEtaArithmeticXiRegularCorrection s + 1 / s := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hspos
  unfold pairedEtaCompletedLaplaceAmplitude
  rw [logDeriv_mul (f := pairedEtaXiCompletionFactor)
    (g := fun z : ℂ => z) s
    (pairedEtaXiCompletionFactor_ne_zero hspos hslt) hs0
    (differentiableAt_pairedEtaXiCompletionFactor hspos hslt)
    differentiableAt_id,
    logDeriv_pairedEtaXiCompletionFactor hspos hslt,
    logDeriv_id']

/-- Differentiating the reflection quotient turns its logarithmic derivative
into the sum of the two complementary amplitude derivatives. -/
theorem logDeriv_pairedEtaLaplaceReflectionMultiplier_eq_sum
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    logDeriv pairedEtaLaplaceReflectionMultiplier s =
      (pairedEtaArithmeticXiRegularCorrection s + 1 / s) +
        (pairedEtaArithmeticXiRegularCorrection (1 - s) + 1 / (1 - s)) := by
  have hpartnerPos : 0 < (1 - s).re := by simpa using sub_pos.mpr hslt
  have hpartnerLt : (1 - s).re < 1 := by simpa using sub_lt_self (1 : ℝ) hspos
  have hsAmp := pairedEtaCompletedLaplaceAmplitude_ne_zero hspos hslt
  have hpartnerAmp :=
    pairedEtaCompletedLaplaceAmplitude_ne_zero hpartnerPos hpartnerLt
  have hsDiff :=
    differentiableAt_pairedEtaCompletedLaplaceAmplitude hspos hslt
  have hpartnerDiff :=
    differentiableAt_pairedEtaCompletedLaplaceAmplitude hpartnerPos hpartnerLt
  have hsubDiff : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := by fun_prop
  have hcompDiff : DifferentiableAt ℂ
      (fun z : ℂ => pairedEtaCompletedLaplaceAmplitude (1 - z)) s :=
    hpartnerDiff.comp s hsubDiff
  unfold pairedEtaLaplaceReflectionMultiplier
  rw [logDeriv_div s hsAmp hpartnerAmp hsDiff hcompDiff]
  have hcomp :
      logDeriv (fun z : ℂ => pairedEtaCompletedLaplaceAmplitude (1 - z)) s =
        -logDeriv pairedEtaCompletedLaplaceAmplitude (1 - s) := by
    rw [show (fun z : ℂ => pairedEtaCompletedLaplaceAmplitude (1 - z)) =
        pairedEtaCompletedLaplaceAmplitude ∘ (fun z : ℂ => 1 - z) by rfl,
      logDeriv_comp hpartnerDiff hsubDiff]
    have hderiv : deriv (fun z : ℂ => 1 - z) s = -1 := by
      simp
    rw [hderiv]
    ring
  rw [hcomp,
    logDeriv_pairedEtaCompletedLaplaceAmplitude hspos hslt,
    logDeriv_pairedEtaCompletedLaplaceAmplitude hpartnerPos hpartnerLt]
  ring

/-- In the positive half-plane, the digamma recurrence moves `digamma (s/2)`
away from its apparent endpoint pole and exposes the exact rational term. -/
theorem digamma_half_eq_shifted_sub_two_div
    {s : ℂ} (hspos : 0 < s.re) :
    Complex.digamma (s / 2) =
      Complex.digamma (1 + s / 2) - 2 / s := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hspos
  have hnotPole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hrec := Complex.digamma_apply_add_one (s / 2) hnotPole
  have hinv : (s / 2)⁻¹ = 2 / s := by
    field_simp
  rw [add_comm] at hrec
  rw [hrec, hinv]
  ring

/-- The elementary eta-factor logarithmic derivative is a dyadic resolvent on
the half-plane `Re s < 1`. -/
theorem pairedEtaFactorLogDerivative_eq_neg_log_two_div_one_sub_cpow
    {s : ℂ} (hslt : s.re < 1) :
    pairedEtaFactorLogDerivative s =
      -Complex.log 2 / (1 - (2 : ℂ) ^ (s - 1)) := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hr : 2 * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    calc
      2 * (2 : ℂ) ^ (-s) =
          (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-s) := by
            rw [Complex.cpow_one]
      _ = (2 : ℂ) ^ ((1 : ℂ) + (-s)) :=
        (Complex.cpow_add _ _ htwo).symm
      _ = (2 : ℂ) ^ (1 - s) := by ring_nf
  have hprod : (2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ (1 - s) = 1 := by
    calc
      (2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ (1 - s) =
          (2 : ℂ) ^ ((s - 1) + (1 - s)) :=
        (Complex.cpow_add _ _ htwo).symm
      _ = (2 : ℂ) ^ (0 : ℂ) := by ring_nf
      _ = 1 := Complex.cpow_zero _
  have hfactor : pairedEtaFactor s ≠ 0 :=
    pairedEtaFactor_ne_zero_of_re_lt_one hslt
  have hq : 1 - (2 : ℂ) ^ (s - 1) ≠ 0 := by
    intro h
    have hqone : (2 : ℂ) ^ (s - 1) = 1 :=
      (sub_eq_zero.mp h).symm
    have hrone : (2 : ℂ) ^ (1 - s) = 1 := by
      rw [hqone, one_mul] at hprod
      exact hprod
    apply hfactor
    unfold pairedEtaFactor
    rw [hr, hrone]
    ring
  have hrden : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
    simpa [pairedEtaFactor, hr] using hfactor
  rw [← hr] at hprod
  have hprod' :
      2 * (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (s - 1) = 1 := by
    calc
      2 * (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (s - 1) =
          (2 : ℂ) ^ (s - 1) * (2 * (2 : ℂ) ^ (-s)) := by ring
      _ = 1 := hprod
  unfold pairedEtaFactorLogDerivative pairedEtaFactor
  rw [hr]
  field_simp [hq, hrden]
  rw [← hr]
  linear_combination -Complex.log 2 * hprod'

/-- The apparent poles at `s = 0` and `s = 1` cancel from the multiplier's
logarithmic derivative, leaving shifted digamma and eta-factor terms. -/
theorem logDeriv_pairedEtaLaplaceReflectionMultiplier_eq_poleFree
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    logDeriv pairedEtaLaplaceReflectionMultiplier s =
      -Complex.log Real.pi +
        (Complex.digamma (1 + s / 2) +
          Complex.digamma (1 + (1 - s) / 2)) / 2 -
        pairedEtaFactorLogDerivative s -
        pairedEtaFactorLogDerivative (1 - s) := by
  have hpartnerPos : 0 < (1 - s).re := by simpa using sub_pos.mpr hslt
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hspos
  have h1s : 1 - s ≠ 0 := by
    intro h
    have h1eq : (1 : ℂ) = s := sub_eq_zero.mp h
    subst s
    norm_num at hslt
  have hs1 : s - 1 ≠ 0 := by
    intro h
    apply h1s
    linear_combination -h
  rw [logDeriv_pairedEtaLaplaceReflectionMultiplier_eq_sum hspos hslt]
  unfold pairedEtaArithmeticXiRegularCorrection
  rw [digamma_half_eq_shifted_sub_two_div hspos,
    digamma_half_eq_shifted_sub_two_div hpartnerPos]
  field_simp [hs0, h1s, hs1]
  ring

/-- The pole-free symmetric logarithmic slope, initially retaining the
elementary eta-factor logarithmic derivatives. -/
def pairedEtaLaplaceReflectionPoleFreeLogSlope (s : ℂ) : ℂ :=
  -Complex.log Real.pi +
    (Complex.digamma (1 + s / 2) +
      Complex.digamma (1 + (1 - s) / 2)) / 2 -
    pairedEtaFactorLogDerivative s -
    pairedEtaFactorLogDerivative (1 - s)

/-- The completely explicit form of the reflection slope, consisting of the
symmetric shifted-digamma term and two dyadic resolvents. -/
def pairedEtaLaplaceReflectionDyadicLogSlope (s : ℂ) : ℂ :=
  -Complex.log Real.pi +
    (Complex.digamma (1 + s / 2) +
      Complex.digamma (1 + (1 - s) / 2)) / 2 +
    Complex.log 2 / (1 - (2 : ℂ) ^ (s - 1)) +
    Complex.log 2 / (1 - (2 : ℂ) ^ (-s))

/-- Throughout the open strip, the pole-free slope is exactly its explicit
dyadic form. -/
theorem pairedEtaLaplaceReflectionPoleFreeLogSlope_eq_dyadicLogSlope
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaLaplaceReflectionPoleFreeLogSlope s =
      pairedEtaLaplaceReflectionDyadicLogSlope s := by
  have hpartnerLt : (1 - s).re < 1 := by
    simpa using sub_lt_self (1 : ℝ) hspos
  rw [pairedEtaLaplaceReflectionPoleFreeLogSlope,
    pairedEtaLaplaceReflectionDyadicLogSlope,
    pairedEtaFactorLogDerivative_eq_neg_log_two_div_one_sub_cpow hslt,
    pairedEtaFactorLogDerivative_eq_neg_log_two_div_one_sub_cpow hpartnerLt]
  ring_nf

/-- The multiplier's logarithmic derivative is exactly the explicit dyadic
slope throughout the open critical strip. -/
theorem logDeriv_pairedEtaLaplaceReflectionMultiplier_eq_dyadicLogSlope
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    logDeriv pairedEtaLaplaceReflectionMultiplier s =
      pairedEtaLaplaceReflectionDyadicLogSlope s := by
  rw [logDeriv_pairedEtaLaplaceReflectionMultiplier_eq_poleFree hspos hslt,
    show -Complex.log Real.pi +
          (Complex.digamma (1 + s / 2) +
            Complex.digamma (1 + (1 - s) / 2)) / 2 -
          pairedEtaFactorLogDerivative s -
          pairedEtaFactorLogDerivative (1 - s) =
        pairedEtaLaplaceReflectionPoleFreeLogSlope s by rfl,
    pairedEtaLaplaceReflectionPoleFreeLogSlope_eq_dyadicLogSlope hspos hslt]

/-- Named pole-free form of the multiplier logarithmic derivative. -/
theorem logDeriv_pairedEtaLaplaceReflectionMultiplier_eq_poleFreeLogSlope
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    logDeriv pairedEtaLaplaceReflectionMultiplier s =
      pairedEtaLaplaceReflectionPoleFreeLogSlope s := by
  exact logDeriv_pairedEtaLaplaceReflectionMultiplier_eq_poleFree hspos hslt

/-- The pole-free logarithmic slope is invariant under reflection about the
critical line. -/
theorem pairedEtaLaplaceReflectionPoleFreeLogSlope_one_sub (s : ℂ) :
    pairedEtaLaplaceReflectionPoleFreeLogSlope (1 - s) =
      pairedEtaLaplaceReflectionPoleFreeLogSlope s := by
  unfold pairedEtaLaplaceReflectionPoleFreeLogSlope
  rw [sub_sub_cancel]
  ring

/-- The same-ordinate real logarithm of the reflection-multiplier norm. -/
def pairedEtaLaplaceReflectionLogNorm (sigma y : ℝ) : ℝ :=
  Real.log ‖pairedEtaLaplaceReflectionMultiplier
    ((sigma : ℂ) + (y : ℂ) * Complex.I)‖

/-- Same-ordinate reflection makes the multiplier log norm antisymmetric
about the critical line. -/
theorem pairedEtaLaplaceReflectionLogNorm_one_sub
    {sigma y : ℝ} (hspos : 0 < sigma) (hslt : sigma < 1) :
    pairedEtaLaplaceReflectionLogNorm (1 - sigma) y =
      -pairedEtaLaplaceReflectionLogNorm sigma y := by
  let s : ℂ := (sigma : ℂ) + (y : ℂ) * Complex.I
  have hsre : s.re = sigma := by simp [s, Complex.mul_re]
  have hconjPos : 0 < (starRingEnd ℂ s).re := by simpa [hsre] using hspos
  have hconjLt : (starRingEnd ℂ s).re < 1 := by simpa [hsre] using hslt
  have hcoord :
      (((1 - sigma : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        1 - starRingEnd ℂ s := by
    apply Complex.ext <;> simp [s, Complex.mul_re, Complex.mul_im]
  have hmult := pairedEtaLaplaceReflectionMultiplier_one_sub
    (s := starRingEnd ℂ s) hconjPos hconjLt
  rw [pairedEtaLaplaceReflectionMultiplier_conj] at hmult
  unfold pairedEtaLaplaceReflectionLogNorm
  rw [hcoord, hmult, norm_inv, Real.log_inv]
  simp [s]

/-- The same-ordinate multiplier log norm vanishes identically on the
critical line. -/
theorem pairedEtaLaplaceReflectionLogNorm_half (y : ℝ) :
    pairedEtaLaplaceReflectionLogNorm (1 / 2) y = 0 := by
  let s : ℂ := (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  have hsre : s.re = 1 / 2 := by simp [s, Complex.mul_re]
  have hsq :=
    normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_of_re_eq_half hsre
  have hnormSq : ‖pairedEtaLaplaceReflectionMultiplier s‖ ^ 2 = 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hsq
  have hnorm : ‖pairedEtaLaplaceReflectionMultiplier s‖ = 1 := by
    nlinarith [norm_nonneg (pairedEtaLaplaceReflectionMultiplier s)]
  unfold pairedEtaLaplaceReflectionLogNorm
  change Real.log ‖pairedEtaLaplaceReflectionMultiplier s‖ = 0
  rw [hnorm, Real.log_one]

private theorem hasDerivAt_log_norm_of_hasDerivAt_mul_self_local
    {g : ℝ → ℂ} {D : ℂ} {x : ℝ}
    (hne : g x ≠ 0) (hg : HasDerivAt g (D * g x) x) :
    HasDerivAt (fun u => Real.log ‖g u‖) D.re x := by
  let q : ℝ → ℝ := fun u => ‖g u‖ ^ 2
  have hinner : inner ℝ (g x) (D * g x) = q x * D.re := by
    rw [Complex.inner]
    dsimp [q]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have hq : HasDerivAt q (2 * q x * D.re) x := by
    have hraw := hg.norm_sq
    simpa [q, hinner, mul_assoc] using hraw
  have hqpos : 0 < q x := by
    dsimp [q]
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hlog := hq.log hqpos.ne'
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  have hhalf' : HasDerivAt
      (fun u => (1 / 2 : ℝ) * Real.log (q u)) D.re x := by
    apply hhalf.congr_deriv
    field_simp [hqpos.ne']
  convert hhalf' using 1
  funext u
  simp [q, Real.log_pow]

/-- The horizontal derivative of the same-ordinate multiplier log norm is the
real part of the pole-free complex logarithmic slope. -/
theorem hasDerivAt_pairedEtaLaplaceReflectionLogNorm
    {sigma y : ℝ} (hspos : 0 < sigma) (hslt : sigma < 1) :
    HasDerivAt (fun u : ℝ => pairedEtaLaplaceReflectionLogNorm u y)
      (pairedEtaLaplaceReflectionPoleFreeLogSlope
        ((sigma : ℂ) + (y : ℂ) * Complex.I)).re sigma := by
  let s : ℂ := (sigma : ℂ) + (y : ℂ) * Complex.I
  let g : ℝ → ℂ := fun u =>
    pairedEtaLaplaceReflectionMultiplier
      ((u : ℂ) + (y : ℂ) * Complex.I)
  let affine : ℂ → ℂ := fun z => z + (y : ℂ) * Complex.I
  have hsre : s.re = sigma := by simp [s, Complex.mul_re]
  have hspos' : 0 < s.re := by simpa [hsre] using hspos
  have hslt' : s.re < 1 := by simpa [hsre] using hslt
  have haffine : HasDerivAt affine 1 (sigma : ℂ) := by
    simpa [affine] using
      (hasDerivAt_id (𝕜 := ℂ) (sigma : ℂ)).add_const
        ((y : ℂ) * Complex.I)
  have hsaffine : affine (sigma : ℂ) = s := by rfl
  have hmult : HasDerivAt pairedEtaLaplaceReflectionMultiplier
      (deriv pairedEtaLaplaceReflectionMultiplier s) s :=
    (differentiableAt_pairedEtaLaplaceReflectionMultiplier hspos' hslt').hasDerivAt
  have hcomp : HasDerivAt
      (pairedEtaLaplaceReflectionMultiplier ∘ affine)
      (deriv pairedEtaLaplaceReflectionMultiplier s) (sigma : ℂ) := by
    simpa only [hsaffine, mul_one] using hmult.comp (sigma : ℂ) haffine
  have hreal := hcomp.comp_ofReal
  have hgraw : HasDerivAt g
      (deriv pairedEtaLaplaceReflectionMultiplier s) sigma := by
    simpa [g, affine, s] using hreal
  let L : ℂ := logDeriv pairedEtaLaplaceReflectionMultiplier s
  have hgs : g sigma = pairedEtaLaplaceReflectionMultiplier s := by rfl
  have hne : pairedEtaLaplaceReflectionMultiplier s ≠ 0 :=
    pairedEtaLaplaceReflectionMultiplier_ne_zero hspos' hslt'
  have hderiv : deriv pairedEtaLaplaceReflectionMultiplier s =
      L * g sigma := by
    rw [hgs]
    dsimp [L]
    rw [logDeriv_apply]
    exact (div_mul_cancel₀ _ hne).symm
  have hg : HasDerivAt g (L * g sigma) sigma := by
    simpa [hderiv] using hgraw
  have hlog := hasDerivAt_log_norm_of_hasDerivAt_mul_self_local
    (by simpa [hgs] using hne) hg
  dsimp [L] at hlog
  rw [logDeriv_pairedEtaLaplaceReflectionMultiplier_eq_poleFreeLogSlope
    hspos' hslt'] at hlog
  simpa [pairedEtaLaplaceReflectionLogNorm, g, s] using hlog

/-- Derivative form of the horizontal log-norm slope identity. -/
theorem deriv_pairedEtaLaplaceReflectionLogNorm_eq_poleFreeLogSlope_re
    {sigma y : ℝ} (hspos : 0 < sigma) (hslt : sigma < 1) :
    deriv (fun u : ℝ => pairedEtaLaplaceReflectionLogNorm u y) sigma =
      (pairedEtaLaplaceReflectionPoleFreeLogSlope
        ((sigma : ℂ) + (y : ℂ) * Complex.I)).re :=
  (hasDerivAt_pairedEtaLaplaceReflectionLogNorm hspos hslt).deriv

/-- Direct dyadic form of the horizontal log-norm derivative. -/
theorem hasDerivAt_pairedEtaLaplaceReflectionLogNorm_dyadic
    {sigma y : ℝ} (hspos : 0 < sigma) (hslt : sigma < 1) :
    HasDerivAt (fun u : ℝ => pairedEtaLaplaceReflectionLogNorm u y)
      (pairedEtaLaplaceReflectionDyadicLogSlope
        ((sigma : ℂ) + (y : ℂ) * Complex.I)).re sigma := by
  have hsre :
      (((sigma : ℂ) + (y : ℂ) * Complex.I)).re = sigma := by
    simp [Complex.mul_re]
  have h := hasDerivAt_pairedEtaLaplaceReflectionLogNorm
    (y := y) hspos hslt
  rw [pairedEtaLaplaceReflectionPoleFreeLogSlope_eq_dyadicLogSlope
    (by simpa [hsre] using hspos) (by simpa [hsre] using hslt)] at h
  exact h

/-- Derivative form of the fully explicit dyadic horizontal slope identity. -/
theorem deriv_pairedEtaLaplaceReflectionLogNorm_eq_dyadicLogSlope_re
    {sigma y : ℝ} (hspos : 0 < sigma) (hslt : sigma < 1) :
    deriv (fun u : ℝ => pairedEtaLaplaceReflectionLogNorm u y) sigma =
      (pairedEtaLaplaceReflectionDyadicLogSlope
        ((sigma : ℂ) + (y : ℂ) * Complex.I)).re :=
  (hasDerivAt_pairedEtaLaplaceReflectionLogNorm_dyadic hspos hslt).deriv

end
end RiemannGaussian
