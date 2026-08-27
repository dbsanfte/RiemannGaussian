import RiemannGaussian.FiniteToEntireHardyReductio
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# The finite-to-entire theta quotient

This file constructs the fixed meromorphic object available in the entire
limit of the finite Krein--Langer quotients.  For an analytic homotopy

`E_eta = f + i * eta * f'`,

it defines `E_eta^sharp = f - i * eta * f'` and
`Theta_eta = E_eta^sharp / E_eta`.  It proves that finite polynomial theta
quotients converge locally uniformly to this quotient on every open region
where the limiting denominator is nonzero.

For spectral xi, `E_eta^sharp` is also proved to be the literal conjugate
reflection of `E_eta`.  The final theorem composes quotient convergence with
the finite Hardy reductio sequence supplied by failure of RH.  It does not
extend the quotient through the pinned homotopy root: identifying the
Krein--Langer-cancelled value there is the remaining limit problem.
-/

open Filter Polynomial Set
open scoped ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- The reflected analytic homotopy `f - i * eta * f'`. -/
def analyticESharpValue (f : ℂ → ℂ) (eta : ℝ) (z : ℂ) : ℂ :=
  f z - Complex.I * (eta : ℂ) * deriv f z

/-- The entire-limit analogue of the finite rational function
`E_eta^sharp / E_eta`. -/
def analyticThetaValue (f : ℂ → ℂ) (eta : ℝ) (z : ℂ) : ℂ :=
  analyticESharpValue f eta z / analyticEValue f eta z

/-- On a real polynomial, the analytic reflected homotopy is exactly the
finite reflected polynomial evaluation. -/
@[simp] theorem analyticESharpValue_realPolynomial
    (A : ℝ[X]) (eta : ℝ) (z : ℂ) :
    analyticESharpValue
        (fun w : ℂ ↦ (A.map Complex.ofRealHom).eval w) eta z =
      (finiteESharpPolynomial A eta).eval z := by
  rw [analyticESharpValue, Polynomial.deriv, finiteESharpPolynomial_eval]
  simp [Polynomial.eval_map]

/-- On a real polynomial, the analytic theta quotient is exactly the finite
theta quotient. -/
@[simp] theorem analyticThetaValue_realPolynomial
    (A : ℝ[X]) (eta : ℝ) (z : ℂ) :
    analyticThetaValue
        (fun w : ℂ ↦ (A.map Complex.ofRealHom).eval w) eta z =
      finiteThetaValue A eta z := by
  simp [analyticThetaValue, finiteThetaValue]

/-- If `f` is invariant under conjugate reflection, then the two analytic
homotopies are literal reflections of one another. -/
theorem analyticESharpValue_eq_conj_analyticEValue_conj
    {f : ℂ → ℂ} (hconj : ∀ z, f (conj z) = conj (f z))
    (eta : ℝ) (z : ℂ) :
    analyticESharpValue f eta z =
      conj (analyticEValue f eta (conj z)) := by
  have hf : f = conj ∘ f ∘ conj := by
    funext w
    simp [Function.comp_def, hconj]
  have hd := congrFun (congrArg deriv hf) z
  rw [deriv_conj_conj] at hd
  have hreflect : conj (deriv f (conj z)) = deriv f z := hd.symm
  rw [analyticESharpValue, analyticEValue, map_add, map_mul,
    map_mul, hreflect]
  have hfreflect : conj (f (conj z)) = f z := by
    rw [hconj]
    simp
  rw [hfreflect]
  simp
  ring

/-- The reflected spectral-xi homotopy is the conjugate reflection of the
positive homotopy. -/
theorem riemannXiSpectral_analyticESharpValue_eq_conj_analyticEValue_conj
    (eta : ℝ) (z : ℂ) :
    analyticESharpValue riemannXiSpectral eta z =
      conj (analyticEValue riemannXiSpectral eta (conj z)) :=
  analyticESharpValue_eq_conj_analyticEValue_conj
    riemannXiSpectral_conj eta z

/-- Locally uniform convergence of holomorphic functions passes through the
reflected homotopy operation. -/
theorem analyticESharpValue_tendstoLocallyUniformlyOn
    {ι : Type*} {phi : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hF : TendstoLocallyUniformlyOn F f phi U)
    (hhol : ∀ᶠ n in phi, DifferentiableOn ℂ (F n) U) (hU : IsOpen U)
    (eta : ℝ) :
    TendstoLocallyUniformlyOn
      (fun n ↦ analyticESharpValue (F n) eta)
      (analyticESharpValue f eta) phi U := by
  have hderiv := hF.deriv hhol hU
  have hscaled :=
    (uniformContinuous_const_smul
      (-(Complex.I * (eta : ℂ)))).comp_tendstoLocallyUniformlyOn hderiv
  refine ((hF.add hscaled).congr
    (G := fun n ↦ analyticESharpValue (F n) eta) ?_).congr_right ?_
  · intro n z _
    simp [analyticESharpValue, Function.comp_def, smul_eq_mul,
      sub_eq_add_neg]
  · intro z _
    simp [analyticESharpValue, Function.comp_def, smul_eq_mul,
      sub_eq_add_neg]

/-- The reflected homotopy is holomorphic wherever `f` is holomorphic. -/
theorem analyticESharpValue_differentiableOn
    {f : ℂ → ℂ} {U : Set ℂ} (hf : DifferentiableOn ℂ f U)
    (hU : IsOpen U) (eta : ℝ) :
    DifferentiableOn ℂ (analyticESharpValue f eta) U := by
  unfold analyticESharpValue
  intro z hz
  exact (hf z hz).sub
    (((hf.deriv hU) z hz).const_mul (Complex.I * (eta : ℂ)))

/-- On a zero-free open region, locally uniform convergence passes to the
meromorphic theta quotient. -/
theorem analyticThetaValue_tendstoLocallyUniformlyOn
    {ι : Type*} {phi : Filter ι} [phi.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hF : TendstoLocallyUniformlyOn F f phi U)
    (hhol : ∀ᶠ n in phi, DifferentiableOn ℂ (F n) U) (hU : IsOpen U)
    (eta : ℝ)
    (hzero : ∀ z ∈ U, analyticEValue f eta z ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun n ↦ analyticThetaValue (F n) eta)
      (analyticThetaValue f eta) phi U := by
  have hfdiff : DifferentiableOn ℂ f U :=
    hF.differentiableOn hhol hU
  have hsharp := analyticESharpValue_tendstoLocallyUniformlyOn
    hF hhol hU eta
  have hE := analyticEValue_tendstoLocallyUniformlyOn hF hhol hU eta
  have hsharpCont : ContinuousOn (analyticESharpValue f eta) U :=
    (analyticESharpValue_differentiableOn hfdiff hU eta).continuousOn
  have hECont : ContinuousOn (analyticEValue f eta) U :=
    (analyticEValue_differentiableOn hfdiff hU eta).continuousOn
  refine ((hsharp.div₀ hE hsharpCont hECont hzero).congr
    (G := fun n ↦ analyticThetaValue (F n) eta) ?_).congr_right ?_
  · intro n w _
    rfl
  · intro w _
    rfl

/-- Polynomial specialization of the zero-free theta convergence theorem. -/
theorem finiteThetaValue_tendstoLocallyUniformlyOn
    {ι : Type*} {phi : Filter ι} [phi.NeBot]
    (A : ι → ℝ[X]) {f : ℂ → ℂ} {U : Set ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n z ↦ ((A n).map Complex.ofRealHom).eval z) f phi U)
    (hU : IsOpen U) (eta : ℝ)
    (hzero : ∀ z ∈ U, analyticEValue f eta z ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun n ↦ finiteThetaValue (A n) eta)
      (analyticThetaValue f eta) phi U := by
  have htheta := analyticThetaValue_tendstoLocallyUniformlyOn hA
    (Eventually.of_forall fun n ↦
      ((A n).map Complex.ofRealHom).differentiableOn)
    hU eta hzero
  exact htheta.congr fun n w _ ↦
    analyticThetaValue_realPolynomial (A n) eta w

/-- Under failure of RH, the same canonical finite Hardy sequence also has
locally uniform theta convergence on every zero-free open region of the
limiting homotopy. -/
theorem exists_canonicalFiniteHardyFrontier_theta_limit_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        ∀ U : Set ℂ, IsOpen U →
          (∀ w ∈ U, analyticEValue riemannXiSpectral eta w ≠ 0) →
          TendstoLocallyUniformlyOn
            (fun n ↦ finiteThetaValue (B n) eta)
            (analyticThetaValue riemannXiSpectral eta) atTop U := by
  obtain ⟨eta, heta, z, hz, B, hB, hfrontier⟩ :=
    exists_canonicalFiniteHardyFrontier_sequence_of_not_rh hRH
  refine ⟨eta, heta, z, hz, B, hB, hfrontier, ?_⟩
  intro U hU hzero
  exact finiteThetaValue_tendstoLocallyUniformlyOn B
    (hB.mono (subset_univ U)) hU eta hzero

end

end RiemannGaussian
