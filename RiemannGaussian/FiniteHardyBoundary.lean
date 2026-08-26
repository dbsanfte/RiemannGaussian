import RiemannGaussian.FiniteModelGeometry
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Finite rational model spaces on the Hardy boundary

This file begins the analytic realization of the finite algebraic model.  A
numerator `q` of degree strictly below a polynomial denominator `P` with no
real zero gives the continuous boundary function `x ↦ q(x) / P(x)`.

We prove directly that it decays as `O(1 / |x|)`, is square-integrable on the
whole real line, and defines a faithful linear map into `L²(ℝ, ℂ)`.  Applied
to the residual and Blaschke denominators, these maps give genuine
finite-dimensional closed subspaces of `L²`.  Their intersection is trivial,
and therefore the actual orthogonal cross angle is pointwise strictly
contractive.

No Hardy orthogonality identity is assumed here.  In particular, injectivity
of the orthogonal cross angle remains a separate analytic theorem.
-/

open Polynomial Filter Asymptotics MeasureTheory

namespace RiemannGaussian

noncomputable section

def finiteModelBoundaryValue (P : ℂ[X]) (q : finiteModelSpace P) (x : ℝ) : ℂ :=
  finiteModelValue P q (x : ℂ)

theorem polynomialBoundaryQuotient_isBigO_inv
    {q P : ℂ[X]} (hdeg : q.natDegree < P.natDegree)
    (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0)
    {l : Filter ℝ}
    (hl : Tendsto (fun x : ℝ ↦ (x : ℂ)) l (Bornology.cobounded ℂ)) :
    (fun x : ℝ ↦ q.eval (x : ℂ) / P.eval (x : ℂ)) =O[l]
      (fun x : ℝ ↦ ((x : ℂ)⁻¹)) := by
  have hP : P ≠ 0 := by
    intro hzero
    simpa [hzero] using hreal 0
  by_cases hq : q = 0
  · apply IsBigO.of_bound 0
    simp [hq]
  have hdegree : (X * q).degree ≤ P.degree := by
    rw [degree_eq_natDegree (mul_ne_zero X_ne_zero hq),
      degree_eq_natDegree hP]
    exact_mod_cast (show (X * q).natDegree ≤ P.natDegree by
      rw [natDegree_X_mul hq]
      omega)
  have hpoly :
      (X * q).eval =O[Bornology.cobounded ℂ] P.eval :=
    Polynomial.isBigO_cobounded_of_degree_le hdegree
  obtain ⟨c, hc⟩ := (hpoly.comp_tendsto hl).bound
  have hnonzero : ∀ᶠ x : ℝ in l, (x : ℂ) ≠ 0 := by
    have haway : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 := by
      filter_upwards [
        (Bornology.isBounded_singleton (x := (0 : ℂ))).compl]
        with z hz
      simpa using hz
    exact hl.eventually haway
  apply IsBigO.of_bound c
  filter_upwards [hc, hnonzero] with x hx hxComplex
  have hxnorm : 0 < ‖(x : ℂ)‖ := norm_pos_iff.mpr hxComplex
  have hPnorm : 0 < ‖P.eval (x : ℂ)‖ :=
    norm_pos_iff.mpr (hreal x)
  change ‖(X * q).eval (x : ℂ)‖ ≤
    c * ‖P.eval (x : ℂ)‖ at hx
  rw [eval_mul, eval_X, norm_mul] at hx
  rw [norm_div, norm_inv]
  calc
    ‖q.eval (x : ℂ)‖ / ‖P.eval (x : ℂ)‖ ≤
        (c * ‖P.eval (x : ℂ)‖ / ‖(x : ℂ)‖) /
          ‖P.eval (x : ℂ)‖ := by
      apply (div_le_div_iff_of_pos_right hPnorm).2
      exact (le_div_iff₀ hxnorm).2 (by simpa [mul_comm] using hx)
    _ = c * (‖(x : ℂ)‖)⁻¹ := by
      field_simp [hxnorm.ne', hPnorm.ne']

theorem polynomialBoundaryQuotient_isBigO_inv_atTop
    {q P : ℂ[X]} (hdeg : q.natDegree < P.natDegree)
    (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0) :
    (fun x : ℝ ↦ q.eval (x : ℂ) / P.eval (x : ℂ)) =O[atTop]
      (fun x : ℝ ↦ ((x : ℂ)⁻¹)) :=
  polynomialBoundaryQuotient_isBigO_inv hdeg hreal
    (RCLike.tendsto_ofReal_atTop_cobounded ℂ)

theorem polynomialBoundaryQuotient_isBigO_inv_atBot
    {q P : ℂ[X]} (hdeg : q.natDegree < P.natDegree)
    (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0) :
    (fun x : ℝ ↦ q.eval (x : ℂ) / P.eval (x : ℂ)) =O[atBot]
      (fun x : ℝ ↦ ((x : ℂ)⁻¹)) :=
  polynomialBoundaryQuotient_isBigO_inv hdeg hreal
    (RCLike.tendsto_ofReal_atBot_cobounded ℂ)

theorem norm_complex_inv_ofReal_sq_le_cauchy
    {x : ℝ} (hx : 1 ≤ |x|) :
    ‖((x : ℂ)⁻¹)‖ ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have hxzero : x ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hx
    linarith
  have hxsq : 0 < x ^ 2 := sq_pos_of_ne_zero hxzero
  have hden : 0 < 1 + x ^ 2 := by positivity
  have hone : 1 ≤ x ^ 2 := by
    nlinarith [sq_abs x]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs]
  have hfrac : 1 / x ^ 2 ≤ 2 / (1 + x ^ 2) := by
    rw [div_le_div_iff₀ hxsq hden]
    nlinarith
  simpa [div_eq_mul_inv] using hfrac

theorem norm_complex_inv_ofReal_sq_isBigO_cauchy
    {l : Filter ℝ} (hfar : ∀ᶠ x in l, 1 ≤ |x|) :
    (fun x : ℝ ↦ ‖((x : ℂ)⁻¹)‖ ^ 2) =O[l]
      (fun x : ℝ ↦ (1 + x ^ 2)⁻¹) := by
  apply IsBigO.of_bound 2
  filter_upwards [hfar] with x hx
  have hden : 0 < 1 + x ^ 2 := by positivity
  simpa [Real.norm_eq_abs, abs_inv, abs_of_pos hden] using
    norm_complex_inv_ofReal_sq_le_cauchy hx

theorem polynomialBoundaryQuotient_continuous
    {q P : ℂ[X]} (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0) :
    Continuous (fun x : ℝ ↦ q.eval (x : ℂ) / P.eval (x : ℂ)) := by
  apply Continuous.div
  · exact q.continuous.comp Complex.continuous_ofReal
  · exact P.continuous.comp Complex.continuous_ofReal
  · exact hreal

theorem polynomialBoundaryQuotient_normSq_integrable
    {q P : ℂ[X]} (hdeg : q.natDegree < P.natDegree)
    (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0) :
    Integrable
      (fun x : ℝ ↦ ‖q.eval (x : ℂ) / P.eval (x : ℂ)‖ ^ 2) := by
  let f : ℝ → ℂ := fun x ↦ q.eval (x : ℂ) / P.eval (x : ℂ)
  let g : ℝ → ℝ := fun x ↦ (1 + x ^ 2)⁻¹
  have hfarTop : ∀ᶠ x : ℝ in atTop, 1 ≤ |x| := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact hx.trans (le_abs_self x)
  have hfarBot : ∀ᶠ x : ℝ in atBot, 1 ≤ |x| := by
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with x hx
    rw [abs_of_nonpos (by linarith)]
    linarith
  have htop : (fun x ↦ ‖f x‖ ^ 2) =O[atTop] g :=
    ((polynomialBoundaryQuotient_isBigO_inv_atTop hdeg hreal).norm_norm.pow 2).trans
      (norm_complex_inv_ofReal_sq_isBigO_cauchy hfarTop)
  have hbot : (fun x ↦ ‖f x‖ ^ 2) =O[atBot] g :=
    ((polynomialBoundaryQuotient_isBigO_inv_atBot hdeg hreal).norm_norm.pow 2).trans
      (norm_complex_inv_ofReal_sq_isBigO_cauchy hfarBot)
  have hlocal : LocallyIntegrable (fun x ↦ ‖f x‖ ^ 2) :=
    (polynomialBoundaryQuotient_continuous hreal).norm.pow 2 |>.locallyIntegrable
  exact hlocal.integrable_of_isBigO_atBot_atTop hbot
    (integrable_inv_one_add_sq.integrableAtFilter atBot) htop
    (integrable_inv_one_add_sq.integrableAtFilter atTop)

theorem polynomialBoundaryQuotient_memLp_two
    {q P : ℂ[X]} (hdeg : q.natDegree < P.natDegree)
    (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0) :
    MemLp (fun x : ℝ ↦ q.eval (x : ℂ) / P.eval (x : ℂ)) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (polynomialBoundaryQuotient_continuous hreal).aestronglyMeasurable).2
  exact polynomialBoundaryQuotient_normSq_integrable hdeg hreal

theorem finiteModelBoundaryValue_memLp_two
    {P : ℂ[X]} (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0)
    (q : finiteModelSpace P) :
    MemLp (finiteModelBoundaryValue P q) 2 := by
  by_cases hq : (q : ℂ[X]) = 0
  · have hzero : finiteModelBoundaryValue P q =
        (fun _ : ℝ ↦ (0 : ℂ)) := by
      funext x
      simp [finiteModelBoundaryValue, finiteModelValue, hq]
    rw [hzero]
    exact MemLp.zero
  · apply polynomialBoundaryQuotient_memLp_two _ hreal
    apply (natDegree_lt_natDegree_iff hq).2
    rw [degree_eq_natDegree (p := P) (by
      intro hP
      exact hreal 0 (by simp [hP]))]
    exact mem_degreeLT.mp q.property

theorem lowerRootFactor_eval_real_ne_zero (p : ℂ[X]) (x : ℝ) :
    (lowerRootFactor p).eval (x : ℂ) ≠ 0 := by
  intro hzero
  have hxmem : (x : ℂ) ∈ (lowerRootFactor p).roots :=
    (mem_roots (lowerRootFactor_ne_zero p)).mpr hzero
  rw [lowerRootFactor_roots, Multiset.mem_filter] at hxmem
  simpa using hxmem.2

theorem conjugate_upperRootFactor_eval_real_ne_zero
    (p : ℂ[X]) (x : ℝ) :
    (conjugatePolynomial (upperRootFactor p)).eval (x : ℂ) ≠ 0 := by
  rw [conjugatePolynomial_eval_real]
  simpa using upperRootFactor_eval_real_ne_zero p x

theorem finitePositiveModelBoundaryValue_memLp_two
    (A : ℝ[X]) (tau : ℝ) (q : finitePositiveModelSpace A tau) :
    MemLp
      (finiteModelBoundaryValue
        (lowerRootFactor (finiteEPolynomial A tau)) q) 2 :=
  finiteModelBoundaryValue_memLp_two
    (lowerRootFactor_eval_real_ne_zero (finiteEPolynomial A tau)) q

theorem finiteNegativeModelBoundaryValue_memLp_two
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    MemLp
      (finiteModelBoundaryValue
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau))) q) 2 :=
  finiteModelBoundaryValue_memLp_two
    (conjugate_upperRootFactor_eval_real_ne_zero
      (finiteEPolynomial A tau)) q

@[simp] theorem finiteModelBoundaryValue_add
    (P : ℂ[X]) (q r : finiteModelSpace P) :
    finiteModelBoundaryValue P (q + r) =
      finiteModelBoundaryValue P q + finiteModelBoundaryValue P r := by
  funext x
  simp [finiteModelBoundaryValue, finiteModelValue]
  ring

@[simp] theorem finiteModelBoundaryValue_smul
    (P : ℂ[X]) (c : ℂ) (q : finiteModelSpace P) :
    finiteModelBoundaryValue P (c • q) =
      c • finiteModelBoundaryValue P q := by
  funext x
  simp [finiteModelBoundaryValue, finiteModelValue]
  ring

noncomputable def finiteModelBoundaryLpLinearMap
    (P : ℂ[X]) (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0) :
    finiteModelSpace P →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun q := (finiteModelBoundaryValue_memLp_two hreal q).toLp
    (finiteModelBoundaryValue P q)
  map_add' q r := by
    let hq := finiteModelBoundaryValue_memLp_two hreal q
    let hr := finiteModelBoundaryValue_memLp_two hreal r
    calc
      (finiteModelBoundaryValue_memLp_two hreal (q + r)).toLp
          (finiteModelBoundaryValue P (q + r)) =
          (hq.add hr).toLp
            (finiteModelBoundaryValue P q +
              finiteModelBoundaryValue P r) := by
        apply MemLp.toLp_congr
        exact Filter.Eventually.of_forall fun x => by
          simpa only [Pi.add_apply] using
            congrFun (finiteModelBoundaryValue_add P q r) x
      _ = hq.toLp (finiteModelBoundaryValue P q) +
          hr.toLp (finiteModelBoundaryValue P r) :=
        MemLp.toLp_add hq hr
  map_smul' c q := by
    let hq := finiteModelBoundaryValue_memLp_two hreal q
    calc
      (finiteModelBoundaryValue_memLp_two hreal (c • q)).toLp
          (finiteModelBoundaryValue P (c • q)) =
          (hq.const_smul c).toLp
            (c • finiteModelBoundaryValue P q) := by
        apply MemLp.toLp_congr
        exact Filter.Eventually.of_forall fun x => by
          simpa only [Pi.smul_apply] using
            congrFun (finiteModelBoundaryValue_smul P c q) x
      _ = c • hq.toLp (finiteModelBoundaryValue P q) :=
        MemLp.toLp_const_smul c hq

theorem finiteModelBoundaryLpLinearMap_injective
    (P : ℂ[X]) (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0) :
    Function.Injective (finiteModelBoundaryLpLinearMap P hreal) := by
  intro q r hqr
  change
    (finiteModelBoundaryValue_memLp_two hreal q).toLp
        (finiteModelBoundaryValue P q) =
      (finiteModelBoundaryValue_memLp_two hreal r).toLp
        (finiteModelBoundaryValue P r) at hqr
  have hae : finiteModelBoundaryValue P q =ᵐ[volume]
      finiteModelBoundaryValue P r :=
    (MemLp.toLp_eq_toLp_iff
      (finiteModelBoundaryValue_memLp_two hreal q)
      (finiteModelBoundaryValue_memLp_two hreal r)).mp hqr
  have hqcont : Continuous (finiteModelBoundaryValue P q) := by
    change Continuous
      (fun x : ℝ ↦ (q : ℂ[X]).eval (x : ℂ) / P.eval (x : ℂ))
    exact polynomialBoundaryQuotient_continuous hreal
  have hrcont : Continuous (finiteModelBoundaryValue P r) := by
    change Continuous
      (fun x : ℝ ↦ (r : ℂ[X]).eval (x : ℂ) / P.eval (x : ℂ))
    exact polynomialBoundaryQuotient_continuous hreal
  have hfun : finiteModelBoundaryValue P q =
      finiteModelBoundaryValue P r :=
    (hqcont.ae_eq_iff_eq volume hrcont).mp hae
  apply Subtype.ext
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective Complex.ofReal_injective).mono ?_
  intro z hz
  obtain ⟨x, rfl⟩ := hz
  apply (div_left_inj' (hreal x)).mp
  simpa [finiteModelBoundaryValue, finiteModelValue] using congrFun hfun x

theorem finiteModelBoundaryLpLinearMap_ae
    (P : ℂ[X]) (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0)
    (q : finiteModelSpace P) :
    finiteModelBoundaryLpLinearMap P hreal q =ᵐ[volume]
      finiteModelBoundaryValue P q :=
  MemLp.coeFn_toLp (finiteModelBoundaryValue_memLp_two hreal q)

/-- Equality of two boundary `L²` classes clears to the exact polynomial
common-numerator identity. -/
theorem finiteModelBoundaryLp_eq_imp_cross_mul
    {P Q : ℂ[X]}
    (hP : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0)
    (hQ : ∀ x : ℝ, Q.eval (x : ℂ) ≠ 0)
    (q : finiteModelSpace P) (r : finiteModelSpace Q)
    (hEq : finiteModelBoundaryLpLinearMap P hP q =
      finiteModelBoundaryLpLinearMap Q hQ r) :
    (q : ℂ[X]) * Q = (r : ℂ[X]) * P := by
  change
    (finiteModelBoundaryValue_memLp_two hP q).toLp
        (finiteModelBoundaryValue P q) =
      (finiteModelBoundaryValue_memLp_two hQ r).toLp
        (finiteModelBoundaryValue Q r) at hEq
  have hae : finiteModelBoundaryValue P q =ᵐ[volume]
      finiteModelBoundaryValue Q r :=
    (MemLp.toLp_eq_toLp_iff
      (finiteModelBoundaryValue_memLp_two hP q)
      (finiteModelBoundaryValue_memLp_two hQ r)).mp hEq
  have hqcont : Continuous (finiteModelBoundaryValue P q) := by
    change Continuous
      (fun x : ℝ ↦ (q : ℂ[X]).eval (x : ℂ) / P.eval (x : ℂ))
    exact polynomialBoundaryQuotient_continuous hP
  have hrcont : Continuous (finiteModelBoundaryValue Q r) := by
    change Continuous
      (fun x : ℝ ↦ (r : ℂ[X]).eval (x : ℂ) / Q.eval (x : ℂ))
    exact polynomialBoundaryQuotient_continuous hQ
  have hfun : finiteModelBoundaryValue P q =
      finiteModelBoundaryValue Q r :=
    (hqcont.ae_eq_iff_eq volume hrcont).mp hae
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective Complex.ofReal_injective).mono ?_
  intro z hz
  obtain ⟨x, rfl⟩ := hz
  change ((q : ℂ[X]) * Q).eval (x : ℂ) =
    ((r : ℂ[X]) * P).eval (x : ℂ)
  rw [eval_mul, eval_mul]
  apply (div_eq_div_iff (hP x) (hQ x)).mp
  simpa [finiteModelBoundaryValue, finiteModelValue] using congrFun hfun x

noncomputable def finitePositiveModelBoundaryLpLinearMap
    (A : ℝ[X]) (tau : ℝ) :
    finitePositiveModelSpace A tau →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) :=
  finiteModelBoundaryLpLinearMap
    (lowerRootFactor (finiteEPolynomial A tau))
    (lowerRootFactor_eval_real_ne_zero (finiteEPolynomial A tau))

noncomputable def finiteNegativeModelBoundaryLpLinearMap
    (A : ℝ[X]) (tau : ℝ) :
    finiteNegativeModelSpace A tau →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) :=
  finiteModelBoundaryLpLinearMap
    (conjugatePolynomial
      (upperRootFactor (finiteEPolynomial A tau)))
    (conjugate_upperRootFactor_eval_real_ne_zero
      (finiteEPolynomial A tau))

theorem finitePositiveModelBoundaryLpLinearMap_injective
    (A : ℝ[X]) (tau : ℝ) :
    Function.Injective (finitePositiveModelBoundaryLpLinearMap A tau) :=
  finiteModelBoundaryLpLinearMap_injective _ _

theorem finiteNegativeModelBoundaryLpLinearMap_injective
    (A : ℝ[X]) (tau : ℝ) :
    Function.Injective (finiteNegativeModelBoundaryLpLinearMap A tau) :=
  finiteModelBoundaryLpLinearMap_injective _ _

/-- The residual finite model, now realized as an actual subspace of
`L²(ℝ, ℂ)` by its rational boundary values. -/
def finitePositiveBoundarySubspace (A : ℝ[X]) (tau : ℝ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  LinearMap.range (finitePositiveModelBoundaryLpLinearMap A tau)

/-- The Blaschke finite model, now realized as an actual subspace of
`L²(ℝ, ℂ)` by its rational boundary values. -/
def finiteNegativeBoundarySubspace (A : ℝ[X]) (tau : ℝ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  LinearMap.range (finiteNegativeModelBoundaryLpLinearMap A tau)

theorem finiteBoundarySubspaces_disjoint
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    Disjoint (finitePositiveBoundarySubspace A tau)
      (finiteNegativeBoundarySubspace A tau) := by
  refine Submodule.disjoint_def.mpr ?_
  intro y hyPositive hyNegative
  change y ∈ LinearMap.range
    (finitePositiveModelBoundaryLpLinearMap A tau) at hyPositive
  change y ∈ LinearMap.range
    (finiteNegativeModelBoundaryLpLinearMap A tau) at hyNegative
  obtain ⟨qS, hqS⟩ := hyPositive
  obtain ⟨qB, hqB⟩ := hyNegative
  have hmaps : finitePositiveModelBoundaryLpLinearMap A tau qS =
      finiteNegativeModelBoundaryLpLinearMap A tau qB :=
    hqS.trans hqB.symm
  have hcommon :
      (qS : ℂ[X]) *
          conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)) =
        (qB : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau) :=
    finiteModelBoundaryLp_eq_imp_cross_mul
      (lowerRootFactor_eval_real_ne_zero (finiteEPolynomial A tau))
      (conjugate_upperRootFactor_eval_real_ne_zero
        (finiteEPolynomial A tau)) qS qB hmaps
  obtain ⟨hqSzero, _⟩ :=
    finiteModel_commonDenominator_transverse hA htau qS qB hcommon
  rw [← hqS, hqSzero, map_zero]

instance finitePositiveBoundarySubspace_finiteDimensional
    (A : ℝ[X]) (tau : ℝ) :
    FiniteDimensional ℂ (finitePositiveBoundarySubspace A tau) := by
  change FiniteDimensional ℂ
    (LinearMap.range (finitePositiveModelBoundaryLpLinearMap A tau))
  infer_instance

instance finiteNegativeBoundarySubspace_finiteDimensional
    (A : ℝ[X]) (tau : ℝ) :
    FiniteDimensional ℂ (finiteNegativeBoundarySubspace A tau) := by
  change FiniteDimensional ℂ
    (LinearMap.range (finiteNegativeModelBoundaryLpLinearMap A tau))
  infer_instance

theorem finitePositiveBoundarySubspace_isClosed
    (A : ℝ[X]) (tau : ℝ) :
    IsClosed (finitePositiveBoundarySubspace A tau :
      Set (Lp ℂ 2 (volume : Measure ℝ))) :=
  Submodule.closed_of_finiteDimensional _

theorem finiteNegativeBoundarySubspace_isClosed
    (A : ℝ[X]) (tau : ℝ) :
    IsClosed (finiteNegativeBoundarySubspace A tau :
      Set (Lp ℂ 2 (volume : Measure ℝ))) :=
  Submodule.closed_of_finiteDimensional _

/-- The actual Hardy-boundary cross angle: include the negative rational
model into `L²(ℝ, ℂ)` and orthogonally project onto the positive model. -/
noncomputable def finiteHardyCrossAngle (A : ℝ[X]) (tau : ℝ) :
    finiteNegativeBoundarySubspace A tau →L[ℂ]
      finitePositiveBoundarySubspace A tau :=
  (finitePositiveBoundarySubspace A tau).orthogonalProjectionOnto.comp
    (finiteNegativeBoundarySubspace A tau).subtypeL

theorem finiteHardyCrossAngle_norm_apply_le
    (A : ℝ[X]) (tau : ℝ)
    (n : finiteNegativeBoundarySubspace A tau) :
    ‖finiteHardyCrossAngle A tau n‖ ≤ ‖n‖ := by
  exact (finitePositiveBoundarySubspace A tau).norm_orthogonalProjectionOnto_apply_le
    (n : Lp ℂ 2 (volume : Measure ℝ))

theorem finiteHardyCrossAngle_pointwiseStrictContraction
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {n : finiteNegativeBoundarySubspace A tau} (hn : n ≠ 0) :
    ‖finiteHardyCrossAngle A tau n‖ < ‖n‖ := by
  refine lt_of_le_of_ne (finiteHardyCrossAngle_norm_apply_le A tau n) ?_
  intro hnorm
  change
    ‖(finitePositiveBoundarySubspace A tau).orthogonalProjectionOnto
        (n : Lp ℂ 2 (volume : Measure ℝ))‖ =
      ‖(n : Lp ℂ 2 (volume : Measure ℝ))‖ at hnorm
  have hstar :
      ‖(finitePositiveBoundarySubspace A tau).starProjection
          (n : Lp ℂ 2 (volume : Measure ℝ))‖ =
        ‖(n : Lp ℂ 2 (volume : Measure ℝ))‖ := by
    simpa only [Submodule.starProjection_apply, Submodule.norm_coe] using hnorm
  have hnPositive : (n : Lp ℂ 2 (volume : Measure ℝ)) ∈
      finitePositiveBoundarySubspace A tau :=
    ((finitePositiveBoundarySubspace A tau).mem_iff_norm_starProjection
      (n : Lp ℂ 2 (volume : Measure ℝ))).2 hstar
  have hnAmbient : (n : Lp ℂ 2 (volume : Measure ℝ)) = 0 :=
    Submodule.disjoint_def.mp (finiteBoundarySubspaces_disjoint hA htau)
      (n : Lp ℂ 2 (volume : Measure ℝ)) hnPositive n.property
  apply hn
  exact Subtype.ext hnAmbient

end
end RiemannGaussian
