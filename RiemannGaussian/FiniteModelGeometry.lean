import RiemannGaussian.FiniteModelSpace
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Algebraic geometry of the two finite model spaces

This file embeds the two algebraic model spaces into a common numerator
space.  It proves all coprimality and transversality statements needed before
an inner product is introduced.  It also packages the relevant Sylvester map
as a genuine linear equivalence, giving the finite algebraic analogue of the
model-space decomposition `K_S ⊕ S K_B`.

No Hardy-space orthogonality is asserted here; that remains a separate
analytic identification.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

/-- A zero of the reflected upper root factor lies strictly in the lower
half-plane. -/
theorem conjugate_upperRootFactor_eval_zero_im_neg
    (p : ℂ[X]) {z : ℂ}
    (hz : (conjugatePolynomial (upperRootFactor p)).eval z = 0) :
    z.im < 0 := by
  have hzmem : z ∈ (conjugatePolynomial (upperRootFactor p)).roots :=
    (mem_roots (conjugatePolynomial_ne_zero
      (upperRootFactor_ne_zero p))).mpr hz
  rw [conjugatePolynomial_roots, Multiset.mem_map] at hzmem
  obtain ⟨w, hw, rfl⟩ := hzmem
  rw [upperRootFactor_roots, Multiset.mem_filter] at hw
  rw [Complex.conj_im]
  linarith

/-- A zero of the reflected lower root factor lies strictly in the upper
half-plane. -/
theorem conjugate_lowerRootFactor_eval_zero_im_pos
    (p : ℂ[X]) {z : ℂ}
    (hz : (conjugatePolynomial (lowerRootFactor p)).eval z = 0) :
    0 < z.im := by
  have hzmem : z ∈ (conjugatePolynomial (lowerRootFactor p)).roots :=
    (mem_roots (conjugatePolynomial_ne_zero
      (lowerRootFactor_ne_zero p))).mpr hz
  rw [conjugatePolynomial_roots, Multiset.mem_map] at hzmem
  obtain ⟨w, hw, rfl⟩ := hzmem
  rw [lowerRootFactor_roots, Multiset.mem_filter] at hw
  rw [Complex.conj_im]
  linarith

/-- The two reflected open-half-plane root factors are coprime. -/
theorem conjugate_rootFactors_isCoprime (p : ℂ[X]) :
    IsCoprime (conjugatePolynomial (upperRootFactor p))
      (conjugatePolynomial (lowerRootFactor p)) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ
    (conjugatePolynomial (upperRootFactor p))
    (conjugatePolynomial (lowerRootFactor p))).2
  intro z
  simp only [aeval_def]
  by_cases hD :
      (conjugatePolynomial (upperRootFactor p)).eval z ≠ 0
  · exact Or.inl hD
  · right
    intro hV
    have hzneg := conjugate_upperRootFactor_eval_zero_im_neg p
      (not_ne_iff.mp hD)
    have hzpos := conjugate_lowerRootFactor_eval_zero_im_pos p hV
    linarith

/-- The Blaschke denominator and residual-inner denominator are coprime in
the finite homotopy.  A common zero would be a common zero of `E_tau` and its
reflection. -/
theorem finiteModelDenominators_isCoprime
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    IsCoprime
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau)))
      (lowerRootFactor (finiteEPolynomial A tau)) := by
  let E := finiteEPolynomial A tau
  let Q := finiteESharpPolynomial A tau
  let U := upperRootFactor E
  let D := conjugatePolynomial U
  let L := lowerRootFactor E
  let V := conjugatePolynomial L
  let c := E.leadingCoeff
  have hE : E = C c * U * L := by
    simpa [E, U, L, c] using finiteEPolynomial_eq_rootFactors hA htau
  have hQ : Q = C c * D * V := by
    simpa [E, Q, U, D, L, V, c] using
      finiteESharpPolynomial_eq_rootFactors hA htau
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ
    D L).2
  intro z
  change D.eval z ≠ 0 ∨ L.eval z ≠ 0
  by_cases hD : D.eval z ≠ 0
  · exact Or.inl hD
  · right
    intro hL
    have hQz : Q.eval z = 0 := by
      rw [hQ]
      simp [not_ne_iff.mp hD]
    have hEz : E.eval z = 0 := by
      rw [hE]
      simp [hL]
    rcases finiteEPolynomial_not_both_roots hA htau z with hne | hne
    · exact hne (by simpa [E] using hEz)
    · exact hne (by simpa [Q] using hQz)

/-- The residual denominator and residual numerator are coprime. -/
theorem finiteResidualFactors_isCoprime
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    IsCoprime
      (lowerRootFactor (finiteEPolynomial A tau))
      (conjugatePolynomial
        (lowerRootFactor (finiteEPolynomial A tau))) := by
  let E := finiteEPolynomial A tau
  let Q := finiteESharpPolynomial A tau
  let U := upperRootFactor E
  let D := conjugatePolynomial U
  let L := lowerRootFactor E
  let V := conjugatePolynomial L
  let c := E.leadingCoeff
  have hE : E = C c * U * L := by
    simpa [E, U, L, c] using finiteEPolynomial_eq_rootFactors hA htau
  have hQ : Q = C c * D * V := by
    simpa [E, Q, U, D, L, V, c] using
      finiteESharpPolynomial_eq_rootFactors hA htau
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ
    L V).2
  intro z
  change L.eval z ≠ 0 ∨ V.eval z ≠ 0
  by_cases hL : L.eval z ≠ 0
  · exact Or.inl hL
  · right
    intro hV
    have hEz : E.eval z = 0 := by
      rw [hE]
      simp [not_ne_iff.mp hL]
    have hQz : Q.eval z = 0 := by
      rw [hQ]
      simp [hV]
    rcases finiteEPolynomial_not_both_roots hA htau z with hne | hne
    · exact hne (by simpa [E] using hEz)
    · exact hne (by simpa [Q] using hQz)

/-- A generic Sylvester map for two coprime complex polynomials is injective.
The proof uses Mathlib's checked adjugate identity and the nonzero resultant. -/
theorem sylvesterMap_injective_of_isCoprime
    {f g : ℂ[X]} (hfg : IsCoprime f g) :
    Function.Injective
      (Polynomial.sylvesterMap f g
        (m := f.natDegree) (n := g.natDegree) le_rfl le_rfl) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hadj := LinearMap.congr_fun
    (Polynomial.adjSylvester_comp_sylveserMap
      (m := f.natDegree) (n := g.natDegree) f g le_rfl le_rfl) x
  have hres : f.resultant g • x = 0 := by
    simpa [hx] using hadj.symm
  exact (smul_eq_zero.mp hres).resolve_left
    (Polynomial.resultant_ne_zero f g hfg)

/-- The Sylvester map of two coprime complex polynomials as a linear
equivalence between coefficient pairs and the full numerator space. -/
noncomputable def sylvesterLinearEquivOfIsCoprime
    (f g : ℂ[X]) (hfg : IsCoprime f g) :
    (Polynomial.degreeLT ℂ f.natDegree ×
        Polynomial.degreeLT ℂ g.natDegree) ≃ₗ[ℂ]
      Polynomial.degreeLT ℂ (f.natDegree + g.natDegree) :=
  (Polynomial.sylvesterMap f g le_rfl le_rfl).linearEquivOfInjective
    (sylvesterMap_injective_of_isCoprime hfg)
    (by simp [Module.finrank_prod,
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℂ f.natDegree),
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℂ g.natDegree),
      Module.finrank_eq_card_basis
        (Polynomial.degreeLT.basis ℂ (f.natDegree + g.natDegree))])

/-- The common numerator space for the decomposition `K_S ⊕ S K_B`. -/
abbrev finiteCommonNumeratorSpace (A : ℝ[X]) (tau : ℝ) :=
  Polynomial.degreeLT ℂ
    ((conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))).natDegree +
      (conjugatePolynomial
        (lowerRootFactor (finiteEPolynomial A tau))).natDegree)

/-- Exact finite Sylvester decomposition.  Its first input is the Blaschke
coordinate and its second input has the residual-inner dimension; the
underlying polynomial is `D * q_S + V * q_B`. -/
noncomputable def finiteModelSylvesterLinearEquiv
    (A : ℝ[X]) (tau : ℝ) :
    (finiteNegativeModelSpace A tau ×
        finiteModelSpace
          (conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau)))) ≃ₗ[ℂ]
      finiteCommonNumeratorSpace A tau :=
  sylvesterLinearEquivOfIsCoprime
    (conjugatePolynomial
      (upperRootFactor (finiteEPolynomial A tau)))
    (conjugatePolynomial
      (lowerRootFactor (finiteEPolynomial A tau)))
    (conjugate_rootFactors_isCoprime (finiteEPolynomial A tau))

/-- Polynomial formula realized by the finite Sylvester equivalence. -/
@[simp] theorem finiteModelSylvesterLinearEquiv_apply_coe
    (A : ℝ[X]) (tau : ℝ)
    (q : finiteNegativeModelSpace A tau ×
      finiteModelSpace
        (conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau)))) :
    ((finiteModelSylvesterLinearEquiv A tau q :
        finiteCommonNumeratorSpace A tau) : ℂ[X]) =
      conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)) * (q.2 : ℂ[X]) +
        conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau)) * (q.1 : ℂ[X]) := by
  rfl

/-- The common-denominator copies of `K_S` and `K_B` have trivial
intersection. -/
theorem finiteModel_commonDenominator_transverse
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (qS : finitePositiveModelSpace A tau)
    (qB : finiteNegativeModelSpace A tau)
    (hcommon :
      (qS : ℂ[X]) *
          conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)) =
        (qB : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau)) :
    qS = 0 ∧ qB = 0 := by
  let D := conjugatePolynomial
    (upperRootFactor (finiteEPolynomial A tau))
  let L := lowerRootFactor (finiteEPolynomial A tau)
  have hcop : IsCoprime D L := by
    simpa [D, L] using finiteModelDenominators_isCoprime hA htau
  have hDdvd : D ∣ (qB : ℂ[X]) * L := by
    refine ⟨(qS : ℂ[X]), ?_⟩
    simpa [D, L, mul_comm] using hcommon.symm
  have hDdvdqB : D ∣ (qB : ℂ[X]) :=
    hcop.dvd_of_dvd_mul_right hDdvd
  have hqBdegreeNat :
      degree (qB : ℂ[X]) < (D.natDegree : WithBot ℕ) := by
    simpa [finiteNegativeModelSpace, finiteModelSpace, D] using
      (Polynomial.mem_degreeLT.mp qB.property)
  have hqBdegree : degree (qB : ℂ[X]) < degree D := by
    calc
      degree (qB : ℂ[X]) < (D.natDegree : WithBot ℕ) := hqBdegreeNat
      _ = degree D := (degree_eq_natDegree
        (conjugatePolynomial_ne_zero
          (upperRootFactor_ne_zero (finiteEPolynomial A tau)))).symm
  have hqBpoly : (qB : ℂ[X]) = 0 :=
    eq_zero_of_dvd_of_degree_lt hDdvdqB hqBdegree
  have hqB : qB = 0 := Subtype.ext hqBpoly
  have hqSpoly : (qS : ℂ[X]) = 0 := by
    have hmul : (qS : ℂ[X]) * D = 0 := by
      simpa [D, L, hqBpoly] using hcommon
    exact (mul_eq_zero.mp hmul).resolve_right
      (conjugatePolynomial_ne_zero
        (upperRootFactor_ne_zero (finiteEPolynomial A tau)))
  exact ⟨Subtype.ext hqSpoly, hqB⟩

/-- Under the natural degree inequality, the Blaschke copy is also
transverse to the algebraic complement `S K_B`.  This is the polynomial
input needed for injectivity of the future cross-angle projection. -/
theorem finiteNegative_residualMultiple_transverse
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (hdegree :
      (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau))).natDegree ≤
        (lowerRootFactor (finiteEPolynomial A tau)).natDegree)
    (q r : finiteNegativeModelSpace A tau)
    (hcommon :
      (q : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau) =
        (r : ℂ[X]) *
          conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau))) :
    q = 0 ∧ r = 0 := by
  let D := conjugatePolynomial
    (upperRootFactor (finiteEPolynomial A tau))
  let L := lowerRootFactor (finiteEPolynomial A tau)
  let V := conjugatePolynomial L
  have hcop : IsCoprime L V := by
    simpa [L, V] using finiteResidualFactors_isCoprime hA htau
  have hLdvd : L ∣ (r : ℂ[X]) * V := by
    refine ⟨(q : ℂ[X]), ?_⟩
    simpa [L, V, mul_comm] using hcommon.symm
  have hLdvdr : L ∣ (r : ℂ[X]) :=
    hcop.dvd_of_dvd_mul_right hLdvd
  have hrdegree : degree (r : ℂ[X]) < degree L := by
    have hrdegreeD :
        degree (r : ℂ[X]) < (D.natDegree : WithBot ℕ) := by
      simpa [finiteNegativeModelSpace, finiteModelSpace, D] using
        (Polynomial.mem_degreeLT.mp r.property)
    calc
      degree (r : ℂ[X]) < (D.natDegree : WithBot ℕ) := hrdegreeD
      _ ≤ (L.natDegree : WithBot ℕ) := by
        exact WithBot.coe_le_coe.mpr (by simpa [D, L] using hdegree)
      _ = degree L := by
        exact (degree_eq_natDegree (lowerRootFactor_ne_zero
          (finiteEPolynomial A tau))).symm
  have hrpoly : (r : ℂ[X]) = 0 :=
    eq_zero_of_dvd_of_degree_lt hLdvdr hrdegree
  have hr : r = 0 := Subtype.ext hrpoly
  have hqpoly : (q : ℂ[X]) = 0 := by
    have hmul : (q : ℂ[X]) * L = 0 := by
      simpa [L, V, hrpoly] using hcommon
    exact (mul_eq_zero.mp hmul).resolve_right
      (lowerRootFactor_ne_zero (finiteEPolynomial A tau))
  exact ⟨Subtype.ext hqpoly, hr⟩

end

end RiemannGaussian
