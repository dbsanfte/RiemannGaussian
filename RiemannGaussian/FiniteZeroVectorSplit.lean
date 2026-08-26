import RiemannGaussian.FiniteKernelDecomposition

/-!
# Zero-vector split in the finite model

At a zero `gamma` of the original polynomial, this file represents
`A(z) / (z - gamma)` by a literal polynomial quotient.  It then proves the
normalized pointwise identity splitting the transformed zero vector into its
residual-inner and Blaschke difference quotients.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

/-- The polynomial obtained by removing the linear factor at `gamma`. -/
def finiteZeroQuotientPolynomial (A : ℝ[X]) (gamma : ℂ) : ℂ[X] :=
  A.map Complex.ofRealHom / (X - C gamma)

/-- At a complex zero of `A`, the quotient reconstructs `A` exactly. -/
theorem X_sub_C_mul_finiteZeroQuotientPolynomial
    (A : ℝ[X]) {gamma : ℂ}
    (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    (X - C gamma) * finiteZeroQuotientPolynomial A gamma =
      A.map Complex.ofRealHom := by
  apply Polynomial.IsRoot.mul_div_eq
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  exact hgamma

/-- Evaluation of the quotient satisfies the expected divided-difference
identity, including at the polynomial level before any cancellation. -/
theorem sub_mul_finiteZeroQuotientPolynomial_eval
    (A : ℝ[X]) {gamma z : ℂ}
    (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    (z - gamma) * (finiteZeroQuotientPolynomial A gamma).eval z =
      A.eval₂ Complex.ofRealHom z := by
  have h := congrArg (Polynomial.eval z)
    (X_sub_C_mul_finiteZeroQuotientPolynomial A hgamma)
  simpa [Polynomial.eval_map] using h

/-- Exact pointwise quotient formula away from the removed zero. -/
theorem finiteZeroQuotientPolynomial_eval_eq_div
    (A : ℝ[X]) {gamma z : ℂ}
    (hgamma : A.eval₂ Complex.ofRealHom gamma = 0)
    (hzgamma : z ≠ gamma) :
    (finiteZeroQuotientPolynomial A gamma).eval z =
      A.eval₂ Complex.ofRealHom z / (z - gamma) := by
  apply (eq_div_iff (sub_ne_zero.mpr hzgamma)).mpr
  simpa [mul_comm] using
    sub_mul_finiteZeroQuotientPolynomial_eval A hgamma

/-- At its removed root, the quotient evaluates to the derivative. -/
theorem finiteZeroQuotientPolynomial_eval_self
    (A : ℝ[X]) {gamma : ℂ}
    (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    (finiteZeroQuotientPolynomial A gamma).eval gamma =
      A.derivative.eval₂ Complex.ofRealHom gamma := by
  have hderiv := congrArg Polynomial.derivative
    (X_sub_C_mul_finiteZeroQuotientPolynomial A hgamma)
  have heval := congrArg (Polynomial.eval gamma) hderiv
  simpa [Polynomial.derivative_map, Polynomial.eval_map] using heval

/-- Removing one root leaves a polynomial that vanishes at every other
root. -/
theorem finiteZeroQuotientPolynomial_eval_eq_zero_of_ne
    (A : ℝ[X]) {gamma delta : ℂ}
    (hgamma : A.eval₂ Complex.ofRealHom gamma = 0)
    (hdelta : A.eval₂ Complex.ofRealHom delta = 0)
    (hne : delta ≠ gamma) :
    (finiteZeroQuotientPolynomial A gamma).eval delta = 0 := by
  have hfactor := sub_mul_finiteZeroQuotientPolynomial_eval
    A (z := delta) hgamma
  rw [hdelta] at hfactor
  exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)

/-- The normalization `i / sqrt pi` used for finite zero vectors. -/
def finiteZeroVectorScale : ℂ :=
  Complex.I / (Real.sqrt Real.pi : ℂ)

/-- Half of the zero-vector normalization. -/
def finiteZeroVectorHalfScale : ℂ :=
  (2 : ℂ)⁻¹ * finiteZeroVectorScale

theorem finiteZeroVectorHalfScale_eq :
    finiteZeroVectorHalfScale =
      Complex.I / (2 * (Real.sqrt Real.pi : ℂ)) := by
  rw [finiteZeroVectorHalfScale, finiteZeroVectorScale]
  field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos]

/-- The normalized finite zero vector, using the genuine polynomial quotient
to remove the apparent singularity at `gamma`. -/
def finiteZeroVectorValue
    (A : ℝ[X]) (tau : ℝ) (gamma z : ℂ) : ℂ :=
  finiteZeroVectorScale *
    ((finiteZeroQuotientPolynomial A gamma).eval z /
      (finiteEPolynomial A tau).eval z)

/-- Candidate residual-inner component of the transformed zero vector. -/
def finitePositiveSplitValue
    (A : ℝ[X]) (tau : ℝ) (gamma z : ℂ) : ℂ :=
  finiteZeroVectorHalfScale *
    ((finiteInnerValue A tau z - finiteInnerValue A tau gamma) /
      (z - gamma))

/-- Candidate Blaschke component, with the sign convention for
`positive - negative`. -/
def finiteNegativeSplitValue
    (A : ℝ[X]) (tau : ℝ) (gamma z : ℂ) : ℂ :=
  -finiteZeroVectorHalfScale *
    ((finiteBlaschkeValue A tau z - finiteBlaschkeValue A tau gamma) /
      (z - gamma))

/-- The defining polynomials satisfy `E_tau + E_tau^sharp = 2 A` at every
complex point. -/
theorem finiteE_add_finiteESharp_eval
    (A : ℝ[X]) (tau : ℝ) (z : ℂ) :
    (finiteEPolynomial A tau).eval z +
        (finiteESharpPolynomial A tau).eval z =
      2 * A.eval₂ Complex.ofRealHom z := by
  rw [finiteEPolynomial_eval, finiteESharpPolynomial_eval]
  ring

/-- The analytic heart of the zero-vector split, before inserting the common
normalization. -/
theorem finiteBlaschke_mul_zeroQuotient_div_E
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma z : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0)
    (hz : 0 < z.im) (hEz : (finiteEPolynomial A tau).eval z ≠ 0)
    (hzgamma : z ≠ gamma) :
    finiteBlaschkeValue A tau z *
        ((finiteZeroQuotientPolynomial A gamma).eval z /
          (finiteEPolynomial A tau).eval z) =
      (finiteBlaschkeValue A tau z + finiteInnerValue A tau z) /
        (2 * (z - gamma)) := by
  let b := finiteBlaschkeValue A tau z
  let s := finiteInnerValue A tau z
  let e := (finiteEPolynomial A tau).eval z
  let q := (finiteESharpPolynomial A tau).eval z
  let a := A.eval₂ Complex.ofRealHom z
  let d := z - gamma
  let p := (finiteZeroQuotientPolynomial A gamma).eval z
  have he : e ≠ 0 := by simpa [e] using hEz
  have hd : d ≠ 0 := by simpa [d] using sub_ne_zero.mpr hzgamma
  have hcancel : b * (q / e) = s := by
    have h := finiteKreinLangerValue_cancellation_of_im_pos
      hA htau hz hEz
    change b * (q / e) = s at h
    exact h
  have hcancel_mul : b * q = s * e := by
    field_simp [he] at hcancel
    simpa [mul_comm] using hcancel
  have hsum : e + q = 2 * a := by
    simpa [e, q, a] using finiteE_add_finiteESharp_eval A tau z
  have hquot : d * p = a := by
    simpa [d, p, a] using
      sub_mul_finiteZeroQuotientPolynomial_eval A hgamma
  change b * (p / e) = (b + s) / (2 * d)
  field_simp [he, hd]
  calc
    b * p * 2 * d = b * (2 * (d * p)) := by ring
    _ = b * (2 * a) := by rw [hquot]
    _ = b * (e + q) := by rw [hsum]
    _ = b * e + b * q := by ring
    _ = b * e + s * e := by rw [hcancel_mul]
    _ = (b + s) * e := by ring
    _ = e * (b + s) := by ring

/-- Exact normalized zero-vector split:
`B F_gamma = u_gamma - n_gamma`. -/
theorem finiteZeroVector_split
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma z : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0)
    (hz : 0 < z.im) (hEz : (finiteEPolynomial A tau).eval z ≠ 0)
    (hzgamma : z ≠ gamma) :
    finiteBlaschkeValue A tau z * finiteZeroVectorValue A tau gamma z =
      finitePositiveSplitValue A tau gamma z -
        finiteNegativeSplitValue A tau gamma z := by
  let b := finiteBlaschkeValue A tau z
  let s := finiteInnerValue A tau z
  let bg := finiteBlaschkeValue A tau gamma
  let sg := finiteInnerValue A tau gamma
  let e := (finiteEPolynomial A tau).eval z
  let p := (finiteZeroQuotientPolynomial A gamma).eval z
  let d := z - gamma
  have hd : d ≠ 0 := by simpa [d] using sub_ne_zero.mpr hzgamma
  have hmain : b * (p / e) = (b + s) / (2 * d) := by
    simpa [b, s, e, p, d] using
      finiteBlaschke_mul_zeroQuotient_div_E
        hA htau hgamma hz hEz hzgamma
  have hroot : sg = -bg := by
    simpa [sg, bg] using
      finiteInnerValue_eq_neg_finiteBlaschkeValue_at_root
        hA htau hgamma
  rw [finiteZeroVectorValue]
  change b * (finiteZeroVectorScale * (p / e)) = _
  calc
    b * (finiteZeroVectorScale * (p / e)) =
        finiteZeroVectorScale * (b * (p / e)) := by ring
    _ = finiteZeroVectorScale * ((b + s) / (2 * d)) := by rw [hmain]
    _ = finitePositiveSplitValue A tau gamma z -
        finiteNegativeSplitValue A tau gamma z := by
      rw [finitePositiveSplitValue, finiteNegativeSplitValue]
      change finiteZeroVectorScale * ((b + s) / (2 * d)) =
        finiteZeroVectorHalfScale * ((s - sg) / d) -
          (-finiteZeroVectorHalfScale * ((b - bg) / d))
      rw [hroot, finiteZeroVectorHalfScale]
      field_simp [hd]
      ring

/-- The finite set of all complex roots of the real polynomial `A`. -/
def finiteComplexRootFinset (A : ℝ[X]) : Finset ℂ :=
  (A.aroots ℂ).toFinset

/-- Membership in the finite complex root set gives the required `eval₂`
root equation. -/
theorem finiteComplexRoot_eval_zero
    (A : ℝ[X]) (gamma : ↑(finiteComplexRootFinset A)) :
    A.eval₂ Complex.ofRealHom gamma = 0 := by
  have hmem : (gamma : ℂ) ∈ A.aroots ℂ :=
    Multiset.mem_toFinset.mp gamma.property
  have hroot := (Polynomial.mem_aroots.mp hmem).2
  rw [aeval_def] at hroot
  have hhom : algebraMap ℝ ℂ = Complex.ofRealHom := by
    ext x
    rfl
  rwa [hhom] at hroot

/-- A separable real polynomial has exactly `natDegree A` distinct complex
roots in the algebraic closure `ℂ`. -/
theorem finiteComplexRootFinset_card
    {A : ℝ[X]} (hA : A.Separable) :
    (finiteComplexRootFinset A).card = A.natDegree := by
  rw [finiteComplexRootFinset,
    Multiset.toFinset_card_of_nodup]
  · exact IsAlgClosed.card_aroots_eq_natDegree
  · rw [Polynomial.aroots_def]
    exact nodup_roots hA.map

/-- For separable `A`, its quotient polynomials indexed by all complex roots
are linearly independent.  This is the finite completeness input behind the
zero-vector family. -/
theorem finiteZeroQuotientPolynomial_linearIndependent
    {A : ℝ[X]} (hA : A.Separable) :
    LinearIndependent ℂ
      (fun gamma : ↑(finiteComplexRootFinset A) =>
        finiteZeroQuotientPolynomial A gamma) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have heval := congrArg (Polynomial.eval (i : ℂ)) hsum
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul,
    Polynomial.eval_zero, smul_eq_mul] at heval
  have hsingle :
      g i * (finiteZeroQuotientPolynomial A i).eval (i : ℂ) = 0 := by
    calc
      g i * (finiteZeroQuotientPolynomial A i).eval (i : ℂ) =
          ∑ j, g j * (finiteZeroQuotientPolynomial A j).eval (i : ℂ) := by
        symm
        apply Finset.sum_eq_single i
        · intro j _ hji
          have hne : (i : ℂ) ≠ (j : ℂ) := by
            intro hij
            apply hji
            exact Subtype.ext hij.symm
          rw [finiteZeroQuotientPolynomial_eval_eq_zero_of_ne A
            (finiteComplexRoot_eval_zero A j)
            (finiteComplexRoot_eval_zero A i) hne, mul_zero]
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      _ = 0 := heval
  have hquot_ne :
      (finiteZeroQuotientPolynomial A i).eval (i : ℂ) ≠ 0 := by
    rw [finiteZeroQuotientPolynomial_eval_self A
      (finiteComplexRoot_eval_zero A i)]
    exact hA.eval₂_derivative_ne_zero Complex.ofRealHom
      (finiteComplexRoot_eval_zero A i)
  exact (mul_eq_zero.mp hsingle).resolve_right hquot_ne

end

end RiemannGaussian
