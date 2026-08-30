import RiemannGaussian.EtaEnergyFiniteWindowHeatMatrix
import RiemannGaussian.EtaEndpointLogHilbert

/-!
# The Gaussian proper-time route to the eta Hilbert kernel

This module turns the Gaussian heat parameter into the reciprocal frequency
kernel used by the checked Montgomery--Vaughan inequality.  For a nonzero real
gap `Delta`, Lean proves both the direct odd proper-time identity

`integral_0^infinity Delta * exp(-u * Delta^2) du = Delta⁻¹`

and the equivalent square-root proper-time identity

`(2 / sqrt pi) * sign(Delta) * integral_0^infinity exp(-t^2 Delta^2) dt
    = Delta⁻¹`.

The direct form retains the sign and oddness of the frequency difference.
The square-root parameter `u = t^2` supplies an equivalent representation
without placing a singular `u^(-1/2)` weight in the formal integral.  Zero
gaps are explicitly assigned the value zero before integration; the
development never treats the nonintegrable diagonal Gaussian as an ordinary
improper integral.

The identity is lifted entrywise to arbitrary finite matrices.  It proves
that an oriented integral of the Gaussian Schur-compression semigroup is
exactly Schur multiplication by the off-diagonal reciprocal-gap matrix.  For
the eta cutoff nodes `log(2N+1)`, a new separation proof then applies the
already checked Montgomery--Vaughan theorem with constant `26` directly to
this heat integral.  Finally, the transform is instantiated on the genuine
eta zero-window matrix work and its leading/remainder decomposition.

This is an exact finite transform and inequality.  It does not estimate the
actual eta leading-current coefficients, sum over spectral windows, or infer
a zero-location consequence.
-/

open Complex MeasureTheory Set
open scoped Classical ComplexConjugate Matrix Real

namespace RiemannGaussian

noncomputable section

/-! ## Scalar square-root heat transform -/

/-- The oriented square-root heat integral of a nonzero real gap is its
reciprocal.  The nonzero hypothesis is essential: the unweighted diagonal
Gaussian is not integrable on the positive half-line. -/
theorem gaussianSqrtHeatIntegral_sign_eq_inv {gap : ℝ} (hgap : gap ≠ 0) :
    (2 / Real.sqrt Real.pi) * (SignType.sign gap : ℝ) *
        (∫ t : ℝ in Set.Ioi 0,
          Real.exp (-(t ^ 2) * gap ^ 2)) = gap⁻¹ := by
  rw [show (fun t : ℝ => Real.exp (-(t ^ 2) * gap ^ 2)) =
      (fun t : ℝ => Real.exp (-(gap ^ 2) * t ^ 2)) by
        funext t
        congr 1
        ring]
  rw [integral_gaussian_Ioi]
  rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq_eq_abs]
  have hsqrt : Real.sqrt Real.pi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have habs : |gap| ≠ 0 := abs_ne_zero.mpr hgap
  field_simp
  exact sign_mul_self gap

/-- Complex scalar multiples pass through the oriented square-root heat
integral, producing multiplication by the reciprocal real gap. -/
theorem gaussianSqrtHeatIntegral_sign_mul_eq_inv_mul
    {gap : ℝ} (hgap : gap ≠ 0) (a : ℂ) :
    (((2 / Real.sqrt Real.pi) *
        (SignType.sign gap : ℝ) : ℝ) : ℂ) *
        (∫ t : ℝ in Set.Ioi 0,
          ((Real.exp (-(t ^ 2) * gap ^ 2) : ℝ) : ℂ) * a) =
      ((gap⁻¹ : ℝ) : ℂ) * a := by
  rw [integral_mul_const, integral_complex_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, gaussianSqrtHeatIntegral_sign_eq_inv hgap]

/-! ## Direct odd proper-time transform -/

/-- The direct odd heat kernel has reciprocal-gap integral:
`∫₀∞ gap * exp (-u * gap²) du = gap⁻¹` for every nonzero real gap. -/
theorem gaussianOddHeatIntegral_eq_inv {gap : ℝ} (hgap : gap ≠ 0) :
    (∫ u : ℝ in Set.Ioi 0,
      gap * Real.exp (-u * gap ^ 2)) = gap⁻¹ := by
  rw [show (fun u : ℝ ↦ gap * Real.exp (-u * gap ^ 2)) =
      (fun u : ℝ ↦ gap * Real.exp ((-gap ^ 2) * u)) by
        funext u
        congr 2
        ring]
  rw [integral_const_mul,
    integral_exp_mul_Ioi (a := -gap ^ 2)
      (neg_neg_of_pos (sq_pos_of_ne_zero hgap)) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- Complex scalar multiples pass through the direct odd proper-time
integral. -/
theorem gaussianOddHeatIntegral_mul_eq_inv_mul
    {gap : ℝ} (hgap : gap ≠ 0) (a : ℂ) :
    (∫ u : ℝ in Set.Ioi 0,
      (((gap : ℝ) : ℂ) *
        ((Real.exp (-u * gap ^ 2) : ℝ) : ℂ)) * a) =
      (((gap⁻¹ : ℝ) : ℂ) * a) := by
  simp_rw [← Complex.ofReal_mul]
  rw [integral_mul_const, integral_complex_ofReal,
    gaussianOddHeatIntegral_eq_inv hgap]

/-- Direct odd proper-time integral of one Gaussian kernel entry.  Equal
frequency nodes are explicitly set to zero before integration. -/
def finiteGaussianOddHeatKernelIntegral {d : Type*}
    (frequency : d → ℝ) (i j : d) : ℂ :=
  if frequency i = frequency j then 0
  else
    ∫ u : ℝ in Set.Ioi 0,
      (((frequency i - frequency j : ℝ) : ℂ) *
        finiteGaussianProperTimeKernelMatrix frequency u i j)

/-- The direct odd heat-kernel integral is exactly the off-diagonal
reciprocal frequency gap. -/
theorem finiteGaussianOddHeatKernelIntegral_eq
    {d : Type*} (frequency : d → ℝ) (i j : d) :
    finiteGaussianOddHeatKernelIntegral frequency i j =
      if frequency i = frequency j then 0
      else (((frequency i - frequency j)⁻¹ : ℝ) : ℂ) := by
  unfold finiteGaussianOddHeatKernelIntegral
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · rw [if_neg hfreq, if_neg hfreq]
    unfold finiteGaussianProperTimeKernelMatrix
    simpa using gaussianOddHeatIntegral_mul_eq_inv_mul
      (sub_ne_zero.mpr hfreq) 1

/-- The direct odd heat kernel reverses sign under exchange of its frequency
indices.  This is the sign information lost by the unoriented Gaussian Gram
kernel. -/
theorem finiteGaussianOddHeatKernelIntegral_swap
    {d : Type*} (frequency : d → ℝ) (i j : d) :
    finiteGaussianOddHeatKernelIntegral frequency j i =
      -finiteGaussianOddHeatKernelIntegral frequency i j := by
  rw [finiteGaussianOddHeatKernelIntegral_eq,
    finiteGaussianOddHeatKernelIntegral_eq]
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · have hrev : frequency j ≠ frequency i := Ne.symm hfreq
    rw [if_neg hrev, if_neg hfreq]
    push_cast
    rw [show ((frequency j : ℝ) : ℂ) - ((frequency i : ℝ) : ℂ) =
        -(((frequency i : ℝ) : ℂ) - ((frequency j : ℝ) : ℂ)) by ring,
      inv_neg]

/-- Direct odd proper-time transform of a Gaussian-compressed matrix. -/
def finiteGaussianOddHeatTransform {d : Type*}
    (frequency : d → ℝ) (A : Matrix d d ℂ) : Matrix d d ℂ :=
  fun i j ↦
    if frequency i = frequency j then 0
    else
      ∫ u : ℝ in Set.Ioi 0,
        (((frequency i - frequency j : ℝ) : ℂ) *
          finiteGaussianProperTimeCompression frequency u A i j)

/-- The direct odd heat transform divides every noncoincident matrix entry
by its frequency gap. -/
theorem finiteGaussianOddHeatTransform_apply
    {d : Type*} (frequency : d → ℝ) (A : Matrix d d ℂ) (i j : d) :
    finiteGaussianOddHeatTransform frequency A i j =
      if frequency i = frequency j then 0
      else (((frequency i - frequency j)⁻¹ : ℝ) : ℂ) * A i j := by
  unfold finiteGaussianOddHeatTransform
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · rw [if_neg hfreq, if_neg hfreq]
    simp only [finiteGaussianProperTimeCompression, Matrix.hadamard_apply,
      finiteGaussianProperTimeKernelMatrix]
    simp_rw [← mul_assoc]
    exact gaussianOddHeatIntegral_mul_eq_inv_mul
      (sub_ne_zero.mpr hfreq) (A i j)

/-! ## The unintegrated odd heat trajectory -/

/-- Sign-bearing Gaussian current at one proper time.  Unlike the unoriented
heat kernel, this current retains the direction of every frequency gap.  Its
coincident-frequency entries vanish pointwise, so no diagonal singularity is
present before time integration. -/
def finiteGaussianOddHeatCurrent {d : Type*} (frequency : d → ℝ)
    (heat : ℝ) (A : Matrix d d ℂ) : Matrix d d ℂ :=
  fun i j ↦
    (((frequency i - frequency j : ℝ) : ℂ) *
      finiteGaussianProperTimeCompression frequency heat A i j)

/-- At every proper time, the odd heat current of a complex-symmetric matrix
is skew-symmetric.  Thus orientation is retained along the full heat
trajectory, not only after integration. -/
theorem finiteGaussianOddHeatCurrent_transpose_of_isSymm
    {d : Type*} (frequency : d → ℝ) (heat : ℝ)
    (A : Matrix d d ℂ) (hA : A.IsSymm) :
    (finiteGaussianOddHeatCurrent frequency heat A)ᵀ =
      -finiteGaussianOddHeatCurrent frequency heat A := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply,
    finiteGaussianOddHeatCurrent, finiteGaussianProperTimeCompression,
    Matrix.hadamard_apply, finiteGaussianProperTimeKernelMatrix]
  rw [hA.apply i j]
  rw [show (frequency j - frequency i) ^ 2 =
      (frequency i - frequency j) ^ 2 by ring]
  rw [show frequency j - frequency i =
      -(frequency i - frequency j) by ring]
  push_cast
  ring

/-- The direct reciprocal-gap transform is the entrywise positive-time
integral of the full odd heat trajectory.  This statement also covers equal
frequencies because their trajectory is identically zero. -/
theorem finiteGaussianOddHeatTransform_apply_eq_integral_current
    {d : Type*} (frequency : d → ℝ) (A : Matrix d d ℂ) (i j : d) :
    finiteGaussianOddHeatTransform frequency A i j =
      ∫ u : ℝ in Set.Ioi 0,
        finiteGaussianOddHeatCurrent frequency u A i j := by
  unfold finiteGaussianOddHeatTransform finiteGaussianOddHeatCurrent
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · rw [if_neg hfreq]

/-- Every entry of the full odd heat trajectory is genuinely integrable over
positive proper time. -/
theorem finiteGaussianOddHeatCurrent_apply_integrableOn
    {d : Type*} (frequency : d → ℝ) (A : Matrix d d ℂ) (i j : d) :
    IntegrableOn
      (fun u : ℝ ↦ finiteGaussianOddHeatCurrent frequency u A i j)
      (Set.Ioi 0) := by
  unfold finiteGaussianOddHeatCurrent
  simp only [finiteGaussianProperTimeCompression, Matrix.hadamard_apply,
    finiteGaussianProperTimeKernelMatrix]
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · have hneg : -(frequency i - frequency j) ^ 2 < 0 :=
      neg_neg_of_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hfreq))
    have hexpR := integrableOn_exp_mul_Ioi hneg 0
    have hexpC : IntegrableOn
        (fun u : ℝ ↦
          ((Real.exp ((-(frequency i - frequency j) ^ 2) * u) : ℝ) : ℂ))
        (Set.Ioi 0) := hexpR.ofReal
    have hscaled :=
      (hexpC.const_mul
        (((frequency i - frequency j : ℝ) : ℂ))).mul_const (A i j)
    change Integrable
      (fun u : ℝ ↦
        (((frequency i - frequency j : ℝ) : ℂ) *
          (((Real.exp (-u * (frequency i - frequency j) ^ 2) : ℝ) : ℂ) *
            A i j))) (volume.restrict (Set.Ioi 0))
    have hfun :
        (fun u : ℝ ↦
          (((frequency i - frequency j : ℝ) : ℂ) *
            (((Real.exp (-u * (frequency i - frequency j) ^ 2) : ℝ) : ℂ) *
              A i j))) =
          (fun u : ℝ ↦
            (((frequency i - frequency j : ℝ) : ℂ) *
              ((Real.exp (-(frequency i - frequency j) ^ 2 * u) : ℝ) : ℂ) *
              A i j)) := by
      funext u
      rw [show -u * (frequency i - frequency j) ^ 2 =
          -(frequency i - frequency j) ^ 2 * u by ring]
      ring
    rw [hfun]
    exact hscaled

/-! ## Gaussian semigroup and reciprocal-gap transform -/

/-- The finite Gaussian kernel has the exact additive proper-time semigroup
law under Hadamard multiplication. -/
theorem finiteGaussianProperTimeKernelMatrix_add
    {d : Type*} (frequency : d → ℝ) (heat₁ heat₂ : ℝ) :
    finiteGaussianProperTimeKernelMatrix frequency (heat₁ + heat₂) =
      finiteGaussianProperTimeKernelMatrix frequency heat₁ ⊙
        finiteGaussianProperTimeKernelMatrix frequency heat₂ := by
  ext i j
  simp only [finiteGaussianProperTimeKernelMatrix, Matrix.hadamard_apply,
    ← Complex.ofReal_mul, Complex.ofReal_inj]
  rw [← Real.exp_add]
  congr 1
  ring_nf

/-- Applying two Gaussian Schur compressions is compression by the sum of
their proper times. -/
theorem finiteGaussianProperTimeCompression_add
    {d : Type*} (frequency : d → ℝ) (heat₁ heat₂ : ℝ)
    (A : Matrix d d ℂ) :
    finiteGaussianProperTimeCompression frequency heat₁
        (finiteGaussianProperTimeCompression frequency heat₂ A) =
      finiteGaussianProperTimeCompression frequency (heat₁ + heat₂) A := by
  ext i j
  simp only [finiteGaussianProperTimeCompression, Matrix.hadamard_apply,
    finiteGaussianProperTimeKernelMatrix]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 1
  ring_nf

/-- Oriented square-root heat integral of one Gaussian kernel entry.  Equal
frequency nodes are explicitly set to zero, so the nonintegrable diagonal is
never evaluated as an ordinary integral. -/
def finiteGaussianOrientedSqrtHeatKernelIntegral {d : Type*}
    (frequency : d → ℝ) (i j : d) : ℂ :=
  if frequency i = frequency j then 0
  else
    (((2 / Real.sqrt Real.pi) *
        (SignType.sign (frequency i - frequency j) : ℝ) : ℝ) : ℂ) *
      ∫ t : ℝ in Set.Ioi 0,
        finiteGaussianProperTimeKernelMatrix frequency (t ^ 2) i j

/-- Every oriented heat-kernel entry is exactly the off-diagonal reciprocal
frequency gap, with zero assigned at coincident nodes. -/
theorem finiteGaussianOrientedSqrtHeatKernelIntegral_eq
    {d : Type*} (frequency : d → ℝ) (i j : d) :
    finiteGaussianOrientedSqrtHeatKernelIntegral frequency i j =
      if frequency i = frequency j then 0
      else (((frequency i - frequency j)⁻¹ : ℝ) : ℂ) := by
  unfold finiteGaussianOrientedSqrtHeatKernelIntegral
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · rw [if_neg hfreq, if_neg hfreq]
    unfold finiteGaussianProperTimeKernelMatrix
    simpa using gaussianSqrtHeatIntegral_sign_mul_eq_inv_mul
      (sub_ne_zero.mpr hfreq) 1

/-- The explicit matrix whose off-diagonal entries are reciprocal frequency
gaps and whose coincident-frequency entries are zero. -/
def finiteGaussianReciprocalGapMatrix {d : Type*}
    (frequency : d → ℝ) : Matrix d d ℂ :=
  fun i j ↦
    if frequency i = frequency j then 0
    else (((frequency i - frequency j)⁻¹ : ℝ) : ℂ)

/-- Oriented square-root proper-time transform of a Gaussian-compressed
matrix.  Coincident-frequency entries are explicitly removed before the
integral is formed. -/
def finiteGaussianOrientedSqrtHeatTransform {d : Type*}
    (frequency : d → ℝ) (A : Matrix d d ℂ) : Matrix d d ℂ :=
  fun i j ↦
    if frequency i = frequency j then 0
    else
      (((2 / Real.sqrt Real.pi) *
          (SignType.sign (frequency i - frequency j) : ℝ) : ℝ) : ℂ) *
        ∫ t : ℝ in Set.Ioi 0,
          finiteGaussianProperTimeCompression frequency (t ^ 2) A i j

/-- The oriented heat transform of a matrix entry is its value divided by
the frequency gap, away from coincident nodes. -/
theorem finiteGaussianOrientedSqrtHeatTransform_apply
    {d : Type*} (frequency : d → ℝ) (A : Matrix d d ℂ) (i j : d) :
    finiteGaussianOrientedSqrtHeatTransform frequency A i j =
      if frequency i = frequency j then 0
      else (((frequency i - frequency j)⁻¹ : ℝ) : ℂ) * A i j := by
  unfold finiteGaussianOrientedSqrtHeatTransform
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · rw [if_neg hfreq, if_neg hfreq]
    change
      (((2 / Real.sqrt Real.pi) *
          (SignType.sign (frequency i - frequency j) : ℝ) : ℝ) : ℂ) *
          (∫ t : ℝ in Set.Ioi 0,
            ((Real.exp (-(t ^ 2) *
                (frequency i - frequency j) ^ 2) : ℝ) : ℂ) * A i j) = _
    exact gaussianSqrtHeatIntegral_sign_mul_eq_inv_mul
      (sub_ne_zero.mpr hfreq) (A i j)

/-- The direct odd and oriented square-root proper-time transforms are the
same reciprocal-gap transform, entry by entry. -/
theorem finiteGaussianOddHeatTransform_eq_orientedSqrt
    {d : Type*} (frequency : d → ℝ) (A : Matrix d d ℂ) :
    finiteGaussianOddHeatTransform frequency A =
      finiteGaussianOrientedSqrtHeatTransform frequency A := by
  ext i j
  rw [finiteGaussianOddHeatTransform_apply,
    finiteGaussianOrientedSqrtHeatTransform_apply]

/-- The direct odd transform of a complex-symmetric matrix is
skew-symmetric.  Thus ordered channel information survives the heat
integration with its orientation intact. -/
theorem finiteGaussianOddHeatTransform_transpose_of_isSymm
    {d : Type*} (frequency : d → ℝ) (A : Matrix d d ℂ)
    (hA : A.IsSymm) :
    (finiteGaussianOddHeatTransform frequency A)ᵀ =
      -finiteGaussianOddHeatTransform frequency A := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply,
    finiteGaussianOddHeatTransform_apply]
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · have hrev : frequency j ≠ frequency i := Ne.symm hfreq
    rw [if_neg hrev, if_neg hfreq, hA.apply i j]
    push_cast
    rw [show ((frequency j : ℝ) : ℂ) - ((frequency i : ℝ) : ℂ) =
        -(((frequency i : ℝ) : ℂ) - ((frequency j : ℝ) : ℂ)) by ring,
      inv_neg]
    simp

/-- Matrix form of the transform: oriented square-root heat integration is
exactly Hadamard multiplication by the reciprocal-gap matrix. -/
theorem finiteGaussianOrientedSqrtHeatTransform_eq_hadamard
    {d : Type*} (frequency : d → ℝ) (A : Matrix d d ℂ) :
    finiteGaussianOrientedSqrtHeatTransform frequency A =
      finiteGaussianReciprocalGapMatrix frequency ⊙ A := by
  ext i j
  rw [finiteGaussianOrientedSqrtHeatTransform_apply]
  simp only [finiteGaussianReciprocalGapMatrix, Matrix.hadamard_apply]
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · simp [hfreq]

/-- The oriented square-root heat transform is additive. -/
theorem finiteGaussianOrientedSqrtHeatTransform_add
    {d : Type*} (frequency : d → ℝ) (A B : Matrix d d ℂ) :
    finiteGaussianOrientedSqrtHeatTransform frequency (A + B) =
      finiteGaussianOrientedSqrtHeatTransform frequency A +
        finiteGaussianOrientedSqrtHeatTransform frequency B := by
  ext i j
  simp only [finiteGaussianOrientedSqrtHeatTransform_apply, Matrix.add_apply]
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · simp [hfreq]
    ring

/-- The direct odd proper-time transform is additive. -/
theorem finiteGaussianOddHeatTransform_add
    {d : Type*} (frequency : d → ℝ) (A B : Matrix d d ℂ) :
    finiteGaussianOddHeatTransform frequency (A + B) =
      finiteGaussianOddHeatTransform frequency A +
        finiteGaussianOddHeatTransform frequency B := by
  rw [finiteGaussianOddHeatTransform_eq_orientedSqrt,
    finiteGaussianOrientedSqrtHeatTransform_add,
    finiteGaussianOddHeatTransform_eq_orientedSqrt,
    finiteGaussianOddHeatTransform_eq_orientedSqrt]

/-! ## Bilinear heat transform and the Montgomery--Vaughan form -/

/-- Finite sesquilinear sum built from the oriented square-root heat-kernel
integral. -/
def finiteGaussianOrientedSqrtHeatBilinear
    {d : Type*} [Fintype d] (frequency : d → ℝ)
    (x z : d → ℂ) : ℂ :=
  ∑ i, ∑ j,
    x i * conj (z j) *
      finiteGaussianOrientedSqrtHeatKernelIntegral frequency i j

/-- Finite sesquilinear sum built directly from the sign-bearing odd
proper-time kernel `gap * exp (-u * gap²)`. -/
def finiteGaussianOddHeatBilinear
    {d : Type*} [Fintype d] (frequency : d → ℝ)
    (x z : d → ℂ) : ℂ :=
  ∑ i, ∑ j,
    x i * conj (z j) *
      finiteGaussianOddHeatKernelIntegral frequency i j

/-- The direct odd and square-root heat bilinear forms agree exactly. -/
theorem finiteGaussianOddHeatBilinear_eq_orientedSqrt
    {d : Type*} [Fintype d] (frequency : d → ℝ)
    (x z : d → ℂ) :
    finiteGaussianOddHeatBilinear frequency x z =
      finiteGaussianOrientedSqrtHeatBilinear frequency x z := by
  unfold finiteGaussianOddHeatBilinear
    finiteGaussianOrientedSqrtHeatBilinear
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [finiteGaussianOddHeatKernelIntegral_eq,
    finiteGaussianOrientedSqrtHeatKernelIntegral_eq]

/-- The heat bilinear form is exactly the reciprocal-gap sum with all
coincident-frequency pairs explicitly removed. -/
theorem finiteGaussianOrientedSqrtHeatBilinear_eq_frequencyOffDiag
    {d : Type*} [Fintype d] (frequency : d → ℝ)
    (x z : d → ℂ) :
    finiteGaussianOrientedSqrtHeatBilinear frequency x z =
      ∑ i, ∑ j,
        if frequency i = frequency j then (0 : ℂ)
        else x i * conj (z j) /
          ((frequency i - frequency j : ℝ) : ℂ) := by
  unfold finiteGaussianOrientedSqrtHeatBilinear
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [finiteGaussianOrientedSqrtHeatKernelIntegral_eq]
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · rw [if_neg hfreq, if_neg hfreq, div_eq_mul_inv,
      ← Complex.ofReal_inv]

/-- For an injective frequency family, the heat bilinear form is literally
the off-diagonal Hilbert form used by `MVHilbert`. -/
theorem finiteGaussianOrientedSqrtHeatBilinear_eq_hilbertSum
    {d : Type*} [Fintype d] [DecidableEq d]
    (frequency : d → ℝ) (x z : d → ℂ)
    (hinj : Function.Injective frequency) :
    finiteGaussianOrientedSqrtHeatBilinear frequency x z =
      ∑ i, ∑ j, if i = j then (0 : ℂ)
        else x i * conj (z j) /
          ((frequency i - frequency j : ℝ) : ℂ) := by
  rw [finiteGaussianOrientedSqrtHeatBilinear_eq_frequencyOffDiag]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hij : i = j
  · subst j
    simp
  · have hfreq : frequency i ≠ frequency j := hinj.ne hij
    simp [hij, hfreq]

/-! ## The separated eta cutoff nodes `log(2N+1)` -/

/-- Logarithmic node of the centered eta cutoff `N`. -/
def pairedEtaCutoffLogFrequency (N : ℕ) : ℝ :=
  Real.log (((2 * N + 1 : ℕ) : ℝ))

/-- Uniform gap weight for the first `K` centered eta cutoff nodes. -/
def pairedEtaFiniteCutoffLogGap (K : ℕ) (_ : Fin K) : ℝ :=
  (((2 * K : ℕ) : ℝ))⁻¹

/-- The centered eta cutoff frequencies are injective on every finite
prefix. -/
theorem pairedEtaCutoffLogFrequency_fin_injective (K : ℕ) :
    Function.Injective
      (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val) := by
  intro r s hrs
  apply Fin.ext
  have hrPos : 0 < ((((2 * r.val + 1 : ℕ) : ℝ))) := by positivity
  have hsPos : 0 < ((((2 * s.val + 1 : ℕ) : ℝ))) := by positivity
  have hLog :
      Real.log ((((2 * r.val + 1 : ℕ) : ℝ))) =
        Real.log ((((2 * s.val + 1 : ℕ) : ℝ))) := by
    simpa [pairedEtaCutoffLogFrequency] using hrs
  have hCast : ((((2 * r.val + 1 : ℕ) : ℝ))) =
      ((((2 * s.val + 1 : ℕ) : ℝ))) := by
    calc
      ((((2 * r.val + 1 : ℕ) : ℝ))) =
          Real.exp (Real.log ((((2 * r.val + 1 : ℕ) : ℝ)))) :=
        (Real.exp_log hrPos).symm
      _ = Real.exp (Real.log ((((2 * s.val + 1 : ℕ) : ℝ)))) := by
        rw [hLog]
      _ = ((((2 * s.val + 1 : ℕ) : ℝ))) := Real.exp_log hsPos
  have hNat : 2 * r.val + 1 = 2 * s.val + 1 := by
    exact_mod_cast hCast
  omega

/-- Distinct centered eta cutoff frequencies among the first `K` nodes are
separated by at least `1/(2K)`. -/
theorem pairedEtaFiniteCutoffLogGap_le_abs_sub {K : ℕ}
    (r s : Fin K) (hrs : r ≠ s) :
    pairedEtaFiniteCutoffLogGap K r ≤
      |pairedEtaCutoffLogFrequency r.val -
        pairedEtaCutoffLogFrequency s.val| := by
  have hrsVal : r.val ≠ s.val := fun h ↦ hrs (Fin.ext h)
  rcases lt_or_gt_of_ne hrsVal with hrsLt | hsrLt
  · have hLog := inv_natCast_le_log_natCast_sub_log_natCast
      (a := 2 * r.val + 1) (b := 2 * s.val + 1) (K := 2 * K)
      (by omega) (by omega) (by omega)
    have hLe : pairedEtaCutoffLogFrequency r.val ≤
        pairedEtaCutoffLogFrequency s.val := by
      unfold pairedEtaCutoffLogFrequency
      apply Real.log_le_log
      · positivity
      · exact_mod_cast (show 2 * r.val + 1 ≤ 2 * s.val + 1 by omega)
    rw [abs_of_nonpos (sub_nonpos.mpr hLe), neg_sub]
    simpa [pairedEtaFiniteCutoffLogGap, pairedEtaCutoffLogFrequency] using hLog
  · have hLog := inv_natCast_le_log_natCast_sub_log_natCast
      (a := 2 * s.val + 1) (b := 2 * r.val + 1) (K := 2 * K)
      (by omega) (by omega) (by omega)
    have hLe : pairedEtaCutoffLogFrequency s.val ≤
        pairedEtaCutoffLogFrequency r.val := by
      unfold pairedEtaCutoffLogFrequency
      apply Real.log_le_log
      · positivity
      · exact_mod_cast (show 2 * s.val + 1 ≤ 2 * r.val + 1 by omega)
    rw [abs_of_nonneg (sub_nonneg.mpr hLe)]
    simpa [pairedEtaFiniteCutoffLogGap, pairedEtaCutoffLogFrequency] using hLog

/-- The first `K` centered eta cutoff frequencies and the constant weight
`1/(2K)` form an admissible Montgomery--Vaughan family. -/
theorem pairedEtaFiniteCutoffLog_admissible {K : ℕ} (hK : 0 < K) :
    MontgomeryVaughan.Adm
      (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val)
      (pairedEtaFiniteCutoffLogGap K) := by
  refine ⟨pairedEtaCutoffLogFrequency_fin_injective K, ?_, ?_⟩
  · intro r
    unfold pairedEtaFiniteCutoffLogGap
    positivity
  · intro r s hrs
    exact pairedEtaFiniteCutoffLogGap_le_abs_sub r s hrs

/-- Montgomery--Vaughan with constant `26`, specialized to the first `K`
centered eta cutoff frequencies. -/
theorem pairedEtaFiniteCutoffLog_mvHilbert_twentySix
    {K : ℕ} (hK : 0 < K) (x z : Fin K → ℂ) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ)
        else x r * conj (z s) /
          ((pairedEtaCutoffLogFrequency r.val -
            pairedEtaCutoffLogFrequency s.val : ℝ) : ℂ)‖ ≤
      26 * Real.sqrt ((((2 * K : ℕ) : ℝ)) * ∑ r, ‖x r‖ ^ 2) *
        Real.sqrt ((((2 * K : ℕ) : ℝ)) * ∑ r, ‖z r‖ ^ 2) := by
  have hadm := pairedEtaFiniteCutoffLog_admissible hK
  have hmv := MontgomeryVaughan.mvHilbert_twentySix (Fin K)
    (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val)
    (pairedEtaFiniteCutoffLogGap K) x z hadm.inj hadm.pos hadm.le
  have hx : (∑ r, ‖x r‖ ^ 2 / pairedEtaFiniteCutoffLogGap K r) =
      (((2 * K : ℕ) : ℝ)) * ∑ r, ‖x r‖ ^ 2 := by
    simp only [pairedEtaFiniteCutoffLogGap, div_eq_mul_inv, inv_inv]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ ↦ by ring
  have hz : (∑ r, ‖z r‖ ^ 2 / pairedEtaFiniteCutoffLogGap K r) =
      (((2 * K : ℕ) : ℝ)) * ∑ r, ‖z r‖ ^ 2 := by
    simp only [pairedEtaFiniteCutoffLogGap, div_eq_mul_inv, inv_inv]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ ↦ by ring
  rw [hx, hz] at hmv
  exact hmv

/-- Direct heat-kernel form of the Montgomery--Vaughan estimate at the
centered eta cutoff nodes.  This theorem is the checked transform bridge from
Gaussian proper time to the reciprocal logarithmic-gap inequality. -/
theorem pairedEtaFiniteCutoffLog_orientedSqrtHeat_mvHilbert_twentySix
    {K : ℕ} (hK : 0 < K) (x z : Fin K → ℂ) :
    ‖finiteGaussianOrientedSqrtHeatBilinear
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val) x z‖ ≤
      26 * Real.sqrt ((((2 * K : ℕ) : ℝ)) * ∑ r, ‖x r‖ ^ 2) *
        Real.sqrt ((((2 * K : ℕ) : ℝ)) * ∑ r, ‖z r‖ ^ 2) := by
  rw [finiteGaussianOrientedSqrtHeatBilinear_eq_hilbertSum _ _ _
    (pairedEtaCutoffLogFrequency_fin_injective K)]
  exact pairedEtaFiniteCutoffLog_mvHilbert_twentySix hK x z

/-- Direct odd proper-time form of Montgomery--Vaughan at the centered eta
cutoff nodes.  Its left side literally integrates
`(lambda_i-lambda_j) * exp(-u*(lambda_i-lambda_j)^2)` before applying the
checked constant-26 Hilbert bound. -/
theorem pairedEtaFiniteCutoffLog_oddHeat_mvHilbert_twentySix
    {K : ℕ} (hK : 0 < K) (x z : Fin K → ℂ) :
    ‖finiteGaussianOddHeatBilinear
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val) x z‖ ≤
      26 * Real.sqrt ((((2 * K : ℕ) : ℝ)) * ∑ r, ‖x r‖ ^ 2) *
        Real.sqrt ((((2 * K : ℕ) : ℝ)) * ∑ r, ‖z r‖ ^ 2) := by
  rw [finiteGaussianOddHeatBilinear_eq_orientedSqrt]
  exact pairedEtaFiniteCutoffLog_orientedSqrtHeat_mvHilbert_twentySix
    hK x z

/-! ## The transform on the genuine eta zero-window matrix work -/

/-- Oriented heat/Hilbert transform of the actual eta zero-window matrix work
on the canonical cutoff family `N = 0, ..., K-1`. -/
def pairedEtaTopPrefixFiniteHeatHilbertMatrixWork (K : ℕ) (T : ℝ) :
    Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  finiteGaussianOrientedSqrtHeatTransform
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
      (fun r : Fin K ↦ r.val))
    (pairedEtaTopPrefixFiniteZeroWindowMatrixWork
      (fun r : Fin K ↦ r.val) T)

/-- Oriented heat/Hilbert transform of the actual leading eta zero-window
matrix current on the canonical cutoff family. -/
def pairedEtaTopPrefixFiniteHeatHilbertLeadingMatrixCurrent
    (K : ℕ) (T : ℝ) : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  finiteGaussianOrientedSqrtHeatTransform
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
      (fun r : Fin K ↦ r.val))
    (pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent
      (fun r : Fin K ↦ r.val) T)

/-- Oriented heat/Hilbert transform of the actual remainder eta zero-window
matrix current on the canonical cutoff family. -/
def pairedEtaTopPrefixFiniteHeatHilbertRemainderMatrixCurrent
    (K : ℕ) (T : ℝ) : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  finiteGaussianOrientedSqrtHeatTransform
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
      (fun r : Fin K ↦ r.val))
    (pairedEtaTopPrefixFiniteZeroWindowRemainderMatrixCurrent
      (fun r : Fin K ↦ r.val) T)

/-- Each actual transformed matrix-work entry is explicitly the oriented
square-root integral of the previously defined heat-compressed work.  Equal
cutoff nodes are removed before integration. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertMatrixWork_apply_eq_heatIntegral
    (K : ℕ) (T : ℝ) (i j : Fin K × Fin 2) :
    pairedEtaTopPrefixFiniteHeatHilbertMatrixWork K T i j =
      if pairedEtaCutoffLogFrequency i.1.val =
          pairedEtaCutoffLogFrequency j.1.val then 0
      else
        (((2 / Real.sqrt Real.pi) *
            (SignType.sign
              (pairedEtaCutoffLogFrequency i.1.val -
                pairedEtaCutoffLogFrequency j.1.val) : ℝ) : ℝ) : ℂ) *
          ∫ t : ℝ in Set.Ioi 0,
            pairedEtaTopPrefixFiniteHeatCompressedZeroWindowMatrixWork
              (fun r : Fin K ↦ r.val) T (t ^ 2) i j := by
  rfl

/-- The actual eta heat/Hilbert matrix work is equally the direct odd
proper-time transform of the checked Gaussian-compressed work. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertMatrixWork_eq_oddHeatTransform
    (K : ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteHeatHilbertMatrixWork K T =
      finiteGaussianOddHeatTransform
        (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
          (fun r : Fin K ↦ r.val))
        (pairedEtaTopPrefixFiniteZeroWindowMatrixWork
          (fun r : Fin K ↦ r.val) T) := by
  unfold pairedEtaTopPrefixFiniteHeatHilbertMatrixWork
  exact (finiteGaussianOddHeatTransform_eq_orientedSqrt _ _).symm

/-- Each actual eta matrix-work entry is the direct signed proper-time
integral `gap * heatCompression`; coincident cutoff frequencies are removed
before integration. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertMatrixWork_apply_eq_oddHeatIntegral
    (K : ℕ) (T : ℝ) (i j : Fin K × Fin 2) :
    pairedEtaTopPrefixFiniteHeatHilbertMatrixWork K T i j =
      if pairedEtaCutoffLogFrequency i.1.val =
          pairedEtaCutoffLogFrequency j.1.val then 0
      else
        ∫ u : ℝ in Set.Ioi 0,
          (((pairedEtaCutoffLogFrequency i.1.val -
            pairedEtaCutoffLogFrequency j.1.val : ℝ) : ℂ) *
            pairedEtaTopPrefixFiniteHeatCompressedZeroWindowMatrixWork
              (fun r : Fin K ↦ r.val) T u i j) := by
  rw [pairedEtaTopPrefixFiniteHeatHilbertMatrixWork_eq_oddHeatTransform]
  rfl

/-- The actual heat/Hilbert matrix-work entry is the matrix work divided by
the logarithmic cutoff gap, with every same-cutoff channel pair explicitly
zeroed. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertMatrixWork_apply
    (K : ℕ) (T : ℝ) (i j : Fin K × Fin 2) :
    pairedEtaTopPrefixFiniteHeatHilbertMatrixWork K T i j =
      if i.1 = j.1 then 0
      else
        (((pairedEtaCutoffLogFrequency i.1.val -
          pairedEtaCutoffLogFrequency j.1.val)⁻¹ : ℝ) : ℂ) *
          pairedEtaTopPrefixFiniteZeroWindowMatrixWork
            (fun r : Fin K ↦ r.val) T i j := by
  unfold pairedEtaTopPrefixFiniteHeatHilbertMatrixWork
  rw [finiteGaussianOrientedSqrtHeatTransform_apply]
  change
    (if pairedEtaCutoffLogFrequency i.1.val =
        pairedEtaCutoffLogFrequency j.1.val then 0
      else
        (((pairedEtaCutoffLogFrequency i.1.val -
          pairedEtaCutoffLogFrequency j.1.val)⁻¹ : ℝ) : ℂ) *
          pairedEtaTopPrefixFiniteZeroWindowMatrixWork
            (fun r : Fin K ↦ r.val) T i j) = _
  by_cases hij : i.1 = j.1
  · simp [hij]
  · have hfreq : pairedEtaCutoffLogFrequency i.1.val ≠
        pairedEtaCutoffLogFrequency j.1.val :=
      (pairedEtaCutoffLogFrequency_fin_injective K).ne hij
    simp [hij, hfreq]

/-- The exact leading/remainder eta matrix-current law survives the complete
oriented heat/Hilbert transform. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertMatrixWork_eq_leading_add_remainder
    (K : ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteHeatHilbertMatrixWork K T =
      pairedEtaTopPrefixFiniteHeatHilbertLeadingMatrixCurrent K T +
        pairedEtaTopPrefixFiniteHeatHilbertRemainderMatrixCurrent K T := by
  unfold pairedEtaTopPrefixFiniteHeatHilbertMatrixWork
    pairedEtaTopPrefixFiniteHeatHilbertLeadingMatrixCurrent
    pairedEtaTopPrefixFiniteHeatHilbertRemainderMatrixCurrent
  rw [topPrefixFiniteZeroWindowMatrixWork_eq_leading_add_remainder,
    finiteGaussianOrientedSqrtHeatTransform_add]

end

end RiemannGaussian
