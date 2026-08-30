import RiemannGaussian.EtaEnergyFiniteWindowHeatHilbertLeading

/-!
# Channel-resolved odd-heat eta currents

The direct odd heat transform retains one oriented mixed channel after the
same-colour block sums cancel.  This module opens that surviving channel into
the two literal completed eta colours from which the hyperbolic feature was
built.

For a generic pair of channel sequences `p,q`, the hyperbolic packing is

`(p+q, I*(p-q))`.

The skew odd-heat bilinear form cancels every same-colour pairing in the
leading transport current.  Its `0,1` block is exactly twice `I` times three
cross-colour Hilbert forms.  Lean then specializes this identity to the
actual partner and aligned-conjugate eta leading increments and successor
features.  The same reduction is proved at every proper time before
integration: the complete finite spectral-window trajectory is an exact
analytic-multiplicity-weighted complex sum of those phase-bearing forms.
Its positive-time integral is then proved equal to the reciprocal-gap block.

No norm or absolute value is taken in the terminal identity.  A future
arithmetic estimate can therefore use the heat scale, cutoff orientation, the
partner versus aligned-conjugate colour, and cancellation between genuine
zeros.
-/

open Complex MeasureTheory Set
open scoped BigOperators Classical ComplexConjugate Matrix Real

namespace RiemannGaussian

noncomputable section

/-! ## Algebra of the odd transpose form -/

/-- Exchanging the two vectors negates the direct odd-heat transpose
bilinear form. -/
theorem finiteGaussianOddHeatTransposeBilinear_swap
    {d : Type*} [Fintype d] (frequency : d → ℝ) (x y : d → ℂ) :
    finiteGaussianOddHeatTransposeBilinear frequency y x =
      -finiteGaussianOddHeatTransposeBilinear frequency x y := by
  unfold finiteGaussianOddHeatTransposeBilinear
  calc
    (∑ i, ∑ j,
        y i * x j * finiteGaussianOddHeatKernelIntegral frequency i j) =
        ∑ j, ∑ i,
          y i * x j * finiteGaussianOddHeatKernelIntegral frequency i j := by
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ i,
        -(x j * y i * finiteGaussianOddHeatKernelIntegral frequency j i) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro i _hi
      rw [finiteGaussianOddHeatKernelIntegral_swap]
      ring
    _ = -∑ j, ∑ i,
        x j * y i * finiteGaussianOddHeatKernelIntegral frequency j i := by
      simp

/-- The direct odd-heat transpose form of one vector with itself vanishes. -/
theorem finiteGaussianOddHeatTransposeBilinear_self_eq_zero
    {d : Type*} [Fintype d] (frequency : d → ℝ) (x : d → ℂ) :
    finiteGaussianOddHeatTransposeBilinear frequency x x = 0 := by
  have h := finiteGaussianOddHeatTransposeBilinear_swap frequency x x
  linear_combination (1 / 2 : ℂ) * h

/-- The direct odd-heat transpose form is additive in its first vector. -/
theorem finiteGaussianOddHeatTransposeBilinear_add_left
    {d : Type*} [Fintype d] (frequency : d → ℝ) (x y z : d → ℂ) :
    finiteGaussianOddHeatTransposeBilinear frequency (x + y) z =
      finiteGaussianOddHeatTransposeBilinear frequency x z +
        finiteGaussianOddHeatTransposeBilinear frequency y z := by
  unfold finiteGaussianOddHeatTransposeBilinear
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Pi.add_apply]
  ring

/-- The direct odd-heat transpose form preserves subtraction in its second
vector. -/
theorem finiteGaussianOddHeatTransposeBilinear_sub_right
    {d : Type*} [Fintype d] (frequency : d → ℝ) (x y z : d → ℂ) :
    finiteGaussianOddHeatTransposeBilinear frequency x (y - z) =
      finiteGaussianOddHeatTransposeBilinear frequency x y -
        finiteGaussianOddHeatTransposeBilinear frequency x z := by
  unfold finiteGaussianOddHeatTransposeBilinear
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Pi.sub_apply]
  ring

/-- A complex scalar in the second vector factors out of the direct odd-heat
transpose form. -/
theorem finiteGaussianOddHeatTransposeBilinear_smul_right
    {d : Type*} [Fintype d] (frequency : d → ℝ) (c : ℂ)
    (x y : d → ℂ) :
    finiteGaussianOddHeatTransposeBilinear frequency x (c • y) =
      c * finiteGaussianOddHeatTransposeBilinear frequency x y := by
  unfold finiteGaussianOddHeatTransposeBilinear
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Expansion of one even/odd hyperbolic slice pairing into the four
underlying colour pairings. -/
theorem finiteGaussianOddHeatTransposeBilinear_hyperbolicSlices
    {d : Type*} [Fintype d] (frequency : d → ℝ)
    (p q P Q : d → ℂ) :
    finiteGaussianOddHeatTransposeBilinear frequency
        (p + q) (fun r ↦ I * (P r - Q r)) =
      I * (finiteGaussianOddHeatTransposeBilinear frequency p P -
        finiteGaussianOddHeatTransposeBilinear frequency p Q +
        finiteGaussianOddHeatTransposeBilinear frequency q P -
        finiteGaussianOddHeatTransposeBilinear frequency q Q) := by
  have hfun : (fun r ↦ I * (P r - Q r)) = I • (P - Q) := by
    funext r
    simp
  rw [hfun, finiteGaussianOddHeatTransposeBilinear_smul_right,
    finiteGaussianOddHeatTransposeBilinear_add_left,
    finiteGaussianOddHeatTransposeBilinear_sub_right,
    finiteGaussianOddHeatTransposeBilinear_sub_right]
  ring

/-! ## Generic two-colour reduction -/

/-- Pack two cutoff vectors into their reflection-even and `I`-twisted
reflection-odd hyperbolic channels. -/
def twoChannelHyperbolicPack {K : ℕ} (p q : Fin K → ℂ) :
    Fin K × Fin 2 → ℂ :=
  fun j ↦ ![p j.1 + q j.1, I * (p j.1 - q j.1)] j.2

/-- The surviving mixed-colour block of a hyperbolically packed leading
current contains exactly three cross-colour odd-heat forms.  Every
same-colour form cancels by skew symmetry. -/
theorem twoChannelHyperbolicLeadingCurrent_oddHeatBlock_eq_crossChannel
    {K : ℕ} (frequency : Fin K → ℝ)
    (p q P Q : Fin K → ℂ) :
    twoChannelMatrixBlockSum
        (finiteGaussianOddHeatTransform
          (fun j : Fin K × Fin 2 ↦ frequency j.1)
          (complexSymmetricLeadingTransportCurrent
            (twoChannelHyperbolicPack p q)
            (twoChannelHyperbolicPack P Q))) 0 1 =
      2 * I *
        (finiteGaussianOddHeatTransposeBilinear frequency q p +
          finiteGaussianOddHeatTransposeBilinear frequency q P +
          finiteGaussianOddHeatTransposeBilinear frequency Q p) := by
  unfold complexSymmetricLeadingTransportCurrent
  rw [finiteGaussianOddHeatTransform_add,
    finiteGaussianOddHeatTransform_add,
    twoChannelMatrixBlockSum_add,
    twoChannelMatrixBlockSum_add,
    twoChannelMatrixBlockSum_oddHeatTransform_vecMulVec,
    twoChannelMatrixBlockSum_oddHeatTransform_vecMulVec,
    twoChannelMatrixBlockSum_oddHeatTransform_vecMulVec]
  change
    finiteGaussianOddHeatTransposeBilinear frequency
          (p + q) (fun r ↦ I * (p r - q r)) +
        (finiteGaussianOddHeatTransposeBilinear frequency
            (p + q) (fun r ↦ I * (P r - Q r)) +
          finiteGaussianOddHeatTransposeBilinear frequency
            (P + Q) (fun r ↦ I * (p r - q r))) = _
  rw [finiteGaussianOddHeatTransposeBilinear_hyperbolicSlices,
    finiteGaussianOddHeatTransposeBilinear_hyperbolicSlices,
    finiteGaussianOddHeatTransposeBilinear_hyperbolicSlices,
    finiteGaussianOddHeatTransposeBilinear_self_eq_zero frequency p,
    finiteGaussianOddHeatTransposeBilinear_self_eq_zero frequency q,
    finiteGaussianOddHeatTransposeBilinear_swap frequency q p,
    finiteGaussianOddHeatTransposeBilinear_swap frequency p P,
    finiteGaussianOddHeatTransposeBilinear_swap frequency q P,
    finiteGaussianOddHeatTransposeBilinear_swap frequency Q p,
    finiteGaussianOddHeatTransposeBilinear_swap frequency q Q]
  ring

/-! ## Pointwise colour algebra along the heat trajectory -/

/-- The direct odd heat transpose form at one proper time.  This carrier
retains the heat scale as well as the orientation of every frequency gap. -/
def finiteGaussianOddHeatTransposeBilinearAt
    (K : ℕ) (frequency : Fin K → ℝ) (heat : ℝ)
    (x y : Fin K → ℂ) : ℂ :=
  ∑ i, ∑ j, x i * y j *
    (((frequency i - frequency j : ℝ) : ℂ) *
      finiteGaussianProperTimeKernelMatrix frequency heat i j)

/-- Exchanging the two vectors negates the pointwise odd heat form. -/
theorem finiteGaussianOddHeatTransposeBilinearAt_swap
    (K : ℕ) (frequency : Fin K → ℝ) (heat : ℝ)
    (x y : Fin K → ℂ) :
    finiteGaussianOddHeatTransposeBilinearAt K frequency heat y x =
      -finiteGaussianOddHeatTransposeBilinearAt K frequency heat x y := by
  unfold finiteGaussianOddHeatTransposeBilinearAt
  calc
    (∑ i, ∑ j, y i * x j *
        (((frequency i - frequency j : ℝ) : ℂ) *
          finiteGaussianProperTimeKernelMatrix frequency heat i j)) =
      ∑ j, ∑ i, y i * x j *
        (((frequency i - frequency j : ℝ) : ℂ) *
          finiteGaussianProperTimeKernelMatrix frequency heat i j) := by
        rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, -(x j * y i *
        (((frequency j - frequency i : ℝ) : ℂ) *
          finiteGaussianProperTimeKernelMatrix frequency heat j i)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro i _hi
      unfold finiteGaussianProperTimeKernelMatrix
      rw [show (frequency j - frequency i) ^ 2 =
          (frequency i - frequency j) ^ 2 by ring]
      rw [show frequency j - frequency i =
          -(frequency i - frequency j) by ring]
      push_cast
      ring
    _ = -∑ j, ∑ i, x j * y i *
        (((frequency j - frequency i : ℝ) : ℂ) *
          finiteGaussianProperTimeKernelMatrix frequency heat j i) := by
      simp

/-- The pointwise odd heat form of one vector with itself vanishes. -/
theorem finiteGaussianOddHeatTransposeBilinearAt_self_eq_zero
    (K : ℕ) (frequency : Fin K → ℝ) (heat : ℝ)
    (x : Fin K → ℂ) :
    finiteGaussianOddHeatTransposeBilinearAt K frequency heat x x = 0 := by
  have h :=
    finiteGaussianOddHeatTransposeBilinearAt_swap K frequency heat x x
  linear_combination (1 / 2 : ℂ) * h

/-- The pointwise odd heat form is additive in its first vector. -/
theorem finiteGaussianOddHeatTransposeBilinearAt_add_left
    (K : ℕ) (frequency : Fin K → ℝ) (heat : ℝ)
    (x y z : Fin K → ℂ) :
    finiteGaussianOddHeatTransposeBilinearAt K frequency heat (x + y) z =
      finiteGaussianOddHeatTransposeBilinearAt K frequency heat x z +
        finiteGaussianOddHeatTransposeBilinearAt K frequency heat y z := by
  unfold finiteGaussianOddHeatTransposeBilinearAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Pi.add_apply]
  ring

/-- The pointwise odd heat form preserves subtraction in its second vector. -/
theorem finiteGaussianOddHeatTransposeBilinearAt_sub_right
    (K : ℕ) (frequency : Fin K → ℝ) (heat : ℝ)
    (x y z : Fin K → ℂ) :
    finiteGaussianOddHeatTransposeBilinearAt K frequency heat x (y - z) =
      finiteGaussianOddHeatTransposeBilinearAt K frequency heat x y -
        finiteGaussianOddHeatTransposeBilinearAt K frequency heat x z := by
  unfold finiteGaussianOddHeatTransposeBilinearAt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Pi.sub_apply]
  ring

/-- A complex scalar in the second vector factors out of the pointwise odd
heat form. -/
theorem finiteGaussianOddHeatTransposeBilinearAt_smul_right
    (K : ℕ) (frequency : Fin K → ℝ) (heat : ℝ)
    (c : ℂ) (x y : Fin K → ℂ) :
    finiteGaussianOddHeatTransposeBilinearAt K frequency heat x (c • y) =
      c * finiteGaussianOddHeatTransposeBilinearAt K frequency heat x y := by
  unfold finiteGaussianOddHeatTransposeBilinearAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Pointwise expansion of one hyperbolic slice pairing into the four
underlying colour pairings. -/
theorem finiteGaussianOddHeatTransposeBilinearAt_hyperbolicSlices
    (K : ℕ) (frequency : Fin K → ℝ) (heat : ℝ)
    (p q P Q : Fin K → ℂ) :
    finiteGaussianOddHeatTransposeBilinearAt K frequency heat
        (p + q) (fun r ↦ I * (P r - Q r)) =
      I * (finiteGaussianOddHeatTransposeBilinearAt K frequency heat p P -
        finiteGaussianOddHeatTransposeBilinearAt K frequency heat p Q +
        finiteGaussianOddHeatTransposeBilinearAt K frequency heat q P -
        finiteGaussianOddHeatTransposeBilinearAt K frequency heat q Q) := by
  have hfun : (fun r ↦ I * (P r - Q r)) = I • (P - Q) := by
    funext r
    simp
  rw [hfun, finiteGaussianOddHeatTransposeBilinearAt_smul_right,
    finiteGaussianOddHeatTransposeBilinearAt_add_left,
    finiteGaussianOddHeatTransposeBilinearAt_sub_right,
    finiteGaussianOddHeatTransposeBilinearAt_sub_right]
  ring

/-- The direct odd heat current is additive in its matrix carrier. -/
theorem finiteGaussianOddHeatCurrent_add {d : Type*}
    (frequency : d → ℝ) (heat : ℝ) (A B : Matrix d d ℂ) :
    finiteGaussianOddHeatCurrent frequency heat (A + B) =
      finiteGaussianOddHeatCurrent frequency heat A +
        finiteGaussianOddHeatCurrent frequency heat B := by
  ext i j
  simp only [finiteGaussianOddHeatCurrent,
    finiteGaussianProperTimeCompression, Matrix.hadamard_apply,
    Matrix.add_apply]
  ring

/-- Complex scaling commutes with the direct odd heat current. -/
theorem finiteGaussianOddHeatCurrent_smul {d : Type*}
    (frequency : d → ℝ) (heat : ℝ) (c : ℂ) (A : Matrix d d ℂ) :
    finiteGaussianOddHeatCurrent frequency heat (c • A) =
      c • finiteGaussianOddHeatCurrent frequency heat A := by
  ext i j
  simp only [finiteGaussianOddHeatCurrent,
    finiteGaussianProperTimeCompression, Matrix.hadamard_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- A finite sum can be transported through the direct odd heat current
without collapsing the proper-time variable. -/
theorem finiteGaussianOddHeatCurrent_finsetSum {d alpha : Type*}
    (frequency : d → ℝ) (heat : ℝ) (S : Finset alpha)
    (A : alpha → Matrix d d ℂ) :
    finiteGaussianOddHeatCurrent frequency heat (∑ q ∈ S, A q) =
      ∑ q ∈ S, finiteGaussianOddHeatCurrent frequency heat (A q) := by
  ext i j
  simp only [finiteGaussianOddHeatCurrent,
    finiteGaussianProperTimeCompression, Matrix.hadamard_apply,
    Matrix.sum_apply, Finset.mul_sum]

/-- One channel block of the odd heat current of an outer product is the
pointwise odd heat transpose form of the corresponding vector slices. -/
theorem twoChannelMatrixBlockSum_oddHeatCurrent_vecMulVec
    (K : ℕ) (frequency : Fin K → ℝ) (heat : ℝ)
    (x y : Fin K × Fin 2 → ℂ) (a b : Fin 2) :
    twoChannelMatrixBlockSum
        (finiteGaussianOddHeatCurrent
          (fun j : Fin K × Fin 2 ↦ frequency j.1) heat
          (Matrix.vecMulVec x y)) a b =
      finiteGaussianOddHeatTransposeBilinearAt K frequency heat
        (twoChannelVectorSlice x a) (twoChannelVectorSlice y b) := by
  unfold twoChannelMatrixBlockSum
    finiteGaussianOddHeatTransposeBilinearAt twoChannelVectorSlice
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [finiteGaussianOddHeatCurrent,
    finiteGaussianProperTimeCompression, Matrix.hadamard_apply,
    Matrix.vecMulVec_apply, finiteGaussianProperTimeKernelMatrix]
  ring

/-- At every proper time, the surviving mixed block of a hyperbolically
packed leading current is exactly the same three cross-colour forms.  Thus
the colour reduction itself does not require integrating away the heat
scale. -/
theorem twoChannelHyperbolicLeadingCurrent_oddHeatBlockAt_eq_crossChannel
    (K : ℕ) (frequency : Fin K → ℝ) (heat : ℝ)
    (p q P Q : Fin K → ℂ) :
    twoChannelMatrixBlockSum
        (finiteGaussianOddHeatCurrent
          (fun j : Fin K × Fin 2 ↦ frequency j.1) heat
          (complexSymmetricLeadingTransportCurrent
            (twoChannelHyperbolicPack p q)
            (twoChannelHyperbolicPack P Q))) 0 1 =
      2 * I *
        (finiteGaussianOddHeatTransposeBilinearAt K frequency heat q p +
          finiteGaussianOddHeatTransposeBilinearAt K frequency heat q P +
          finiteGaussianOddHeatTransposeBilinearAt K frequency heat Q p) := by
  unfold complexSymmetricLeadingTransportCurrent
  rw [finiteGaussianOddHeatCurrent_add, finiteGaussianOddHeatCurrent_add,
    twoChannelMatrixBlockSum_add, twoChannelMatrixBlockSum_add,
    twoChannelMatrixBlockSum_oddHeatCurrent_vecMulVec,
    twoChannelMatrixBlockSum_oddHeatCurrent_vecMulVec,
    twoChannelMatrixBlockSum_oddHeatCurrent_vecMulVec]
  change
    finiteGaussianOddHeatTransposeBilinearAt K frequency heat
          (p + q) (fun r ↦ I * (p r - q r)) +
        (finiteGaussianOddHeatTransposeBilinearAt K frequency heat
            (p + q) (fun r ↦ I * (P r - Q r)) +
          finiteGaussianOddHeatTransposeBilinearAt K frequency heat
            (P + Q) (fun r ↦ I * (p r - q r))) = _
  rw [finiteGaussianOddHeatTransposeBilinearAt_hyperbolicSlices,
    finiteGaussianOddHeatTransposeBilinearAt_hyperbolicSlices,
    finiteGaussianOddHeatTransposeBilinearAt_hyperbolicSlices,
    finiteGaussianOddHeatTransposeBilinearAt_self_eq_zero K frequency heat p,
    finiteGaussianOddHeatTransposeBilinearAt_self_eq_zero K frequency heat q,
    finiteGaussianOddHeatTransposeBilinearAt_swap K frequency heat q p,
    finiteGaussianOddHeatTransposeBilinearAt_swap K frequency heat p P,
    finiteGaussianOddHeatTransposeBilinearAt_swap K frequency heat q P,
    finiteGaussianOddHeatTransposeBilinearAt_swap K frequency heat Q p,
    finiteGaussianOddHeatTransposeBilinearAt_swap K frequency heat q Q]
  ring

/-! ## Lossless transport of the heat-time trajectory -/

/-- A finite channel block of the reciprocal-gap transform is the integral
of the corresponding channel block along the full direct odd heat trajectory.
The finite sum-integral exchange is justified entry by entry. -/
theorem twoChannelMatrixBlockSum_oddHeatTransform_eq_integral_current
    {K : ℕ} (frequency : Fin K → ℝ)
    (A : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ)
    (a b : Fin 2) :
    twoChannelMatrixBlockSum
        (finiteGaussianOddHeatTransform
          (fun j : Fin K × Fin 2 ↦ frequency j.1) A) a b =
      ∫ u : ℝ in Set.Ioi 0,
        twoChannelMatrixBlockSum
          (finiteGaussianOddHeatCurrent
            (fun j : Fin K × Fin 2 ↦ frequency j.1) u A) a b := by
  unfold twoChannelMatrixBlockSum
  have hInt : ∀ x : Fin K × Fin K,
      IntegrableOn
        (fun u : ℝ ↦
          finiteGaussianOddHeatCurrent
            (fun j : Fin K × Fin 2 ↦ frequency j.1) u A
            (x.1, a) (x.2, b)) (Set.Ioi 0) := by
    intro x
    exact finiteGaussianOddHeatCurrent_apply_integrableOn _ _ _ _
  have hsum :
      (∫ u : ℝ in Set.Ioi 0,
        ∑ x : Fin K × Fin K,
          finiteGaussianOddHeatCurrent
            (fun j : Fin K × Fin 2 ↦ frequency j.1) u A
            (x.1, a) (x.2, b)) =
        ∑ x : Fin K × Fin K,
          ∫ u : ℝ in Set.Ioi 0,
            finiteGaussianOddHeatCurrent
              (fun j : Fin K × Fin 2 ↦ frequency j.1) u A
              (x.1, a) (x.2, b) := by
    simpa using
      (integral_finsetSum (s := Finset.univ)
        (f := fun x : Fin K × Fin K ↦ fun u : ℝ ↦
          finiteGaussianOddHeatCurrent
            (fun j : Fin K × Fin 2 ↦ frequency j.1) u A
            (x.1, a) (x.2, b))
        (fun x _hx ↦ hInt x))
  calc
    (∑ r, ∑ s,
        finiteGaussianOddHeatTransform
          (fun j : Fin K × Fin 2 ↦ frequency j.1) A (r, a) (s, b)) =
        ∑ r, ∑ s,
          ∫ u : ℝ in Set.Ioi 0,
            finiteGaussianOddHeatCurrent
              (fun j : Fin K × Fin 2 ↦ frequency j.1) u A
              (r, a) (s, b) := by
      apply Finset.sum_congr rfl
      intro r _hr
      apply Finset.sum_congr rfl
      intro s _hs
      exact finiteGaussianOddHeatTransform_apply_eq_integral_current _ _ _ _
    _ = ∑ x : Fin K × Fin K,
          ∫ u : ℝ in Set.Ioi 0,
            finiteGaussianOddHeatCurrent
              (fun j : Fin K × Fin 2 ↦ frequency j.1) u A
              (x.1, a) (x.2, b) := by
      rw [Fintype.sum_prod_type]
    _ = ∫ u : ℝ in Set.Ioi 0,
        ∑ x : Fin K × Fin K,
          finiteGaussianOddHeatCurrent
            (fun j : Fin K × Fin 2 ↦ frequency j.1) u A
            (x.1, a) (x.2, b) := hsum.symm
    _ = ∫ u : ℝ in Set.Ioi 0,
        ∑ r, ∑ s,
          finiteGaussianOddHeatCurrent
            (fun j : Fin K × Fin 2 ↦ frequency j.1) u A
            (r, a) (s, b) := by
      congr 1
      funext u
      rw [Fintype.sum_prod_type]

/-! ## Literal eta colour vectors -/

/-- Reflected-partner leading arithmetic increments on the first `K`
cutoffs. -/
def pairedEtaTopPrefixFinitePartnerLeadingCutoffVector
    (K : ℕ) (rho : NontrivialZetaZero) : Fin K → ℂ :=
  fun r ↦ pairedEtaTopPrefixFinitePartnerLeadingArithmeticIncrement rho r.val

/-- Parity-aligned conjugate leading arithmetic increments on the first `K`
cutoffs. -/
def pairedEtaTopPrefixFiniteAlignedLeadingCutoffVector
    (K : ℕ) (rho : NontrivialZetaZero) : Fin K → ℂ :=
  fun r ↦
    pairedEtaTopPrefixFiniteAlignedConjugateLeadingArithmeticIncrement rho r.val

/-- Reflected-partner completed eta features at the successor cutoffs. -/
def pairedEtaTopPrefixFinitePartnerSuccessorCutoffVector
    (K : ℕ) (rho : NontrivialZetaZero) : Fin K → ℂ :=
  fun r ↦
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
      rho (r.val + 1)

/-- Parity-aligned conjugate completed eta features at the successor
cutoffs. -/
def pairedEtaTopPrefixFiniteAlignedSuccessorCutoffVector
    (K : ℕ) (rho : NontrivialZetaZero) : Fin K → ℂ :=
  fun r ↦ pairedEtaTopPrefixFiniteAlignedConjugateTerm rho (r.val + 1)

/-- The actual packed eta leading increment is the generic hyperbolic pack
of its two literal colour vectors. -/
theorem pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement_eq_hyperbolicPack
    (K : ℕ) (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement
        (fun r : Fin K ↦ r.val) rho =
      twoChannelHyperbolicPack
        (pairedEtaTopPrefixFinitePartnerLeadingCutoffVector K rho)
        (pairedEtaTopPrefixFiniteAlignedLeadingCutoffVector K rho) := by
  funext j
  rcases j with ⟨r, a⟩
  fin_cases a <;>
    simp [pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement,
      pairedEtaTopPrefixFiniteHyperbolicLeadingArithmeticIncrement,
      twoChannelHyperbolicPack,
      pairedEtaTopPrefixFinitePartnerLeadingCutoffVector,
      pairedEtaTopPrefixFiniteAlignedLeadingCutoffVector]

/-- The actual packed successor eta feature is the generic hyperbolic pack
of its two literal successor colour vectors. -/
theorem pairedEtaTopPrefixFiniteSuccessorCutoffFamilyFeature_eq_hyperbolicPack
    (K : ℕ) (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyFeature
        (pairedEtaTopPrefixFiniteSuccessorCutoff
          (fun r : Fin K ↦ r.val)) rho =
      twoChannelHyperbolicPack
        (pairedEtaTopPrefixFinitePartnerSuccessorCutoffVector K rho)
        (pairedEtaTopPrefixFiniteAlignedSuccessorCutoffVector K rho) := by
  funext j
  rcases j with ⟨r, a⟩
  fin_cases a <;>
    simp [pairedEtaTopPrefixFiniteCutoffFamilyFeature,
      pairedEtaTopPrefixFiniteSuccessorCutoff,
      pairedEtaTopPrefixFiniteHyperbolicFeature,
      pairedEtaTopPrefixFiniteEvenCoordinate,
      pairedEtaTopPrefixFiniteOddCoordinate,
      twoChannelHyperbolicPack,
      pairedEtaTopPrefixFinitePartnerSuccessorCutoffVector,
      pairedEtaTopPrefixFiniteAlignedSuccessorCutoffVector]

/-! ## The actual unintegrated eta trajectory -/

/-- The genuine finite-window leading eta current at one direct odd Gaussian
proper time.  This is the richer trajectory whose integral is the Hilbert
current. -/
def pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory
    (K : ℕ) (T heat : ℝ) : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  finiteGaussianOddHeatCurrent
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
      (fun r : Fin K ↦ r.val)) heat
    (pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent
      (fun r : Fin K ↦ r.val) T)

/-- One ordered channel block along the full odd-heat leading trajectory. -/
def pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock
    (K : ℕ) (T heat : ℝ) (a b : Fin 2) : ℂ :=
  twoChannelMatrixBlockSum
    (pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory K T heat) a b

/-- At every proper time, the actual finite-window odd-heat leading current
is skew-symmetric. -/
theorem pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory_transpose_eq_neg
    (K : ℕ) (T heat : ℝ) :
    (pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory K T heat)ᵀ =
      -pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory K T heat := by
  unfold pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory
  exact finiteGaussianOddHeatCurrent_transpose_of_isSymm _ _ _
    (pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent_isSymm _ T)

/-- Swapping the two eta colours negates the trajectory block at every
proper time. -/
theorem pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock_swap
    (K : ℕ) (T heat : ℝ) (a b : Fin 2) :
    pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock
        K T heat b a =
      -pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock
        K T heat a b := by
  unfold pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock
  exact twoChannelMatrixBlockSum_swap_of_transpose_eq_neg _
    (pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory_transpose_eq_neg
      K T heat) a b

/-- Both same-colour blocks vanish pointwise along the entire odd-heat
trajectory. -/
theorem pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock_self_eq_zero
    (K : ℕ) (T heat : ℝ) (a : Fin 2) :
    pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock
        K T heat a a = 0 := by
  unfold pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock
  exact twoChannelMatrixBlockSum_self_eq_zero_of_transpose_eq_neg _
    (pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory_transpose_eq_neg
      K T heat) a

/-! ## Exact phase-bearing colour data at every heat scale -/

/-- One genuine zero's leading eta current at one direct odd Gaussian
proper time. -/
def pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectory
    (K : ℕ) (rho : NontrivialZetaZero) (heat : ℝ) :
    Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  finiteGaussianOddHeatCurrent
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
      (fun r : Fin K ↦ r.val)) heat
    (pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent
      (fun r : Fin K ↦ r.val) rho)

/-- One ordered channel block of a single zero's scale-resolved current. -/
def pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectoryBlock
    (K : ℕ) (rho : NontrivialZetaZero) (heat : ℝ)
    (a b : Fin 2) : ℂ :=
  twoChannelMatrixBlockSum
    (pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectory K rho heat) a b

/-- The full finite-window trajectory is the exact signed sum of the
scale-resolved currents of its genuine zeros. -/
theorem pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory_eq_zeroSum
    (K : ℕ) (T heat : ℝ) :
    pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory K T heat =
      ∑ rho ∈ spectralZetaZeroWindow T,
        pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectory K rho heat := by
  unfold pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory
    pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectory
    pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent
  exact finiteGaussianOddHeatCurrent_finsetSum _ _ _ _

/-- Exact three-colour form contributed by one genuine zero at one heat
scale, with its analytic multiplicity and complex phase still present. -/
def pairedEtaTopPrefixFiniteOddHeatZeroLeadingMixedChannelFormAt
    (K : ℕ) (rho : NontrivialZetaZero) (heat : ℝ) : ℂ :=
  2 * I * (analyticZetaZeroMultiplicity rho : ℂ) *
    (finiteGaussianOddHeatTransposeBilinearAt K
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val) heat
        (pairedEtaTopPrefixFiniteAlignedLeadingCutoffVector K rho)
        (pairedEtaTopPrefixFinitePartnerLeadingCutoffVector K rho) +
      finiteGaussianOddHeatTransposeBilinearAt K
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val) heat
        (pairedEtaTopPrefixFiniteAlignedLeadingCutoffVector K rho)
        (pairedEtaTopPrefixFinitePartnerSuccessorCutoffVector K rho) +
      finiteGaussianOddHeatTransposeBilinearAt K
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val) heat
        (pairedEtaTopPrefixFiniteAlignedSuccessorCutoffVector K rho)
        (pairedEtaTopPrefixFinitePartnerLeadingCutoffVector K rho))

/-- At every proper time, one zero's surviving `0,1` block is exactly its
three cross-colour form.  Same-colour cancellation is therefore pointwise
in heat scale, not an artefact of the final integration. -/
theorem pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectoryBlock_zero_one_eq_mixedChannelFormAt
    (K : ℕ) (rho : NontrivialZetaZero) (heat : ℝ) :
    pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectoryBlock
        K rho heat 0 1 =
      pairedEtaTopPrefixFiniteOddHeatZeroLeadingMixedChannelFormAt
        K rho heat := by
  unfold pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectoryBlock
    pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectory
    pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent
  rw [finiteGaussianOddHeatCurrent_smul, twoChannelMatrixBlockSum_smul,
    pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement_eq_hyperbolicPack,
    pairedEtaTopPrefixFiniteSuccessorCutoffFamilyFeature_eq_hyperbolicPack]
  have hnode :
      pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
          (fun r : Fin K ↦ r.val) =
        (fun j : Fin K × Fin 2 ↦
          pairedEtaCutoffLogFrequency j.1.val) := rfl
  rw [hnode,
    twoChannelHyperbolicLeadingCurrent_oddHeatBlockAt_eq_crossChannel
      (K := K)
      (frequency := fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val)
      (heat := heat)
      (p := pairedEtaTopPrefixFinitePartnerLeadingCutoffVector K rho)
      (q := pairedEtaTopPrefixFiniteAlignedLeadingCutoffVector K rho)
      (P := pairedEtaTopPrefixFinitePartnerSuccessorCutoffVector K rho)
      (Q := pairedEtaTopPrefixFiniteAlignedSuccessorCutoffVector K rho)]
  unfold pairedEtaTopPrefixFiniteOddHeatZeroLeadingMixedChannelFormAt
  ring

/-- At every heat scale, the complete finite-window `0,1` block is the
exact complex signed zero sum of the three-colour forms.  No norm, absolute
value, or proper-time integration has yet been applied. -/
theorem pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock_zero_one_eq_mixedChannelZeroSumAt
    (K : ℕ) (T heat : ℝ) :
    pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock
        K T heat 0 1 =
      ∑ rho ∈ spectralZetaZeroWindow T,
        pairedEtaTopPrefixFiniteOddHeatZeroLeadingMixedChannelFormAt
          K rho heat := by
  unfold pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock
  rw [pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory_eq_zeroSum,
    twoChannelMatrixBlockSum_finsetSum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  exact
    pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectoryBlock_zero_one_eq_mixedChannelFormAt
      K rho heat

/-- Every integrated eta heat/Hilbert leading block is the genuine integral
of its named full proper-time trajectory.  The downstream reciprocal-gap
observable therefore does not replace the richer scale-resolved carrier. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock_eq_integral_trajectory
    (K : ℕ) (T : ℝ) (a b : Fin 2) :
    pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock K T a b =
      ∫ u : ℝ in Set.Ioi 0,
        pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock
          K T u a b := by
  unfold pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock
    pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent
    pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock
    pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectory
  have hnode :
      pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
          (fun r : Fin K ↦ r.val) =
        (fun j : Fin K × Fin 2 ↦
          pairedEtaCutoffLogFrequency j.1.val) := rfl
  rw [hnode]
  exact twoChannelMatrixBlockSum_oddHeatTransform_eq_integral_current
    (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val) _ a b

/-! ## Actual phase-bearing mixed channel -/

/-- Exact cross-colour odd-heat form contributed by one genuine nontrivial
zero, including its analytic multiplicity. -/
def pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMixedChannelForm
    (K : ℕ) (rho : NontrivialZetaZero) : ℂ :=
  2 * I * (analyticZetaZeroMultiplicity rho : ℂ) *
    (finiteGaussianOddHeatTransposeBilinear
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val)
        (pairedEtaTopPrefixFiniteAlignedLeadingCutoffVector K rho)
        (pairedEtaTopPrefixFinitePartnerLeadingCutoffVector K rho) +
      finiteGaussianOddHeatTransposeBilinear
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val)
        (pairedEtaTopPrefixFiniteAlignedLeadingCutoffVector K rho)
        (pairedEtaTopPrefixFinitePartnerSuccessorCutoffVector K rho) +
      finiteGaussianOddHeatTransposeBilinear
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val)
        (pairedEtaTopPrefixFiniteAlignedSuccessorCutoffVector K rho)
        (pairedEtaTopPrefixFinitePartnerLeadingCutoffVector K rho))

/-- One zero's surviving `0,1` leading block is exactly its three-term
cross-colour form; no same-colour Hilbert form remains. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock_zero_one_eq_mixedChannelForm
    (K : ℕ) (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock K rho 0 1 =
      pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMixedChannelForm
        K rho := by
  unfold pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock
    pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMatrixCurrent
    pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent
  rw [finiteGaussianOddHeatTransform_smul,
    twoChannelMatrixBlockSum_smul,
    pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement_eq_hyperbolicPack,
    pairedEtaTopPrefixFiniteSuccessorCutoffFamilyFeature_eq_hyperbolicPack]
  have hnode :
      pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
          (fun r : Fin K ↦ r.val) =
        (fun j : Fin K × Fin 2 ↦
          pairedEtaCutoffLogFrequency j.1.val) := rfl
  rw [hnode,
    twoChannelHyperbolicLeadingCurrent_oddHeatBlock_eq_crossChannel
      (K := K)
      (frequency := fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val)
      (p := pairedEtaTopPrefixFinitePartnerLeadingCutoffVector K rho)
      (q := pairedEtaTopPrefixFiniteAlignedLeadingCutoffVector K rho)
      (P := pairedEtaTopPrefixFinitePartnerSuccessorCutoffVector K rho)
      (Q := pairedEtaTopPrefixFiniteAlignedSuccessorCutoffVector K rho)]
  unfold pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMixedChannelForm
  ring

/-- The complete surviving mixed-colour leading block is the exact complex
signed sum of the three-term per-zero arithmetic forms, with analytic
multiplicity and every phase retained. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock_zero_one_eq_mixedChannelZeroSum
    (K : ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock K T 0 1 =
      ∑ rho ∈ spectralZetaZeroWindow T,
        pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMixedChannelForm
          K rho := by
  rw [pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock_eq_zeroSum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  exact
    pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock_zero_one_eq_mixedChannelForm
      K rho

/-- One zero's integrated three-colour Hilbert form is exactly the
positive-time integral of its scale-resolved three-colour heat form.  This
commuting edge certifies that the reciprocal-gap summary is downstream of,
and remains linked to, the richer heat trajectory. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMixedChannelForm_eq_integral_at
    (K : ℕ) (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMixedChannelForm K rho =
      ∫ u : ℝ in Set.Ioi 0,
        pairedEtaTopPrefixFiniteOddHeatZeroLeadingMixedChannelFormAt
          K rho u := by
  rw [←
    pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock_zero_one_eq_mixedChannelForm]
  calc
    pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock K rho 0 1 =
        ∫ u : ℝ in Set.Ioi 0,
          pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectoryBlock
            K rho u 0 1 := by
      unfold pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock
        pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMatrixCurrent
        pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectoryBlock
        pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectory
      have hnode :
          pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
              (fun r : Fin K ↦ r.val) =
            (fun j : Fin K × Fin 2 ↦
              pairedEtaCutoffLogFrequency j.1.val) := rfl
      rw [hnode]
      exact twoChannelMatrixBlockSum_oddHeatTransform_eq_integral_current
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val) _ 0 1
    _ = ∫ u : ℝ in Set.Ioi 0,
        pairedEtaTopPrefixFiniteOddHeatZeroLeadingMixedChannelFormAt
          K rho u := by
      congr 1
      funext u
      exact
        pairedEtaTopPrefixFiniteOddHeatZeroLeadingTrajectoryBlock_zero_one_eq_mixedChannelFormAt
          K rho u

/-- The complete integrated eta `0,1` block is the integral of the exact
complex signed three-colour zero sum at each heat scale.  The terminal
identity retains heat scale, channel orientation, analytic multiplicity,
and phase until the final explicitly displayed integration. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock_zero_one_eq_integral_mixedChannelZeroSumAt
    (K : ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock K T 0 1 =
      ∫ u : ℝ in Set.Ioi 0,
        ∑ rho ∈ spectralZetaZeroWindow T,
          pairedEtaTopPrefixFiniteOddHeatZeroLeadingMixedChannelFormAt
            K rho u := by
  rw [pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock_eq_integral_trajectory]
  congr 1
  funext u
  exact
    pairedEtaTopPrefixFiniteOddHeatWindowLeadingTrajectoryBlock_zero_one_eq_mixedChannelZeroSumAt
      K T u

end

end RiemannGaussian
