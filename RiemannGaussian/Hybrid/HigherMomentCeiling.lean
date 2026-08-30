import RiemannGaussian.Hybrid.EtaSpectralHeatArithmeticBridge

/-!
# A sharp degree-four moment certificate

This module formalizes the finite moment calculation suggested by the signed
heat ceiling steer.  It is deliberately abstract: no eta arithmetic theorem
is assumed to provide the moments below.

A nonnegative finite weighted model is required to have moments

`m₀ = 1`, `m₁ = 1`, `m₂ = 4/3`, `m₃ = 2`, `m₄ = 13/4`.

The explicit quadratic witness

`p(x) = 1 - (7/4)x + (2/3)x²`

has weighted square exactly `5/36`.  Since `p(0)=1`, the total weight at zero
is at most `5/36`, so the associated certificate `1 - 2 * zeroMass` is at
least `13/18`.

Lean also constructs a nonnegative three-atom model attaining equality.  The
bound is therefore the exact ceiling of this degree-four information class,
not merely a lower estimate.  This proves that extra moments can strengthen a
low-moment certificate, but it does not connect these five moments to the
literal eta window and does not prove a zeta-zero proportion.
-/

open Finset
open scoped BigOperators Classical

namespace RiemannGaussian

noncomputable section

/-! ## Abstract moment models and the quadratic witness -/

/-- A finite nonnegative weighted model with the five normalized moments used
by the degree-four certificate experiment. -/
structure DegreeFourMomentModel (ι : Type*) [Fintype ι] where
  /-- Nonnegative mass at each atom. -/
  weight : ι → ℝ
  /-- Real location of each atom. -/
  node : ι → ℝ
  /-- Every atom weight is nonnegative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i
  /-- Zeroth moment. -/
  moment_zero : ∑ i, weight i = 1
  /-- First moment. -/
  moment_one : ∑ i, weight i * node i = 1
  /-- Second moment. -/
  moment_two : ∑ i, weight i * node i ^ 2 = (4 : ℝ) / 3
  /-- Third moment. -/
  moment_three : ∑ i, weight i * node i ^ 3 = 2
  /-- Fourth moment. -/
  moment_four : ∑ i, weight i * node i ^ 4 = (13 : ℝ) / 4

/-- The complete weighted spectral heat-moment hierarchy of a degree-four
model.  The prescribed moments are its first five zero-scale values. -/
def DegreeFourMomentModel.heatMoment
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι)
    (order : ℕ) (u : ℝ) : ℝ :=
  ∑ i, M.weight i * M.node i ^ order *
    Real.exp (-u * M.node i ^ 2)

/-- At zero scale, the weighted heat hierarchy is the ordinary weighted
moment sequence. -/
theorem DegreeFourMomentModel.heatMoment_zeroScale
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) (order : ℕ) :
    M.heatMoment order 0 = ∑ i, M.weight i * M.node i ^ order := by
  simp [DegreeFourMomentModel.heatMoment]

/-- Differentiating a weighted heat moment raises its order by two and changes
the sign. -/
theorem DegreeFourMomentModel.hasDerivAt_heatMoment
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι)
    (order : ℕ) (u : ℝ) :
    HasDerivAt (M.heatMoment order) (-M.heatMoment (order + 2) u) u := by
  have hsum : HasDerivAt
      (fun v : ℝ ↦ ∑ i, M.weight i *
        (M.node i ^ order * Real.exp (-v * M.node i ^ 2)))
      (∑ i, M.weight i *
        (-M.node i ^ (order + 2) * Real.exp (-u * M.node i ^ 2))) u := by
    exact HasDerivAt.fun_sum fun i _hi ↦
      (HermitianRankTrace.hasDerivAt_heatMomentScalar
        (M.node i) order u).const_mul (M.weight i)
  convert hsum using 1
  · funext v
    unfold DegreeFourMomentModel.heatMoment
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  · unfold DegreeFourMomentModel.heatMoment
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring

/-- The normalized zeroth heat moment starts at one. -/
@[simp] theorem DegreeFourMomentModel.heatMoment_zero_zero
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    M.heatMoment 0 0 = 1 := by
  rw [M.heatMoment_zeroScale]
  simpa using M.moment_zero

/-- The normalized first heat moment starts at one. -/
@[simp] theorem DegreeFourMomentModel.heatMoment_one_zero
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    M.heatMoment 1 0 = 1 := by
  rw [M.heatMoment_zeroScale]
  simpa using M.moment_one

/-- The normalized second heat moment starts at `4/3`. -/
@[simp] theorem DegreeFourMomentModel.heatMoment_two_zero
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    M.heatMoment 2 0 = (4 : ℝ) / 3 := by
  rw [M.heatMoment_zeroScale]
  exact M.moment_two

/-- The normalized third heat moment starts at two. -/
@[simp] theorem DegreeFourMomentModel.heatMoment_three_zero
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    M.heatMoment 3 0 = 2 := by
  rw [M.heatMoment_zeroScale]
  exact M.moment_three

/-- The normalized fourth heat moment starts at `13/4`. -/
@[simp] theorem DegreeFourMomentModel.heatMoment_four_zero
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    M.heatMoment 4 0 = (13 : ℝ) / 4 := by
  rw [M.heatMoment_zeroScale]
  exact M.moment_four

/-- The total mass carried by atoms at zero. -/
def DegreeFourMomentModel.zeroMass
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) : ℝ :=
  ∑ i, if M.node i = 0 then M.weight i else 0

/-- The normalized good-direction certificate associated with the possible
zero atom. -/
def DegreeFourMomentModel.certificate
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) : ℝ :=
  1 - 2 * M.zeroMass

/-- The degree-two Christoffel witness normalized to take value one at zero. -/
def degreeFourMomentWitness (x : ℝ) : ℝ :=
  1 - (7 / 4 : ℝ) * x + (2 / 3 : ℝ) * x ^ 2

/-- The witness is one at the distinguished zero location. -/
@[simp] theorem degreeFourMomentWitness_zero :
    degreeFourMomentWitness 0 = 1 := by
  norm_num [degreeFourMomentWitness]

/-- The five prescribed moments evaluate the squared quadratic witness
exactly to `5/36`. -/
theorem DegreeFourMomentModel.sum_weight_mul_witness_sq_eq
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    ∑ i, M.weight i * degreeFourMomentWitness (M.node i) ^ 2 =
      (5 : ℝ) / 36 := by
  calc
    ∑ i, M.weight i * degreeFourMomentWitness (M.node i) ^ 2 =
        ∑ i, (M.weight i -
          (7 / 2 : ℝ) * (M.weight i * M.node i) +
          (211 / 48 : ℝ) * (M.weight i * M.node i ^ 2) -
          (7 / 3 : ℝ) * (M.weight i * M.node i ^ 3) +
          (4 / 9 : ℝ) * (M.weight i * M.node i ^ 4)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      unfold degreeFourMomentWitness
      ring
    _ = (∑ i, M.weight i) -
          (7 / 2 : ℝ) * (∑ i, M.weight i * M.node i) +
          (211 / 48 : ℝ) * (∑ i, M.weight i * M.node i ^ 2) -
          (7 / 3 : ℝ) * (∑ i, M.weight i * M.node i ^ 3) +
          (4 / 9 : ℝ) * (∑ i, M.weight i * M.node i ^ 4) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]
    _ = (5 : ℝ) / 36 := by
      rw [M.moment_zero, M.moment_one, M.moment_two,
        M.moment_three, M.moment_four]
      norm_num

/-- No nonnegative model with the five prescribed moments can place more
than `5/36` of its mass at zero. -/
theorem DegreeFourMomentModel.zeroMass_le_five_thirtySix
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    M.zeroMass ≤ (5 : ℝ) / 36 := by
  calc
    M.zeroMass ≤
        ∑ i, M.weight i * degreeFourMomentWitness (M.node i) ^ 2 := by
      unfold DegreeFourMomentModel.zeroMass
      apply Finset.sum_le_sum
      intro i _hi
      by_cases hi : M.node i = 0
      · simp [hi]
      · simp only [hi, ↓reduceIte]
        exact mul_nonneg (M.weight_nonneg i)
          (sq_nonneg (degreeFourMomentWitness (M.node i)))
    _ = (5 : ℝ) / 36 := M.sum_weight_mul_witness_sq_eq

/-- Every degree-four model has certificate at least `13/18`. -/
theorem DegreeFourMomentModel.thirteen_eighteen_le_certificate
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    (13 : ℝ) / 18 ≤ M.certificate := by
  unfold DegreeFourMomentModel.certificate
  linarith [M.zeroMass_le_five_thirtySix]

/-! ## A sharp three-atom model -/

/-- The three atom locations of an extremal model.  The two nonzero atoms are
the roots of the quadratic witness. -/
def degreeFourSharpNode : Fin 3 → ℝ :=
  ![0, (21 - Real.sqrt 57) / 16, (21 + Real.sqrt 57) / 16]

/-- The three nonnegative weights of the extremal model. -/
def degreeFourSharpWeight : Fin 3 → ℝ :=
  ![(5 : ℝ) / 36,
    (31 : ℝ) / 72 + 25 * Real.sqrt 57 / 1368,
    (31 : ℝ) / 72 - 25 * Real.sqrt 57 / 1368]

/-- Every weight in the sharp three-atom model is nonnegative. -/
theorem degreeFourSharpWeight_nonneg (i : Fin 3) :
    0 ≤ degreeFourSharpWeight i := by
  have hsqrt : 0 ≤ Real.sqrt 57 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 57) ^ 2 = 57 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtLe : Real.sqrt 57 ≤ 8 := by
    nlinarith
  fin_cases i
  · norm_num [degreeFourSharpWeight]
  · change 0 ≤ (31 : ℝ) / 72 + 25 * Real.sqrt 57 / 1368
    positivity
  · change 0 ≤ (31 : ℝ) / 72 - 25 * Real.sqrt 57 / 1368
    rw [sub_nonneg]
    calc
      25 * Real.sqrt 57 / 1368 ≤ 25 * 8 / 1368 := by gcongr
      _ ≤ (31 : ℝ) / 72 := by norm_num

/-- The sharp weights have total mass one. -/
theorem degreeFourSharpMoment_zero :
    ∑ i, degreeFourSharpWeight i = 1 := by
  simp [degreeFourSharpWeight, Fin.sum_univ_succ]
  ring

/-- The sharp model has first moment one. -/
theorem degreeFourSharpMoment_one :
    ∑ i, degreeFourSharpWeight i * degreeFourSharpNode i = 1 := by
  have hsqrtSq : (Real.sqrt 57) ^ 2 = 57 :=
    Real.sq_sqrt (by norm_num)
  simp [degreeFourSharpWeight, degreeFourSharpNode, Fin.sum_univ_succ]
  nlinarith

/-- The sharp model has second moment `4/3`. -/
theorem degreeFourSharpMoment_two :
    ∑ i, degreeFourSharpWeight i * degreeFourSharpNode i ^ 2 =
      (4 : ℝ) / 3 := by
  have hsqrtSq : (Real.sqrt 57) ^ 2 = 57 :=
    Real.sq_sqrt (by norm_num)
  simp [degreeFourSharpWeight, degreeFourSharpNode, Fin.sum_univ_succ]
  nlinarith

/-- The sharp model has third moment two. -/
theorem degreeFourSharpMoment_three :
    ∑ i, degreeFourSharpWeight i * degreeFourSharpNode i ^ 3 = 2 := by
  have hsqrtSq : (Real.sqrt 57) ^ 2 = 57 :=
    Real.sq_sqrt (by norm_num)
  simp [degreeFourSharpWeight, degreeFourSharpNode, Fin.sum_univ_succ]
  nlinarith

/-- The sharp model has fourth moment `13/4`. -/
theorem degreeFourSharpMoment_four :
    ∑ i, degreeFourSharpWeight i * degreeFourSharpNode i ^ 4 =
      (13 : ℝ) / 4 := by
  have hsqrtSq : (Real.sqrt 57) ^ 2 = 57 :=
    Real.sq_sqrt (by norm_num)
  simp [degreeFourSharpWeight, degreeFourSharpNode, Fin.sum_univ_succ]
  nlinarith

/-- The explicit three-atom model realizing the prescribed five moments. -/
def degreeFourSharpModel : DegreeFourMomentModel (Fin 3) where
  weight := degreeFourSharpWeight
  node := degreeFourSharpNode
  weight_nonneg := degreeFourSharpWeight_nonneg
  moment_zero := degreeFourSharpMoment_zero
  moment_one := degreeFourSharpMoment_one
  moment_two := degreeFourSharpMoment_two
  moment_three := degreeFourSharpMoment_three
  moment_four := degreeFourSharpMoment_four

/-- The smaller nonzero sharp atom is strictly positive. -/
theorem degreeFourSharpNode_one_pos :
    0 < degreeFourSharpNode 1 := by
  have hsqrt : 0 ≤ Real.sqrt 57 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 57) ^ 2 = 57 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtLe : Real.sqrt 57 ≤ 8 := by
    nlinarith
  simp [degreeFourSharpNode]
  linarith

/-- The larger nonzero sharp atom is strictly positive. -/
theorem degreeFourSharpNode_two_pos :
    0 < degreeFourSharpNode 2 := by
  have hsqrt : 0 ≤ Real.sqrt 57 := Real.sqrt_nonneg _
  simp [degreeFourSharpNode]
  positivity

/-- The sharp model places exactly `5/36` of its mass at zero. -/
theorem degreeFourSharpModel_zeroMass :
    degreeFourSharpModel.zeroMass = (5 : ℝ) / 36 := by
  have hone : (21 : ℝ) - Real.sqrt 57 ≠ 0 := by
    have h := degreeFourSharpNode_one_pos
    simp [degreeFourSharpNode] at h
    linarith
  have htwo : (21 : ℝ) + Real.sqrt 57 ≠ 0 := by
    have h := degreeFourSharpNode_two_pos
    simp [degreeFourSharpNode] at h
    linarith
  simp [DegreeFourMomentModel.zeroMass, degreeFourSharpModel,
    degreeFourSharpNode, degreeFourSharpWeight, Fin.sum_univ_succ,
    hone, htwo]

/-- The universal `13/18` lower bound is attained by the sharp model.  Hence
the degree-four certificate cannot force a larger value without additional
observables. -/
theorem degreeFourSharpModel_certificate :
    degreeFourSharpModel.certificate = (13 : ℝ) / 18 := by
  unfold DegreeFourMomentModel.certificate
  rw [degreeFourSharpModel_zeroMass]
  norm_num

/-- The `13/18` lower bound holds for every finite degree-four model and is
simultaneously attained by the explicit three-atom model. -/
theorem DegreeFourMomentModel.thirteen_eighteen_bound_attained
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    (13 : ℝ) / 18 ≤ M.certificate ∧
      degreeFourSharpModel.certificate = (13 : ℝ) / 18 :=
  ⟨M.thirteen_eighteen_le_certificate,
    degreeFourSharpModel_certificate⟩

end

end RiemannGaussian
