import RiemannGaussian.RiemannXiSuzukiCarrierCayleySynthesisOperator

/-!
# Bilateral coefficient vectors for off-axis xi nodes

The upper- and lower-half-plane rational carrier features already have exact
finite geometric expansions in opposite Cayley--Hardy orbits.  The bounded
bilateral synthesis operator now permits those expansions to be assembled in
coefficient Hilbert space itself.

This file constructs the corresponding geometric vectors in `ℓ²(ℤ, ℂ)` and
proves that their infinite carrier syntheses are exactly the genuine rational
node features.  Thus every off-axis node has a concrete coefficient-space
preimage.  No assertion is made for real spectral nodes, whose Cayley
parameters lie on the unit circle.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-! ## Backward geometric coefficient vector -/

/-- The bilateral `ℓ²` candidate for the backward expansion with parameter
`a`: its coefficient at frequency `-n` is `(1-a) a^n`. -/
def suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
    (a : ℂ) : ℓ²(ℤ, ℂ) :=
  ∑' n : ℕ, lp.single 2 (-(n : ℤ)) ((1 - a) * a ^ n)

/-- If `a` is strictly contractive, the defining backward geometric series
is absolutely summable in bilateral `ℓ²`. -/
theorem summable_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
    {a : ℂ} (ha : ‖a‖ < 1) :
    Summable (fun n : ℕ ↦
      lp.single 2 (-(n : ℤ)) ((1 - a) * a ^ n) :
        ℕ → ℓ²(ℤ, ℂ)) := by
  apply Summable.of_norm
  have hgeom :=
    (summable_norm_geometric_of_norm_lt_one ha).mul_left ‖1 - a‖
  apply hgeom.congr
  intro n
  rw [lp.norm_single (by norm_num), norm_mul]

/-- The defining backward geometric series has sum equal to the packaged
coefficient vector. -/
theorem hasSum_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
    {a : ℂ} (ha : ‖a‖ < 1) :
    HasSum (fun n : ℕ ↦
      lp.single 2 (-(n : ℤ)) ((1 - a) * a ^ n))
      (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector a) := by
  exact
    (summable_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector ha).hasSum

/-- Synthesizing the backward geometric coefficient vector sums the
backward Hardy-orbit geometric series. -/
theorem hasSum_synthesis_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
    {a : ℂ} (ha : ‖a‖ < 1) :
    HasSum (fun n : ℕ ↦
      ((1 - a) * a ^ n) • suzukiXiCarrierCayleyBackwardOrbit n)
      (suzukiXiCarrierCayleyBilateralSynthesisOperator
        (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector a)) := by
  have hmapped := suzukiXiCarrierCayleyBilateralSynthesisOperator.hasSum
    (hasSum_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector ha)
  simpa only [suzukiXiCarrierCayleyBilateralSynthesisOperator_single,
    suzukiXiCarrierCayleyBackwardOrbit_eq_bilateralOrbit] using hmapped

/-- For an upper-half-plane xi node, the synthesized backward geometric
coefficient vector is exactly its rational carrier feature. -/
theorem suzukiXiCarrierCayleyBilateralSynthesisOperator_backwardNode
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    suzukiXiCarrierCayleyBilateralSynthesisOperator
        (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
          (suzukiXiCarrierCayleyNodeParameter rho)) =
      suzukiXiCarrierNevanlinnaNodeFeatureLp rho := by
  have ha : ‖suzukiXiCarrierCayleyNodeParameter rho‖ < 1 :=
    (norm_suzukiXiCarrierCayleyNodeParameter_lt_one_iff rho).2 hupper
  have hseries :=
    (hasSum_synthesis_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
      ha).tendsto_sum_nat
  have happrox :
      (fun n : ℕ ↦
        ∑ k ∈ Finset.range n,
          ((1 - suzukiXiCarrierCayleyNodeParameter rho) *
              suzukiXiCarrierCayleyNodeParameter rho ^ k) •
            suzukiXiCarrierCayleyBackwardOrbit k) =
        fun n : ℕ ↦
          suzukiXiCarrierCayleyBackwardGeometricApproximation
            (suzukiXiCarrierCayleyNodeParameter rho) n := by
    rfl
  rw [happrox] at hseries
  exact tendsto_nhds_unique hseries
    (tendsto_suzukiXiCarrierCayleyBackwardGeometricApproximation rho hupper)

/-! ## Forward geometric coefficient vector -/

/-- The bilateral `ℓ²` candidate for the forward expansion with parameter
`a`: its coefficient at frequency `n+1` is `(1-a⁻¹) (a⁻¹)^n`. -/
def suzukiXiCarrierCayleyForwardGeometricCoefficientVector
    (a : ℂ) : ℓ²(ℤ, ℂ) :=
  ∑' n : ℕ,
    lp.single 2 ((n + 1 : ℕ) : ℤ) ((1 - a⁻¹) * (a⁻¹) ^ n)

/-- If `a⁻¹` is strictly contractive, the defining forward geometric
series is absolutely summable in bilateral `ℓ²`. -/
theorem summable_suzukiXiCarrierCayleyForwardGeometricCoefficientVector
    {a : ℂ} (ha : ‖a⁻¹‖ < 1) :
    Summable (fun n : ℕ ↦
      lp.single 2 ((n + 1 : ℕ) : ℤ) ((1 - a⁻¹) * (a⁻¹) ^ n) :
        ℕ → ℓ²(ℤ, ℂ)) := by
  apply Summable.of_norm
  have hgeom :=
    (summable_norm_geometric_of_norm_lt_one ha).mul_left ‖1 - a⁻¹‖
  apply hgeom.congr
  intro n
  rw [lp.norm_single (by norm_num), norm_mul]

/-- The defining forward geometric series has sum equal to the packaged
coefficient vector. -/
theorem hasSum_suzukiXiCarrierCayleyForwardGeometricCoefficientVector
    {a : ℂ} (ha : ‖a⁻¹‖ < 1) :
    HasSum (fun n : ℕ ↦
      lp.single 2 ((n + 1 : ℕ) : ℤ) ((1 - a⁻¹) * (a⁻¹) ^ n))
      (suzukiXiCarrierCayleyForwardGeometricCoefficientVector a) := by
  exact
    (summable_suzukiXiCarrierCayleyForwardGeometricCoefficientVector ha).hasSum

/-- Synthesizing the forward geometric coefficient vector sums the forward
Hardy-orbit geometric series. -/
theorem hasSum_synthesis_suzukiXiCarrierCayleyForwardGeometricCoefficientVector
    {a : ℂ} (ha : ‖a⁻¹‖ < 1) :
    HasSum (fun n : ℕ ↦
      ((1 - a⁻¹) * (a⁻¹) ^ n) • suzukiXiCarrierCayleyForwardOrbit n)
      (suzukiXiCarrierCayleyBilateralSynthesisOperator
        (suzukiXiCarrierCayleyForwardGeometricCoefficientVector a)) := by
  have hmapped := suzukiXiCarrierCayleyBilateralSynthesisOperator.hasSum
    (hasSum_suzukiXiCarrierCayleyForwardGeometricCoefficientVector ha)
  simpa only [suzukiXiCarrierCayleyBilateralSynthesisOperator_single,
    suzukiXiCarrierCayleyForwardOrbit_eq_bilateralOrbit] using hmapped

/-- For a lower-half-plane xi node, the synthesized forward geometric
coefficient vector is exactly its rational carrier feature. -/
theorem suzukiXiCarrierCayleyBilateralSynthesisOperator_forwardNode
    (rho : NontrivialZetaZero)
    (hlower : (zetaSpectralCoordinate rho.1).im < 0) :
    suzukiXiCarrierCayleyBilateralSynthesisOperator
        (suzukiXiCarrierCayleyForwardGeometricCoefficientVector
          (suzukiXiCarrierCayleyNodeParameter rho)) =
      suzukiXiCarrierNevanlinnaNodeFeatureLp rho := by
  have ha : 1 < ‖suzukiXiCarrierCayleyNodeParameter rho‖ :=
    (one_lt_norm_suzukiXiCarrierCayleyNodeParameter_iff rho).2 hlower
  have hainv : ‖(suzukiXiCarrierCayleyNodeParameter rho)⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ ha
  have hseries :=
    (hasSum_synthesis_suzukiXiCarrierCayleyForwardGeometricCoefficientVector
      hainv).tendsto_sum_nat
  have happrox :
      (fun n : ℕ ↦
        ∑ k ∈ Finset.range n,
          ((1 - (suzukiXiCarrierCayleyNodeParameter rho)⁻¹) *
              ((suzukiXiCarrierCayleyNodeParameter rho)⁻¹) ^ k) •
            suzukiXiCarrierCayleyForwardOrbit k) =
        fun n : ℕ ↦
          suzukiXiCarrierCayleyForwardGeometricApproximation
            (suzukiXiCarrierCayleyNodeParameter rho) n := by
    rfl
  rw [happrox] at hseries
  exact tendsto_nhds_unique hseries
    (tendsto_suzukiXiCarrierCayleyForwardGeometricApproximation rho hlower)

/-! ## Uniform off-axis node and finite synthesis -/

/-- A single coefficient-space representative selected by the half-plane of
the spectral node.  Its value at a real node is intentionally arbitrary for
the present theorem; correctness is asserted only away from the real axis. -/
def suzukiXiCarrierCayleyOffAxisNodeCoefficientVector
    (rho : NontrivialZetaZero) : ℓ²(ℤ, ℂ) :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
      (suzukiXiCarrierCayleyNodeParameter rho)
  else
    suzukiXiCarrierCayleyForwardGeometricCoefficientVector
      (suzukiXiCarrierCayleyNodeParameter rho)

/-- Every genuine off-axis rational node feature has the selected explicit
bilateral coefficient-space preimage. -/
theorem suzukiXiCarrierCayleyBilateralSynthesisOperator_offAxisNode
    (rho : NontrivialZetaZero)
    (hoffAxis : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    suzukiXiCarrierCayleyBilateralSynthesisOperator
        (suzukiXiCarrierCayleyOffAxisNodeCoefficientVector rho) =
      suzukiXiCarrierNevanlinnaNodeFeatureLp rho := by
  rcases lt_or_gt_of_ne hoffAxis with hlower | hupper
  · rw [suzukiXiCarrierCayleyOffAxisNodeCoefficientVector,
      if_neg (not_lt_of_ge hlower.le)]
    exact suzukiXiCarrierCayleyBilateralSynthesisOperator_forwardNode
      rho hlower
  · rw [suzukiXiCarrierCayleyOffAxisNodeCoefficientVector,
      if_pos hupper]
    exact suzukiXiCarrierCayleyBilateralSynthesisOperator_backwardNode
      rho hupper

/-- The combined bilateral coefficient vector of a finite Cayley-weighted
Suzuki synthesis whose support is intended to be off the real axis. -/
def suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector
    (c : NontrivialZetaZero →₀ ℂ) : ℓ²(ℤ, ℂ) :=
  ∑ rho ∈ c.support,
    (((suzukiXiZeroNormalization rho : ℂ) * c rho) *
        suzukiXiCarrierCayleyNodeParameter rho) •
      suzukiXiCarrierCayleyOffAxisNodeCoefficientVector rho

/-- On an off-axis-supported finite family, the Cayley-weighted rational
synthesis is exactly the bounded bilateral synthesis of the combined
geometric coefficient vector. -/
theorem suzukiXiCarrierCayleyBilateralSynthesisOperator_weightedOffAxis
    (c : NontrivialZetaZero →₀ ℂ)
    (hoffAxis : ∀ rho ∈ c.support,
      (zetaSpectralCoordinate rho.1).im ≠ 0) :
    suzukiXiCarrierCayleyBilateralSynthesisOperator
        (suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector c) =
      suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis c := by
  unfold suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector
    suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [map_smul,
    suzukiXiCarrierCayleyBilateralSynthesisOperator_offAxisNode rho
      (hoffAxis rho hrho)]

/-- Coefficient-space control of every finite off-axis Cayley-weighted
Suzuki synthesis. -/
theorem norm_sq_suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_le_offAxis
    (c : NontrivialZetaZero →₀ ℂ)
    (hoffAxis : ∀ rho ∈ c.support,
      (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ‖suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis c‖ ^ 2 ≤
      Real.pi *
        ‖suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector c‖ ^ 2 := by
  rw [←
    suzukiXiCarrierCayleyBilateralSynthesisOperator_weightedOffAxis c hoffAxis]
  exact
    norm_sq_suzukiXiCarrierCayleyBilateralSynthesisOperator_apply_le
      (suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector c)

end

end RiemannGaussian
