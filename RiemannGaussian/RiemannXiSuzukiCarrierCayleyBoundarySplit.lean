import RiemannGaussian.RiemannXiSuzukiCarrierCayleyNodeEnergy

/-!
# Exact off-axis and real-boundary split

Every finite Cayley-weighted Suzuki family splits canonically into nodes away
from the real spectral axis and nodes on that axis. This file packages the
finite synthesis as a complex-linear map, proves the exact split, realizes
the off-axis part through the bounded bilateral coefficient synthesis, and
isolates the remaining real-node term in both an equality and a norm bound.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- The restriction of a finite zero family to nonreal spectral nodes. -/
def suzukiXiCarrierCayleyOffAxisPart
    (c : NontrivialZetaZero →₀ ℂ) : NontrivialZetaZero →₀ ℂ :=
  c.filter fun rho ↦ (zetaSpectralCoordinate rho.1).im ≠ 0

/-- The restriction of a finite zero family to real spectral nodes. -/
def suzukiXiCarrierCayleyRealAxisPart
    (c : NontrivialZetaZero →₀ ℂ) : NontrivialZetaZero →₀ ℂ :=
  c.filter fun rho ↦ ¬(zetaSpectralCoordinate rho.1).im ≠ 0

/-- The off-axis and real-axis restrictions reconstruct the original finite
family exactly. -/
theorem suzukiXiCarrierCayleyOffAxisPart_add_realAxisPart
    (c : NontrivialZetaZero →₀ ℂ) :
    suzukiXiCarrierCayleyOffAxisPart c +
        suzukiXiCarrierCayleyRealAxisPart c = c := by
  exact Finsupp.filter_add_filter_not c
    (fun rho ↦ (zetaSpectralCoordinate rho.1).im ≠ 0)

/-- Every node in the support of the off-axis restriction is genuinely away
from the real spectral axis. -/
theorem suzukiXiCarrierCayleyOffAxisPart_support
    (c : NontrivialZetaZero →₀ ℂ) (rho : NontrivialZetaZero)
    (hrho : rho ∈ (suzukiXiCarrierCayleyOffAxisPart c).support) :
    (zetaSpectralCoordinate rho.1).im ≠ 0 := by
  rw [suzukiXiCarrierCayleyOffAxisPart, Finsupp.support_filter,
    Finset.mem_filter] at hrho
  exact hrho.2

/-- Every node in the support of the real-axis restriction lies on the real
spectral axis. -/
theorem suzukiXiCarrierCayleyRealAxisPart_support
    (c : NontrivialZetaZero →₀ ℂ) (rho : NontrivialZetaZero)
    (hrho : rho ∈ (suzukiXiCarrierCayleyRealAxisPart c).support) :
    (zetaSpectralCoordinate rho.1).im = 0 := by
  rw [suzukiXiCarrierCayleyRealAxisPart, Finsupp.support_filter,
    Finset.mem_filter] at hrho
  exact Classical.not_not.mp hrho.2

/-- The coordinatewise complex-linear contribution of one node to the
Cayley-weighted finite synthesis. -/
def suzukiXiCarrierNevanlinnaCayleyWeightedCoordinateLinearMap
    (rho : NontrivialZetaZero) :
    ℂ →ₗ[ℂ] Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure where
  toFun c :=
    (((suzukiXiZeroNormalization rho : ℂ) * c) *
        suzukiXiCarrierCayleyNodeParameter rho) •
      suzukiXiCarrierNevanlinnaNodeFeatureLp rho
  map_add' c d := by
    simp only [mul_add, add_mul, add_smul]
  map_smul' c d := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [smul_smul]
    congr 1
    ring

/-- The Cayley-weighted finite synthesis as an actual complex-linear map on
finitely supported zero coefficients. -/
def suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesisLinearMap :
    (NontrivialZetaZero →₀ ℂ) →ₗ[ℂ]
      Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  Finsupp.lsum ℂ
    suzukiXiCarrierNevanlinnaCayleyWeightedCoordinateLinearMap

/-- The linear-map packaging agrees definitionally with the original finite
support synthesis. -/
@[simp] theorem suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesisLinearMap_apply
    (c : NontrivialZetaZero →₀ ℂ) :
    suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesisLinearMap c =
      suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis c := by
  rfl

/-- Every finite Cayley-weighted synthesis is exactly the sum of its
off-axis and real-boundary syntheses. -/
theorem suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_boundarySplit
    (c : NontrivialZetaZero →₀ ℂ) :
    suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis c =
      suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis
          (suzukiXiCarrierCayleyOffAxisPart c) +
        suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis
          (suzukiXiCarrierCayleyRealAxisPart c) := by
  rw [←
    suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesisLinearMap_apply]
  conv_lhs =>
    rw [← suzukiXiCarrierCayleyOffAxisPart_add_realAxisPart c]
  rw [map_add]
  simp only [
    suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesisLinearMap_apply]

/-- The exact boundary split with the off-axis summand represented by the
bounded bilateral coefficient synthesis operator. -/
theorem suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_boundarySplit_operator
    (c : NontrivialZetaZero →₀ ℂ) :
    suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis c =
      suzukiXiCarrierCayleyBilateralSynthesisOperator
          (suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector
            (suzukiXiCarrierCayleyOffAxisPart c)) +
        suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis
          (suzukiXiCarrierCayleyRealAxisPart c) := by
  rw [suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_boundarySplit]
  rw [suzukiXiCarrierCayleyBilateralSynthesisOperator_weightedOffAxis
    (suzukiXiCarrierCayleyOffAxisPart c)
    (fun rho hrho ↦ suzukiXiCarrierCayleyOffAxisPart_support c rho hrho)]

/-- After subtracting the explicit real-boundary remainder, every finite
Cayley-weighted synthesis is exactly the bounded synthesis of its combined
off-axis coefficient vector. -/
theorem suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_sub_realAxisPart
    (c : NontrivialZetaZero →₀ ℂ) :
    suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis c -
        suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis
          (suzukiXiCarrierCayleyRealAxisPart c) =
      suzukiXiCarrierCayleyBilateralSynthesisOperator
        (suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector
          (suzukiXiCarrierCayleyOffAxisPart c)) := by
  rw [
    suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_boundarySplit_operator]
  exact add_sub_cancel_right _ _

/-- Quantitative control of the full finite synthesis modulo its literal
real-boundary contribution. -/
theorem norm_sq_suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_sub_realAxisPart_le
    (c : NontrivialZetaZero →₀ ℂ) :
    ‖suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis c -
        suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis
          (suzukiXiCarrierCayleyRealAxisPart c)‖ ^ 2 ≤
      Real.pi *
        ‖suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector
          (suzukiXiCarrierCayleyOffAxisPart c)‖ ^ 2 := by
  rw [
    suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_sub_realAxisPart]
  exact norm_sq_suzukiXiCarrierCayleyBilateralSynthesisOperator_apply_le _

end

end RiemannGaussian
