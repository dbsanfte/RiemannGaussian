import RiemannGaussian.RiemannXiSuzukiCarrierCayleyBoundarySplit

/-!
# Explicit Hardy Gram kernel for off-axis xi coefficients

This file computes the coefficient-space geometry that was hidden behind the
bounded bilateral Cayley synthesis. Backward geometric vectors have an exact
Szegő kernel, forward reciprocal-geometric vectors have the corresponding
exterior kernel, and the two frequency halves are exactly orthogonal.

These formulas define an explicit finite off-axis Gram quadratic. Lean proves
that this quadratic is exactly the squared `ℓ²(ℤ, ℂ)` norm of the combined
Cayley-weighted coefficient vector. Consequently all same-half-plane cross
terms—and therefore all available cancellation—remain visible in the bound
for finite carrier synthesis.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- A negative-frequency coordinate of a contractive backward geometric
vector is its defining geometric coefficient. -/
theorem suzukiXiCarrierCayleyBackwardGeometricCoefficientVector_apply_neg
    {a : ℂ} (ha : ‖a‖ < 1) (m : ℕ) :
    suzukiXiCarrierCayleyBackwardGeometricCoefficientVector a (-(m : ℤ)) =
      (1 - a) * a ^ m := by
  have hmap :=
    (lp.evalCLM ℂ (fun _ : ℤ ↦ ℂ) 2 (-(m : ℤ))).hasSum
      (hasSum_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector ha)
  change HasSum
    (fun n : ℕ ↦
      (lp.single 2 (-(n : ℤ)) ((1 - a) * a ^ n) : ℓ²(ℤ, ℂ))
        (-(m : ℤ)))
    (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector a (-(m : ℤ)))
    at hmap
  apply hmap.unique
  convert hasSum_ite_eq m ((1 - a) * a ^ m) using 1
  ext n
  by_cases hnm : n = m
  · subst n
    simp only [lp.single_apply_self, if_pos]
  · rw [lp.single_apply_ne]
    · simp [hnm]
    · intro h
      apply hnm
      exact_mod_cast neg_inj.mp h.symm

/-- Every strictly positive-frequency coordinate of a backward geometric
vector vanishes. -/
theorem suzukiXiCarrierCayleyBackwardGeometricCoefficientVector_apply_pos
    {a : ℂ} (ha : ‖a‖ < 1) (m : ℕ) :
    suzukiXiCarrierCayleyBackwardGeometricCoefficientVector a
        ((m + 1 : ℕ) : ℤ) = 0 := by
  have hmap :=
    (lp.evalCLM ℂ (fun _ : ℤ ↦ ℂ) 2 ((m + 1 : ℕ) : ℤ)).hasSum
      (hasSum_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector ha)
  change HasSum
    (fun n : ℕ ↦
      (lp.single 2 (-(n : ℤ)) ((1 - a) * a ^ n) : ℓ²(ℤ, ℂ))
        ((m + 1 : ℕ) : ℤ))
    (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector a
      ((m + 1 : ℕ) : ℤ)) at hmap
  apply hmap.unique
  have hterm : ∀ n : ℕ,
      (lp.single 2 (-(n : ℤ)) ((1 - a) * a ^ n) : ℓ²(ℤ, ℂ))
          ((m + 1 : ℕ) : ℤ) = 0 := by
    intro n
    rw [lp.single_apply_ne]
    intro h
    have hpos : (0 : ℤ) < ((m + 1 : ℕ) : ℤ) := by omega
    have hnonpos : -(n : ℤ) ≤ 0 := neg_nonpos.mpr (Int.natCast_nonneg n)
    omega
  simpa only [hterm] using (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℂ)) 0)

/-- Exact Szegő inner-product kernel for two contractive backward geometric
coefficient vectors. -/
theorem inner_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
    {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    inner ℂ
        (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector a)
        (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector b) =
      conj (1 - a) * (1 - b) * (1 - conj a * b)⁻¹ := by
  have hbase :=
    (hasSum_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
      ha).tendsto_sum_nat
  have hinner :=
    Filter.Tendsto.inner (𝕜 := ℂ) hbase
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ ↦
          suzukiXiCarrierCayleyBackwardGeometricCoefficientVector b)
        atTop
        (𝓝 (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector b)))
  have hseq :
      Tendsto
          (fun N : ℕ ↦
            ∑ n ∈ Finset.range N,
              inner ℂ ((1 - a) * a ^ n) ((1 - b) * b ^ n))
          atTop
          (𝓝 (inner ℂ
            (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector a)
            (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector b))) := by
    convert hinner using 1
    ext N
    simp only [sum_inner, lp.inner_single_left,
      suzukiXiCarrierCayleyBackwardGeometricCoefficientVector_apply_neg hb]
  have hq : ‖conj a * b‖ < 1 := by
    rw [norm_mul, norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg b]
  have hsummable : Summable (fun n : ℕ ↦
      inner ℂ ((1 - a) * a ^ n) ((1 - b) * b ^ n)) := by
    have hgeom :=
      (summable_geometric_of_norm_lt_one hq).mul_left
        (conj (1 - a) * (1 - b))
    apply hgeom.congr
    intro n
    simp only [RCLike.inner_apply', map_mul, map_sub, map_one, map_pow]
    ring
  have htsum :
      ∑' n : ℕ, inner ℂ ((1 - a) * a ^ n) ((1 - b) * b ^ n) =
        conj (1 - a) * (1 - b) * (1 - conj a * b)⁻¹ := by
    calc
      ∑' n : ℕ, inner ℂ ((1 - a) * a ^ n) ((1 - b) * b ^ n) =
          ∑' n : ℕ,
            (conj (1 - a) * (1 - b)) * (conj a * b) ^ n := by
              apply tsum_congr
              intro n
              simp only [RCLike.inner_apply', map_mul, map_sub, map_one,
                map_pow]
              ring
      _ = (conj (1 - a) * (1 - b)) *
          ∑' n : ℕ, (conj a * b) ^ n := by
        rw [tsum_mul_left]
      _ = conj (1 - a) * (1 - b) * (1 - conj a * b)⁻¹ := by
        rw [tsum_geometric_of_norm_lt_one hq]
  rw [← htsum]
  exact tendsto_nhds_unique hseq hsummable.hasSum.tendsto_sum_nat

/-- A strictly positive-frequency coordinate of a contractive forward
geometric vector is its defining reciprocal-geometric coefficient. -/
theorem suzukiXiCarrierCayleyForwardGeometricCoefficientVector_apply_pos
    {a : ℂ} (ha : ‖a⁻¹‖ < 1) (m : ℕ) :
    suzukiXiCarrierCayleyForwardGeometricCoefficientVector a
        ((m + 1 : ℕ) : ℤ) =
      (1 - a⁻¹) * (a⁻¹) ^ m := by
  have hmap :=
    (lp.evalCLM ℂ (fun _ : ℤ ↦ ℂ) 2 ((m + 1 : ℕ) : ℤ)).hasSum
      (hasSum_suzukiXiCarrierCayleyForwardGeometricCoefficientVector ha)
  change HasSum
    (fun n : ℕ ↦
      (lp.single 2 ((n + 1 : ℕ) : ℤ)
          ((1 - a⁻¹) * (a⁻¹) ^ n) : ℓ²(ℤ, ℂ))
        ((m + 1 : ℕ) : ℤ))
    (suzukiXiCarrierCayleyForwardGeometricCoefficientVector a
      ((m + 1 : ℕ) : ℤ)) at hmap
  apply hmap.unique
  convert hasSum_ite_eq m ((1 - a⁻¹) * (a⁻¹) ^ m) using 1
  ext n
  by_cases hnm : n = m
  · subst n
    simp only [lp.single_apply_self, if_pos]
  · rw [lp.single_apply_ne]
    · simp [hnm]
    · intro h
      apply hnm
      have hplus : m + 1 = n + 1 := by exact_mod_cast h
      exact (Nat.add_right_cancel hplus).symm

/-- Every nonpositive-frequency coordinate of a forward geometric vector
vanishes. -/
theorem suzukiXiCarrierCayleyForwardGeometricCoefficientVector_apply_neg
    {a : ℂ} (ha : ‖a⁻¹‖ < 1) (m : ℕ) :
    suzukiXiCarrierCayleyForwardGeometricCoefficientVector a (-(m : ℤ)) =
      0 := by
  have hmap :=
    (lp.evalCLM ℂ (fun _ : ℤ ↦ ℂ) 2 (-(m : ℤ))).hasSum
      (hasSum_suzukiXiCarrierCayleyForwardGeometricCoefficientVector ha)
  change HasSum
    (fun n : ℕ ↦
      (lp.single 2 ((n + 1 : ℕ) : ℤ)
          ((1 - a⁻¹) * (a⁻¹) ^ n) : ℓ²(ℤ, ℂ))
        (-(m : ℤ)))
    (suzukiXiCarrierCayleyForwardGeometricCoefficientVector a (-(m : ℤ)))
    at hmap
  apply hmap.unique
  have hterm : ∀ n : ℕ,
      (lp.single 2 ((n + 1 : ℕ) : ℤ)
          ((1 - a⁻¹) * (a⁻¹) ^ n) : ℓ²(ℤ, ℂ)) (-(m : ℤ)) = 0 := by
    intro n
    rw [lp.single_apply_ne]
    intro h
    have hnonpos : -(m : ℤ) ≤ 0 := neg_nonpos.mpr (Int.natCast_nonneg m)
    have hpos : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) := by omega
    omega
  simpa only [hterm] using (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℂ)) 0)

/-- Exact exterior Szegő inner-product kernel for two contractive reciprocal
forward geometric coefficient vectors. -/
theorem inner_suzukiXiCarrierCayleyForwardGeometricCoefficientVector
    {a b : ℂ} (ha : ‖a⁻¹‖ < 1) (hb : ‖b⁻¹‖ < 1) :
    inner ℂ
        (suzukiXiCarrierCayleyForwardGeometricCoefficientVector a)
        (suzukiXiCarrierCayleyForwardGeometricCoefficientVector b) =
      conj (1 - a⁻¹) * (1 - b⁻¹) *
        (1 - conj (a⁻¹) * b⁻¹)⁻¹ := by
  have hbase :=
    (hasSum_suzukiXiCarrierCayleyForwardGeometricCoefficientVector
      ha).tendsto_sum_nat
  have hinner :=
    Filter.Tendsto.inner (𝕜 := ℂ) hbase
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ ↦
          suzukiXiCarrierCayleyForwardGeometricCoefficientVector b)
        atTop
        (𝓝 (suzukiXiCarrierCayleyForwardGeometricCoefficientVector b)))
  have hseq :
      Tendsto
          (fun N : ℕ ↦
            ∑ n ∈ Finset.range N,
              inner ℂ ((1 - a⁻¹) * (a⁻¹) ^ n)
                ((1 - b⁻¹) * (b⁻¹) ^ n))
          atTop
          (𝓝 (inner ℂ
            (suzukiXiCarrierCayleyForwardGeometricCoefficientVector a)
            (suzukiXiCarrierCayleyForwardGeometricCoefficientVector b))) := by
    convert hinner using 1
    ext N
    simp only [sum_inner, lp.inner_single_left,
      suzukiXiCarrierCayleyForwardGeometricCoefficientVector_apply_pos hb]
  have hq : ‖conj (a⁻¹) * b⁻¹‖ < 1 := by
    rw [norm_mul, norm_conj]
    nlinarith [norm_nonneg a⁻¹, norm_nonneg b⁻¹]
  have hsummable : Summable (fun n : ℕ ↦
      inner ℂ ((1 - a⁻¹) * (a⁻¹) ^ n)
        ((1 - b⁻¹) * (b⁻¹) ^ n)) := by
    have hgeom :=
      (summable_geometric_of_norm_lt_one hq).mul_left
        (conj (1 - a⁻¹) * (1 - b⁻¹))
    apply hgeom.congr
    intro n
    simp only [RCLike.inner_apply', map_mul, map_sub, map_one, map_pow]
    ring
  have htsum :
      ∑' n : ℕ,
          inner ℂ ((1 - a⁻¹) * (a⁻¹) ^ n)
            ((1 - b⁻¹) * (b⁻¹) ^ n) =
        conj (1 - a⁻¹) * (1 - b⁻¹) *
          (1 - conj (a⁻¹) * b⁻¹)⁻¹ := by
    calc
      ∑' n : ℕ,
          inner ℂ ((1 - a⁻¹) * (a⁻¹) ^ n)
            ((1 - b⁻¹) * (b⁻¹) ^ n) =
          ∑' n : ℕ,
            (conj (1 - a⁻¹) * (1 - b⁻¹)) *
              (conj (a⁻¹) * b⁻¹) ^ n := by
                apply tsum_congr
                intro n
                simp only [RCLike.inner_apply', map_mul, map_sub, map_one,
                  map_pow]
                ring
      _ = (conj (1 - a⁻¹) * (1 - b⁻¹)) *
          ∑' n : ℕ, (conj (a⁻¹) * b⁻¹) ^ n := by
        rw [tsum_mul_left]
      _ = conj (1 - a⁻¹) * (1 - b⁻¹) *
          (1 - conj (a⁻¹) * b⁻¹)⁻¹ := by
        rw [tsum_geometric_of_norm_lt_one hq]
  rw [← htsum]
  exact tendsto_nhds_unique hseq hsummable.hasSum.tendsto_sum_nat

/-- Backward and forward geometric coefficient vectors are orthogonal because
their frequency supports are disjoint. -/
theorem inner_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector_forward
    {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b⁻¹‖ < 1) :
    inner ℂ
        (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector a)
        (suzukiXiCarrierCayleyForwardGeometricCoefficientVector b) = 0 := by
  have hbase :=
    (hasSum_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
      ha).tendsto_sum_nat
  have hinner :=
    Filter.Tendsto.inner (𝕜 := ℂ) hbase
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ ↦
          suzukiXiCarrierCayleyForwardGeometricCoefficientVector b)
        atTop
        (𝓝 (suzukiXiCarrierCayleyForwardGeometricCoefficientVector b)))
  have hzero :
      Tendsto
          (fun N : ℕ ↦ inner ℂ
            (∑ n ∈ Finset.range N,
              lp.single 2 (-(n : ℤ)) ((1 - a) * a ^ n) : ℓ²(ℤ, ℂ))
            (suzukiXiCarrierCayleyForwardGeometricCoefficientVector b))
          atTop (𝓝 0) := by
    refine (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0)).congr' ?_
    exact Eventually.of_forall fun N ↦ by
      simp only [sum_inner, lp.inner_single_left,
        suzukiXiCarrierCayleyForwardGeometricCoefficientVector_apply_neg hb,
        inner_zero_right, Finset.sum_const_zero]
  exact tendsto_nhds_unique hinner hzero

/-- Forward and backward geometric coefficient vectors are orthogonal in the
reverse inner-product order as well. -/
theorem inner_suzukiXiCarrierCayleyForwardGeometricCoefficientVector_backward
    {a b : ℂ} (ha : ‖a⁻¹‖ < 1) (hb : ‖b‖ < 1) :
    inner ℂ
        (suzukiXiCarrierCayleyForwardGeometricCoefficientVector a)
        (suzukiXiCarrierCayleyBackwardGeometricCoefficientVector b) = 0 := by
  rw [← inner_conj_symm,
    inner_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector_forward hb ha,
    map_zero]

/-- The explicit coefficient-space Gram kernel for two xi nodes. It is the
appropriate Szegő kernel when the nodes occupy the same half-plane and zero
when they occupy opposite half-planes. Correctness is asserted below for
off-axis nodes. -/
def suzukiXiCarrierCayleyOffAxisCoefficientKernel
    (rho sigma : NontrivialZetaZero) : ℂ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    if 0 < (zetaSpectralCoordinate sigma.1).im then
      conj (1 - suzukiXiCarrierCayleyNodeParameter rho) *
        (1 - suzukiXiCarrierCayleyNodeParameter sigma) *
          (1 - conj (suzukiXiCarrierCayleyNodeParameter rho) *
            suzukiXiCarrierCayleyNodeParameter sigma)⁻¹
    else 0
  else if 0 < (zetaSpectralCoordinate sigma.1).im then 0
  else
    conj (1 - (suzukiXiCarrierCayleyNodeParameter rho)⁻¹) *
      (1 - (suzukiXiCarrierCayleyNodeParameter sigma)⁻¹) *
        (1 - conj ((suzukiXiCarrierCayleyNodeParameter rho)⁻¹) *
          (suzukiXiCarrierCayleyNodeParameter sigma)⁻¹)⁻¹

/-- For two off-axis xi nodes, the explicit kernel is exactly the inner
product of their selected bilateral geometric coefficient vectors. -/
theorem inner_suzukiXiCarrierCayleyOffAxisNodeCoefficientVector
    (rho sigma : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0)
    (hsigma : (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    inner ℂ
        (suzukiXiCarrierCayleyOffAxisNodeCoefficientVector rho)
        (suzukiXiCarrierCayleyOffAxisNodeCoefficientVector sigma) =
      suzukiXiCarrierCayleyOffAxisCoefficientKernel rho sigma := by
  by_cases hrhoUpper : 0 < (zetaSpectralCoordinate rho.1).im
  · have harho : ‖suzukiXiCarrierCayleyNodeParameter rho‖ < 1 :=
      (norm_suzukiXiCarrierCayleyNodeParameter_lt_one_iff rho).2 hrhoUpper
    by_cases hsigmaUpper : 0 < (zetaSpectralCoordinate sigma.1).im
    · have hasigma : ‖suzukiXiCarrierCayleyNodeParameter sigma‖ < 1 :=
        (norm_suzukiXiCarrierCayleyNodeParameter_lt_one_iff sigma).2
          hsigmaUpper
      simp only [suzukiXiCarrierCayleyOffAxisNodeCoefficientVector,
        suzukiXiCarrierCayleyOffAxisCoefficientKernel, if_pos hrhoUpper,
        if_pos hsigmaUpper]
      exact inner_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
        harho hasigma
    · have hsigmaLower : (zetaSpectralCoordinate sigma.1).im < 0 :=
        lt_of_le_of_ne (not_lt.mp hsigmaUpper) hsigma
      have ha : 1 < ‖suzukiXiCarrierCayleyNodeParameter sigma‖ :=
        (one_lt_norm_suzukiXiCarrierCayleyNodeParameter_iff sigma).2
          hsigmaLower
      have hasigmaInv :
          ‖(suzukiXiCarrierCayleyNodeParameter sigma)⁻¹‖ < 1 := by
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ ha
      simp only [suzukiXiCarrierCayleyOffAxisNodeCoefficientVector,
        suzukiXiCarrierCayleyOffAxisCoefficientKernel, if_pos hrhoUpper,
        if_neg hsigmaUpper]
      exact
        inner_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector_forward
          harho hasigmaInv
  · have hrhoLower : (zetaSpectralCoordinate rho.1).im < 0 :=
      lt_of_le_of_ne (not_lt.mp hrhoUpper) hrho
    have harhoNorm : 1 < ‖suzukiXiCarrierCayleyNodeParameter rho‖ :=
      (one_lt_norm_suzukiXiCarrierCayleyNodeParameter_iff rho).2 hrhoLower
    have harhoInv : ‖(suzukiXiCarrierCayleyNodeParameter rho)⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ harhoNorm
    by_cases hsigmaUpper : 0 < (zetaSpectralCoordinate sigma.1).im
    · have hasigma : ‖suzukiXiCarrierCayleyNodeParameter sigma‖ < 1 :=
        (norm_suzukiXiCarrierCayleyNodeParameter_lt_one_iff sigma).2
          hsigmaUpper
      simp only [suzukiXiCarrierCayleyOffAxisNodeCoefficientVector,
        suzukiXiCarrierCayleyOffAxisCoefficientKernel, if_neg hrhoUpper,
        if_pos hsigmaUpper]
      exact
        inner_suzukiXiCarrierCayleyForwardGeometricCoefficientVector_backward
          harhoInv hasigma
    · have hsigmaLower : (zetaSpectralCoordinate sigma.1).im < 0 :=
        lt_of_le_of_ne (not_lt.mp hsigmaUpper) hsigma
      have hasigmaNorm : 1 < ‖suzukiXiCarrierCayleyNodeParameter sigma‖ :=
        (one_lt_norm_suzukiXiCarrierCayleyNodeParameter_iff sigma).2
          hsigmaLower
      have hasigmaInv :
          ‖(suzukiXiCarrierCayleyNodeParameter sigma)⁻¹‖ < 1 := by
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hasigmaNorm
      simp only [suzukiXiCarrierCayleyOffAxisNodeCoefficientVector,
        suzukiXiCarrierCayleyOffAxisCoefficientKernel, if_neg hrhoUpper,
        if_neg hsigmaUpper]
      exact inner_suzukiXiCarrierCayleyForwardGeometricCoefficientVector
        harhoInv hasigmaInv

/-- The off-axis coefficient kernel is Hermitian on genuine off-axis nodes. -/
theorem suzukiXiCarrierCayleyOffAxisCoefficientKernel_conj_symm
    (rho sigma : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0)
    (hsigma : (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    suzukiXiCarrierCayleyOffAxisCoefficientKernel sigma rho =
      conj (suzukiXiCarrierCayleyOffAxisCoefficientKernel rho sigma) := by
  rw [← inner_suzukiXiCarrierCayleyOffAxisNodeCoefficientVector sigma rho
      hsigma hrho,
    ← inner_suzukiXiCarrierCayleyOffAxisNodeCoefficientVector rho sigma
      hrho hsigma]
  exact (inner_conj_symm (𝕜 := ℂ)
    (suzukiXiCarrierCayleyOffAxisNodeCoefficientVector sigma)
    (suzukiXiCarrierCayleyOffAxisNodeCoefficientVector rho)).symm

/-- The real diagonal of the explicit coefficient kernel is the reciprocal
distance of the node from the real spectral axis. -/
theorem re_suzukiXiCarrierCayleyOffAxisCoefficientKernel_self
    (rho : NontrivialZetaZero)
    (hoffAxis : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    (suzukiXiCarrierCayleyOffAxisCoefficientKernel rho rho).re =
      |(zetaSpectralCoordinate rho.1).im|⁻¹ := by
  rw [← inner_suzukiXiCarrierCayleyOffAxisNodeCoefficientVector rho rho
      hoffAxis hoffAxis]
  change RCLike.re (inner ℂ
    (suzukiXiCarrierCayleyOffAxisNodeCoefficientVector rho)
    (suzukiXiCarrierCayleyOffAxisNodeCoefficientVector rho)) = _
  rw [← @norm_sq_eq_re_inner ℂ (ℓ²(ℤ, ℂ)) _ _ _]
  exact norm_sq_suzukiXiCarrierCayleyOffAxisNodeCoefficientVector rho hoffAxis

/-- The scalar multiplying one node vector in a finite Cayley-weighted
off-axis coefficient synthesis. -/
def suzukiXiCarrierCayleyOffAxisWeightedCoefficient
    (c : NontrivialZetaZero →₀ ℂ) (rho : NontrivialZetaZero) : ℂ :=
  ((suzukiXiZeroNormalization rho : ℂ) * c rho) *
    suzukiXiCarrierCayleyNodeParameter rho

/-- The finite quadratic form of the explicit off-axis coefficient Gram
kernel with the genuine Suzuki normalization and Cayley weights. -/
def suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic
    (c : NontrivialZetaZero →₀ ℂ) : ℂ :=
  ∑ rho ∈ c.support, ∑ sigma ∈ c.support,
    conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
      suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma *
        suzukiXiCarrierCayleyOffAxisCoefficientKernel rho sigma

/-- The inner product of a combined off-axis coefficient vector with itself
is exactly its explicit finite Gram quadratic. -/
theorem inner_suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector
    (c : NontrivialZetaZero →₀ ℂ)
    (hoffAxis : ∀ rho ∈ c.support,
      (zetaSpectralCoordinate rho.1).im ≠ 0) :
    inner ℂ
        (suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector c)
        (suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector c) =
      suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic c := by
  unfold suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector
    suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic
    suzukiXiCarrierCayleyOffAxisWeightedCoefficient
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rho hrho
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [inner_suzukiXiCarrierCayleyOffAxisNodeCoefficientVector rho sigma
    (hoffAxis rho hrho) (hoffAxis sigma hsigma)]
  ring

/-- Complex-valued squared-norm realization of the explicit off-axis
coefficient Gram quadratic. -/
theorem suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic_eq_norm_sq
    (c : NontrivialZetaZero →₀ ℂ)
    (hoffAxis : ∀ rho ∈ c.support,
      (zetaSpectralCoordinate rho.1).im ≠ 0) :
    suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic c =
      (‖suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector c‖ : ℂ) ^ 2 := by
  rw [← inner_suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector c hoffAxis]
  exact inner_self_eq_norm_sq_to_K _

/-- The real part of the explicit off-axis Gram quadratic is exactly the
squared `ℓ²` norm of the combined coefficient vector. -/
theorem re_suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic_eq_norm_sq
    (c : NontrivialZetaZero →₀ ℂ)
    (hoffAxis : ∀ rho ∈ c.support,
      (zetaSpectralCoordinate rho.1).im ≠ 0) :
    (suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic c).re =
      ‖suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector c‖ ^ 2 := by
  rw [suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic_eq_norm_sq c
    hoffAxis]
  norm_cast

/-- The explicit off-axis coefficient Gram quadratic has nonnegative real
part on every genuinely off-axis finite family. -/
theorem re_suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic_nonneg
    (c : NontrivialZetaZero →₀ ℂ)
    (hoffAxis : ∀ rho ∈ c.support,
      (zetaSpectralCoordinate rho.1).im ≠ 0) :
    0 ≤ (suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic c).re := by
  rw [re_suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic_eq_norm_sq c
    hoffAxis]
  positivity

/-- The carrier norm of every finite off-axis Cayley-weighted synthesis is
bounded by `pi` times its explicit cancellation-preserving coefficient Gram
quadratic. -/
theorem norm_sq_suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_le_coefficientGram
    (c : NontrivialZetaZero →₀ ℂ)
    (hoffAxis : ∀ rho ∈ c.support,
      (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ‖suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis c‖ ^ 2 ≤
      Real.pi *
        (suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic c).re := by
  rw [re_suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic_eq_norm_sq c
    hoffAxis]
  exact
    norm_sq_suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_le_offAxis
      c hoffAxis

end

end RiemannGaussian
