import RiemannGaussian.RiemannXiSuzukiCarrierCayleyNodeCoefficients

/-!
# Exact coefficient energy of off-axis xi nodes

The geometric Cayley coefficient vectors of an off-axis node are not merely
square-summable. Their squared norms have closed formulas. For an abstract
contractive parameter the formula is the energy of a geometric series. For
a genuine xi node the Cayley algebra collapses this expression to the
reciprocal distance of its spectral coordinate from the real axis:

`‖v rho‖² = |Im z_rho|⁻¹`.

This identity makes the boundary obstruction quantitative. Nodewise norm
estimates necessarily blow up as an off-axis node approaches the real axis;
any uniform xi tail theorem must therefore retain cancellation between the
combined coefficient vectors or separately control the real boundary.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

private theorem backward_partial_norm_sq (a : ℂ) (N : ℕ) :
    ‖(∑ n ∈ Finset.range N,
        lp.single 2 (-(n : ℤ)) ((1 - a) * a ^ n) : ℓ²(ℤ, ℂ))‖ ^ 2 =
      ∑ n ∈ Finset.range N, ‖(1 - a) * a ^ n‖ ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [pow_two]
      rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)]
      · rw [show ‖(∑ n ∈ Finset.range N,
              lp.single 2 (-(n : ℤ)) ((1 - a) * a ^ n) : ℓ²(ℤ, ℂ))‖ *
              ‖(∑ n ∈ Finset.range N,
                lp.single 2 (-(n : ℤ)) ((1 - a) * a ^ n) : ℓ²(ℤ, ℂ))‖ =
              ∑ n ∈ Finset.range N, ‖(1 - a) * a ^ n‖ *
                ‖(1 - a) * a ^ n‖ by simpa only [pow_two] using ih,
            lp.norm_single (by norm_num)]
      · rw [lp.inner_single_right]
        simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
        have hzero :
            ∑ n ∈ Finset.range N,
                (Pi.single (-(n : ℤ)) ((1 - a) * a ^ n) : ℤ → ℂ)
                  (-(N : ℤ)) = 0 := by
          apply Finset.sum_eq_zero
          intro n hn
          rw [Pi.single_eq_of_ne]
          intro h
          have : N = n := by exact_mod_cast neg_inj.mp h
          subst n
          exact (Nat.lt_irrefl N (Finset.mem_range.mp hn)).elim
        rw [hzero, inner_zero_left]

/-- The exact squared energy of a backward geometric coefficient vector. -/
theorem norm_sq_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
    {a : ℂ} (ha : ‖a‖ < 1) :
    ‖suzukiXiCarrierCayleyBackwardGeometricCoefficientVector a‖ ^ 2 =
      ‖1 - a‖ ^ 2 * (1 - ‖a‖ ^ 2)⁻¹ := by
  have hnorm :
      Tendsto
          (fun N : ℕ ↦
            ∑ n ∈ Finset.range N, ‖(1 - a) * a ^ n‖ ^ 2)
          atTop
          (𝓝 (‖suzukiXiCarrierCayleyBackwardGeometricCoefficientVector a‖ ^ 2)) := by
    have hbase :=
      (hasSum_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
        ha).tendsto_sum_nat
    have hnorm' := hbase.norm
    have h := hnorm'.pow 2
    convert h using 1
    ext N
    exact (backward_partial_norm_sq a N).symm
  have haSq : ‖a‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg a]
  have hsummable : Summable (fun n : ℕ ↦ ‖(1 - a) * a ^ n‖ ^ 2) := by
    have hgeom :=
      (summable_geometric_of_lt_one (sq_nonneg ‖a‖) haSq).mul_left
        (‖1 - a‖ ^ 2)
    apply hgeom.congr
    intro n
    rw [norm_mul, norm_pow]
    ring
  have htsum :
      ∑' n : ℕ, ‖(1 - a) * a ^ n‖ ^ 2 =
        ‖1 - a‖ ^ 2 * (1 - ‖a‖ ^ 2)⁻¹ := by
    calc
      ∑' n : ℕ, ‖(1 - a) * a ^ n‖ ^ 2 =
          ∑' n : ℕ, ‖1 - a‖ ^ 2 * (‖a‖ ^ 2) ^ n := by
            apply tsum_congr
            intro n
            rw [norm_mul, norm_pow]
            ring
      _ = ‖1 - a‖ ^ 2 * ∑' n : ℕ, (‖a‖ ^ 2) ^ n := by
        rw [tsum_mul_left]
      _ = ‖1 - a‖ ^ 2 * (1 - ‖a‖ ^ 2)⁻¹ := by
        rw [tsum_geometric_of_lt_one (sq_nonneg ‖a‖) haSq]
  rw [← htsum]
  exact tendsto_nhds_unique hnorm hsummable.hasSum.tendsto_sum_nat

private theorem forward_partial_norm_sq (a : ℂ) (N : ℕ) :
    ‖(∑ n ∈ Finset.range N,
        lp.single 2 ((n + 1 : ℕ) : ℤ)
          ((1 - a⁻¹) * (a⁻¹) ^ n) : ℓ²(ℤ, ℂ))‖ ^ 2 =
      ∑ n ∈ Finset.range N, ‖(1 - a⁻¹) * (a⁻¹) ^ n‖ ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [pow_two]
      rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)]
      · rw [show ‖(∑ n ∈ Finset.range N,
              lp.single 2 ((n + 1 : ℕ) : ℤ)
                ((1 - a⁻¹) * (a⁻¹) ^ n) : ℓ²(ℤ, ℂ))‖ *
              ‖(∑ n ∈ Finset.range N,
                lp.single 2 ((n + 1 : ℕ) : ℤ)
                  ((1 - a⁻¹) * (a⁻¹) ^ n) : ℓ²(ℤ, ℂ))‖ =
              ∑ n ∈ Finset.range N, ‖(1 - a⁻¹) * (a⁻¹) ^ n‖ *
                ‖(1 - a⁻¹) * (a⁻¹) ^ n‖ by
                  simpa only [pow_two] using ih,
            lp.norm_single (by norm_num)]
      · rw [lp.inner_single_right]
        simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
        have hzero :
            ∑ n ∈ Finset.range N,
                (Pi.single (((n + 1 : ℕ) : ℤ))
                    ((1 - a⁻¹) * (a⁻¹) ^ n) : ℤ → ℂ)
                  ((N + 1 : ℕ) : ℤ) = 0 := by
          apply Finset.sum_eq_zero
          intro n hn
          rw [Pi.single_eq_of_ne]
          intro h
          have hplus : N + 1 = n + 1 := by exact_mod_cast h
          have : N = n := Nat.add_right_cancel hplus
          subst n
          exact (Nat.lt_irrefl N (Finset.mem_range.mp hn)).elim
        rw [hzero, inner_zero_left]

/-- The exact squared energy of a forward reciprocal-geometric coefficient
vector. -/
theorem norm_sq_suzukiXiCarrierCayleyForwardGeometricCoefficientVector
    {a : ℂ} (ha : ‖a⁻¹‖ < 1) :
    ‖suzukiXiCarrierCayleyForwardGeometricCoefficientVector a‖ ^ 2 =
      ‖1 - a⁻¹‖ ^ 2 * (1 - ‖a⁻¹‖ ^ 2)⁻¹ := by
  have hnorm :
      Tendsto
          (fun N : ℕ ↦
            ∑ n ∈ Finset.range N, ‖(1 - a⁻¹) * (a⁻¹) ^ n‖ ^ 2)
          atTop
          (𝓝 (‖suzukiXiCarrierCayleyForwardGeometricCoefficientVector a‖ ^ 2)) := by
    have hbase :=
      (hasSum_suzukiXiCarrierCayleyForwardGeometricCoefficientVector
        ha).tendsto_sum_nat
    have hnorm' := hbase.norm
    have h := hnorm'.pow 2
    convert h using 1
    ext N
    exact (forward_partial_norm_sq a N).symm
  have haSq : ‖a⁻¹‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg a⁻¹]
  have hsummable : Summable (fun n : ℕ ↦
      ‖(1 - a⁻¹) * (a⁻¹) ^ n‖ ^ 2) := by
    have hgeom :=
      (summable_geometric_of_lt_one (sq_nonneg ‖a⁻¹‖) haSq).mul_left
        (‖1 - a⁻¹‖ ^ 2)
    apply hgeom.congr
    intro n
    rw [norm_mul, norm_pow]
    ring
  have htsum :
      ∑' n : ℕ, ‖(1 - a⁻¹) * (a⁻¹) ^ n‖ ^ 2 =
        ‖1 - a⁻¹‖ ^ 2 * (1 - ‖a⁻¹‖ ^ 2)⁻¹ := by
    calc
      ∑' n : ℕ, ‖(1 - a⁻¹) * (a⁻¹) ^ n‖ ^ 2 =
          ∑' n : ℕ, ‖1 - a⁻¹‖ ^ 2 * (‖a⁻¹‖ ^ 2) ^ n := by
            apply tsum_congr
            intro n
            rw [norm_mul, norm_pow]
            ring
      _ = ‖1 - a⁻¹‖ ^ 2 * ∑' n : ℕ, (‖a⁻¹‖ ^ 2) ^ n := by
        rw [tsum_mul_left]
      _ = ‖1 - a⁻¹‖ ^ 2 * (1 - ‖a⁻¹‖ ^ 2)⁻¹ := by
        rw [tsum_geometric_of_lt_one (sq_nonneg ‖a⁻¹‖) haSq]
  rw [← htsum]
  exact tendsto_nhds_unique hnorm hsummable.hasSum.tendsto_sum_nat

private theorem cayley_backward_energy_identity
    {z : ℂ} (hz : z + Complex.I ≠ 0) (him : 0 < z.im) :
    ‖1 - suzukiXiCarrierCayleyParameter z‖ ^ 2 *
        (1 - ‖suzukiXiCarrierCayleyParameter z‖ ^ 2)⁻¹ =
      (z.im)⁻¹ := by
  have hOneSub :
      1 - suzukiXiCarrierCayleyParameter z =
        (2 * Complex.I) / (z + Complex.I) := by
    unfold suzukiXiCarrierCayleyParameter
    field_simp [hz]
    ring
  have ha : ‖suzukiXiCarrierCayleyParameter z‖ < 1 :=
    (norm_suzukiXiCarrierCayleyParameter_lt_one_iff hz).2 him
  have hgap : 1 - ‖suzukiXiCarrierCayleyParameter z‖ ^ 2 ≠ 0 := by
    nlinarith [norm_nonneg (suzukiXiCarrierCayleyParameter z)]
  have hden : ‖z + Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have himne : z.im ≠ 0 := ne_of_gt him
  have hdiff := norm_sq_add_I_sub_norm_sq_sub_I z
  rw [hOneSub]
  unfold suzukiXiCarrierCayleyParameter at hgap ⊢
  rw [norm_div, norm_mul, norm_ofNat, norm_I, mul_one, norm_div]
  field_simp [hgap, hden, himne]
  rw [hdiff]
  field_simp [himne]
  norm_num

private theorem cayley_forward_energy_identity
    {z : ℂ} (hminus : z - Complex.I ≠ 0) (him : z.im < 0) :
    ‖1 - (suzukiXiCarrierCayleyParameter z)⁻¹‖ ^ 2 *
        (1 - ‖(suzukiXiCarrierCayleyParameter z)⁻¹‖ ^ 2)⁻¹ =
      (-z.im)⁻¹ := by
  have hneg : -z + Complex.I ≠ 0 := by
    intro hzero
    apply hminus
    calc
      z - Complex.I = -(-z + Complex.I) := by ring
      _ = 0 := by rw [hzero]; simp
  have hupper : 0 < (-z).im := by
    simp only [neg_im]
    linarith
  have h := cayley_backward_energy_identity hneg hupper
  rw [suzukiXiCarrierCayleyParameter_neg z hminus] at h
  simpa only [neg_im] using h

/-- For an upper-half-plane xi node, the backward coefficient energy is the
reciprocal of its positive spectral height. -/
theorem norm_sq_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector_upperNode
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    ‖suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
        (suzukiXiCarrierCayleyNodeParameter rho)‖ ^ 2 =
      ((zetaSpectralCoordinate rho.1).im)⁻¹ := by
  calc
    ‖suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
        (suzukiXiCarrierCayleyNodeParameter rho)‖ ^ 2 =
        ‖1 - suzukiXiCarrierCayleyNodeParameter rho‖ ^ 2 *
          (1 - ‖suzukiXiCarrierCayleyNodeParameter rho‖ ^ 2)⁻¹ :=
      norm_sq_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector
        ((norm_suzukiXiCarrierCayleyNodeParameter_lt_one_iff rho).2 hupper)
    _ = ((zetaSpectralCoordinate rho.1).im)⁻¹ :=
      cayley_backward_energy_identity
        (zetaSpectralCoordinate_add_I_ne_zero rho) hupper

/-- For a lower-half-plane xi node, the forward coefficient energy is the
reciprocal of the negated spectral height. -/
theorem norm_sq_suzukiXiCarrierCayleyForwardGeometricCoefficientVector_lowerNode
    (rho : NontrivialZetaZero)
    (hlower : (zetaSpectralCoordinate rho.1).im < 0) :
    ‖suzukiXiCarrierCayleyForwardGeometricCoefficientVector
        (suzukiXiCarrierCayleyNodeParameter rho)‖ ^ 2 =
      (-(zetaSpectralCoordinate rho.1).im)⁻¹ := by
  have ha : 1 < ‖suzukiXiCarrierCayleyNodeParameter rho‖ :=
    (one_lt_norm_suzukiXiCarrierCayleyNodeParameter_iff rho).2 hlower
  have hainv : ‖(suzukiXiCarrierCayleyNodeParameter rho)⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ ha
  calc
    ‖suzukiXiCarrierCayleyForwardGeometricCoefficientVector
        (suzukiXiCarrierCayleyNodeParameter rho)‖ ^ 2 =
        ‖1 - (suzukiXiCarrierCayleyNodeParameter rho)⁻¹‖ ^ 2 *
          (1 - ‖(suzukiXiCarrierCayleyNodeParameter rho)⁻¹‖ ^ 2)⁻¹ :=
      norm_sq_suzukiXiCarrierCayleyForwardGeometricCoefficientVector hainv
    _ = (-(zetaSpectralCoordinate rho.1).im)⁻¹ :=
      cayley_forward_energy_identity
        (zetaSpectralCoordinate_sub_I_ne_zero rho) hlower

/-- Every off-axis xi node has coefficient energy exactly equal to the
reciprocal of its distance from the real spectral boundary. -/
theorem norm_sq_suzukiXiCarrierCayleyOffAxisNodeCoefficientVector
    (rho : NontrivialZetaZero)
    (hoffAxis : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ‖suzukiXiCarrierCayleyOffAxisNodeCoefficientVector rho‖ ^ 2 =
      |(zetaSpectralCoordinate rho.1).im|⁻¹ := by
  rcases lt_or_gt_of_ne hoffAxis with hlower | hupper
  · rw [suzukiXiCarrierCayleyOffAxisNodeCoefficientVector,
      if_neg (not_lt_of_ge hlower.le),
      norm_sq_suzukiXiCarrierCayleyForwardGeometricCoefficientVector_lowerNode
        rho hlower,
      abs_of_neg hlower]
  · rw [suzukiXiCarrierCayleyOffAxisNodeCoefficientVector, if_pos hupper,
      norm_sq_suzukiXiCarrierCayleyBackwardGeometricCoefficientVector_upperNode
        rho hupper,
      abs_of_pos hupper]

end

end RiemannGaussian
