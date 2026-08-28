import RiemannGaussian.RiemannXiSuzukiPointwiseFirstTailBarrier
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

/-!
# The Chebyshev--Legendre form of the Suzuki first-tail frontier

The remaining first-tail obligations are indexed by complete finite
von-Mangoldt prefixes.  This file removes the synthetic reset bookkeeping
from those obligations and exposes their two arithmetic statistics directly:

* weighted mass `sum Lambda(n) / sqrt(n)`, and
* weighted log-moment `sum Lambda(n) log(n) / sqrt(n)`.

Finite Abel summation identifies both statistics exactly with integrals
against `Chebyshev.psi`.  The canonical reset mass point is then proved to be
the point where the literal Archimedean slope matches the complete prime
prefix mass, and its transport gap becomes the corresponding finite
Legendre defect.  Thus the open infinite family can be attacked through the
classical Chebyshev function without chaining numerical cutoff certificates.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## The two Abel kernels -/

/-- Multiplicative kernel for Suzuki's weighted von-Mangoldt mass. -/
def suzukiChebyshevMassKernel (x : ℝ) : ℝ :=
  x ^ (-1 / 2 : ℝ)

/-- Multiplicative kernel for Suzuki's weighted von-Mangoldt log-moment. -/
def suzukiChebyshevLogMomentKernel (x : ℝ) : ℝ :=
  Real.log x * suzukiChebyshevMassKernel x

/-- Abel functional for weighted von-Mangoldt mass up to a real endpoint. -/
def suzukiChebyshevWeightedMass (b : ℝ) : ℝ :=
  suzukiChebyshevMassKernel b * Chebyshev.psi b -
    ∫ x in Set.Ioc (1 : ℝ) b,
      deriv suzukiChebyshevMassKernel x * Chebyshev.psi x

/-- Abel functional for the weighted von-Mangoldt log-moment up to a real
endpoint. -/
def suzukiChebyshevWeightedLogMoment (b : ℝ) : ℝ :=
  suzukiChebyshevLogMomentKernel b * Chebyshev.psi b -
    ∫ x in Set.Ioc (1 : ℝ) b,
      deriv suzukiChebyshevLogMomentKernel x * Chebyshev.psi x

/-- Weighted logarithmic moment centered at a supplied Legendre point.  It is
one explicit linear functional of `Chebyshev.psi`. -/
def suzukiChebyshevWeightedCenteredLogMoment
    (center b : ℝ) : ℝ :=
  suzukiChebyshevWeightedLogMoment b -
    center * suzukiChebyshevWeightedMass b

private theorem contDiffOn_suzukiChebyshevMassKernel_Ioi :
    ContDiffOn ℝ 2 suzukiChebyshevMassKernel (Set.Ioi 0) := by
  intro x hx
  unfold suzukiChebyshevMassKernel
  exact (Real.contDiffAt_rpow_const (n := 2) (Or.inl hx.ne'))
    |>.contDiffWithinAt

private theorem contDiffOn_suzukiChebyshevLogMomentKernel_Ioi :
    ContDiffOn ℝ 2 suzukiChebyshevLogMomentKernel (Set.Ioi 0) := by
  intro x hx
  unfold suzukiChebyshevLogMomentKernel
  exact ((Real.contDiffAt_log (n := (2 : WithTop ℕ∞))).2 hx.ne')
    |>.contDiffWithinAt
    |>.mul (contDiffOn_suzukiChebyshevMassKernel_Ioi x hx)

private theorem integrableOn_deriv_suzukiChebyshevMassKernel_Icc
    {b : ℝ} :
    IntegrableOn (deriv suzukiChebyshevMassKernel) (Set.Icc 1 b) := by
  have hcontinuous : ContinuousOn
      (deriv suzukiChebyshevMassKernel) (Set.Ioi 0) :=
    contDiffOn_suzukiChebyshevMassKernel_Ioi
      |>.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  apply (hcontinuous.mono _).integrableOn_Icc
  intro x hx
  exact zero_lt_one.trans_le hx.1

private theorem integrableOn_deriv_suzukiChebyshevLogMomentKernel_Icc
    {b : ℝ} :
    IntegrableOn (deriv suzukiChebyshevLogMomentKernel) (Set.Icc 1 b) := by
  have hcontinuous : ContinuousOn
      (deriv suzukiChebyshevLogMomentKernel) (Set.Ioi 0) :=
    contDiffOn_suzukiChebyshevLogMomentKernel_Ioi
      |>.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  apply (hcontinuous.mono _).integrableOn_Icc
  intro x hx
  exact zero_lt_one.trans_le hx.1

/-- Finite Abel summation for the weighted mass kernel. -/
theorem suzukiChebyshevMassAbel_eq
    {b : ℝ} (hb : 1 ≤ b) :
    ∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
        suzukiChebyshevMassKernel n *
          ArithmeticFunction.vonMangoldt n =
      suzukiChebyshevMassKernel b * Chebyshev.psi b -
        ∫ x in Set.Ioc (1 : ℝ) b,
          deriv suzukiChebyshevMassKernel x * Chebyshev.psi x := by
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (a := (1 : ℝ)) (b := b) (by norm_num) hb
    (fun x hx => by
      unfold suzukiChebyshevMassKernel
      exact Real.differentiableAt_rpow_const_of_ne _
        (by linarith [hx.1]))
    integrableOn_deriv_suzukiChebyshevMassKernel_Icc
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at h
  simpa [Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (1 : ℝ) < 2)]
    using h

/-- Finite Abel summation for the weighted log-moment kernel. -/
theorem suzukiChebyshevLogMomentAbel_eq
    {b : ℝ} (hb : 1 ≤ b) :
    ∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
        suzukiChebyshevLogMomentKernel n *
          ArithmeticFunction.vonMangoldt n =
      suzukiChebyshevLogMomentKernel b * Chebyshev.psi b -
        ∫ x in Set.Ioc (1 : ℝ) b,
          deriv suzukiChebyshevLogMomentKernel x *
            Chebyshev.psi x := by
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (a := (1 : ℝ)) (b := b) (by norm_num) hb
    (fun x hx => by
      unfold suzukiChebyshevLogMomentKernel
      exact (Real.differentiableAt_log (by linarith [hx.1])).mul
        (Real.differentiableAt_rpow_const_of_ne _
          (by linarith [hx.1])))
    integrableOn_deriv_suzukiChebyshevLogMomentKernel_Icc
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at h
  simpa [Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (1 : ℝ) < 2)]
    using h

/-! ## Exact identification with the Suzuki prefix statistics -/

/-- On natural arguments the mass kernel is exactly reciprocal square root. -/
theorem suzukiChebyshevMassKernel_nat_eq (n : ℕ) :
    suzukiChebyshevMassKernel (n : ℝ) = 1 / Real.sqrt n := by
  unfold suzukiChebyshevMassKernel
  rw [Real.sqrt_eq_rpow, one_div,
    ← Real.rpow_neg (Nat.cast_nonneg n) (1 / 2 : ℝ)]
  congr 1
  ring_nf

/-- On natural arguments the second kernel is `log(n) / sqrt(n)`. -/
theorem suzukiChebyshevLogMomentKernel_nat_eq (n : ℕ) :
    suzukiChebyshevLogMomentKernel (n : ℝ) =
      Real.log n / Real.sqrt n := by
  unfold suzukiChebyshevLogMomentKernel
  rw [suzukiChebyshevMassKernel_nat_eq]
  ring_nf

/-- Suzuki's prime-prefix mass is the Abel mass sum over integers
`2, ..., cutoff + 1`. -/
theorem screwPrefixMass_suzukiPrimeWeight_eq_suzukiChebyshevMassSum
    (cutoff : ℕ) :
    screwPrefixMass suzukiPrimeWeight cutoff =
      ∑ n ∈ Finset.Ioc 1 (cutoff + 1),
        suzukiChebyshevMassKernel n *
          ArithmeticFunction.vonMangoldt n := by
  unfold screwPrefixMass
  refine Finset.sum_bij (fun n _hn => n + 2) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_Ioc] at hn ⊢
    omega
  · intro a ha b hb hab
    omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    refine ⟨n - 2, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro n hn
    unfold suzukiPrimeWeight
    rw [suzukiChebyshevMassKernel_nat_eq]
    ring_nf

/-- Suzuki's prime-prefix first moment is the corresponding Abel log-moment
sum over integers `2, ..., cutoff + 1`. -/
theorem screwPrefixMoment_suzukiPrime_eq_suzukiChebyshevLogMomentSum
    (cutoff : ℕ) :
    screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight cutoff =
      ∑ n ∈ Finset.Ioc 1 (cutoff + 1),
        suzukiChebyshevLogMomentKernel n *
          ArithmeticFunction.vonMangoldt n := by
  unfold screwPrefixMoment
  refine Finset.sum_bij (fun n _hn => n + 2) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_Ioc] at hn ⊢
    omega
  · intro a ha b hb hab
    omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    refine ⟨n - 2, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro n hn
    unfold suzukiPrimeLocation suzukiPrimeWeight
    rw [suzukiChebyshevLogMomentKernel_nat_eq]
    ring_nf

/-- Exact Chebyshev-`psi` representation of every Suzuki prefix mass. -/
theorem screwPrefixMass_suzukiPrimeWeight_eq_chebyshevPsi
    (cutoff : ℕ) :
    screwPrefixMass suzukiPrimeWeight cutoff =
      suzukiChebyshevMassKernel ((cutoff + 1 : ℕ) : ℝ) *
          Chebyshev.psi ((cutoff + 1 : ℕ) : ℝ) -
        ∫ x in Set.Ioc (1 : ℝ) ((cutoff + 1 : ℕ) : ℝ),
          deriv suzukiChebyshevMassKernel x * Chebyshev.psi x := by
  rw [screwPrefixMass_suzukiPrimeWeight_eq_suzukiChebyshevMassSum]
  simpa only [Nat.floor_natCast] using
    (suzukiChebyshevMassAbel_eq
      (b := ((cutoff + 1 : ℕ) : ℝ)) (by
        norm_num only [Nat.cast_add, Nat.cast_one]
        have hcutoff : (0 : ℝ) ≤ cutoff := Nat.cast_nonneg cutoff
        linarith))

/-- Exact Chebyshev-`psi` representation of every Suzuki prefix log-moment. -/
theorem screwPrefixMoment_suzukiPrime_eq_chebyshevPsi
    (cutoff : ℕ) :
    screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight cutoff =
      suzukiChebyshevLogMomentKernel ((cutoff + 1 : ℕ) : ℝ) *
          Chebyshev.psi ((cutoff + 1 : ℕ) : ℝ) -
        ∫ x in Set.Ioc (1 : ℝ) ((cutoff + 1 : ℕ) : ℝ),
          deriv suzukiChebyshevLogMomentKernel x *
            Chebyshev.psi x := by
  rw [screwPrefixMoment_suzukiPrime_eq_suzukiChebyshevLogMomentSum]
  simpa only [Nat.floor_natCast] using
    (suzukiChebyshevLogMomentAbel_eq
      (b := ((cutoff + 1 : ℕ) : ℝ)) (by
        norm_num only [Nat.cast_add, Nat.cast_one]
        have hcutoff : (0 : ℝ) ≤ cutoff := Nat.cast_nonneg cutoff
        linarith))

/-- Prefix mass is exactly the Chebyshev Abel mass functional at its integer
endpoint. -/
theorem screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass
    (cutoff : ℕ) :
    screwPrefixMass suzukiPrimeWeight cutoff =
      suzukiChebyshevWeightedMass ((cutoff + 1 : ℕ) : ℝ) := by
  simpa [suzukiChebyshevWeightedMass] using
    screwPrefixMass_suzukiPrimeWeight_eq_chebyshevPsi cutoff

/-- Prefix first moment is exactly the Chebyshev Abel log-moment functional
at its integer endpoint. -/
theorem screwPrefixMoment_suzukiPrime_eq_chebyshevWeightedLogMoment
    (cutoff : ℕ) :
    screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight cutoff =
      suzukiChebyshevWeightedLogMoment ((cutoff + 1 : ℕ) : ℝ) := by
  simpa [suzukiChebyshevWeightedLogMoment] using
    screwPrefixMoment_suzukiPrime_eq_chebyshevPsi cutoff

/-! ## Removing the synthetic reset from finite prefixes -/

private theorem frozenScrewHingeModel_succ_eq
    (archimedean : ℝ → ℝ) (location weight : ℕ → ℝ)
    (cutoff : ℕ) (t : ℝ) :
    frozenScrewHingeModel archimedean location weight (cutoff + 1) t =
      frozenScrewHingeModel archimedean location weight cutoff t +
        screwAffineKick (weight cutoff) (location cutoff) t := by
  simp [frozenScrewHingeModel, Finset.sum_range_succ]
  ring_nf

/-- A corrected reset prefix with its synthetic first event is exactly the
corresponding literal full prime prefix on the normalized tail. -/
theorem frozenScrewHingeModel_resetPrefix_succ_eq_fullPrefix
    {archimedean : ℝ → ℝ} {baseValue baseSlope base : ℝ}
    {start : ℕ}
    (hnormalization : SuzukiTailNormalization archimedean
      baseValue baseSlope base start)
    {t : ℝ} (ht : base ≤ t) (count : ℕ) :
    frozenScrewHingeModel
        (zeroSlopeCurvatureBackground baseValue base
          suzukiSmoothCurvature)
        (suzukiResetLocation base start)
        (suzukiResetWeight baseSlope start) (count + 1) t =
      frozenScrewHingeModel archimedean suzukiPrimeLocation
        suzukiPrimeWeight (count + start) t := by
  induction count with
  | zero =>
      calc
        frozenScrewHingeModel
            (zeroSlopeCurvatureBackground baseValue base
              suzukiSmoothCurvature)
            (suzukiResetLocation base start)
            (suzukiResetWeight baseSlope start) (0 + 1) t =
            slopeResetCurvatureBackground baseValue baseSlope base
              suzukiSmoothCurvature t := by
                unfold frozenScrewHingeModel
                  slopeResetCurvatureBackground
                simp [screwAffineKick]
        _ = frozenScrewHingeModel archimedean suzukiPrimeLocation
              suzukiPrimeWeight (0 + start) t := by
                simpa using (hnormalization t ht).symm
  | succ count ih =>
      rw [frozenScrewHingeModel_succ_eq, ih]
      have hindex : count + 1 + start = (count + start) + 1 := by
        omega
      rw [hindex, frozenScrewHingeModel_succ_eq]
      simp [suzukiResetLocation_succ, suzukiResetWeight_succ]

/-! ## The literal first-tail Legendre point -/

/-- After adding back the Archimedean slope at `log 2`, every corrected
prefix mass is exactly the mass of the corresponding complete prime prefix. -/
theorem suzukiFirstTailResetPrefixMass_succ_add_archimedeanSlope_eq
    (count : ℕ) :
    screwPrefixMass
        (suzukiResetWeight
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
        (count + 1) +
      suzukiPointwiseArchimedeanSlope (Real.log 2) =
        screwPrefixMass suzukiPrimeWeight (count + 1) := by
  induction count with
  | zero =>
      simp [screwPrefixMass, suzukiPointwiseFrozenBaseSlope]
  | succ count ih =>
      calc
        screwPrefixMass
              (suzukiResetWeight
                (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
              ((count + 1) + 1) +
            suzukiPointwiseArchimedeanSlope (Real.log 2) =
            (screwPrefixMass
                (suzukiResetWeight
                  (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
                (count + 1) +
              suzukiPointwiseArchimedeanSlope (Real.log 2)) +
                suzukiResetWeight
                  (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1
                  (count + 1) := by
                    rw [screwPrefixMass_succ]
                    ring_nf
        _ = screwPrefixMass suzukiPrimeWeight (count + 1) +
              suzukiPrimeWeight (count + 1) := by
                rw [ih]
                simp [suzukiResetWeight_succ]
        _ = screwPrefixMass suzukiPrimeWeight ((count + 1) + 1) := by
              exact (screwPrefixMass_succ suzukiPrimeWeight
                (count + 1)).symm

/-- The corrected mass point for prefix `count + 1` is exactly the point
where the literal Archimedean slope matches the complete prime-prefix mass. -/
theorem suzukiPointwiseArchimedeanSlope_firstTailResetMassPoint_succ_eq
    (count : ℕ) :
    suzukiPointwiseArchimedeanSlope
        (suzukiResetTransportMassPoint (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
          (count + 1)) =
      screwPrefixMass suzukiPrimeWeight (count + 1) := by
  let r := suzukiResetTransportMassPoint (Real.log 2)
    (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
    (le_refl (Real.log 2))
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 (count + 1)
  have hbasePoint : Real.log 2 ≤ r := by
    dsimp only [r]
    exact base_le_suzukiResetTransportMassPoint
      (Real.log 2)
      (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
      (le_refl (Real.log 2))
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 (count + 1)
  have hmass := suzukiResetTransportMassPoint_mass_eq
    (Real.log 2)
    (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
    (le_refl (Real.log 2))
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 (count + 1)
  have hslope := suzukiPointwiseArchimedeanSlope_eq_integrated
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    ((Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hbasePoint)
  change suzukiPointwiseArchimedeanSlope r =
      transportCurvatureMass suzukiSmoothCurvature (Real.log 2) r +
        suzukiPointwiseArchimedeanSlope (Real.log 2) at hslope
  rw [hmass] at hslope
  exact hslope.trans
    (suzukiFirstTailResetPrefixMass_succ_add_archimedeanSlope_eq count)

/-- At its canonical mass point, the corrected transport gap is the value of
the corresponding literal finite prime prefix. -/
theorem suzukiFirstTailResetTransportGap_succ_eq_fullFrozenPrefix
    (count : ℕ) :
    curvatureTransportGap
        (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
        (Real.log 2) suzukiSmoothCurvature
        (suzukiResetLocation (Real.log 2) 1)
        (suzukiResetWeight
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
        (suzukiResetTransportMassPoint (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
        (count + 1) =
      frozenScrewHingeModel suzukiPointwiseArchimedean
        suzukiPrimeLocation suzukiPrimeWeight (count + 1)
        (suzukiResetTransportMassPoint (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
          (count + 1)) := by
  let r := suzukiResetTransportMassPoint (Real.log 2)
    (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
    (le_refl (Real.log 2))
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 (count + 1)
  have hbasePoint : Real.log 2 ≤ r := by
    dsimp only [r]
    exact base_le_suzukiResetTransportMassPoint
      (Real.log 2)
      (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
      (le_refl (Real.log 2))
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 (count + 1)
  have hmass := suzukiResetTransportMassPoint_mass_eq
    (Real.log 2)
    (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
    (le_refl (Real.log 2))
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 (count + 1)
  have hgapModel :
      curvatureTransportGap
          (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
          (Real.log 2) suzukiSmoothCurvature
          (suzukiResetLocation (Real.log 2) 1)
          (suzukiResetWeight
            (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
          (suzukiResetTransportMassPoint (Real.log 2)
            (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
            (le_refl (Real.log 2))
            suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
          (count + 1) =
        frozenScrewHingeModel
          (zeroSlopeCurvatureBackground
            (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
            (Real.log 2) suzukiSmoothCurvature)
          (suzukiResetLocation (Real.log 2) 1)
          (suzukiResetWeight
            (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
          (count + 1) r := by
    unfold curvatureTransportGap
    change suzukiPointwiseFrozenBaseValue (Real.log 2) 1 +
          screwPrefixMoment (suzukiResetLocation (Real.log 2) 1)
            (suzukiResetWeight
              (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
            (count + 1) -
          transportCurvatureMoment suzukiSmoothCurvature
            (Real.log 2) r = _
    rw [frozenScrewHingeModel_zeroSlopeCurvature_eq, hmass]
    ring
  rw [hgapModel]
  exact frozenScrewHingeModel_resetPrefix_succ_eq_fullPrefix
    (suzukiPointwiseTailNormalization
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)) 1)
    hbasePoint count

/-- Expanded form of the preceding identity: the remaining frontier is a
literal finite arithmetic Legendre defect, with no synthetic terms. -/
theorem suzukiFirstTailResetTransportGap_succ_eq_literalLegendreDefect
    (count : ℕ) :
    curvatureTransportGap
        (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
        (Real.log 2) suzukiSmoothCurvature
        (suzukiResetLocation (Real.log 2) 1)
        (suzukiResetWeight
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
        (suzukiResetTransportMassPoint (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
        (count + 1) =
      suzukiPointwiseArchimedean
          (suzukiResetTransportMassPoint (Real.log 2)
            (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
            (le_refl (Real.log 2))
            suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
            (count + 1)) -
        suzukiResetTransportMassPoint (Real.log 2)
            (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
            (le_refl (Real.log 2))
            suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
            (count + 1) *
          screwPrefixMass suzukiPrimeWeight (count + 1) +
        screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight
          (count + 1) := by
  rw [suzukiFirstTailResetTransportGap_succ_eq_fullFrozenPrefix,
    frozenScrewHingeModel_eq_arch_sub_mass_add_moment]

/-- The literal finite Legendre defect written entirely through the two
Chebyshev-`psi` Abel functionals. -/
theorem suzukiFirstTailResetTransportGap_succ_eq_chebyshevLegendreDefect
    (count : ℕ) :
    curvatureTransportGap
        (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
        (Real.log 2) suzukiSmoothCurvature
        (suzukiResetLocation (Real.log 2) 1)
        (suzukiResetWeight
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
        (suzukiResetTransportMassPoint (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
        (count + 1) =
      suzukiPointwiseArchimedean
          (suzukiResetTransportMassPoint (Real.log 2)
            (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
            (le_refl (Real.log 2))
            suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
            (count + 1)) -
        suzukiResetTransportMassPoint (Real.log 2)
            (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
            (le_refl (Real.log 2))
            suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
            (count + 1) *
          suzukiChebyshevWeightedMass ((count + 2 : ℕ) : ℝ) +
        suzukiChebyshevWeightedLogMoment ((count + 2 : ℕ) : ℝ) := by
  rw [suzukiFirstTailResetTransportGap_succ_eq_literalLegendreDefect,
    screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass,
    screwPrefixMoment_suzukiPrime_eq_chebyshevWeightedLogMoment]

/-- Centered-moment form of the same equality.  This is the compact analytic
interface for estimating the entire infinite family through `Chebyshev.psi`. -/
theorem suzukiFirstTailResetTransportGap_succ_eq_archimedean_add_chebyshevCenteredMoment
    (count : ℕ) :
    curvatureTransportGap
        (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
        (Real.log 2) suzukiSmoothCurvature
        (suzukiResetLocation (Real.log 2) 1)
        (suzukiResetWeight
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
        (suzukiResetTransportMassPoint (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
        (count + 1) =
      suzukiPointwiseArchimedean
          (suzukiResetTransportMassPoint (Real.log 2)
            (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
            (le_refl (Real.log 2))
            suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
            (count + 1)) +
        suzukiChebyshevWeightedCenteredLogMoment
          (suzukiResetTransportMassPoint (Real.log 2)
            (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
            (le_refl (Real.log 2))
            suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
            (count + 1))
          ((count + 2 : ℕ) : ℝ) := by
  rw [suzukiFirstTailResetTransportGap_succ_eq_chebyshevLegendreDefect]
  unfold suzukiChebyshevWeightedCenteredLogMoment
  ring_nf

/-- The cutoff-at-least-two surplus criterion in its equivalent canonical
transport-gap form. -/
theorem
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_two_le_cutoff_transportGap :
    (∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t) ↔
      ∀ cutoff : ℕ, 2 ≤ cutoff →
        0 ≤ curvatureTransportGap
          (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
          (Real.log 2) suzukiSmoothCurvature
          (suzukiResetLocation (Real.log 2) 1)
          (suzukiResetWeight
            (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
          (suzukiResetTransportMassPoint (Real.log 2)
            (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
            (le_refl (Real.log 2))
            suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
          cutoff := by
  rw [
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_two_le_cutoff_cumulativeTransportSurplus]
  constructor
  · intro hsums cutoff hcutoff
    rw [suzukiResetTransportGap_eq_baseValue_add_sum]
    have hsum := hsums cutoff hcutoff
    linarith
  · intro hgaps cutoff hcutoff
    have hgap := hgaps cutoff hcutoff
    rw [suzukiResetTransportGap_eq_baseValue_add_sum] at hgap
    linarith

/-- Exact Chebyshev--Legendre frontier.  The only remaining first-tail
obligations are the displayed inequalities for complete prime prefixes
through integer `count + 2`; both arithmetic functionals are explicit finite
Abel transforms of `Chebyshev.psi`. -/
theorem
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_chebyshevLegendreDefect :
    (∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t) ↔
      ∀ count : ℕ, 1 ≤ count →
        0 ≤ suzukiPointwiseArchimedean
            (suzukiResetTransportMassPoint (Real.log 2)
              (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
              (le_refl (Real.log 2))
              suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
              (count + 1)) -
          suzukiResetTransportMassPoint (Real.log 2)
              (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
              (le_refl (Real.log 2))
              suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
              (count + 1) *
            suzukiChebyshevWeightedMass ((count + 2 : ℕ) : ℝ) +
          suzukiChebyshevWeightedLogMoment ((count + 2 : ℕ) : ℝ) := by
  rw [
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_two_le_cutoff_transportGap]
  constructor
  · intro hgaps count hcount
    have hgap := hgaps (count + 1) (by omega)
    rw [suzukiFirstTailResetTransportGap_succ_eq_chebyshevLegendreDefect]
      at hgap
    exact hgap
  · intro hdefects cutoff hcutoff
    let count := cutoff - 1
    have hcount : 1 ≤ count := by
      dsimp only [count]
      omega
    have hdefect := hdefects count hcount
    have hcutoffEq : cutoff = count + 1 := by
      dsimp only [count]
      omega
    rw [hcutoffEq,
      suzukiFirstTailResetTransportGap_succ_eq_chebyshevLegendreDefect]
    exact hdefect

/-- Compact final form: tail positivity is exactly the uniform lower bound
for the Archimedean term plus the `Chebyshev.psi` centered moment at every
literal finite-prefix Legendre point beyond the discharged first prefix. -/
theorem
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_chebyshevCenteredMoment :
    (∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t) ↔
      ∀ count : ℕ, 1 ≤ count →
        0 ≤ suzukiPointwiseArchimedean
            (suzukiResetTransportMassPoint (Real.log 2)
              (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
              (le_refl (Real.log 2))
              suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
              (count + 1)) +
          suzukiChebyshevWeightedCenteredLogMoment
            (suzukiResetTransportMassPoint (Real.log 2)
              (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
              (le_refl (Real.log 2))
              suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
              (count + 1))
            ((count + 2 : ℕ) : ℝ) := by
  rw [
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_chebyshevLegendreDefect]
  constructor
  · intro hdefects count hcount
    have hdefect := hdefects count hcount
    unfold suzukiChebyshevWeightedCenteredLogMoment
    linarith
  · intro hcentered count hcount
    have hcenter := hcentered count hcount
    unfold suzukiChebyshevWeightedCenteredLogMoment at hcenter
    linarith

end

end RiemannGaussian
