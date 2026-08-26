import RiemannGaussian.SuzukiTransportBarrier

/-!
# Correctly normalized Suzuki transport tails

The first transport criterion used the complete Suzuki event schedule together
with a zero-slope background at an arbitrary positive base.  An actual tail
of the screw trajectory has two additional pieces of data:

* a finite prefix of prime events has already occurred; and
* the trajectory can have a nonzero slope at the chosen base.

This file handles both points exactly.  It splits an infinite hinge model at
an arbitrary event cutoff and absorbs a nonpositive initial slope as one
synthetic downward kick at the base.  The resulting schedule again has only
nonnegative weights, so the curvature-mass minimizer machinery applies
without changing its hypotheses.

No numerical normalization is assumed here.  The final theorem exposes the
precise tail-normalization identity that an audited Suzuki base certificate
must establish.
-/

namespace RiemannGaussian

noncomputable section

open scoped BigOperators Topology

/-! ## Shifted and prepended event schedules -/

/-- Discard the first `start` entries of a sequence. -/
def screwTailSequence {α : Type*} (sequence : ℕ → α)
    (start n : ℕ) : α :=
  sequence (n + start)

@[simp] theorem screwTailSequence_apply {α : Type*}
    (sequence : ℕ → α) (start n : ℕ) :
    screwTailSequence sequence start n = sequence (n + start) := rfl

/-- Prepend one synthetic event to a schedule. -/
def screwPrepend {α : Type*} (head : α) (tail : ℕ → α) : ℕ → α
  | 0 => head
  | n + 1 => tail n

@[simp] theorem screwPrepend_zero {α : Type*}
    (head : α) (tail : ℕ → α) :
    screwPrepend head tail 0 = head := rfl

@[simp] theorem screwPrepend_succ {α : Type*}
    (head : α) (tail : ℕ → α) (n : ℕ) :
    screwPrepend head tail (n + 1) = tail n := rfl

theorem monotone_screwTailSequence
    {sequence : ℕ → ℝ} (hmono : Monotone sequence) (start : ℕ) :
    Monotone (screwTailSequence sequence start) := by
  intro a b hab
  exact hmono (Nat.add_le_add_right hab start)

theorem screwTailSequence_unbounded
    {sequence : ℕ → ℝ} (hmono : Monotone sequence)
    (hunbounded : ∀ t : ℝ, ∃ n : ℕ, t < sequence n)
    (start : ℕ) :
    ∀ t : ℝ, ∃ n : ℕ, t < screwTailSequence sequence start n := by
  intro t
  obtain ⟨n, hn⟩ := hunbounded t
  exact ⟨n, hn.trans_le (hmono (Nat.le_add_right n start))⟩

theorem monotone_screwPrepend
    {head : ℝ} {tail : ℕ → ℝ}
    (hhead : head ≤ tail 0) (htail : Monotone tail) :
    Monotone (screwPrepend head tail) := by
  intro a b hab
  cases a with
  | zero =>
      cases b with
      | zero => rfl
      | succ b => exact hhead.trans (htail (Nat.zero_le b))
  | succ a =>
      cases b with
      | zero => omega
      | succ b =>
          exact htail (Nat.succ_le_succ_iff.mp hab)

theorem screwPrepend_unbounded
    {head : ℝ} {tail : ℕ → ℝ}
    (hunbounded : ∀ t : ℝ, ∃ n : ℕ, t < tail n) :
    ∀ t : ℝ, ∃ n : ℕ, t < screwPrepend head tail n := by
  intro t
  obtain ⟨n, hn⟩ := hunbounded t
  exact ⟨n + 1, by simpa using hn⟩

theorem summable_screwPrepend
    {head : ℝ} {tail : ℕ → ℝ} (htail : Summable tail) :
    Summable (screwPrepend head tail) := by
  apply (summable_nat_add_iff 1).mp
  simpa using htail

/-! ## Exact full-model/tail splitting -/

/-- Once every event before `start` lies to the left of `t`, the full hinge
model is exactly the shifted tail model whose background is the frozen
affine continuation of that finite prefix. -/
theorem screwHingeModel_eq_frozenPrefix_tail
    {archimedean : ℝ → ℝ} {location weight : ℕ → ℝ}
    {start : ℕ} {t : ℝ}
    (hsummable : Summable (fun n : ℕ =>
      screwNegativeHinge (weight n) (location n) t))
    (hpast : ∀ n : ℕ, n < start → location n ≤ t) :
    screwHingeModel archimedean location weight t =
      screwHingeModel
        (frozenScrewHingeModel archimedean location weight start)
        (screwTailSequence location start)
        (screwTailSequence weight start) t := by
  let f : ℕ → ℝ := fun n =>
    screwNegativeHinge (weight n) (location n) t
  have hsplit :
      (∑' n : ℕ, f n) =
        (∑ n ∈ Finset.range start, f n) +
          ∑' k : ℕ, f (k + start) := by
    exact (hsummable.sum_add_tsum_nat_add start).symm
  have hprefix :
      (∑ n ∈ Finset.range start, f n) =
        ∑ n ∈ Finset.range start,
          screwAffineKick (weight n) (location n) t := by
    apply Finset.sum_congr rfl
    intro n hn
    exact screwNegativeHinge_eq_affineKick_of_location_le
      (hpast n (Finset.mem_range.mp hn))
  unfold screwHingeModel frozenScrewHingeModel screwTailSequence
  change archimedean t + ∑' n : ℕ, f n =
    (archimedean t +
      ∑ n ∈ Finset.range start,
        screwAffineKick (weight n) (location n) t) +
      ∑' n : ℕ, f (n + start)
  rw [hsplit, hprefix]
  ring

/-! ## Suzuki shifted tail plus its synthetic slope event -/

/-- Future Suzuki event locations after a finite integer cutoff. -/
def suzukiPrimeTailLocation (start : ℕ) : ℕ → ℝ :=
  screwTailSequence suzukiPrimeLocation start

/-- Future Suzuki event weights after a finite integer cutoff. -/
def suzukiPrimeTailWeight (start : ℕ) : ℕ → ℝ :=
  screwTailSequence suzukiPrimeWeight start

/-- The corrected reset schedule: a synthetic event at the base followed by
all prime events after `start`. -/
def suzukiResetLocation (base : ℝ) (start : ℕ) : ℕ → ℝ :=
  screwPrepend base (suzukiPrimeTailLocation start)

/-- The synthetic event has weight `-baseSlope`; it is nonnegative precisely
when the audited tail starts with nonpositive slope. -/
def suzukiResetWeight (baseSlope : ℝ) (start : ℕ) : ℕ → ℝ :=
  screwPrepend (-baseSlope) (suzukiPrimeTailWeight start)

@[simp] theorem suzukiResetLocation_zero (base : ℝ) (start : ℕ) :
    suzukiResetLocation base start 0 = base := rfl

@[simp] theorem suzukiResetLocation_succ
    (base : ℝ) (start n : ℕ) :
    suzukiResetLocation base start (n + 1) =
      suzukiPrimeLocation (n + start) := rfl

@[simp] theorem suzukiResetWeight_zero (baseSlope : ℝ) (start : ℕ) :
    suzukiResetWeight baseSlope start 0 = -baseSlope := rfl

@[simp] theorem suzukiResetWeight_succ
    (baseSlope : ℝ) (start n : ℕ) :
    suzukiResetWeight baseSlope start (n + 1) =
      suzukiPrimeWeight (n + start) := rfl

/-- Smooth background with prescribed value and slope at the base. -/
def slopeResetCurvatureBackground
    (baseValue baseSlope base : ℝ) (curvature : ℝ → ℝ) (t : ℝ) : ℝ :=
  zeroSlopeCurvatureBackground baseValue base curvature t +
    baseSlope * (t - base)

@[simp] theorem slopeResetCurvatureBackground_at_base
    (baseValue baseSlope base : ℝ) (curvature : ℝ → ℝ) :
    slopeResetCurvatureBackground baseValue baseSlope base curvature base =
      baseValue := by
  simp [slopeResetCurvatureBackground]

theorem suzukiPrimeTailWeight_nonnegative (start n : ℕ) :
    0 ≤ suzukiPrimeTailWeight start n :=
  suzukiPrimeWeight_nonnegative (n + start)

theorem suzukiResetWeight_nonnegative
    {baseSlope : ℝ} (hslope : baseSlope ≤ 0) (start n : ℕ) :
    0 ≤ suzukiResetWeight baseSlope start n := by
  cases n with
  | zero => simpa [suzukiResetWeight] using neg_nonneg.mpr hslope
  | succ n =>
      exact suzukiPrimeTailWeight_nonnegative start n

theorem monotone_suzukiPrimeTailLocation (start : ℕ) :
    Monotone (suzukiPrimeTailLocation start) :=
  monotone_screwTailSequence monotone_suzukiPrimeLocation start

theorem suzukiPrimeTailLocation_unbounded (start : ℕ) :
    ∀ t : ℝ, ∃ n : ℕ, t < suzukiPrimeTailLocation start n :=
  screwTailSequence_unbounded monotone_suzukiPrimeLocation
    suzukiPrimeLocation_unbounded start

theorem monotone_suzukiResetLocation
    {base : ℝ} {start : ℕ}
    (hfuture : base ≤ suzukiPrimeLocation start) :
    Monotone (suzukiResetLocation base start) := by
  apply monotone_screwPrepend
  · simpa [suzukiResetLocation, suzukiPrimeTailLocation] using hfuture
  · exact monotone_suzukiPrimeTailLocation start

theorem suzukiResetLocation_unbounded (base : ℝ) (start : ℕ) :
    ∀ t : ℝ, ∃ n : ℕ, t < suzukiResetLocation base start n :=
  screwPrepend_unbounded (suzukiPrimeTailLocation_unbounded start)

theorem suzukiResetEventCutsCover
    {base : ℝ} {start : ℕ}
    (hfuture : base ≤ suzukiPrimeLocation start) :
    ScrewEventCutsCover (suzukiResetLocation base start) :=
  screwEventCutsCover_of_monotone_unbounded
    (monotone_suzukiResetLocation hfuture)
    (suzukiResetLocation_unbounded base start)

theorem summable_suzukiPrimeTailNegativeHinge
    (start : ℕ) (t : ℝ) :
    Summable (fun n : ℕ =>
      screwNegativeHinge (suzukiPrimeTailWeight start n)
        (suzukiPrimeTailLocation start n) t) := by
  exact (summable_nat_add_iff start).mpr
    (summable_suzukiPrimeNegativeHinge t)

theorem summable_suzukiResetNegativeHinge
    (base baseSlope : ℝ) (start : ℕ) (t : ℝ) :
    Summable (fun n : ℕ =>
      screwNegativeHinge (suzukiResetWeight baseSlope start n)
        (suzukiResetLocation base start n) t) := by
  have heq :
      (fun n : ℕ =>
        screwNegativeHinge (suzukiResetWeight baseSlope start n)
          (suzukiResetLocation base start n) t) =
        screwPrepend (screwNegativeHinge (-baseSlope) base t)
          (fun n : ℕ =>
            screwNegativeHinge (suzukiPrimeTailWeight start n)
              (suzukiPrimeTailLocation start n) t) := by
    funext n
    cases n <;> rfl
  rw [heq]
  exact summable_screwPrepend
    (summable_suzukiPrimeTailNegativeHinge start t)

/-- On the tail half-line, the synthetic base kick is exactly the prescribed
affine initial-slope term. -/
theorem suzukiResetModel_eq_slopeResetTail
    (baseValue baseSlope base : ℝ) (start : ℕ) {t : ℝ}
    (ht : base ≤ t) :
    screwHingeModel
        (zeroSlopeCurvatureBackground baseValue base
          suzukiSmoothCurvature)
        (suzukiResetLocation base start)
        (suzukiResetWeight baseSlope start) t =
      screwHingeModel
        (slopeResetCurvatureBackground baseValue baseSlope base
          suzukiSmoothCurvature)
        (suzukiPrimeTailLocation start)
        (suzukiPrimeTailWeight start) t := by
  rw [screwHingeModel_eq_frozenPrefix_tail
    (summable_suzukiResetNegativeHinge base baseSlope start t)
    (start := 1) (fun n hn => by
      have hn0 : n = 0 := by omega
      subst n
      simpa [suzukiResetLocation] using ht)]
  congr 1
  funext s
  unfold frozenScrewHingeModel slopeResetCurvatureBackground
    suzukiResetLocation suzukiResetWeight
  simp [screwAffineKick]

/-! ## The exact normalization interface -/

/-- Exact data needed to reset the full Suzuki hinge model at `base` after
the finite prime prefix `start`.  It is deliberately a function identity on
the entire tail, not an informal value/derivative assertion. -/
def SuzukiTailNormalization
    (archimedean : ℝ → ℝ) (baseValue baseSlope base : ℝ)
    (start : ℕ) : Prop :=
  ∀ t : ℝ, base ≤ t →
    frozenScrewHingeModel archimedean suzukiPrimeLocation
        suzukiPrimeWeight start t =
      slopeResetCurvatureBackground baseValue baseSlope base
        suzukiSmoothCurvature t

/-- A verified normalization converts the complete Suzuki model exactly into
the corrected reset-tail model. -/
theorem suzukiFullModel_eq_resetModel_on_tail
    {archimedean : ℝ → ℝ} {baseValue baseSlope base : ℝ}
    {start : ℕ}
    (hcut : ScrewEventCut suzukiPrimeLocation base start)
    (hnormalization : SuzukiTailNormalization archimedean
      baseValue baseSlope base start) :
    ∀ t : ℝ, base ≤ t →
      screwHingeModel archimedean suzukiPrimeLocation
          suzukiPrimeWeight t =
        screwHingeModel
          (zeroSlopeCurvatureBackground baseValue base
            suzukiSmoothCurvature)
          (suzukiResetLocation base start)
          (suzukiResetWeight baseSlope start) t := by
  intro t ht
  rw [screwHingeModel_eq_frozenPrefix_tail
    (summable_suzukiPrimeNegativeHinge t)
    (fun n hn => (hcut.1 n hn).trans ht)]
  unfold screwHingeModel
  rw [hnormalization t ht]
  exact (suzukiResetModel_eq_slopeResetTail
    baseValue baseSlope base start ht).symm

/-! ## Generic recurrence for a supplied mass-point sequence -/

/-- Prefix gap associated with an arbitrary sequence of curvature-mass
matching points. -/
def curvatureTransportGap
    (baseValue base : ℝ) (curvature : ℝ → ℝ)
    (location weight : ℕ → ℝ) (massPoint : ℕ → ℝ)
    (cutoff : ℕ) : ℝ :=
  baseValue + screwPrefixMoment location weight cutoff -
    transportCurvatureMoment curvature base (massPoint cutoff)

/-- Signed barycenter surplus of one arbitrary transport cell. -/
def curvatureTransportCellSurplus
    (curvature : ℝ → ℝ) (location massPoint : ℕ → ℝ)
    (cutoff : ℕ) : ℝ :=
  ∫ s in massPoint cutoff..massPoint (cutoff + 1),
    (location cutoff - s) * curvature s

private theorem tail_intervalIntegrable_of_continuousOn_Ici
    {curvature : ℝ → ℝ} {base a b : ℝ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (ha : base ≤ a) (hb : base ≤ b) :
    IntervalIntegrable curvature MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hcontinuous.mono
  intro s hs
  rcases Set.mem_uIcc.mp hs with has | hbs
  · exact ha.trans has.1
  · exact hb.trans hbs.1

private theorem tail_intervalIntegrable_moment_of_continuousOn_Ici
    {curvature : ℝ → ℝ} {base a b : ℝ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (ha : base ≤ a) (hb : base ≤ b) :
    IntervalIntegrable (fun s : ℝ => s * curvature s)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_id.mul hcontinuous).mono
  intro s hs
  rcases Set.mem_uIcc.mp hs with has | hbs
  · exact ha.trans has.1
  · exact hb.trans hbs.1

/-- Every supplied mass cell carries exactly its corresponding event weight. -/
theorem integral_curvature_transportCell_eq_weight
    {base : ℝ} {curvature : ℝ → ℝ}
    {weight massPoint : ℕ → ℝ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (hbase : ∀ cutoff : ℕ, base ≤ massPoint cutoff)
    (hmass : ∀ cutoff : ℕ,
      transportCurvatureMass curvature base (massPoint cutoff) =
        screwPrefixMass weight cutoff)
    (cutoff : ℕ) :
    (∫ s in massPoint cutoff..massPoint (cutoff + 1), curvature s) =
      weight cutoff := by
  let r := massPoint cutoff
  let r' := massPoint (cutoff + 1)
  have hc_base_r := tail_intervalIntegrable_of_continuousOn_Ici
    hcontinuous (le_refl base) (hbase cutoff)
  have hc_r_r' := tail_intervalIntegrable_of_continuousOn_Ici
    hcontinuous (hbase cutoff) (hbase (cutoff + 1))
  have hsplit :
      transportCurvatureMass curvature base r' =
        transportCurvatureMass curvature base r +
          ∫ s in r..r', curvature s := by
    unfold transportCurvatureMass
    exact (intervalIntegral.integral_add_adjacent_intervals
      hc_base_r hc_r_r').symm
  change (∫ s in r..r', curvature s) = _
  rw [hmass (cutoff + 1), hmass cutoff, screwPrefixMass_succ] at hsplit
  linarith

/-- First moments split across every supplied consecutive mass cell. -/
theorem transportCurvatureMoment_massPoint_succ
    {base : ℝ} {curvature : ℝ → ℝ} {massPoint : ℕ → ℝ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (hbase : ∀ cutoff : ℕ, base ≤ massPoint cutoff)
    (cutoff : ℕ) :
    transportCurvatureMoment curvature base (massPoint (cutoff + 1)) =
      transportCurvatureMoment curvature base (massPoint cutoff) +
        ∫ s in massPoint cutoff..massPoint (cutoff + 1),
          s * curvature s := by
  have hj_base_r := tail_intervalIntegrable_moment_of_continuousOn_Ici
    hcontinuous (le_refl base) (hbase cutoff)
  have hj_r_r' := tail_intervalIntegrable_moment_of_continuousOn_Ici
    hcontinuous (hbase cutoff) (hbase (cutoff + 1))
  unfold transportCurvatureMoment
  exact (intervalIntegral.integral_add_adjacent_intervals
    hj_base_r hj_r_r').symm

/-- A generic cell surplus is atomic first moment minus smooth first moment. -/
theorem curvatureTransportCellSurplus_eq
    {base : ℝ} {curvature : ℝ → ℝ}
    {location weight massPoint : ℕ → ℝ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (hbase : ∀ cutoff : ℕ, base ≤ massPoint cutoff)
    (hmass : ∀ cutoff : ℕ,
      transportCurvatureMass curvature base (massPoint cutoff) =
        screwPrefixMass weight cutoff)
    (cutoff : ℕ) :
    curvatureTransportCellSurplus curvature location massPoint cutoff =
      weight cutoff * location cutoff -
        ∫ s in massPoint cutoff..massPoint (cutoff + 1),
          s * curvature s := by
  let r := massPoint cutoff
  let r' := massPoint (cutoff + 1)
  have hc := tail_intervalIntegrable_of_continuousOn_Ici hcontinuous
    (hbase cutoff) (hbase (cutoff + 1))
  have hj := tail_intervalIntegrable_moment_of_continuousOn_Ici hcontinuous
    (hbase cutoff) (hbase (cutoff + 1))
  have hfun :
      (fun s : ℝ => (location cutoff - s) * curvature s) =
        fun s : ℝ => location cutoff * curvature s - s * curvature s := by
    funext s
    ring
  unfold curvatureTransportCellSurplus
  change (∫ s in r..r', (location cutoff - s) * curvature s) = _
  rw [hfun, intervalIntegral.integral_sub
    (hc.const_mul (location cutoff)) hj,
    intervalIntegral.integral_const_mul,
    integral_curvature_transportCell_eq_weight hcontinuous hbase hmass]
  ring

/-- Exact generic gap recurrence. -/
theorem curvatureTransportGap_succ
    {baseValue base : ℝ} {curvature : ℝ → ℝ}
    {location weight massPoint : ℕ → ℝ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (hbase : ∀ cutoff : ℕ, base ≤ massPoint cutoff)
    (hmass : ∀ cutoff : ℕ,
      transportCurvatureMass curvature base (massPoint cutoff) =
        screwPrefixMass weight cutoff)
    (cutoff : ℕ) :
    curvatureTransportGap baseValue base curvature location weight massPoint
        (cutoff + 1) =
      curvatureTransportGap baseValue base curvature location weight massPoint
          cutoff +
        curvatureTransportCellSurplus curvature location massPoint cutoff := by
  unfold curvatureTransportGap
  rw [screwPrefixMoment_succ,
    transportCurvatureMoment_massPoint_succ hcontinuous hbase,
    curvatureTransportCellSurplus_eq hcontinuous hbase hmass]
  ring

/-- Generic telescoping identity from a base mass point. -/
theorem curvatureTransportGap_eq_baseValue_add_sum
    {baseValue base : ℝ} {curvature : ℝ → ℝ}
    {location weight massPoint : ℕ → ℝ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (hbase : ∀ cutoff : ℕ, base ≤ massPoint cutoff)
    (hmass : ∀ cutoff : ℕ,
      transportCurvatureMass curvature base (massPoint cutoff) =
        screwPrefixMass weight cutoff)
    (hmassPoint_zero : massPoint 0 = base)
    (cutoff : ℕ) :
    curvatureTransportGap baseValue base curvature location weight massPoint
        cutoff =
      baseValue +
        ∑ n ∈ Finset.range cutoff,
          curvatureTransportCellSurplus curvature location massPoint n := by
  induction cutoff with
  | zero =>
      simp [curvatureTransportGap, screwPrefixMoment, hmassPoint_zero]
  | succ cutoff ih =>
      rw [curvatureTransportGap_succ hcontinuous hbase hmass, ih,
        Finset.sum_range_succ]
      ring

/-! ## Canonical corrected Suzuki mass points -/

/-- Canonical mass point for a prefix of the corrected reset schedule. -/
def suzukiResetTransportMassPoint
    (base baseSlope : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start cutoff : ℕ) : ℝ :=
  Classical.choose (exists_suzukiTransportMass_eq hlog
    (screwPrefixMass_nonnegative
      (suzukiResetWeight_nonnegative hslope start) cutoff))

theorem base_le_suzukiResetTransportMassPoint
    (base baseSlope : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start cutoff : ℕ) :
    base ≤ suzukiResetTransportMassPoint base baseSlope hlog hslope
      start cutoff := by
  unfold suzukiResetTransportMassPoint
  exact (Classical.choose_spec (exists_suzukiTransportMass_eq hlog
    (screwPrefixMass_nonnegative
      (suzukiResetWeight_nonnegative hslope start) cutoff))).1

theorem suzukiResetTransportMassPoint_mass_eq
    (base baseSlope : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start cutoff : ℕ) :
    transportCurvatureMass suzukiSmoothCurvature base
        (suzukiResetTransportMassPoint base baseSlope hlog hslope
          start cutoff) =
      screwPrefixMass (suzukiResetWeight baseSlope start) cutoff := by
  unfold suzukiResetTransportMassPoint
  exact (Classical.choose_spec (exists_suzukiTransportMass_eq hlog
    (screwPrefixMass_nonnegative
      (suzukiResetWeight_nonnegative hslope start) cutoff))).2

@[simp] theorem suzukiResetTransportMassPoint_zero
    (base baseSlope : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start : ℕ) :
    suzukiResetTransportMassPoint base baseSlope hlog hslope start 0 =
      base := by
  apply (strictlyMonoOn_suzukiTransportCurvatureMass hlog).injOn
  · exact base_le_suzukiResetTransportMassPoint
      base baseSlope hlog hslope start 0
  · exact le_refl base
  · rw [suzukiResetTransportMassPoint_mass_eq]
    simp [screwPrefixMass]

/-- Generic pointwise barrier equivalence used by the corrected schedule. -/
theorem frozenScrewRegime_nonnegativeOn_iff_transportGap
    {baseValue base r : ℝ} {curvature : ℝ → ℝ}
    {location weight : ℕ → ℝ} {cutoff : ℕ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (hcurvature : ∀ t : ℝ, base ≤ t → 0 ≤ curvature t)
    (hbase_r : base ≤ r)
    (hmass : transportCurvatureMass curvature base r =
      screwPrefixMass weight cutoff) :
    (∀ t : ℝ, base ≤ t →
      0 ≤ frozenScrewHingeModel
        (zeroSlopeCurvatureBackground baseValue base curvature)
        location weight cutoff t) ↔
      0 ≤ baseValue + screwPrefixMoment location weight cutoff -
        transportCurvatureMoment curvature base r := by
  have hmin := frozenScrewHingeModel_minimized_at_massPoint
    (baseMargin := baseValue) (location := location) (weight := weight)
    hcontinuous hcurvature hbase_r hmass
  have hvalue :
      frozenScrewHingeModel
          (zeroSlopeCurvatureBackground baseValue base curvature)
          location weight cutoff r =
        baseValue + screwPrefixMoment location weight cutoff -
          transportCurvatureMoment curvature base r := by
    rw [frozenScrewHingeModel_zeroSlopeCurvature_eq, hmass]
    ring
  constructor
  · intro hall
    rw [← hvalue]
    exact hall r hbase_r
  · intro hgap t ht
    rw [← hvalue] at hgap
    exact hgap.trans (hmin t ht)

/-- Corrected reset-tail positivity is exactly the family of its canonical
transport gaps. -/
theorem suzukiResetModel_nonnegativeOn_tail_iff_transportGaps
    (baseValue baseSlope base : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start : ℕ)
    (hfuture : base ≤ suzukiPrimeLocation start) :
    (∀ t : ℝ, base ≤ t →
      0 ≤ screwHingeModel
        (zeroSlopeCurvatureBackground baseValue base
          suzukiSmoothCurvature)
        (suzukiResetLocation base start)
        (suzukiResetWeight baseSlope start) t) ↔
      ∀ cutoff : ℕ,
        0 ≤ curvatureTransportGap baseValue base suzukiSmoothCurvature
          (suzukiResetLocation base start)
          (suzukiResetWeight baseSlope start)
          (suzukiResetTransportMassPoint base baseSlope hlog hslope start)
          cutoff := by
  have hcontinuous :
      ContinuousOn suzukiSmoothCurvature (Set.Ici base) :=
    continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro t ht
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog.trans ht))
  have hcurvature : ∀ t : ℝ, base ≤ t →
      0 ≤ suzukiSmoothCurvature t := by
    intro t ht
    exact (suzukiSmoothCurvature_pos_of_log_two_le (hlog.trans ht)).le
  have hfreeze := screwHingeModel_nonnegativeOn_iff_all_frozen
    (archimedean := zeroSlopeCurvatureBackground baseValue base
      suzukiSmoothCurvature)
    (Set.Ici base) (suzukiResetWeight_nonnegative hslope start)
    (summable_suzukiResetNegativeHinge base baseSlope start)
    (suzukiResetEventCutsCover hfuture)
  constructor
  · intro hmodel cutoff
    have hall := hfreeze.mp (by
      intro t ht
      exact hmodel t ht)
    apply (frozenScrewRegime_nonnegativeOn_iff_transportGap
      hcontinuous hcurvature
      (base_le_suzukiResetTransportMassPoint
        base baseSlope hlog hslope start cutoff)
      (suzukiResetTransportMassPoint_mass_eq
        base baseSlope hlog hslope start cutoff)).1
    intro t ht
    exact hall cutoff t ht
  · intro hgaps
    apply hfreeze.mpr
    intro cutoff t ht
    apply (frozenScrewRegime_nonnegativeOn_iff_transportGap
      hcontinuous hcurvature
      (base_le_suzukiResetTransportMassPoint
        base baseSlope hlog hslope start cutoff)
      (suzukiResetTransportMassPoint_mass_eq
        base baseSlope hlog hslope start cutoff)).2 (hgaps cutoff)
    exact ht

/-- Canonical corrected cell surplus.  Cell zero transports the synthetic
initial-slope mass; every later cell transports one future prime weight. -/
def suzukiResetTransportCellSurplus
    (base baseSlope : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start cutoff : ℕ) : ℝ :=
  curvatureTransportCellSurplus suzukiSmoothCurvature
    (suzukiResetLocation base start)
    (suzukiResetTransportMassPoint base baseSlope hlog hslope start)
    cutoff

/-- The first corrected cell carries exactly the mass needed to cancel the
audited nonpositive base slope. -/
theorem suzukiResetTransportMassPoint_one_mass_eq_neg_slope
    (base baseSlope : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start : ℕ) :
    transportCurvatureMass suzukiSmoothCurvature base
        (suzukiResetTransportMassPoint base baseSlope hlog hslope start 1) =
      -baseSlope := by
  simpa [screwPrefixMass] using
    suzukiResetTransportMassPoint_mass_eq
      base baseSlope hlog hslope start 1

/-- Cell zero is the exact descent from the audited base to the zero-slope
point preceding the first future prime event. -/
theorem suzukiResetTransportCellSurplus_zero
    (base baseSlope : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start : ℕ) :
    suzukiResetTransportCellSurplus base baseSlope hlog hslope start 0 =
      ∫ s in base..
          suzukiResetTransportMassPoint base baseSlope hlog hslope start 1,
        (base - s) * suzukiSmoothCurvature s := by
  simp [suzukiResetTransportCellSurplus,
    curvatureTransportCellSurplus]

/-- Every later corrected cell is indexed by the corresponding future
integer in the original Suzuki schedule. -/
theorem suzukiResetTransportCellSurplus_succ
    (base baseSlope : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start n : ℕ) :
    suzukiResetTransportCellSurplus base baseSlope hlog hslope
        start (n + 1) =
      ∫ s in
          suzukiResetTransportMassPoint base baseSlope hlog hslope
            start (n + 1)..
          suzukiResetTransportMassPoint base baseSlope hlog hslope
            start (n + 2),
        (suzukiPrimeLocation (n + start) - s) *
          suzukiSmoothCurvature s := by
  rfl

/-- Every corrected gap is the audited base value plus the cumulative signed
surplus, including the initial synthetic-slope cell. -/
theorem suzukiResetTransportGap_eq_baseValue_add_sum
    (baseValue baseSlope base : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start cutoff : ℕ) :
    curvatureTransportGap baseValue base suzukiSmoothCurvature
        (suzukiResetLocation base start)
        (suzukiResetWeight baseSlope start)
        (suzukiResetTransportMassPoint base baseSlope hlog hslope start)
        cutoff =
      baseValue +
        ∑ n ∈ Finset.range cutoff,
          suzukiResetTransportCellSurplus base baseSlope hlog hslope
            start n := by
  apply curvatureTransportGap_eq_baseValue_add_sum
  · exact continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro t ht
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog.trans ht))
  · exact base_le_suzukiResetTransportMassPoint
      base baseSlope hlog hslope start
  · exact suzukiResetTransportMassPoint_mass_eq
      base baseSlope hlog hslope start
  · exact suzukiResetTransportMassPoint_zero
      base baseSlope hlog hslope start

/-- The first nontrivial gap is exactly the initial zero-slope barrier used
in the transport note, obtained without postulating an exact zero of a
derivative. -/
theorem suzukiResetTransportGap_one
    (baseValue baseSlope base : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start : ℕ) :
    curvatureTransportGap baseValue base suzukiSmoothCurvature
        (suzukiResetLocation base start)
        (suzukiResetWeight baseSlope start)
        (suzukiResetTransportMassPoint base baseSlope hlog hslope start) 1 =
      baseValue +
        ∫ s in base..
            suzukiResetTransportMassPoint base baseSlope hlog hslope start 1,
          (base - s) * suzukiSmoothCurvature s := by
  rw [suzukiResetTransportGap_eq_baseValue_add_sum]
  simp [suzukiResetTransportCellSurplus_zero]

/-- Corrected reset-tail positivity in its exact cumulative form. -/
theorem suzukiResetModel_nonnegativeOn_tail_iff_cumulativeSurplus
    (baseValue baseSlope base : ℝ) (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0) (start : ℕ)
    (hfuture : base ≤ suzukiPrimeLocation start) :
    (∀ t : ℝ, base ≤ t →
      0 ≤ screwHingeModel
        (zeroSlopeCurvatureBackground baseValue base
          suzukiSmoothCurvature)
        (suzukiResetLocation base start)
        (suzukiResetWeight baseSlope start) t) ↔
      ∀ cutoff : ℕ,
        -baseValue ≤
          ∑ n ∈ Finset.range cutoff,
            suzukiResetTransportCellSurplus base baseSlope hlog hslope
              start n := by
  rw [suzukiResetModel_nonnegativeOn_tail_iff_transportGaps
    baseValue baseSlope base hlog hslope start hfuture]
  constructor
  · intro hgaps cutoff
    have hgap := hgaps cutoff
    rw [suzukiResetTransportGap_eq_baseValue_add_sum] at hgap
    linarith
  · intro hsums cutoff
    rw [suzukiResetTransportGap_eq_baseValue_add_sum]
    have hsum := hsums cutoff
    linarith

/-- Final corrected full-model frontier.  Once the finite base normalization
is audited, nonnegativity on the complete future tail is equivalent to a
single cumulative-surplus theorem over the shifted prime schedule. -/
theorem suzukiFullModel_nonnegativeOn_tail_iff_cumulativeTransportSurplus
    {archimedean : ℝ → ℝ} {baseValue baseSlope base : ℝ}
    {start : ℕ} (hlog : Real.log 2 ≤ base)
    (hslope : baseSlope ≤ 0)
    (hcut : ScrewEventCut suzukiPrimeLocation base start)
    (hnormalization : SuzukiTailNormalization archimedean
      baseValue baseSlope base start) :
    (∀ t : ℝ, base ≤ t →
      0 ≤ screwHingeModel archimedean suzukiPrimeLocation
        suzukiPrimeWeight t) ↔
      ∀ cutoff : ℕ,
        -baseValue ≤
          ∑ n ∈ Finset.range cutoff,
            suzukiResetTransportCellSurplus base baseSlope hlog hslope
              start n := by
  have hfuture : base ≤ suzukiPrimeLocation start := by
    simpa using hcut.2 0
  rw [← suzukiResetModel_nonnegativeOn_tail_iff_cumulativeSurplus
    baseValue baseSlope base hlog hslope start hfuture]
  constructor
  · intro hfull t ht
    rw [← suzukiFullModel_eq_resetModel_on_tail hcut hnormalization t ht]
    exact hfull t ht
  · intro hreset t ht
    rw [suzukiFullModel_eq_resetModel_on_tail hcut hnormalization t ht]
    exact hreset t ht

end

end RiemannGaussian
