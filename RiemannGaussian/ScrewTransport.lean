import RiemannGaussian.GaussianPositivityCertificate

/-!
# Frozen-hinge and Legendre barriers for the screw-function route

Suzuki's pointwise screw-function criterion writes its prime contribution as
a locally finite sum of negative hinges.  The research note
`RH_Screw_Transport_Legendre_Attack` observes that replacing the first
`cutoff` hinges by their affine extensions and omitting all later hinges
gives a pointwise majorant which agrees with the true function on the
corresponding prime cell.

This file kernel-checks that reduction without assuming RH.  It separates
the formal convex geometry from the two genuinely number-theoretic tasks:
identifying the full Suzuki Archimedean term and proving every resulting
barrier nonnegative.  The latter remains an RH-strength obligation.
-/

namespace RiemannGaussian

noncomputable section

open scoped BigOperators Topology

/-! ## Abstract negative hinges -/

/-- A downward slope jump of size `weight` at `location`. -/
def screwNegativeHinge (weight location t : ℝ) : ℝ :=
  -(weight * max (t - location) 0)

/-- The affine continuation of a negative hinge through its event point. -/
def screwAffineKick (weight location t : ℝ) : ℝ :=
  -(weight * (t - location))

theorem screwNegativeHinge_nonpositive
    {weight location t : ℝ} (hweight : 0 ≤ weight) :
    screwNegativeHinge weight location t ≤ 0 := by
  unfold screwNegativeHinge
  exact neg_nonpos.mpr (mul_nonneg hweight (le_max_right _ _))

/-- Extending a past hinge affinely can only raise it before its event. -/
theorem screwNegativeHinge_le_affineKick
    {weight location t : ℝ} (hweight : 0 ≤ weight) :
    screwNegativeHinge weight location t ≤
      screwAffineKick weight location t := by
  unfold screwNegativeHinge screwAffineKick
  exact neg_le_neg
    (mul_le_mul_of_nonneg_left (le_max_left (t - location) 0) hweight)

theorem screwNegativeHinge_eq_affineKick_of_location_le
    {weight location t : ℝ} (hlocation : location ≤ t) :
    screwNegativeHinge weight location t =
      screwAffineKick weight location t := by
  simp [screwNegativeHinge, screwAffineKick,
    max_eq_left (sub_nonneg.mpr hlocation)]

theorem screwNegativeHinge_eq_zero_of_le_location
    {weight location t : ℝ} (ht : t ≤ location) :
    screwNegativeHinge weight location t = 0 := by
  simp [screwNegativeHinge, max_eq_right (sub_nonpos.mpr ht)]

/-- A smooth background plus the complete, locally finite negative-hinge
sum. -/
def screwHingeModel
    (archimedean : ℝ → ℝ) (location weight : ℕ → ℝ) (t : ℝ) : ℝ :=
  archimedean t +
    ∑' n : ℕ, screwNegativeHinge (weight n) (location n) t

/-- The frozen regime: the first `cutoff` hinges are continued affinely and
all later hinges are omitted. -/
def frozenScrewHingeModel
    (archimedean : ℝ → ℝ) (location weight : ℕ → ℝ)
    (cutoff : ℕ) (t : ℝ) : ℝ :=
  archimedean t +
    ∑ n ∈ Finset.range cutoff,
      screwAffineKick (weight n) (location n) t

/-- Cumulative slope-jump mass in a frozen regime. -/
def screwPrefixMass (weight : ℕ → ℝ) (cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff, weight n

/-- Cumulative first location moment in a frozen regime. -/
def screwPrefixMoment
    (location weight : ℕ → ℝ) (cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff, weight n * location n

/-- Exact affine/Legendre form of a frozen regime. -/
theorem frozenScrewHingeModel_eq_arch_sub_mass_add_moment
    (archimedean : ℝ → ℝ) (location weight : ℕ → ℝ)
    (cutoff : ℕ) (t : ℝ) :
    frozenScrewHingeModel archimedean location weight cutoff t =
      archimedean t - t * screwPrefixMass weight cutoff +
        screwPrefixMoment location weight cutoff := by
  unfold frozenScrewHingeModel screwPrefixMass screwPrefixMoment
  have hterm : ∀ n : ℕ,
      screwAffineKick (weight n) (location n) t =
        -(t * weight n) + weight n * location n := by
    intro n
    unfold screwAffineKick
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  ring

/-- The frozen regime majorizes the true infinite hinge model everywhere. -/
theorem screwHingeModel_le_frozen
    {archimedean : ℝ → ℝ} {location weight : ℕ → ℝ}
    (hweight : ∀ n, 0 ≤ weight n) {t : ℝ}
    (hsummable : Summable
      (fun n : ℕ => screwNegativeHinge (weight n) (location n) t))
    (cutoff : ℕ) :
    screwHingeModel archimedean location weight t ≤
      frozenScrewHingeModel archimedean location weight cutoff t := by
  let f : ℕ → ℝ := fun n =>
    screwNegativeHinge (weight n) (location n) t
  have hsplit :
      (∑' n : ℕ, f n) =
        (∑ n ∈ Finset.range cutoff, f n) +
          ∑' k : ℕ, f (k + cutoff) := by
    exact (hsummable.sum_add_tsum_nat_add cutoff).symm
  have hprefix :
      (∑ n ∈ Finset.range cutoff, f n) ≤
        ∑ n ∈ Finset.range cutoff,
          screwAffineKick (weight n) (location n) t := by
    apply Finset.sum_le_sum
    intro n hn
    exact screwNegativeHinge_le_affineKick (hweight n)
  have htail : (∑' k : ℕ, f (k + cutoff)) ≤ 0 := by
    apply tsum_nonpos
    intro k
    exact screwNegativeHinge_nonpositive (hweight (k + cutoff))
  unfold screwHingeModel frozenScrewHingeModel
  change archimedean t + ∑' n : ℕ, f n ≤ _
  rw [hsplit]
  linarith

/-- A cutoff separates the already active events from all future events. -/
def ScrewEventCut (location : ℕ → ℝ) (t : ℝ) (cutoff : ℕ) : Prop :=
  (∀ n, n < cutoff → location n ≤ t) ∧
    (∀ k, t ≤ location (k + cutoff))

/-- Every center lies in one of the event cells. -/
def ScrewEventCutsCover (location : ℕ → ℝ) : Prop :=
  ∀ t : ℝ, ∃ cutoff : ℕ, ScrewEventCut location t cutoff

/-- On its own event cell, the frozen regime is exactly the true model. -/
theorem screwHingeModel_eq_frozen_of_eventCut
    {archimedean : ℝ → ℝ} {location weight : ℕ → ℝ}
    {t : ℝ} {cutoff : ℕ}
    (hsummable : Summable
      (fun n : ℕ => screwNegativeHinge (weight n) (location n) t))
    (hcut : ScrewEventCut location t cutoff) :
    screwHingeModel archimedean location weight t =
      frozenScrewHingeModel archimedean location weight cutoff t := by
  let f : ℕ → ℝ := fun n =>
    screwNegativeHinge (weight n) (location n) t
  have hsplit :
      (∑' n : ℕ, f n) =
        (∑ n ∈ Finset.range cutoff, f n) +
          ∑' k : ℕ, f (k + cutoff) := by
    exact (hsummable.sum_add_tsum_nat_add cutoff).symm
  have hprefix :
      (∑ n ∈ Finset.range cutoff, f n) =
        ∑ n ∈ Finset.range cutoff,
          screwAffineKick (weight n) (location n) t := by
    apply Finset.sum_congr rfl
    intro n hn
    exact screwNegativeHinge_eq_affineKick_of_location_le
      (hcut.1 n (Finset.mem_range.mp hn))
  have htailterm : ∀ k : ℕ, f (k + cutoff) = 0 := by
    intro k
    exact screwNegativeHinge_eq_zero_of_le_location (hcut.2 k)
  have htail : (∑' k : ℕ, f (k + cutoff)) = 0 := by
    simp_rw [htailterm]
    exact tsum_zero
  unfold screwHingeModel frozenScrewHingeModel
  change archimedean t + ∑' n : ℕ, f n = _
  rw [hsplit, hprefix, htail, add_zero]

/-- A monotone event schedule escaping to the right covers every real
center by an event cell. -/
theorem screwEventCutsCover_of_monotone_unbounded
    {location : ℕ → ℝ} (hmono : Monotone location)
    (hunbounded : ∀ t : ℝ, ∃ n : ℕ, t < location n) :
    ScrewEventCutsCover location := by
  intro t
  let cutoff := Nat.find (hunbounded t)
  have hcutoff : t < location cutoff := Nat.find_spec (hunbounded t)
  refine ⟨cutoff, ?_, ?_⟩
  · intro n hn
    apply le_of_not_gt
    intro htn
    have hle : cutoff ≤ n := Nat.find_min' (hunbounded t) htn
    exact (not_le_of_gt hn) hle
  · intro k
    exact hcutoff.le.trans (hmono (Nat.le_add_left cutoff k))

/-- The note's exact frozen-regime reduction.  It uses only nonnegative jump
weights, local finiteness, and coverage by event cells. -/
theorem screwHingeModel_nonnegative_iff_all_frozen
    {archimedean : ℝ → ℝ} {location weight : ℕ → ℝ}
    (hweight : ∀ n, 0 ≤ weight n)
    (hsummable : ∀ t : ℝ, Summable
      (fun n : ℕ => screwNegativeHinge (weight n) (location n) t))
    (hcover : ScrewEventCutsCover location) :
    (∀ t : ℝ, 0 ≤ screwHingeModel archimedean location weight t) ↔
      ∀ cutoff : ℕ, ∀ t : ℝ,
        0 ≤ frozenScrewHingeModel archimedean location weight cutoff t := by
  constructor
  · intro hnonnegative cutoff t
    exact (hnonnegative t).trans
      (screwHingeModel_le_frozen hweight (hsummable t) cutoff)
  · intro hfrozen t
    obtain ⟨cutoff, hcut⟩ := hcover t
    rw [screwHingeModel_eq_frozen_of_eventCut (hsummable t) hcut]
    exact hfrozen cutoff t

/-- Domain-restricted form of the frozen-regime reduction.  This is the
version used for Suzuki's formula on the nonnegative half-line before its
even extension. -/
theorem screwHingeModel_nonnegativeOn_iff_all_frozen
    {archimedean : ℝ → ℝ} {location weight : ℕ → ℝ}
    (domain : Set ℝ) (hweight : ∀ n, 0 ≤ weight n)
    (hsummable : ∀ t : ℝ, Summable
      (fun n : ℕ => screwNegativeHinge (weight n) (location n) t))
    (hcover : ScrewEventCutsCover location) :
    (∀ t : ℝ, t ∈ domain →
      0 ≤ screwHingeModel archimedean location weight t) ↔
      ∀ cutoff : ℕ, ∀ t : ℝ, t ∈ domain →
        0 ≤ frozenScrewHingeModel archimedean location weight cutoff t := by
  constructor
  · intro hnonnegative cutoff t ht
    exact (hnonnegative t ht).trans
      (screwHingeModel_le_frozen hweight (hsummable t) cutoff)
  · intro hfrozen t ht
    obtain ⟨cutoff, hcut⟩ := hcover t
    rw [screwHingeModel_eq_frozen_of_eventCut (hsummable t) hcut]
    exact hfrozen cutoff t ht

/-! ## Infimum barriers -/

/-- The global lower barrier of one frozen regime. -/
def frozenScrewBarrier
    (archimedean : ℝ → ℝ) (location weight : ℕ → ℝ)
    (cutoff : ℕ) : ℝ :=
  sInf (Set.range
    (frozenScrewHingeModel archimedean location weight cutoff))

/-- Lower barrier restricted to a chosen center domain. -/
def frozenScrewBarrierOn
    (domain : Set ℝ) (archimedean : ℝ → ℝ)
    (location weight : ℕ → ℝ) (cutoff : ℕ) : ℝ :=
  sInf (frozenScrewHingeModel archimedean location weight cutoff '' domain)

theorem frozenScrewBarrier_nonnegative_iff
    {archimedean : ℝ → ℝ} {location weight : ℕ → ℝ}
    {cutoff : ℕ}
    (hbdd : BddBelow (Set.range
      (frozenScrewHingeModel archimedean location weight cutoff))) :
    0 ≤ frozenScrewBarrier archimedean location weight cutoff ↔
      ∀ t : ℝ,
        0 ≤ frozenScrewHingeModel archimedean location weight cutoff t := by
  constructor
  · intro hbarrier t
    exact hbarrier.trans (csInf_le hbdd ⟨t, rfl⟩)
  · intro hnonnegative
    unfold frozenScrewBarrier
    apply le_csInf (Set.range_nonempty _)
    intro value hvalue
    obtain ⟨t, rfl⟩ := hvalue
    exact hnonnegative t

theorem frozenScrewBarrierOn_nonnegative_iff
    {domain : Set ℝ} {archimedean : ℝ → ℝ}
    {location weight : ℕ → ℝ} {cutoff : ℕ}
    (hdomain : domain.Nonempty)
    (hbdd : BddBelow
      (frozenScrewHingeModel archimedean location weight cutoff '' domain)) :
    0 ≤ frozenScrewBarrierOn domain archimedean location weight cutoff ↔
      ∀ t : ℝ, t ∈ domain →
        0 ≤ frozenScrewHingeModel archimedean location weight cutoff t := by
  constructor
  · intro hbarrier t ht
    exact hbarrier.trans (csInf_le hbdd ⟨t, ht, rfl⟩)
  · intro hnonnegative
    unfold frozenScrewBarrierOn
    apply le_csInf (hdomain.image _)
    intro value hvalue
    obtain ⟨t, ht, rfl⟩ := hvalue
    exact hnonnegative t ht

/-- Exact Legendre-barrier criterion, with boundedness of each frozen regime
stated explicitly rather than hidden in the notation `inf`. -/
theorem screwHingeModel_nonnegative_iff_barriers
    {archimedean : ℝ → ℝ} {location weight : ℕ → ℝ}
    (hweight : ∀ n, 0 ≤ weight n)
    (hsummable : ∀ t : ℝ, Summable
      (fun n : ℕ => screwNegativeHinge (weight n) (location n) t))
    (hcover : ScrewEventCutsCover location)
    (hbdd : ∀ cutoff : ℕ, BddBelow (Set.range
      (frozenScrewHingeModel archimedean location weight cutoff))) :
    (∀ t : ℝ, 0 ≤ screwHingeModel archimedean location weight t) ↔
      ∀ cutoff : ℕ,
        0 ≤ frozenScrewBarrier archimedean location weight cutoff := by
  rw [screwHingeModel_nonnegative_iff_all_frozen hweight hsummable hcover]
  constructor
  · intro hfrozen cutoff
    exact (frozenScrewBarrier_nonnegative_iff (hbdd cutoff)).2
      (hfrozen cutoff)
  · intro hbarrier cutoff
    exact (frozenScrewBarrier_nonnegative_iff (hbdd cutoff)).1
      (hbarrier cutoff)

/-- Exact domain-restricted barrier criterion. -/
theorem screwHingeModel_nonnegativeOn_iff_barriersOn
    {archimedean : ℝ → ℝ} {location weight : ℕ → ℝ}
    (domain : Set ℝ) (hdomain : domain.Nonempty)
    (hweight : ∀ n, 0 ≤ weight n)
    (hsummable : ∀ t : ℝ, Summable
      (fun n : ℕ => screwNegativeHinge (weight n) (location n) t))
    (hcover : ScrewEventCutsCover location)
    (hbdd : ∀ cutoff : ℕ, BddBelow
      (frozenScrewHingeModel archimedean location weight cutoff '' domain)) :
    (∀ t : ℝ, t ∈ domain →
      0 ≤ screwHingeModel archimedean location weight t) ↔
      ∀ cutoff : ℕ,
        0 ≤ frozenScrewBarrierOn domain archimedean location weight cutoff := by
  rw [screwHingeModel_nonnegativeOn_iff_all_frozen domain hweight
    hsummable hcover]
  constructor
  · intro hfrozen cutoff
    exact (frozenScrewBarrierOn_nonnegative_iff hdomain (hbdd cutoff)).2
      (hfrozen cutoff)
  · intro hbarrier cutoff
    exact (frozenScrewBarrierOn_nonnegative_iff hdomain (hbdd cutoff)).1
      (hbarrier cutoff)

/-! ## Abstract transport / Legendre comparison -/

/-- Convex-dual potential on nonnegative transported mass.  In the intended
application `moment M` is the integral of a quantile up to mass `M`. -/
def nonnegativeLegendrePotential (moment : ℝ → ℝ) (t : ℝ) : ℝ :=
  sSup ((fun mass : ℝ => t * mass - moment mass) '' Set.Ici 0)

/-- A larger cumulative quantile moment produces a smaller hinge potential.
This is the order-theoretic core of the transport argument; the quantile
representation itself remains a separate analytic bridge. -/
theorem nonnegativeLegendrePotential_anti_mono
    {smoothMoment primeMoment : ℝ → ℝ} {t : ℝ}
    (hmoment : ∀ mass : ℝ, 0 ≤ mass →
      smoothMoment mass ≤ primeMoment mass)
    (hbdd : BddAbove
      ((fun mass : ℝ => t * mass - smoothMoment mass) '' Set.Ici 0)) :
    nonnegativeLegendrePotential primeMoment t ≤
      nonnegativeLegendrePotential smoothMoment t := by
  unfold nonnegativeLegendrePotential
  apply csSup_le
  · exact (show (Set.Ici (0 : ℝ)).Nonempty from ⟨0, by simp⟩).image _
  · intro value hvalue
    obtain ⟨mass, hmass, rfl⟩ := hvalue
    calc
      t * mass - primeMoment mass ≤
          t * mass - smoothMoment mass :=
        sub_le_sub_left (hmoment mass hmass) _
      _ ≤ sSup
          ((fun mass : ℝ => t * mass - smoothMoment mass) '' Set.Ici 0) :=
        le_csSup hbdd ⟨mass, hmass, rfl⟩

/-- The exact margin-aware transport obligation.  Requiring the smooth
potential to dominate the prime potential discards the available positive
margin and is therefore sufficient but not necessary. -/
theorem transportBarrier_nonnegative_iff
    (baseMargin smoothPotential primePotential : ℝ) :
    0 ≤ baseMargin + smoothPotential - primePotential ↔
      primePotential - smoothPotential ≤ baseMargin := by
  constructor <;> intro h <;> linarith

/-- Cumulative quantile-moment dominance is a clean sufficient transport
certificate.  This theorem deliberately does not call it an equivalence. -/
theorem transportMomentDominance_nonnegative
    {smoothMoment primeMoment : ℝ → ℝ} {baseMargin t : ℝ}
    (hbase : 0 ≤ baseMargin)
    (hmoment : ∀ mass : ℝ, 0 ≤ mass →
      smoothMoment mass ≤ primeMoment mass)
    (hbdd : BddAbove
      ((fun mass : ℝ => t * mass - smoothMoment mass) '' Set.Ici 0)) :
    0 ≤ baseMargin + nonnegativeLegendrePotential smoothMoment t -
      nonnegativeLegendrePotential primeMoment t := by
  have hpotential :=
    nonnegativeLegendrePotential_anti_mono hmoment hbdd
  linarith

/-! ## The actual von-Mangoldt event schedule -/

/-- Enumerate every integer `n ≥ 2`; non-prime-powers simply have zero
von-Mangoldt weight. -/
def suzukiPrimeLocation (n : ℕ) : ℝ :=
  Real.log ((n + 2 : ℕ) : ℝ)

/-- The downward slope jump in Suzuki's pointwise screw function. -/
def suzukiPrimeWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (n + 2) /
    Real.sqrt ((n + 2 : ℕ) : ℝ)

theorem suzukiPrimeWeight_nonnegative (n : ℕ) :
    0 ≤ suzukiPrimeWeight n := by
  unfold suzukiPrimeWeight
  positivity

theorem monotone_suzukiPrimeLocation : Monotone suzukiPrimeLocation := by
  intro a b hab
  unfold suzukiPrimeLocation
  apply Real.log_le_log
  · positivity
  · exact_mod_cast Nat.add_le_add_right hab 2

theorem suzukiPrimeLocation_unbounded :
    ∀ t : ℝ, ∃ n : ℕ, t < suzukiPrimeLocation n := by
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp t)
  refine ⟨n, ?_⟩
  unfold suzukiPrimeLocation
  apply (Real.lt_log_iff_exp_lt (by positivity)).2
  exact hn.trans_le (by
    exact_mod_cast Nat.le_add_right n 2)

theorem suzukiPrimeEventCutsCover :
    ScrewEventCutsCover suzukiPrimeLocation :=
  screwEventCutsCover_of_monotone_unbounded
    monotone_suzukiPrimeLocation suzukiPrimeLocation_unbounded

/-- At every fixed center only finitely many Suzuki prime hinges are active. -/
theorem summable_suzukiPrimeNegativeHinge (t : ℝ) :
    Summable (fun n : ℕ =>
      screwNegativeHinge (suzukiPrimeWeight n)
        (suzukiPrimeLocation n) t) := by
  obtain ⟨cutoff, hcutoff⟩ := suzukiPrimeLocation_unbounded t
  apply summable_of_ne_finset_zero (s := Finset.range cutoff)
  intro n hn
  have hcutoff_le : cutoff ≤ n := by simpa using hn
  apply screwNegativeHinge_eq_zero_of_le_location
  exact hcutoff.le.trans
    (monotone_suzukiPrimeLocation hcutoff_le)

/-- The exact frozen-cell criterion specialized to Suzuki's prime schedule,
for an arbitrary choice of the smooth Archimedean background. -/
theorem suzukiPrimeHingeModel_nonnegative_iff_all_frozen
    (archimedean : ℝ → ℝ) :
    (∀ t : ℝ, 0 ≤ screwHingeModel archimedean suzukiPrimeLocation
      suzukiPrimeWeight t) ↔
      ∀ cutoff : ℕ, ∀ t : ℝ,
        0 ≤ frozenScrewHingeModel archimedean suzukiPrimeLocation
          suzukiPrimeWeight cutoff t := by
  exact screwHingeModel_nonnegative_iff_all_frozen
    suzukiPrimeWeight_nonnegative summable_suzukiPrimeNegativeHinge
      suzukiPrimeEventCutsCover

/-- Accurate half-line version for the prime part of Suzuki's explicit
formula.  Evenness is a separate bridge for the full screw function. -/
theorem suzukiPrimeHingeModel_nonnegativeOn_nonnegative_iff_all_frozen
    (archimedean : ℝ → ℝ) :
    (∀ t : ℝ, t ∈ Set.Ici 0 →
      0 ≤ screwHingeModel archimedean suzukiPrimeLocation
        suzukiPrimeWeight t) ↔
      ∀ cutoff : ℕ, ∀ t : ℝ, t ∈ Set.Ici 0 →
        0 ≤ frozenScrewHingeModel archimedean suzukiPrimeLocation
          suzukiPrimeWeight cutoff t := by
  exact screwHingeModel_nonnegativeOn_iff_all_frozen (Set.Ici 0)
    suzukiPrimeWeight_nonnegative summable_suzukiPrimeNegativeHinge
      suzukiPrimeEventCutsCover

/-- The corresponding exact infimum-barrier criterion.  The hypothesis says
only that each smooth frozen regime has a finite lower barrier. -/
theorem suzukiPrimeHingeModel_nonnegative_iff_barriers
    (archimedean : ℝ → ℝ)
    (hbdd : ∀ cutoff : ℕ, BddBelow (Set.range
      (frozenScrewHingeModel archimedean suzukiPrimeLocation
        suzukiPrimeWeight cutoff))) :
    (∀ t : ℝ, 0 ≤ screwHingeModel archimedean suzukiPrimeLocation
      suzukiPrimeWeight t) ↔
      ∀ cutoff : ℕ,
        0 ≤ frozenScrewBarrier archimedean suzukiPrimeLocation
          suzukiPrimeWeight cutoff := by
  exact screwHingeModel_nonnegative_iff_barriers
    suzukiPrimeWeight_nonnegative summable_suzukiPrimeNegativeHinge
      suzukiPrimeEventCutsCover hbdd

end

end RiemannGaussian
