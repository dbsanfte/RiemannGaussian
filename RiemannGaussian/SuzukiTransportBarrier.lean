import RiemannGaussian.ScrewTransport

/-!
# Exact curvature-mass barriers for the screw-transport route

The frozen-regime reduction in `ScrewTransport` turns every finite prefix of
the prime hinges into a smooth background minus an affine function.  This
file identifies the minimizer of that affine perturbation without taking
derivatives.

Starting at a zero-slope base point `base`, let

* `M(t) = ∫ s in base..t, curvature s` be accumulated curvature mass, and
* `J(t) = ∫ s in base..t, s * curvature s` be its first moment.

The zero-slope background is `baseMargin + t * M(t) - J(t)`.  If a frozen
prime prefix has mass `S` and `M(r) = S`, then its value at any `t ≥ base`
exceeds its value at `r` by a nonnegative weighted interval integral.  Its
entire half-line infimum is consequently the single scalar

`baseMargin + primeMoment - J(r)`.

This is the cumulative-barycenter/Legendre barrier from the uploaded
screw-transport note.  It is uniform in the cutoff; no finite list of
epsilon or prime-prefix certificates is built into the result.
-/

namespace RiemannGaussian

noncomputable section

open scoped BigOperators Topology

/-! ## Curvature mass and its zero-slope primitive -/

/-- Curvature mass accumulated from `base` to `t`. -/
def transportCurvatureMass
    (curvature : ℝ → ℝ) (base t : ℝ) : ℝ :=
  ∫ s in base..t, curvature s

/-- First location moment of the curvature accumulated from `base` to `t`. -/
def transportCurvatureMoment
    (curvature : ℝ → ℝ) (base t : ℝ) : ℝ :=
  ∫ s in base..t, s * curvature s

/-- The twice-integrated curvature background normalized to have value
`baseMargin` and slope zero at `base`. -/
def zeroSlopeCurvatureBackground
    (baseMargin base : ℝ) (curvature : ℝ → ℝ) (t : ℝ) : ℝ :=
  baseMargin + t * transportCurvatureMass curvature base t -
    transportCurvatureMoment curvature base t

@[simp] theorem transportCurvatureMass_self
    (curvature : ℝ → ℝ) (base : ℝ) :
    transportCurvatureMass curvature base base = 0 := by
  simp [transportCurvatureMass]

@[simp] theorem transportCurvatureMoment_self
    (curvature : ℝ → ℝ) (base : ℝ) :
    transportCurvatureMoment curvature base base = 0 := by
  simp [transportCurvatureMoment]

@[simp] theorem zeroSlopeCurvatureBackground_at_base
    (baseMargin base : ℝ) (curvature : ℝ → ℝ) :
    zeroSlopeCurvatureBackground baseMargin base curvature base =
      baseMargin := by
  simp [zeroSlopeCurvatureBackground]

/-- A frozen regime over a zero-slope curvature background, written solely
in terms of its curvature mass and the two prime-prefix statistics. -/
theorem frozenScrewHingeModel_zeroSlopeCurvature_eq
    (baseMargin base : ℝ) (curvature : ℝ → ℝ)
    (location weight : ℕ → ℝ) (cutoff : ℕ) (t : ℝ) :
    frozenScrewHingeModel
        (zeroSlopeCurvatureBackground baseMargin base curvature)
        location weight cutoff t =
      baseMargin +
        t * (transportCurvatureMass curvature base t -
          screwPrefixMass weight cutoff) +
        screwPrefixMoment location weight cutoff -
          transportCurvatureMoment curvature base t := by
  rw [frozenScrewHingeModel_eq_arch_sub_mass_add_moment]
  unfold zeroSlopeCurvatureBackground
  ring

private theorem intervalIntegrable_of_continuousOn_Ici
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

private theorem intervalIntegrable_moment_of_continuousOn_Ici
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

/-! ## Exact minimizer identities -/

/-- To the right of a mass-matching point, the frozen regime increases by
the curvature weighted by its distance from the new endpoint. -/
theorem frozenScrewHingeModel_sub_massPoint_of_le
    {baseMargin base r t : ℝ} {curvature : ℝ → ℝ}
    {location weight : ℕ → ℝ} {cutoff : ℕ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (hbase_r : base ≤ r) (hrt : r ≤ t)
    (hmass : transportCurvatureMass curvature base r =
      screwPrefixMass weight cutoff) :
    frozenScrewHingeModel
          (zeroSlopeCurvatureBackground baseMargin base curvature)
          location weight cutoff t -
        frozenScrewHingeModel
          (zeroSlopeCurvatureBackground baseMargin base curvature)
          location weight cutoff r =
      ∫ s in r..t, (t - s) * curvature s := by
  have hbase_t : base ≤ t := hbase_r.trans hrt
  have hc_base_r := intervalIntegrable_of_continuousOn_Ici
    hcontinuous (le_refl base) hbase_r
  have hc_r_t := intervalIntegrable_of_continuousOn_Ici
    hcontinuous hbase_r hbase_t
  have hj_base_r := intervalIntegrable_moment_of_continuousOn_Ici
    hcontinuous (le_refl base) hbase_r
  have hj_r_t := intervalIntegrable_moment_of_continuousOn_Ici
    hcontinuous hbase_r hbase_t
  have hmass_split :
      transportCurvatureMass curvature base t =
        transportCurvatureMass curvature base r +
          ∫ s in r..t, curvature s := by
    unfold transportCurvatureMass
    exact (intervalIntegral.integral_add_adjacent_intervals
      hc_base_r hc_r_t).symm
  have hmoment_split :
      transportCurvatureMoment curvature base t =
        transportCurvatureMoment curvature base r +
          ∫ s in r..t, s * curvature s := by
    unfold transportCurvatureMoment
    exact (intervalIntegral.integral_add_adjacent_intervals
      hj_base_r hj_r_t).symm
  have hintegral :
      (∫ s in r..t, (t - s) * curvature s) =
        t * (∫ s in r..t, curvature s) -
          ∫ s in r..t, s * curvature s := by
    have hfun : (fun s : ℝ => (t - s) * curvature s) =
        fun s : ℝ => t * curvature s - s * curvature s := by
      funext s
      ring
    rw [hfun,
      intervalIntegral.integral_sub (hc_r_t.const_mul t) hj_r_t,
      intervalIntegral.integral_const_mul]
  rw [frozenScrewHingeModel_zeroSlopeCurvature_eq,
    frozenScrewHingeModel_zeroSlopeCurvature_eq,
    hmass_split, hmoment_split, hmass, hintegral]
  ring

/-- To the left of a mass-matching point, the frozen regime increases by
the curvature weighted by its distance from the old endpoint. -/
theorem frozenScrewHingeModel_sub_massPoint_of_ge
    {baseMargin base r t : ℝ} {curvature : ℝ → ℝ}
    {location weight : ℕ → ℝ} {cutoff : ℕ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (hbase_t : base ≤ t) (htr : t ≤ r)
    (hmass : transportCurvatureMass curvature base r =
      screwPrefixMass weight cutoff) :
    frozenScrewHingeModel
          (zeroSlopeCurvatureBackground baseMargin base curvature)
          location weight cutoff t -
        frozenScrewHingeModel
          (zeroSlopeCurvatureBackground baseMargin base curvature)
          location weight cutoff r =
      ∫ s in t..r, (s - t) * curvature s := by
  have hbase_r : base ≤ r := hbase_t.trans htr
  have hc_base_t := intervalIntegrable_of_continuousOn_Ici
    hcontinuous (le_refl base) hbase_t
  have hc_t_r := intervalIntegrable_of_continuousOn_Ici
    hcontinuous hbase_t hbase_r
  have hj_base_t := intervalIntegrable_moment_of_continuousOn_Ici
    hcontinuous (le_refl base) hbase_t
  have hj_t_r := intervalIntegrable_moment_of_continuousOn_Ici
    hcontinuous hbase_t hbase_r
  have hmass_split :
      transportCurvatureMass curvature base r =
        transportCurvatureMass curvature base t +
          ∫ s in t..r, curvature s := by
    unfold transportCurvatureMass
    exact (intervalIntegral.integral_add_adjacent_intervals
      hc_base_t hc_t_r).symm
  have hmoment_split :
      transportCurvatureMoment curvature base r =
        transportCurvatureMoment curvature base t +
          ∫ s in t..r, s * curvature s := by
    unfold transportCurvatureMoment
    exact (intervalIntegral.integral_add_adjacent_intervals
      hj_base_t hj_t_r).symm
  have hintegral :
      (∫ s in t..r, (s - t) * curvature s) =
        (∫ s in t..r, s * curvature s) -
          t * (∫ s in t..r, curvature s) := by
    have hfun : (fun s : ℝ => (s - t) * curvature s) =
        fun s : ℝ => s * curvature s - t * curvature s := by
      funext s
      ring
    rw [hfun,
      intervalIntegral.integral_sub hj_t_r (hc_t_r.const_mul t),
      intervalIntegral.integral_const_mul]
  rw [frozenScrewHingeModel_zeroSlopeCurvature_eq,
    frozenScrewHingeModel_zeroSlopeCurvature_eq,
    hmoment_split, ← hmass, hmass_split, hintegral]
  ring

/-- A point where smooth curvature mass equals frozen prime mass is a global
minimizer of that frozen regime on the tail half-line. -/
theorem frozenScrewHingeModel_minimized_at_massPoint
    {baseMargin base r : ℝ} {curvature : ℝ → ℝ}
    {location weight : ℕ → ℝ} {cutoff : ℕ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (hcurvature : ∀ s : ℝ, base ≤ s → 0 ≤ curvature s)
    (hbase_r : base ≤ r)
    (hmass : transportCurvatureMass curvature base r =
      screwPrefixMass weight cutoff) :
    ∀ t : ℝ, base ≤ t →
      frozenScrewHingeModel
          (zeroSlopeCurvatureBackground baseMargin base curvature)
          location weight cutoff r ≤
        frozenScrewHingeModel
          (zeroSlopeCurvatureBackground baseMargin base curvature)
          location weight cutoff t := by
  intro t hbase_t
  rcases le_total r t with hrt | htr
  · have hdiff := frozenScrewHingeModel_sub_massPoint_of_le
      (baseMargin := baseMargin) (location := location)
      hcontinuous hbase_r hrt hmass
    have hnonnegative :
        0 ≤ ∫ s in r..t, (t - s) * curvature s := by
      apply intervalIntegral.integral_nonneg hrt
      intro s hs
      exact mul_nonneg (sub_nonneg.mpr hs.2)
        (hcurvature s (hbase_r.trans hs.1))
    linarith
  · have hdiff := frozenScrewHingeModel_sub_massPoint_of_ge
      (baseMargin := baseMargin) (location := location)
      hcontinuous hbase_t htr hmass
    have hnonnegative :
        0 ≤ ∫ s in t..r, (s - t) * curvature s := by
      apply intervalIntegral.integral_nonneg htr
      intro s hs
      exact mul_nonneg (sub_nonneg.mpr hs.1)
        (hcurvature s (hbase_t.trans hs.1))
    linarith

/-! ## Exact half-line barrier -/

/-- The half-line infimum of a mass-matched frozen regime is exactly its
cumulative barycenter gap. -/
theorem frozenScrewBarrierOn_zeroSlopeCurvature_eq
    {baseMargin base r : ℝ} {curvature : ℝ → ℝ}
    {location weight : ℕ → ℝ} {cutoff : ℕ}
    (hcontinuous : ContinuousOn curvature (Set.Ici base))
    (hcurvature : ∀ s : ℝ, base ≤ s → 0 ≤ curvature s)
    (hbase_r : base ≤ r)
    (hmass : transportCurvatureMass curvature base r =
      screwPrefixMass weight cutoff) :
    frozenScrewBarrierOn (Set.Ici base)
        (zeroSlopeCurvatureBackground baseMargin base curvature)
        location weight cutoff =
      baseMargin + screwPrefixMoment location weight cutoff -
        transportCurvatureMoment curvature base r := by
  let model : ℝ → ℝ :=
    frozenScrewHingeModel
      (zeroSlopeCurvatureBackground baseMargin base curvature)
      location weight cutoff
  have hmin : ∀ t : ℝ, base ≤ t → model r ≤ model t :=
    frozenScrewHingeModel_minimized_at_massPoint
      hcontinuous hcurvature hbase_r hmass
  have hbdd : BddBelow (model '' Set.Ici base) := by
    refine ⟨model r, ?_⟩
    intro value hvalue
    obtain ⟨t, ht, rfl⟩ := hvalue
    exact hmin t ht
  have hrange : model r ∈ model '' Set.Ici base :=
    ⟨r, hbase_r, rfl⟩
  have hinf : sInf (model '' Set.Ici base) = model r := by
    apply le_antisymm
    · exact csInf_le hbdd hrange
    · apply le_csInf
      · exact ⟨model r, hrange⟩
      · intro value hvalue
        obtain ⟨t, ht, rfl⟩ := hvalue
        exact hmin t ht
  change sInf (model '' Set.Ici base) = _
  rw [hinf]
  dsimp only [model]
  rw [frozenScrewHingeModel_zeroSlopeCurvature_eq, hmass]
  ring

/-! ## Suzuki specialization -/

/-- Suzuki's smooth curvature is continuous on every tail strictly to the
right of the origin. -/
theorem continuousOn_suzukiSmoothCurvature_Ioi :
    ContinuousOn suzukiSmoothCurvature (Set.Ioi 0) := by
  intro t ht
  have htpos : 0 < t := ht
  have hden : 1 - Real.exp (-2 * t) ≠ 0 :=
    ne_of_gt (one_sub_exp_neg_two_mul_pos htpos)
  apply ContinuousAt.continuousWithinAt
  unfold suzukiSmoothCurvature suzukiMissingCurvature
  fun_prop

/-- A quantitative form of tail convexity.  The constant `1/2` is very
conservative, but it makes accumulated Suzuki curvature visibly unbounded
and therefore guarantees every finite prime mass has a matching point. -/
theorem half_le_suzukiSmoothCurvature_of_log_two_le
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    (1 : ℝ) / 2 ≤ suzukiSmoothCurvature t := by
  have htpos : 0 < t :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le ht
  have hden : 0 < 1 - Real.exp (-2 * t) :=
    one_sub_exp_neg_two_mul_pos htpos
  let x : ℝ := Real.exp t
  have hxpos : 0 < x := Real.exp_pos t
  have hx2 : 2 ≤ x := by
    dsimp only [x]
    calc
      2 = Real.exp (Real.log 2) :=
        (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr ht
  have hxpoly : 2 + x ≤ x ^ 3 := by
    nlinarith [sq_nonneg (x - 2), mul_nonneg hxpos.le (sq_nonneg x)]
  have hleftScale :
      (2 * Real.exp (-(5 * t) / 2) + Real.exp (-(3 * t) / 2)) *
          Real.exp ((5 * t) / 2) = 2 + x := by
    rw [add_mul, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    dsimp only [x]
    ring_nf
    simp
  have hrightScale :
      Real.exp (t / 2) * Real.exp ((5 * t) / 2) = x ^ 3 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  have hsum :
      2 * Real.exp (-(5 * t) / 2) + Real.exp (-(3 * t) / 2) ≤
        Real.exp (t / 2) := by
    have hscaled :
        (2 * Real.exp (-(5 * t) / 2) + Real.exp (-(3 * t) / 2)) *
            Real.exp ((5 * t) / 2) ≤
          Real.exp (t / 2) * Real.exp ((5 * t) / 2) := by
      rw [hleftScale, hrightScale]
      exact hxpoly
    exact le_of_mul_le_mul_right hscaled
      (Real.exp_pos ((5 * t) / 2))
  have hproductExp :
      Real.exp (t / 2) * Real.exp (-2 * t) =
        Real.exp (-(3 * t) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmissing :
      suzukiMissingCurvature t ≤ Real.exp (t / 2) / 2 := by
    unfold suzukiMissingCurvature
    apply (div_le_iff₀ hden).2
    have hhalfProduct :
        (Real.exp (t / 2) / 2) * Real.exp (-2 * t) =
          Real.exp (-(3 * t) / 2) / 2 := by
      rw [div_mul_eq_mul_div, hproductExp]
    rw [mul_sub, hhalfProduct]
    linarith
  have hone : 1 ≤ Real.exp (t / 2) :=
    Real.one_le_exp (by linarith)
  unfold suzukiSmoothCurvature
  linarith

theorem screwPrefixMass_nonnegative
    {weight : ℕ → ℝ} (hweight : ∀ n : ℕ, 0 ≤ weight n)
    (cutoff : ℕ) :
    0 ≤ screwPrefixMass weight cutoff := by
  unfold screwPrefixMass
  exact Finset.sum_nonneg fun n _ => hweight n

/-- Every nonnegative amount of smooth mass occurs at some point of the
Suzuki tail.  This removes the existence assumption behind the transport
quantile used in the research note. -/
theorem exists_suzukiTransportMass_eq
    {base mass : ℝ} (hlog : Real.log 2 ≤ base) (hmass : 0 ≤ mass) :
    ∃ r : ℝ, base ≤ r ∧
      transportCurvatureMass suzukiSmoothCurvature base r = mass := by
  let upper : ℝ := base + 2 * mass
  have hbase_upper : base ≤ upper := by
    dsimp only [upper]
    linarith
  have hcontinuous :
      ContinuousOn suzukiSmoothCurvature (Set.Ici base) :=
    continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro t ht
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog.trans ht))
  have hcurvInt : IntervalIntegrable suzukiSmoothCurvature
      MeasureTheory.volume base upper :=
    intervalIntegrable_of_continuousOn_Ici hcontinuous
      (le_refl base) hbase_upper
  have hconstInt : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 2)
      MeasureTheory.volume base upper :=
    continuous_const.intervalIntegrable _ _
  have hlowerIntegral :
      (∫ _s : ℝ in base..upper, (1 : ℝ) / 2) ≤
        ∫ s in base..upper, suzukiSmoothCurvature s := by
    apply intervalIntegral.integral_mono_on hbase_upper hconstInt hcurvInt
    intro s hs
    exact half_le_suzukiSmoothCurvature_of_log_two_le
      (hlog.trans hs.1)
  have hmass_upper : mass ≤
      transportCurvatureMass suzukiSmoothCurvature base upper := by
    unfold transportCurvatureMass
    calc
      mass = ∫ _s : ℝ in base..upper, (1 : ℝ) / 2 := by
        simp [upper]
        ring
      _ ≤ ∫ s in base..upper, suzukiSmoothCurvature s := hlowerIntegral
  have hcontinuousMass : ContinuousOn
      (transportCurvatureMass suzukiSmoothCurvature base)
      (Set.Icc base upper) := by
    unfold transportCurvatureMass
    simpa only [Set.uIcc_of_le hbase_upper] using
      (intervalIntegral.continuousOn_primitive_interval' hcurvInt
        (Set.left_mem_uIcc : base ∈ Set.uIcc base upper))
  have hmass_mem : mass ∈ Set.Icc
      (transportCurvatureMass suzukiSmoothCurvature base base)
      (transportCurvatureMass suzukiSmoothCurvature base upper) := by
    constructor
    · simpa using hmass
    · exact hmass_upper
  obtain ⟨r, hr, hrequal⟩ :=
    (intermediate_value_Icc hbase_upper hcontinuousMass hmass_mem)
  exact ⟨r, hr.1, hrequal⟩

/-- Accumulated Suzuki curvature mass is strictly increasing on every tail
starting at or after `log 2`. -/
theorem strictlyMonoOn_suzukiTransportCurvatureMass
    {base : ℝ} (hlog : Real.log 2 ≤ base) :
    StrictMonoOn
      (transportCurvatureMass suzukiSmoothCurvature base)
      (Set.Ici base) := by
  intro a ha b hb hab
  have hcontinuous :
      ContinuousOn suzukiSmoothCurvature (Set.Ici base) :=
    continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro t ht
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog.trans ht))
  have hc_base_a := intervalIntegrable_of_continuousOn_Ici
    hcontinuous (le_refl base) ha
  have hc_a_b := intervalIntegrable_of_continuousOn_Ici
    hcontinuous ha hb
  have hsplit :
      transportCurvatureMass suzukiSmoothCurvature base b =
        transportCurvatureMass suzukiSmoothCurvature base a +
          ∫ s in a..b, suzukiSmoothCurvature s := by
    unfold transportCurvatureMass
    exact (intervalIntegral.integral_add_adjacent_intervals
      hc_base_a hc_a_b).symm
  have hpositive : 0 < ∫ s in a..b, suzukiSmoothCurvature s := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hc_a_b
    · intro s hs
      exact suzukiSmoothCurvature_pos_of_log_two_le
        (hlog.trans (ha.trans hs.1.le))
    · exact hab
  rw [hsplit]
  linarith

/-- Hence the tail mass-matching point exists uniquely. -/
theorem existsUnique_suzukiTransportMass_eq
    {base mass : ℝ} (hlog : Real.log 2 ≤ base) (hmass : 0 ≤ mass) :
    ∃! r : ℝ, base ≤ r ∧
      transportCurvatureMass suzukiSmoothCurvature base r = mass := by
  obtain ⟨r, hbase_r, hr⟩ :=
    exists_suzukiTransportMass_eq hlog hmass
  refine ⟨r, ⟨hbase_r, hr⟩, ?_⟩
  intro t ht
  exact ((strictlyMonoOn_suzukiTransportCurvatureMass hlog).injOn
    hbase_r ht.1 (hr.trans ht.2.symm)).symm

/-- Canonical smooth-curvature quantile at the cumulative mass of a Suzuki
prime prefix. -/
def suzukiTransportMassPoint
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) : ℝ :=
  Classical.choose (exists_suzukiTransportMass_eq hlog
    (screwPrefixMass_nonnegative suzukiPrimeWeight_nonnegative cutoff))

theorem base_le_suzukiTransportMassPoint
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) :
    base ≤ suzukiTransportMassPoint base hlog cutoff := by
  unfold suzukiTransportMassPoint
  exact (Classical.choose_spec (exists_suzukiTransportMass_eq hlog
    (screwPrefixMass_nonnegative suzukiPrimeWeight_nonnegative cutoff))).1

theorem suzukiTransportMassPoint_mass_eq
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) :
    transportCurvatureMass suzukiSmoothCurvature base
        (suzukiTransportMassPoint base hlog cutoff) =
      screwPrefixMass suzukiPrimeWeight cutoff := by
  unfold suzukiTransportMassPoint
  exact (Classical.choose_spec (exists_suzukiTransportMass_eq hlog
    (screwPrefixMass_nonnegative suzukiPrimeWeight_nonnegative cutoff))).2

/-- The exact curvature-mass/prime-moment formula for every Suzuki frozen
prefix whose cumulative mass has a matching tail point. -/
theorem suzukiFrozenBarrierOn_eq_transportGap
    {baseMargin base r : ℝ} {cutoff : ℕ}
    (hlog : Real.log 2 ≤ base) (hbase_r : base ≤ r)
    (hmass : transportCurvatureMass suzukiSmoothCurvature base r =
      screwPrefixMass suzukiPrimeWeight cutoff) :
    frozenScrewBarrierOn (Set.Ici base)
        (zeroSlopeCurvatureBackground baseMargin base
          suzukiSmoothCurvature)
        suzukiPrimeLocation suzukiPrimeWeight cutoff =
      baseMargin +
        screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight cutoff -
          transportCurvatureMoment suzukiSmoothCurvature base r := by
  apply frozenScrewBarrierOn_zeroSlopeCurvature_eq
  · exact continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro t ht
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog.trans ht))
  · intro t ht
    exact (suzukiSmoothCurvature_pos_of_log_two_le
      (hlog.trans ht)).le
  · exact hbase_r
  · exact hmass

/-- The frozen Suzuki prefix is nonnegative on the tail exactly when its
single transport gap is nonnegative. -/
theorem suzukiFrozenRegime_nonnegativeOn_iff_transportGap
    {baseMargin base r : ℝ} {cutoff : ℕ}
    (hlog : Real.log 2 ≤ base) (hbase_r : base ≤ r)
    (hmass : transportCurvatureMass suzukiSmoothCurvature base r =
      screwPrefixMass suzukiPrimeWeight cutoff) :
    (∀ t : ℝ, base ≤ t →
      0 ≤ frozenScrewHingeModel
        (zeroSlopeCurvatureBackground baseMargin base
          suzukiSmoothCurvature)
        suzukiPrimeLocation suzukiPrimeWeight cutoff t) ↔
      0 ≤ baseMargin +
        screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight cutoff -
          transportCurvatureMoment suzukiSmoothCurvature base r := by
  have hcontinuous :
      ContinuousOn suzukiSmoothCurvature (Set.Ici base) :=
    continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro t ht
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog.trans ht))
  have hcurvature : ∀ t : ℝ, base ≤ t →
      0 ≤ suzukiSmoothCurvature t := by
    intro t ht
    exact (suzukiSmoothCurvature_pos_of_log_two_le
      (hlog.trans ht)).le
  have hmin := frozenScrewHingeModel_minimized_at_massPoint
    (baseMargin := baseMargin) (location := suzukiPrimeLocation)
    (weight := suzukiPrimeWeight) hcontinuous hcurvature hbase_r hmass
  have hvalue :
      frozenScrewHingeModel
          (zeroSlopeCurvatureBackground baseMargin base
            suzukiSmoothCurvature)
          suzukiPrimeLocation suzukiPrimeWeight cutoff r =
        baseMargin +
          screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight cutoff -
            transportCurvatureMoment suzukiSmoothCurvature base r := by
    rw [frozenScrewHingeModel_zeroSlopeCurvature_eq, hmass]
    ring
  constructor
  · intro hall
    rw [← hvalue]
    exact hall r hbase_r
  · intro hgap t ht
    rw [← hvalue] at hgap
    exact hgap.trans (hmin t ht)

/-- Once one mass-matching point is supplied for every prime prefix, tail
nonnegativity of the entire Suzuki hinge model is *equivalent* to the
uniform family of scalar transport gaps.  This is the scalable discrete
Legendre criterion: its remaining obligation is one theorem quantified over
all cutoffs, not a chain of finite certificates. -/
theorem suzukiPrimeHingeModel_nonnegativeOn_tail_iff_transportGaps
    {baseMargin base : ℝ} (massPoint : ℕ → ℝ)
    (hlog : Real.log 2 ≤ base)
    (hbase_massPoint : ∀ cutoff : ℕ, base ≤ massPoint cutoff)
    (hmass : ∀ cutoff : ℕ,
      transportCurvatureMass suzukiSmoothCurvature base
          (massPoint cutoff) =
        screwPrefixMass suzukiPrimeWeight cutoff) :
    (∀ t : ℝ, base ≤ t →
      0 ≤ screwHingeModel
        (zeroSlopeCurvatureBackground baseMargin base
          suzukiSmoothCurvature)
        suzukiPrimeLocation suzukiPrimeWeight t) ↔
      ∀ cutoff : ℕ,
        0 ≤ baseMargin +
          screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight cutoff -
            transportCurvatureMoment suzukiSmoothCurvature base
              (massPoint cutoff) := by
  constructor
  · intro hmodel cutoff
    have hall : ∀ cutoff : ℕ, ∀ t : ℝ, t ∈ Set.Ici base →
        0 ≤ frozenScrewHingeModel
          (zeroSlopeCurvatureBackground baseMargin base
            suzukiSmoothCurvature)
          suzukiPrimeLocation suzukiPrimeWeight cutoff t :=
      (screwHingeModel_nonnegativeOn_iff_all_frozen (Set.Ici base)
        suzukiPrimeWeight_nonnegative summable_suzukiPrimeNegativeHinge
          suzukiPrimeEventCutsCover).1 (by
            intro t ht
            exact hmodel t ht)
    exact (suzukiFrozenRegime_nonnegativeOn_iff_transportGap
      hlog (hbase_massPoint cutoff) (hmass cutoff)).1
        (hall cutoff)
  · intro hgaps
    apply (screwHingeModel_nonnegativeOn_iff_all_frozen (Set.Ici base)
      suzukiPrimeWeight_nonnegative summable_suzukiPrimeNegativeHinge
        suzukiPrimeEventCutsCover).2
    intro cutoff
    exact (suzukiFrozenRegime_nonnegativeOn_iff_transportGap
      hlog (hbase_massPoint cutoff) (hmass cutoff)).2 (hgaps cutoff)

/-- Fully canonical tail criterion, with existence and uniqueness of every
mass point already discharged by positivity of Suzuki's smooth curvature.
The right side is the exact infinite frontier left by the transport attack. -/
theorem suzukiPrimeHingeModel_nonnegativeOn_tail_iff_canonicalTransportGaps
    (baseMargin base : ℝ) (hlog : Real.log 2 ≤ base) :
    (∀ t : ℝ, base ≤ t →
      0 ≤ screwHingeModel
        (zeroSlopeCurvatureBackground baseMargin base
          suzukiSmoothCurvature)
        suzukiPrimeLocation suzukiPrimeWeight t) ↔
      ∀ cutoff : ℕ,
        0 ≤ baseMargin +
          screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight cutoff -
            transportCurvatureMoment suzukiSmoothCurvature base
              (suzukiTransportMassPoint base hlog cutoff) := by
  exact suzukiPrimeHingeModel_nonnegativeOn_tail_iff_transportGaps
    (suzukiTransportMassPoint base hlog) hlog
    (base_le_suzukiTransportMassPoint base hlog)
    (suzukiTransportMassPoint_mass_eq base hlog)

/-! ## Consecutive transport cells

The canonical criterion above is quantified over prefix gaps.  The following
identities turn those gaps into cumulative sums of exact one-cell surpluses.
This is the form needed by a genuinely scalable block argument: individual
cells may have either sign, while a block can retain a positive cumulative
margin. -/

/-- The canonical scalar gap at one Suzuki prefix. -/
def suzukiTransportGap
    (baseMargin base : ℝ) (hlog : Real.log 2 ≤ base)
    (cutoff : ℕ) : ℝ :=
  baseMargin +
    screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight cutoff -
      transportCurvatureMoment suzukiSmoothCurvature base
        (suzukiTransportMassPoint base hlog cutoff)

/-- The signed barycenter surplus contributed by the curvature cell carrying
the mass of the next von-Mangoldt atom. -/
def suzukiTransportCellSurplus
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) : ℝ :=
  ∫ s in
      suzukiTransportMassPoint base hlog cutoff..
        suzukiTransportMassPoint base hlog (cutoff + 1),
    (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s

@[simp] theorem screwPrefixMass_succ
    (weight : ℕ → ℝ) (cutoff : ℕ) :
    screwPrefixMass weight (cutoff + 1) =
      screwPrefixMass weight cutoff + weight cutoff := by
  simp [screwPrefixMass, Finset.sum_range_succ]

@[simp] theorem screwPrefixMoment_succ
    (location weight : ℕ → ℝ) (cutoff : ℕ) :
    screwPrefixMoment location weight (cutoff + 1) =
      screwPrefixMoment location weight cutoff +
        weight cutoff * location cutoff := by
  simp [screwPrefixMoment, Finset.sum_range_succ]

/-- The zero-mass quantile is the chosen tail base itself. -/
@[simp] theorem suzukiTransportMassPoint_zero
    (base : ℝ) (hlog : Real.log 2 ≤ base) :
    suzukiTransportMassPoint base hlog 0 = base := by
  apply (strictlyMonoOn_suzukiTransportCurvatureMass hlog).injOn
  · exact base_le_suzukiTransportMassPoint base hlog 0
  · exact le_refl base
  · rw [suzukiTransportMassPoint_mass_eq]
    simp [screwPrefixMass]

/-- Adding one nonnegative prime weight can only move the smooth mass
quantile to the right. -/
theorem suzukiTransportMassPoint_le_succ
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) :
    suzukiTransportMassPoint base hlog cutoff ≤
      suzukiTransportMassPoint base hlog (cutoff + 1) := by
  apply le_of_not_gt
  intro hreverse
  have hstrict := (strictlyMonoOn_suzukiTransportCurvatureMass hlog)
    (base_le_suzukiTransportMassPoint base hlog (cutoff + 1))
    (base_le_suzukiTransportMassPoint base hlog cutoff) hreverse
  rw [suzukiTransportMassPoint_mass_eq,
    suzukiTransportMassPoint_mass_eq, screwPrefixMass_succ] at hstrict
  have hweight := suzukiPrimeWeight_nonnegative cutoff
  linarith

/-- The smooth curvature mass of one canonical cell is exactly the new
von-Mangoldt weight. -/
theorem integral_suzukiSmoothCurvature_transportCell
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) :
    (∫ s in
        suzukiTransportMassPoint base hlog cutoff..
          suzukiTransportMassPoint base hlog (cutoff + 1),
      suzukiSmoothCurvature s) = suzukiPrimeWeight cutoff := by
  let r := suzukiTransportMassPoint base hlog cutoff
  let r' := suzukiTransportMassPoint base hlog (cutoff + 1)
  have hr : base ≤ r := base_le_suzukiTransportMassPoint base hlog cutoff
  have hr' : base ≤ r' :=
    base_le_suzukiTransportMassPoint base hlog (cutoff + 1)
  have hcontinuous :
      ContinuousOn suzukiSmoothCurvature (Set.Ici base) :=
    continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro t ht
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog.trans ht))
  have hc_base_r := intervalIntegrable_of_continuousOn_Ici
    hcontinuous (le_refl base) hr
  have hc_r_r' := intervalIntegrable_of_continuousOn_Ici
    hcontinuous hr hr'
  have hsplit :
      transportCurvatureMass suzukiSmoothCurvature base r' =
        transportCurvatureMass suzukiSmoothCurvature base r +
          ∫ s in r..r', suzukiSmoothCurvature s := by
    unfold transportCurvatureMass
    exact (intervalIntegral.integral_add_adjacent_intervals
      hc_base_r hc_r_r').symm
  change (∫ s in r..r', suzukiSmoothCurvature s) = _
  rw [suzukiTransportMassPoint_mass_eq,
    suzukiTransportMassPoint_mass_eq, screwPrefixMass_succ] at hsplit
  linarith

/-- The first curvature moment also splits exactly across consecutive
canonical mass cells. -/
theorem transportCurvatureMoment_suzukiTransportMassPoint_succ
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) :
    transportCurvatureMoment suzukiSmoothCurvature base
        (suzukiTransportMassPoint base hlog (cutoff + 1)) =
      transportCurvatureMoment suzukiSmoothCurvature base
          (suzukiTransportMassPoint base hlog cutoff) +
        ∫ s in
          suzukiTransportMassPoint base hlog cutoff..
            suzukiTransportMassPoint base hlog (cutoff + 1),
          s * suzukiSmoothCurvature s := by
  let r := suzukiTransportMassPoint base hlog cutoff
  let r' := suzukiTransportMassPoint base hlog (cutoff + 1)
  have hr : base ≤ r := base_le_suzukiTransportMassPoint base hlog cutoff
  have hr' : base ≤ r' :=
    base_le_suzukiTransportMassPoint base hlog (cutoff + 1)
  have hcontinuous :
      ContinuousOn suzukiSmoothCurvature (Set.Ici base) :=
    continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro t ht
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog.trans ht))
  have hj_base_r := intervalIntegrable_moment_of_continuousOn_Ici
    hcontinuous (le_refl base) hr
  have hj_r_r' := intervalIntegrable_moment_of_continuousOn_Ici
    hcontinuous hr hr'
  unfold transportCurvatureMoment
  exact (intervalIntegral.integral_add_adjacent_intervals
    hj_base_r hj_r_r').symm

/-- One cell surplus is its atomic first moment minus the corresponding
smooth first moment. -/
theorem suzukiTransportCellSurplus_eq
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) :
    suzukiTransportCellSurplus base hlog cutoff =
      suzukiPrimeWeight cutoff * suzukiPrimeLocation cutoff -
        ∫ s in
          suzukiTransportMassPoint base hlog cutoff..
            suzukiTransportMassPoint base hlog (cutoff + 1),
          s * suzukiSmoothCurvature s := by
  let r := suzukiTransportMassPoint base hlog cutoff
  let r' := suzukiTransportMassPoint base hlog (cutoff + 1)
  have hr : base ≤ r := base_le_suzukiTransportMassPoint base hlog cutoff
  have hr' : base ≤ r' :=
    base_le_suzukiTransportMassPoint base hlog (cutoff + 1)
  have hcontinuous :
      ContinuousOn suzukiSmoothCurvature (Set.Ici base) :=
    continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro t ht
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog.trans ht))
  have hc := intervalIntegrable_of_continuousOn_Ici hcontinuous hr hr'
  have hj := intervalIntegrable_moment_of_continuousOn_Ici hcontinuous hr hr'
  have hfun :
      (fun s : ℝ =>
        (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s) =
      fun s : ℝ =>
        suzukiPrimeLocation cutoff * suzukiSmoothCurvature s -
          s * suzukiSmoothCurvature s := by
    funext s
    ring
  unfold suzukiTransportCellSurplus
  change (∫ s in r..r',
    (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s) = _
  rw [hfun, intervalIntegral.integral_sub
    (hc.const_mul (suzukiPrimeLocation cutoff)) hj,
    intervalIntegral.integral_const_mul,
    integral_suzukiSmoothCurvature_transportCell]
  ring

/-- Exact recurrence: the next prefix gap is the old gap plus one signed
transport-cell surplus. -/
theorem suzukiTransportGap_succ
    (baseMargin base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) :
    suzukiTransportGap baseMargin base hlog (cutoff + 1) =
      suzukiTransportGap baseMargin base hlog cutoff +
        suzukiTransportCellSurplus base hlog cutoff := by
  unfold suzukiTransportGap
  rw [screwPrefixMoment_succ,
    transportCurvatureMoment_suzukiTransportMassPoint_succ,
    suzukiTransportCellSurplus_eq]
  ring

@[simp] theorem suzukiTransportGap_zero
    (baseMargin base : ℝ) (hlog : Real.log 2 ≤ base) :
    suzukiTransportGap baseMargin base hlog 0 = baseMargin := by
  simp [suzukiTransportGap, screwPrefixMoment]

/-- Every prefix gap is the initial margin plus the cumulative signed cell
surplus.  This identity retains cancellation between adjacent cells. -/
theorem suzukiTransportGap_eq_baseMargin_add_sum
    (baseMargin base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) :
    suzukiTransportGap baseMargin base hlog cutoff =
      baseMargin +
        ∑ n ∈ Finset.range cutoff,
          suzukiTransportCellSurplus base hlog n := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [suzukiTransportGap_succ, ih, Finset.sum_range_succ]
      ring

/-- Exact block form of the recurrence, starting at an arbitrary prefix.
This permits collective estimates without expanding the whole earlier
history of the transport process. -/
theorem suzukiTransportGap_add_eq_gap_add_sum
    (baseMargin base : ℝ) (hlog : Real.log 2 ≤ base)
    (start count : ℕ) :
    suzukiTransportGap baseMargin base hlog (start + count) =
      suzukiTransportGap baseMargin base hlog start +
        ∑ n ∈ Finset.range count,
          suzukiTransportCellSurplus base hlog (start + n) := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Nat.add_succ, suzukiTransportGap_succ, ih,
        Finset.sum_range_succ]
      ring

/-- A cell surplus is trapped between the prime weight times its displacement
from the two cell endpoints.  This is the rigorous local estimate behind
blockwise barycenter bounds. -/
theorem suzukiPrimeWeight_mul_location_sub_massPoint_succ_le_cellSurplus
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) :
    suzukiPrimeWeight cutoff *
        (suzukiPrimeLocation cutoff -
          suzukiTransportMassPoint base hlog (cutoff + 1)) ≤
      suzukiTransportCellSurplus base hlog cutoff := by
  let r := suzukiTransportMassPoint base hlog cutoff
  let r' := suzukiTransportMassPoint base hlog (cutoff + 1)
  have hr : base ≤ r := base_le_suzukiTransportMassPoint base hlog cutoff
  have hr' : base ≤ r' :=
    base_le_suzukiTransportMassPoint base hlog (cutoff + 1)
  have hrr' : r ≤ r' := suzukiTransportMassPoint_le_succ base hlog cutoff
  have hcontinuous :
      ContinuousOn suzukiSmoothCurvature (Set.Ici base) :=
    continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro t ht
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog.trans ht))
  have hc := intervalIntegrable_of_continuousOn_Ici hcontinuous hr hr'
  have hj := intervalIntegrable_moment_of_continuousOn_Ici hcontinuous hr hr'
  have hcellInt : IntervalIntegrable
      (fun s : ℝ =>
        (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s)
      MeasureTheory.volume r r' := by
    have heq :
        (fun s : ℝ =>
          (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s) =
        fun s : ℝ =>
          suzukiPrimeLocation cutoff * suzukiSmoothCurvature s -
            s * suzukiSmoothCurvature s := by
      funext s
      ring
    rw [heq]
    exact (hc.const_mul (suzukiPrimeLocation cutoff)).sub hj
  have hlowerInt : IntervalIntegrable
      (fun s : ℝ =>
        (suzukiPrimeLocation cutoff - r') * suzukiSmoothCurvature s)
      MeasureTheory.volume r r' :=
    hc.const_mul (suzukiPrimeLocation cutoff - r')
  have hmono :
      (∫ s in r..r',
          (suzukiPrimeLocation cutoff - r') * suzukiSmoothCurvature s) ≤
        ∫ s in r..r',
          (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s := by
    apply intervalIntegral.integral_mono_on hrr' hlowerInt hcellInt
    intro s hs
    apply mul_le_mul_of_nonneg_right
    · linarith [hs.2]
    · exact (suzukiSmoothCurvature_pos_of_log_two_le
        (hlog.trans (hr.trans hs.1))).le
  change suzukiPrimeWeight cutoff *
      (suzukiPrimeLocation cutoff - r') ≤ _
  unfold suzukiTransportCellSurplus
  change _ ≤ ∫ s in r..r',
    (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s
  calc
    suzukiPrimeWeight cutoff * (suzukiPrimeLocation cutoff - r') =
        (suzukiPrimeLocation cutoff - r') *
          (∫ s in r..r', suzukiSmoothCurvature s) := by
      rw [integral_suzukiSmoothCurvature_transportCell]
      ring
    _ = ∫ s in r..r',
        (suzukiPrimeLocation cutoff - r') * suzukiSmoothCurvature s := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ _ := hmono

theorem suzukiTransportCellSurplus_le_primeWeight_mul_location_sub_massPoint
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ) :
    suzukiTransportCellSurplus base hlog cutoff ≤
      suzukiPrimeWeight cutoff *
        (suzukiPrimeLocation cutoff -
          suzukiTransportMassPoint base hlog cutoff) := by
  let r := suzukiTransportMassPoint base hlog cutoff
  let r' := suzukiTransportMassPoint base hlog (cutoff + 1)
  have hr : base ≤ r := base_le_suzukiTransportMassPoint base hlog cutoff
  have hr' : base ≤ r' :=
    base_le_suzukiTransportMassPoint base hlog (cutoff + 1)
  have hrr' : r ≤ r' := suzukiTransportMassPoint_le_succ base hlog cutoff
  have hcontinuous :
      ContinuousOn suzukiSmoothCurvature (Set.Ici base) :=
    continuousOn_suzukiSmoothCurvature_Ioi.mono (by
      intro t ht
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog.trans ht))
  have hc := intervalIntegrable_of_continuousOn_Ici hcontinuous hr hr'
  have hj := intervalIntegrable_moment_of_continuousOn_Ici hcontinuous hr hr'
  have hcellInt : IntervalIntegrable
      (fun s : ℝ =>
        (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s)
      MeasureTheory.volume r r' := by
    have heq :
        (fun s : ℝ =>
          (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s) =
        fun s : ℝ =>
          suzukiPrimeLocation cutoff * suzukiSmoothCurvature s -
            s * suzukiSmoothCurvature s := by
      funext s
      ring
    rw [heq]
    exact (hc.const_mul (suzukiPrimeLocation cutoff)).sub hj
  have hupperInt : IntervalIntegrable
      (fun s : ℝ =>
        (suzukiPrimeLocation cutoff - r) * suzukiSmoothCurvature s)
      MeasureTheory.volume r r' :=
    hc.const_mul (suzukiPrimeLocation cutoff - r)
  have hmono :
      (∫ s in r..r',
          (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s) ≤
        ∫ s in r..r',
          (suzukiPrimeLocation cutoff - r) * suzukiSmoothCurvature s := by
    apply intervalIntegral.integral_mono_on hrr' hcellInt hupperInt
    intro s hs
    apply mul_le_mul_of_nonneg_right
    · linarith [hs.1]
    · exact (suzukiSmoothCurvature_pos_of_log_two_le
        (hlog.trans (hr.trans hs.1))).le
  unfold suzukiTransportCellSurplus
  change (∫ s in r..r',
    (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s) ≤ _
  calc
    (∫ s in r..r',
        (suzukiPrimeLocation cutoff - s) * suzukiSmoothCurvature s) ≤
        ∫ s in r..r',
          (suzukiPrimeLocation cutoff - r) * suzukiSmoothCurvature s := hmono
    _ = (suzukiPrimeLocation cutoff - r) *
        (∫ s in r..r', suzukiSmoothCurvature s) := by
      rw [intervalIntegral.integral_const_mul]
    _ = suzukiPrimeWeight cutoff *
        (suzukiPrimeLocation cutoff - r) := by
      rw [integral_suzukiSmoothCurvature_transportCell]
      ring

/-- If the next prime location lies to the right of its complete smooth-mass
cell, that cell makes a nonnegative contribution.  The converse need not hold
because the relevant datum is the cell barycenter. -/
theorem suzukiTransportCellSurplus_nonnegative_of_massPoint_succ_le_location
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ)
    (hcell : suzukiTransportMassPoint base hlog (cutoff + 1) ≤
      suzukiPrimeLocation cutoff) :
    0 ≤ suzukiTransportCellSurplus base hlog cutoff := by
  unfold suzukiTransportCellSurplus
  apply intervalIntegral.integral_nonneg
    (suzukiTransportMassPoint_le_succ base hlog cutoff)
  intro s hs
  apply mul_nonneg
  · exact sub_nonneg.mpr (hs.2.trans hcell)
  · exact (suzukiSmoothCurvature_pos_of_log_two_le
      (hlog.trans ((base_le_suzukiTransportMassPoint base hlog cutoff).trans
        hs.1))).le

/-- If the prime atom lies to the left of the entire smooth cell, its local
surplus is nonpositive. -/
theorem suzukiTransportCellSurplus_nonpositive_of_location_le_massPoint
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ)
    (hcell : suzukiPrimeLocation cutoff ≤
      suzukiTransportMassPoint base hlog cutoff) :
    suzukiTransportCellSurplus base hlog cutoff ≤ 0 := by
  calc
    suzukiTransportCellSurplus base hlog cutoff ≤
        suzukiPrimeWeight cutoff *
          (suzukiPrimeLocation cutoff -
            suzukiTransportMassPoint base hlog cutoff) :=
      suzukiTransportCellSurplus_le_primeWeight_mul_location_sub_massPoint
        base hlog cutoff
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      (suzukiPrimeWeight_nonnegative cutoff) (sub_nonpos.mpr hcell)

/-- A zero-weight integer contributes no transport cell and no change of
gap.  Thus the recurrence automatically ignores non-prime-powers. -/
theorem suzukiTransportMassPoint_succ_eq_of_weight_eq_zero
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ)
    (hweight : suzukiPrimeWeight cutoff = 0) :
    suzukiTransportMassPoint base hlog (cutoff + 1) =
      suzukiTransportMassPoint base hlog cutoff := by
  apply (strictlyMonoOn_suzukiTransportCurvatureMass hlog).injOn
  · exact base_le_suzukiTransportMassPoint base hlog (cutoff + 1)
  · exact base_le_suzukiTransportMassPoint base hlog cutoff
  · rw [suzukiTransportMassPoint_mass_eq,
      suzukiTransportMassPoint_mass_eq, screwPrefixMass_succ, hweight,
      add_zero]

theorem suzukiTransportCellSurplus_eq_zero_of_weight_eq_zero
    (base : ℝ) (hlog : Real.log 2 ≤ base) (cutoff : ℕ)
    (hweight : suzukiPrimeWeight cutoff = 0) :
    suzukiTransportCellSurplus base hlog cutoff = 0 := by
  unfold suzukiTransportCellSurplus
  rw [suzukiTransportMassPoint_succ_eq_of_weight_eq_zero
    base hlog cutoff hweight]
  simp

/-- Final cumulative-surplus form of the tail frontier.  It is equivalent,
not merely sufficient: every initial-margin loss must be repaid by the
collective signed barycenter surplus of the prime cells. -/
theorem
    suzukiPrimeHingeModel_nonnegativeOn_tail_iff_cumulativeTransportSurplus
    (baseMargin base : ℝ) (hlog : Real.log 2 ≤ base) :
    (∀ t : ℝ, base ≤ t →
      0 ≤ screwHingeModel
        (zeroSlopeCurvatureBackground baseMargin base
          suzukiSmoothCurvature)
        suzukiPrimeLocation suzukiPrimeWeight t) ↔
      ∀ cutoff : ℕ,
        -baseMargin ≤
          ∑ n ∈ Finset.range cutoff,
            suzukiTransportCellSurplus base hlog n := by
  rw [suzukiPrimeHingeModel_nonnegativeOn_tail_iff_canonicalTransportGaps]
  change (∀ cutoff : ℕ,
      0 ≤ suzukiTransportGap baseMargin base hlog cutoff) ↔ _
  constructor
  · intro hgaps cutoff
    have hgap := hgaps cutoff
    rw [suzukiTransportGap_eq_baseMargin_add_sum] at hgap
    linarith
  · intro hsums cutoff
    rw [suzukiTransportGap_eq_baseMargin_add_sum]
    have hsum := hsums cutoff
    linarith

end

end RiemannGaussian
