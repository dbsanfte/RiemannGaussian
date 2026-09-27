/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOrderedCapacity

/-!
# Whole-period phase budgets for the four/five signed comparison

The exact original radial kernel and prime-product cosine have a common
relative error budget. Three-percent angular surplus tolerates a one-percent
population/allocation loss, radial oscillation 501/500, and fixed phase
uncertainty 1/10000. The entire period, including cosine-zero neighborhoods,
is charged. No actual angular surplus, prime-population transport, whole
carrier floor or zero exclusion is assumed to have been discharged here.
-/

namespace RiemannGaussian.ZetaRieszPhaseBudget
noncomputable section
open MeasureTheory Filter Topology
open ZetaRieszAllowancePrimeBoxes
open scoped BigOperators Classical
open scoped Interval

/-- The negative-cosine credit over a full phase period has exact mass two. -/
theorem integral_positive_cos :
    (∫ x in (-Real.pi)..Real.pi, max 0 (Real.cos x)) = 2 := by
  have hc : Continuous (fun x : ℝ => max 0 (Real.cos x)) :=
    continuous_const.max Real.continuous_cos
  have hp := Real.pi_pos
  have hleft : (∫ x in (-Real.pi)..(-(Real.pi/2)), max 0 (Real.cos x)) = 0 := by
    have he : (∫ x in (-Real.pi)..(-(Real.pi/2)), max 0 (Real.cos x)) =
        ∫ _x in (-Real.pi)..(-(Real.pi/2)), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      have hs := Real.cos_nonpos_of_pi_div_two_le_of_le
        (show Real.pi/2 ≤ -x by linarith [hx.2])
        (show -x ≤ Real.pi+Real.pi/2 by linarith [hx.1])
      rw [Real.cos_neg] at hs
      exact max_eq_left hs
    simpa using he
  have hright : (∫ x in (Real.pi/2)..Real.pi, max 0 (Real.cos x)) = 0 := by
    have he : (∫ x in (Real.pi/2)..Real.pi, max 0 (Real.cos x)) =
        ∫ _x in (Real.pi/2)..Real.pi, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact max_eq_left (Real.cos_nonpos_of_pi_div_two_le_of_le hx.1 (by linarith [hx.2]))
    simpa using he
  have hmiddle : (∫ x in (-(Real.pi/2))..(Real.pi/2), max 0 (Real.cos x)) = 2 := by
    calc
      _ = ∫ x in (-(Real.pi/2))..(Real.pi/2), Real.cos x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by linarith)] at hx
        exact max_eq_right (Real.cos_nonneg_of_mem_Icc hx)
      _ = 2 := by rw [integral_cos, Real.sin_neg, Real.sin_pi_div_two]; norm_num
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-Real.pi) (-(Real.pi/2)))
    (hc.intervalIntegrable (μ := volume) (-(Real.pi/2)) (Real.pi/2))
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-Real.pi) (Real.pi/2))
    (hc.intervalIntegrable (μ := volume) (Real.pi/2) Real.pi)
  rw [hleft, hmiddle] at h₁
  rw [← h₂, ← h₁, hright]
  norm_num

/-- Fixed phase uncertainty is charged relatively over the complete
period, including points at which the cosine changes sign. -/
theorem integral_phase_lower {ε : ℝ} (hε : 0 ≤ ε) :
    2-2*Real.pi*ε ≤
      ∫ x in (-Real.pi)..Real.pi, max 0 (Real.cos x-ε) := by
  have h₁ : Continuous (fun x : ℝ => max 0 (Real.cos x)-ε) :=
    (continuous_const.max Real.continuous_cos).sub continuous_const
  have h₂ : Continuous (fun x : ℝ => max 0 (Real.cos x-ε)) :=
    continuous_const.max (Real.continuous_cos.sub continuous_const)
  have he : (∫ x in (-Real.pi)..Real.pi, max 0 (Real.cos x)-ε) =
      2-2*Real.pi*ε := by
    rw [intervalIntegral.integral_sub
      ((continuous_const.max Real.continuous_cos).intervalIntegrable _ _)
      (intervalIntegrable_const), integral_positive_cos, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [← he]
  apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _)
  intro x _
  by_cases hc : 0 ≤ Real.cos x
  · rw [max_eq_right hc]
    exact le_max_right _ _
  · rw [max_eq_left (le_of_not_ge hc)]
    exact (by linarith : (0 : ℝ)-ε ≤ 0).trans (le_max_left _ _)

/-- Every point of a phase box, including either sign of the cosine,
lies in these explicit one-sided envelopes. -/
theorem phase_enclosure {x a ε : ℝ} (hε : 0 ≤ ε) (hx : |x-a| ≤ ε) :
    max 0 (Real.cos a-ε) ≤ max 0 (Real.cos x) ∧
      max 0 (Real.cos x) ≤ max 0 (Real.cos a)+ε := by
  have h := abs_le.mp ((Real.abs_cos_sub_cos_le x a).trans hx)
  constructor
  · exact max_le_max le_rfl (by linarith)
  · apply max_le
    · linarith [le_max_left 0 (Real.cos a)]
    · linarith [le_max_right 0 (Real.cos a)]

/-- The upper phase envelope retains the entire period. -/
theorem integral_phase_upper (ε : ℝ) :
    (∫ x in (-Real.pi)..Real.pi, max 0 (Real.cos x)+ε) =
      2+2*Real.pi*ε := by
  rw [intervalIntegral.integral_add
    ((continuous_const.max Real.continuous_cos).intervalIntegrable _ _)
    intervalIntegrable_const, integral_positive_cos, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- A phase error of at most one ten-thousandth costs less than one
thousandth of the total mass. The intervals adjacent to cosine zeros
are retained and charged in this inequality. -/
theorem rational_phase_budgets {ε : ℝ} (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000) :
    (1999/1000 : ℝ) ≤ (∫ x in (-Real.pi)..Real.pi, max 0 (Real.cos x-ε)) ∧
      (∫ x in (-Real.pi)..Real.pi, max 0 (Real.cos x)+ε) ≤ 2001/1000 := by
  have hp : Real.pi*ε ≤ 4/10000 := by
    have h₁ := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hε
    nlinarith
  constructor
  · exact (by nlinarith : (1999/1000 : ℝ) ≤ 2-2*Real.pi*ε).trans
      (integral_phase_lower hε)
  · rw [integral_phase_upper]
    nlinarith

/-- A three-percent angular surplus tolerates a one-percent aggregate
population/allocation loss, the proved radial cost 501/500, and full
phase-box uncertainty. The result is a joint signed inequality, not an
absolute error charged against the growing source envelope. -/
theorem joint_phase_budget {D S ε : ℝ} (hD : 0 ≤ D)
    (hS : (103/100 : ℝ)*D ≤ S) (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000) :
    (3/100 : ℝ)*D ≤ ∫ x in (-Real.pi)..Real.pi,
      (99/100 : ℝ)*S*max 0 (Real.cos x-ε)-
        (501/500 : ℝ)*D*(max 0 (Real.cos x)+ε) := by
  have hb := rational_phase_budgets hε hεu
  have hS0 : 0 ≤ S := (by positivity : (0 : ℝ) ≤ (103/100)*D).trans hS
  have hc₁ : Continuous (fun x : ℝ => max 0 (Real.cos x-ε)) :=
    continuous_const.max (Real.continuous_cos.sub continuous_const)
  have hc₂ : Continuous (fun x : ℝ => max 0 (Real.cos x)+ε) :=
    (continuous_const.max Real.continuous_cos).add continuous_const
  rw [intervalIntegral.integral_sub
    ((hc₁.const_mul ((99/100 : ℝ)*S)).intervalIntegrable _ _)
    ((hc₂.const_mul ((501/500 : ℝ)*D)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hl := mul_le_mul_of_nonneg_left hb.1
    (by positivity : (0 : ℝ) ≤ (99/100)*S)
  have hu := mul_le_mul_of_nonneg_left hb.2
    (by positivity : (0 : ℝ) ≤ (501/500)*D)
  nlinarith

/-- The sign-reversed form applies to the adverse four-prime and favorable
five-prime populations, both of which are compared on negative cosine. -/
theorem negative_phase_enclosure {x a ε : ℝ} (hε : 0 ≤ ε) (hx : |x-a| ≤ ε) :
    max 0 (-Real.cos a-ε) ≤ max 0 (-Real.cos x) ∧
      max 0 (-Real.cos x) ≤ max 0 (-Real.cos a)+ε := by
  have h := phase_enclosure hε (show |(x+Real.pi)-(a+Real.pi)| ≤ ε by
    simpa only [add_sub_add_right_eq_sub] using hx)
  simpa only [Real.cos_add_pi] using h

/-- Prime-window transport keeps the full product phase. Its error is
bounded by the fixed total window width, independent of the moment order. -/
theorem tuple_negative_phase_enclosure {k : ℕ} {a : Fin k → ℝ} {h y : ℝ}
    (hh : 0 ≤ h) {p : Fin k → ℕ}
    (hp : p ∈ Fintype.piFinset (fun i =>
      ZetaRieszAllowancePrimeBoxes.logPrimes (a i) h)) :
    max 0 (-Real.cos (y*∑ i, a i)-|y| * k*h) ≤
        max 0 (-Real.cos (y*Real.log (∏ i, p i : ℕ))) ∧
      max 0 (-Real.cos (y*Real.log (∏ i, p i : ℕ))) ≤
        max 0 (-Real.cos (y*∑ i, a i))+|y| * k*h := by
  have hb (i : Fin k) := ZetaRieszAllowancePrimeBoxes.logPrimes_bounds
    (Fintype.mem_piFinset.mp hp i)
  have he : Real.log (∏ i, p i : ℕ) = ∑ i, Real.log (p i) := by
    rw [Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hb i).1.ne_zero)]
  have hl : (∑ i, a i) ≤ Real.log (∏ i, p i : ℕ) := by
    rw [he]
    exact Finset.sum_le_sum (fun i _ => (hb i).2.1.le)
  have hu : Real.log (∏ i, p i : ℕ) ≤ (∑ i, a i)+k*h := by
    rw [he]
    calc
      _ ≤ ∑ i, (a i+h) := Finset.sum_le_sum (fun i _ => (hb i).2.2)
      _ = _ := by simp [Finset.sum_add_distrib]
  apply negative_phase_enclosure (by positivity)
  rw [← mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr hl)]
  have hm := mul_le_mul_of_nonneg_left (show
    Real.log (∏ i, p i : ℕ)-(∑ i, a i) ≤ k*h by linarith) (abs_nonneg y)
  simpa only [mul_assoc] using hm

/-- One fixed positive prime-window width simultaneously gives the small
phase uncertainty and short physical arc needed for counts four and five.
It may depend on the fixed height, but it never shrinks with the moment. -/
theorem exists_fixed_phase_width (y : ℝ) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1/100000 ∧ 5*h ≤ 1/8 ∧ |y| * 5*h ≤ 1/10000 := by
  let h : ℝ := 1/(100000*(|y|+1))
  have hy : 0 < |y|+1 := by linarith [abs_nonneg y]
  have hh : 0 < h := by dsimp [h]; positivity
  have he : h*(100000*(|y|+1)) = 1 := by
    dsimp [h]
    field_simp
  refine ⟨h,hh,?_,?_,?_⟩ <;> nlinarith [abs_nonneg y,mul_nonneg hh.le (abs_nonneg y)]

/-- Keeping a common varying radial weight preserves the signed surplus.
The debit and credit are compared jointly before integration. -/
theorem weighted_joint_phase_budget {D S ε V₀ : ℝ} {V : ℝ → ℝ}
    (hD : 0 ≤ D) (hS : (103/100 : ℝ)*D ≤ S)
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000) (hV₀ : 0 ≤ V₀)
    (hVc : ContinuousOn V (Set.Icc (-Real.pi) Real.pi))
    (hV : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      V₀ ≤ V x ∧ V x ≤ (501/500 : ℝ)*V₀) :
    (3/100 : ℝ)*D*V₀ ≤ ∫ x in (-Real.pi)..Real.pi,
      V x*((99/100 : ℝ)*S*max 0 (Real.cos x-ε)-
        D*(max 0 (Real.cos x)+ε)) := by
  have hS0 : 0 ≤ S := (by positivity : (0 : ℝ) ≤ (103/100)*D).trans hS
  have hc₁ : Continuous (fun x : ℝ => max 0 (Real.cos x-ε)) :=
    continuous_const.max (Real.continuous_cos.sub continuous_const)
  have hc₂ : Continuous (fun x : ℝ => max 0 (Real.cos x)+ε) :=
    (continuous_const.max Real.continuous_cos).add continuous_const
  have ha : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hi := intervalIntegral.integral_mono_on (μ := volume) ha
    ((((hc₁.const_mul ((99/100 : ℝ)*S)).sub
      (hc₂.const_mul ((501/500 : ℝ)*D))).const_mul V₀).intervalIntegrable _ _)
    ((hVc.mul ((hc₁.const_mul ((99/100 : ℝ)*S)).sub
      (hc₂.const_mul D)).continuousOn).intervalIntegrable_of_Icc ha)
    (fun x hx => show V₀*((99/100 : ℝ)*S*max 0 (Real.cos x-ε)-
          (501/500 : ℝ)*D*(max 0 (Real.cos x)+ε)) ≤
        V x*((99/100 : ℝ)*S*max 0 (Real.cos x-ε)-
          D*(max 0 (Real.cos x)+ε)) by
      have h₁ := mul_le_mul_of_nonneg_right (hV x hx).1
        (show 0 ≤ (99/100 : ℝ)*S*max 0 (Real.cos x-ε) by positivity)
      have h₂ := mul_le_mul_of_nonneg_right (hV x hx).2
        (show 0 ≤ D*(max 0 (Real.cos x)+ε) by positivity)
      nlinarith)
  rw [intervalIntegral.integral_const_mul] at hi
  have hj := mul_le_mul_of_nonneg_left (joint_phase_budget hD hS hε hεu) hV₀
  simpa only [Pi.mul_apply, Pi.sub_apply, mul_comm, mul_left_comm, mul_assoc] using hj.trans hi

/-- On an entire phase period inside the original core, the literal
radial factorial kernel has a positive minimum and relative oscillation
at most 501/500. No nearby moment is substituted. -/
theorem radial_period_comparable {N : ℕ} (hN : 0 < N) {b y : ℝ}
    (hy : 54 ≤ |y|)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N) :
    ∃ V₀ : ℝ, 0 < V₀ ∧ ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      V₀ ≤ Real.exp (-(b+x/|y|)/2)*(b+x/|y|)^N/N.factorial ∧
      Real.exp (-(b+x/|y|)/2)*(b+x/|y|)^N/N.factorial ≤
        (501/500 : ℝ)*V₀ := by
  let V : ℝ → ℝ := fun x => Real.exp (-(b+x/|y|)/2)*(b+x/|y|)^N/N.factorial
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hb (x : ℝ) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
      (39/20 : ℝ)*N ≤ b+x/|y| ∧ b+x/|y| ≤ (203/100 : ℝ)*N := by
    have ha := div_le_div_of_nonneg_right hx.1 hy0.le
    have hc := div_le_div_of_nonneg_right hx.2 hy0.le
    rw [neg_div] at ha
    constructor <;> linarith
  have hc : Continuous V := by dsimp [V]; fun_prop
  obtain ⟨x₀,hx₀,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (-Real.pi) Real.pi).Nonempty from ⟨0,by
      constructor <;> linarith [Real.pi_pos]⟩) hc.continuousOn
  have hv : 0 < V x₀ := by
    have hh := (hb x₀ hx₀).1
    have hpos : 0 < b+x₀/|y| := by nlinarith
    dsimp [V]
    positivity
  refine ⟨V x₀,hv,?_⟩
  intro x hx
  refine ⟨hmin hx,?_⟩
  apply ZetaRieszOrderedCapacity.radial_kernel_le_phase_arc hN
    (hb x₀ hx₀).1 (hb x₀ hx₀).2 (hb x hx).1 (hb x hx).2
  have he : |(b+x/|y|)-(b+x₀/|y|)| = |x-x₀|/|y| := by
    rw [add_sub_add_left_eq_sub, ← sub_div, abs_div, abs_abs]
  rw [he]
  apply (div_le_iff₀ hy0).mpr
  have hh := abs_le.mpr (show -(2*Real.pi) ≤ x-x₀ ∧ x-x₀ ≤ 2*Real.pi by
    constructor <;> linarith [hx.1,hx.2,hx₀.1,hx₀.2])
  nlinarith [Real.pi_lt_d4]

/-- Centering at a negative cosine peak is exact for either sign of the
fixed ordinate; it does not freeze any literal prime-product phase. -/
theorem phase_at_negative_peak {b y : ℝ} (hy : y ≠ 0)
    (hb : Real.cos (y*b) = -1) (x : ℝ) :
    -Real.cos (y*(b+x/|y|)) = Real.cos x := by
  have hs : Real.sin (y*b) = 0 := by
    have hsq := Real.sin_sq_add_cos_sq (y*b)
    rw [hb] at hsq
    nlinarith [sq_nonneg (Real.sin (y*b))]
  have hc : Real.cos (y*(x/|y|)) = Real.cos x := by
    rcases lt_or_gt_of_ne hy with hn | hp
    · rw [abs_of_neg hn]
      have he : y*(x/(-y)) = -x := by field_simp
      rw [he,Real.cos_neg]
    · rw [abs_of_pos hp]
      have he : y*(x/y) = x := by field_simp
      rw [he]
  rw [mul_add,Real.cos_add,hb,hs,hc]
  ring

/-- The complete original radial/phase period has a positive joint
budget whenever the angular supply exceeds the debit by three percent.
The numerical angular and actual prime-population premises still have to
be proved separately; this theorem pays their common radial/phase cost. -/
theorem original_radial_phase_budget {N : ℕ} (hN : 0 < N) {b y D S ε : ℝ}
    (hy : 54 ≤ |y|) (hpeak : Real.cos (y*b) = -1)
    (hlo : (39/20 : ℝ)*N ≤ b-Real.pi/|y|)
    (hhi : b+Real.pi/|y| ≤ (203/100 : ℝ)*N)
    (hD : 0 < D) (hS : (103/100 : ℝ)*D ≤ S)
    (hε : 0 ≤ ε) (hεu : ε ≤ 1/10000) :
    0 < ∫ x in (-Real.pi)..Real.pi,
      (Real.exp (-(b+x/|y|)/2)*(b+x/|y|)^N/N.factorial)*
        ((99/100 : ℝ)*S*max 0 (-Real.cos (y*(b+x/|y|))-ε)-
          D*(max 0 (-Real.cos (y*(b+x/|y|)))+ε)) := by
  obtain ⟨V₀,hV₀,hV⟩ := radial_period_comparable hN hy hlo hhi
  have hy0 : y ≠ 0 := by intro he; simp only [he,abs_zero] at hy; linarith
  simp_rw [phase_at_negative_peak hy0 hpeak]
  have hc : Continuous (fun x : ℝ =>
      Real.exp (-(b+x/|y|)/2)*(b+x/|y|)^N/N.factorial) := by fun_prop
  have hh := weighted_joint_phase_budget hD.le hS hε hεu hV₀.le hc.continuousOn hV
  exact (by positivity : (0 : ℝ) < (3/100)*D*V₀).trans_le hh

/-- A fixed small log window has asymptotically sharp harmonic prime mass,
with explicit relative constants suitable for the signed phase budget. -/
theorem eventually_phase_window_mass {h α : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, α*N ≤ a →
      (9999/10000 : ℝ)*h/a ≤ ∑ p ∈ logPrimes a h, (p : ℝ)⁻¹ ∧
      (∑ p ∈ logPrimes a h, (p : ℝ)⁻¹) ≤ (10001/10000 : ℝ)*h/a := by
  have hsmall : h < 1 := by linarith
  have hplus : 0 < 1+h := by linarith
  have hminus : 0 < 1-h := by linarith
  have hc : (99999/100000 : ℝ)*(1+h) ≤ 1 := by linarith
  have hd : (1 : ℝ) ≤ (50001/50000)*(1-h) := by linarith
  have heinv : Real.exp (-h) ≤ 1/(1+h) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hplus (by simpa only [add_comm] using Real.add_one_le_exp h)
  have hlow : (99999/100000 : ℝ)*h ≤ 1-Real.exp (-h) := by
    have ht : (99999/100000 : ℝ)*h ≤ h/(1+h) := by
      apply (le_div_iff₀ hplus).mpr
      nlinarith [mul_le_mul_of_nonneg_right hc hh.le]
    have he : h/(1+h) = 1-1/(1+h) := by field_simp; ring
    rw [he] at ht
    linarith
  have hupp : Real.exp h-1 ≤ (50001/50000 : ℝ)*h := by
    have he := Real.exp_bound_div_one_sub_of_interval hh.le hsmall
    have ht : h/(1-h) ≤ (50001/50000 : ℝ)*h := by
      apply (div_le_iff₀ hminus).mpr
      nlinarith [mul_le_mul_of_nonneg_right hd hh.le]
    have hi : h/(1-h) = 1/(1-h)-1 := by field_simp; ring
    rw [hi] at ht
    linarith
  have ht : Tendsto (fun N : ℕ => α*N) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hα
  filter_upwards [ZetaRieszSharpPrimeWindows.eventually_reciprocal_bounds hh hα
      (by norm_num : (0 : ℝ) < 1/100000), ht.eventually_ge_atTop 1]
    with N hN hN1 a ha
  have ha1 : (1 : ℝ) ≤ a := hN1.trans ha
  have ha0 : 0 < a := by linarith
  have hah : 0 < a+h := by positivity
  have hend : (99999/100000 : ℝ)/a ≤ 1/(a+h) := by
    apply (div_le_div_iff₀ ha0 hah).mpr
    nlinarith
  have hmass := hN a ha
  constructor
  · calc
      _ ≤ (99999/100000 : ℝ)*((99999/100000)*h)*((99999/100000)/a) := by
        have hc : (9999/10000 : ℝ) ≤ (99999/100000)^3 := by norm_num
        have hm := mul_le_mul_of_nonneg_right hc (div_nonneg hh.le ha0.le)
        calc
          _ = (9999/10000 : ℝ)*(h/a) := by ring
          _ ≤ (99999/100000 : ℝ)^3*(h/a) := hm
          _ = _ := by ring
      _ ≤ (1-1/100000)*(1-Real.exp (-h))/(a+h) := by
        have hm := mul_le_mul hlow hend (by positivity)
          (by linarith : 0 ≤ 1-Real.exp (-h))
        have hc := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 99999/100000)
        calc
          _ = (99999/100000 : ℝ)*(((99999/100000)*h)*((99999/100000)/a)) := by ring
          _ ≤ (99999/100000 : ℝ)*((1-Real.exp (-h))*(1/(a+h))) := hc
          _ = _ := by ring
      _ ≤ _ := hmass.1
  · calc
      _ ≤ (1+1/100000)*(Real.exp h-1)/a := hmass.2
      _ ≤ (1+1/100000)*((50001/50000)*h)/a :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hupp (by norm_num)) ha0.le
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ ha0.le
        nlinarith
/-- Four- and five-leg prime populations together cost less than one
thousandth relatively. The actual Cartesian prime sets are retained. -/
theorem eventually_phase_tuple_mass {h α : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) {k : ℕ} (hk : k ≤ 5) :
    ∀ᶠ N : ℕ in atTop, ∀ a : Fin k → ℝ, (∀ i, α*N ≤ a i) →
      (999/1000 : ℝ)*(∏ i, h/a i) ≤
        ∑ p ∈ Fintype.piFinset (fun i => logPrimes (a i) h), ∏ i, (p i : ℝ)⁻¹ ∧
      (∑ p ∈ Fintype.piFinset (fun i => logPrimes (a i) h), ∏ i, (p i : ℝ)⁻¹) ≤
        (1001/1000 : ℝ)*(∏ i, h/a i) := by
  have hlow : (999/1000 : ℝ) ≤ (9999/10000 : ℝ)^k := by
    interval_cases k <;> norm_num
  have hupp : (10001/10000 : ℝ)^k ≤ (1001/1000 : ℝ) := by
    interval_cases k <;> norm_num
  filter_upwards [eventually_phase_window_mass hh hhu hα,eventually_ge_atTop (1 : ℕ)]
    with N hN hN1 a ha
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have ha0 (i : Fin k) : 0 < a i := by nlinarith [ha i]
  have hprod : 0 ≤ ∏ i, h/a i := Finset.prod_nonneg (fun i _ => div_nonneg hh.le (ha0 i).le)
  have hlo : (∏ i, (9999/10000 : ℝ)*(h/a i)) ≤
      ∏ i, ∑ p ∈ logPrimes (a i) h, (p : ℝ)⁻¹ := by
    apply Finset.prod_le_prod
    · intro i _
      exact mul_nonneg (by norm_num) (div_nonneg hh.le (ha0 i).le)
    · intro i _
      simpa only [mul_div_assoc] using (hN (a i) (ha i)).1
  have hhi : (∏ i, ∑ p ∈ logPrimes (a i) h, (p : ℝ)⁻¹) ≤
      ∏ i, (10001/10000 : ℝ)*(h/a i) := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
    · intro i _
      simpa only [mul_div_assoc] using (hN (a i) (ha i)).2
  rw [Finset.prod_mul_distrib] at hlo hhi
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hlo hhi
  rw [← Finset.prod_univ_sum (fun i : Fin k => logPrimes (a i) h)
    (fun (_ : Fin k) (p : ℕ) => (p : ℝ)⁻¹)]
  exact ⟨(mul_le_mul_of_nonneg_right hlow hprod).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right hupp hprod)⟩


end
end RiemannGaussian.ZetaRieszPhaseBudget
