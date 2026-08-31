import RiemannGaussian.External.Zeta23Baseline

/-!
# Exact comparison and distinct-denominator form of the Zeta23 benchmark

The vendored Montgomery--Taylor theorem uses the exact transcendental
constant `Zeta23.ThmD.HD 1`. Its upstream source reports a decimal value but
does not formalize a comparison with `2/3`. This module proves inside Lean
that `HD 1 > 2/3`.

The analytic input is a strict fifth-order lower bound

`x + x^3 / 3 + 2 x^5 / 15 < tan x`,

proved by two derivative-monotonicity arguments on `(0, pi/2)`. At
`x = 1 / sqrt 2` its polynomial side is exactly `3 sqrt 2 / 5`, which gives
`cStar 1 > 3/4` and hence `HD 1 > 2/3` without numerical evaluation.

The final theorems expose a named positive gain above `2/3` in the literal
zeta-zero inequality and transport the exact benchmark from the
multiplicity-counted denominator `Ncount` to the distinct-zero denominator
`Ndist`. This is a checked normalization of the attributed external result,
not a new RiemannGaussian zero-proportion improvement.
-/

open Set

namespace RiemannGaussian

noncomputable section

/-- The cubic truncation is a strict lower bound for tangent on the positive
half-period. Its derivative is `tan(x)^2 - x^2`, positive by `x < tan x`. -/
theorem tan_gt_linear_add_cube
    {x : ℝ} (hx0 : 0 < x) (hxpi : x < Real.pi / 2) :
    x + x ^ 3 / 3 < Real.tan x := by
  let U : Set ℝ := Set.Ico 0 (Real.pi / 2)
  let f : ℝ → ℝ :=
    Real.tan - (id + fun y ↦ (1 / 3 : ℝ) * y ^ 3)
  have hinterior : interior U = Set.Ioo 0 (Real.pi / 2) := interior_Ico
  have hcos_pos {y : ℝ} (hy : y ∈ U) : 0 < Real.cos y := by
    exact Real.cos_pos_of_mem_Ioo
      (Set.Ico_subset_Ioo_left (by
        have := Real.pi_pos
        linarith : -(Real.pi / 2) < 0) hy)
  have hcontinuous : ContinuousOn f U := by
    apply ContinuousOn.sub
    · apply ContinuousOn.mono Real.continuousOn_tan
      intro y hy
      exact (hcos_pos hy).ne'
    · fun_prop
  have hderiv_pos (y : ℝ) (hy : y ∈ interior U) : 0 < deriv f y := by
    have hyU : y ∈ U := interior_subset hy
    rw [hinterior] at hy
    have hy0 : 0 < y := hy.1
    have hypi : y < Real.pi / 2 := hy.2
    have hcos : Real.cos y ≠ 0 := (hcos_pos hyU).ne'
    have htan : y < Real.tan y := Real.lt_tan hy0 hypi
    have htan0 : 0 < Real.tan y := hy0.trans htan
    have hsq : y ^ 2 < Real.tan y ^ 2 := by nlinarith
    have hsec : 1 / Real.cos y ^ 2 = 1 + Real.tan y ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq y]
    have hd : HasDerivAt f
        (1 / Real.cos y ^ 2 - (1 + y ^ 2)) y := by
      have hraw := (Real.hasDerivAt_tan hcos).sub
        ((hasDerivAt_id y).add
          (((hasDerivAt_pow 3 y).const_mul (1 / 3 : ℝ))))
      simpa [f] using hraw
    rw [hd.deriv]
    rw [hsec]
    nlinarith
  have hmono : StrictMonoOn f U :=
    strictMonoOn_of_deriv_pos (convex_Ico 0 (Real.pi / 2)) hcontinuous hderiv_pos
  have hzero : (0 : ℝ) ∈ U := by simp [U, Real.pi_pos]
  have hxU : x ∈ U := ⟨hx0.le, hxpi⟩
  have := hmono hzero hxU hx0
  have hresult : x + (1 / 3 : ℝ) * x ^ 3 < Real.tan x := by
    simpa [f] using this
  convert hresult using 1
  ring

/-- The fifth-order truncation is a strict lower bound for tangent on the
positive half-period. Its derivative is positive by the cubic bound. -/
theorem tan_gt_fifth_order
    {x : ℝ} (hx0 : 0 < x) (hxpi : x < Real.pi / 2) :
    x + x ^ 3 / 3 + 2 * x ^ 5 / 15 < Real.tan x := by
  let U : Set ℝ := Set.Ico 0 (Real.pi / 2)
  let f : ℝ → ℝ :=
    Real.tan - ((id + fun y ↦ (1 / 3 : ℝ) * y ^ 3) +
      fun y ↦ (2 / 15 : ℝ) * y ^ 5)
  have hinterior : interior U = Set.Ioo 0 (Real.pi / 2) := interior_Ico
  have hcos_pos {y : ℝ} (hy : y ∈ U) : 0 < Real.cos y := by
    exact Real.cos_pos_of_mem_Ioo
      (Set.Ico_subset_Ioo_left (by
        have := Real.pi_pos
        linarith : -(Real.pi / 2) < 0) hy)
  have hcontinuous : ContinuousOn f U := by
    apply ContinuousOn.sub
    · apply ContinuousOn.mono Real.continuousOn_tan
      intro y hy
      exact (hcos_pos hy).ne'
    · fun_prop
  have hderiv_pos (y : ℝ) (hy : y ∈ interior U) : 0 < deriv f y := by
    have hyU : y ∈ U := interior_subset hy
    rw [hinterior] at hy
    have hy0 : 0 < y := hy.1
    have hypi : y < Real.pi / 2 := hy.2
    have hcos : Real.cos y ≠ 0 := (hcos_pos hyU).ne'
    have htan := tan_gt_linear_add_cube hy0 hypi
    have hbase : 0 < y + y ^ 3 / 3 := by positivity
    have hsq : (y + y ^ 3 / 3) ^ 2 < Real.tan y ^ 2 := by
      nlinarith
    have hsec : 1 / Real.cos y ^ 2 = 1 + Real.tan y ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq y]
    have hd : HasDerivAt f
        (1 / Real.cos y ^ 2 -
          (1 + y ^ 2 + (2 / 3) * y ^ 4)) y := by
      have hraw := (Real.hasDerivAt_tan hcos).sub
        (((hasDerivAt_id y).add
          ((hasDerivAt_pow 3 y).const_mul (1 / 3 : ℝ))).add
            ((hasDerivAt_pow 5 y).const_mul (2 / 15 : ℝ)))
      have hrawF : HasDerivAt f
          (1 / Real.cos y ^ 2 -
            (1 + (1 / 3 : ℝ) * (3 * y ^ 2) +
              (2 / 15 : ℝ) * (5 * y ^ 4))) y := by
        simpa [f] using hraw
      exact hrawF.congr_deriv (by ring)
    rw [hd.deriv]
    rw [hsec]
    nlinarith [sq_nonneg (y ^ 3)]
  have hmono : StrictMonoOn f U :=
    strictMonoOn_of_deriv_pos (convex_Ico 0 (Real.pi / 2)) hcontinuous hderiv_pos
  have hzero : (0 : ℝ) ∈ U := by simp [U, Real.pi_pos]
  have hxU : x ∈ U := ⟨hx0.le, hxpi⟩
  have := hmono hzero hxU hx0
  have hresult :
      x + (1 / 3 : ℝ) * x ^ 3 + (2 / 15 : ℝ) * x ^ 5 <
        Real.tan x := by
    simpa [f] using this
  convert hresult using 1
  ring

/-- Exact tangent bound at the Montgomery--Taylor evaluation point. -/
theorem tan_inv_sqrt_two_gt_three_sqrt_two_div_five :
    3 * Real.sqrt 2 / 5 < Real.tan (Real.sqrt 2)⁻¹ := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hsSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx0 : 0 < (Real.sqrt 2)⁻¹ := inv_pos.mpr hs
  have hxpi : (Real.sqrt 2)⁻¹ < Real.pi / 2 := by
    exact Zeta23.ThmD.sqrt_two_inv_lt_one.trans (by
      have := Real.pi_gt_three
      linarith)
  have htan := tan_gt_fifth_order hx0 hxpi
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp [hs.ne']
    nlinarith [hsSq]
  have hcube : (Real.sqrt 2 / 2) ^ 3 = Real.sqrt 2 / 4 := by
    rw [div_pow]
    norm_num
    calc
      Real.sqrt 2 ^ 3 / 8 =
          (Real.sqrt 2 ^ 2) * Real.sqrt 2 / 8 := by ring
      _ = Real.sqrt 2 / 4 := by rw [hsSq]; ring
  have hfifth : (Real.sqrt 2 / 2) ^ 5 = Real.sqrt 2 / 8 := by
    rw [div_pow]
    norm_num
    calc
      Real.sqrt 2 ^ 5 / 32 =
          (Real.sqrt 2 ^ 2) ^ 2 * Real.sqrt 2 / 32 := by ring
      _ = Real.sqrt 2 / 8 := by rw [hsSq]; ring
  have hpoly :
      (Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹ ^ 3 / 3 +
          2 * (Real.sqrt 2)⁻¹ ^ 5 / 15 =
        3 * Real.sqrt 2 / 5 := by
    rw [hinv, hcube, hfifth]
    ring
  rwa [hpoly] at htan

/-- The exact optimized Montgomery--Taylor ratio constant at bandwidth one is
strictly greater than `3/4`. -/
theorem externalZeta23_cStar_one_gt_three_four :
    (3 : ℝ) / 4 < Zeta23.ThmD.cStar 1 := by
  rw [Zeta23.ThmD.cStar_eq_tan_form zero_le_one le_rfl,
    Zeta23.ThmD.theta_one]
  let s : ℝ := Real.sqrt 2
  let t : ℝ := Real.tan (Real.sqrt 2)⁻¹
  have hs : 0 < s := by dsimp [s]; positivity
  have hsSq : s ^ 2 = 2 := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hinv : s⁻¹ = s / 2 := by
    field_simp [hs.ne']
    nlinarith [hsSq]
  have ht : 3 * s / 5 < t := by
    simpa [s, t] using tan_inv_sqrt_two_gt_three_sqrt_two_div_five
  have ht0 : 0 < t := by
    have hs0 : 0 < 3 * s / 5 := by positivity
    exact hs0.trans ht
  rw [show (Real.sqrt 2) = s by rfl, show Real.tan (Real.sqrt 2)⁻¹ = t by rfl,
    show (Real.sqrt 2)⁻¹ = s⁻¹ by rfl, hinv]
  have hden : 0 < 1 + s / 2 * t := by positivity
  rw [lt_div_iff₀ hden]
  nlinarith [hsSq]

/-- The exact imported Montgomery--Taylor zero-proportion constant is
strictly greater than the earlier two-thirds constant. -/
theorem externalZeta23_HD_one_gt_two_thirds :
    (2 : ℝ) / 3 < Zeta23.ThmD.HD 1 := by
  have hc : (3 : ℝ) / 4 < Zeta23.ThmD.cStar 1 :=
    externalZeta23_cStar_one_gt_three_four
  have hc0 : 0 < Zeta23.ThmD.cStar 1 :=
    Zeta23.ThmD.cStar_pos one_pos le_rfl
  have hinv : 1 / Zeta23.ThmD.cStar 1 < (4 : ℝ) / 3 := by
    rw [div_lt_iff₀ hc0]
    nlinarith
  unfold Zeta23.ThmD.HD
  linarith

/-- A concrete positive margin halfway between `2/3` and the exact imported
Montgomery--Taylor constant. -/
def externalZeta23StrictGainOverTwoThirds : ℝ :=
  (Zeta23.ThmD.HD 1 - (2 : ℝ) / 3) / 2

/-- The named exact margin over two-thirds is strictly positive. -/
theorem externalZeta23_strictGainOverTwoThirds_pos :
    0 < externalZeta23StrictGainOverTwoThirds := by
  unfold externalZeta23StrictGainOverTwoThirds
  linarith [externalZeta23_HD_one_gt_two_thirds]

/-- Literal zeta-count form of a strict positive gain over two-thirds. The
denominator retains analytic multiplicity and the numerator counts distinct
critical-line zeros, exactly as in the attributed external theorem. -/
theorem externalZeta23_strictlyAboveTwoThirds_distinctCritical :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2 : ℝ) / 3 + externalZeta23StrictGainOverTwoThirds - ε) *
          (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0star T (2 * T) := by
  intro ε hε
  have hgain := externalZeta23_strictGainOverTwoThirds_pos
  obtain ⟨T₀, hT₀⟩ := externalZeta23_montgomeryTaylor_distinctCritical
    (ε + externalZeta23StrictGainOverTwoThirds) (by positivity)
  refine ⟨T₀, fun T hT ↦ ?_⟩
  have h := hT₀ T hT
  convert h using 1
  unfold externalZeta23StrictGainOverTwoThirds
  ring

/-- The exact Montgomery--Taylor benchmark also holds with the smaller
distinct-zero denominator. This aligns its normalization with the finite eta
carrier while remaining a corollary of the external result. -/
theorem externalZeta23_montgomeryTaylor_distinctDenominator :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 - ε) *
          (Zeta23.Ndist T (2 * T) : ℝ) ≤
        Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    externalZeta23_montgomeryTaylor_distinctCritical ε hε
  refine ⟨T₀, fun T hT ↦ ?_⟩
  let c : ℝ := Zeta23.ThmD.HD 1 - ε
  by_cases hc : 0 ≤ c
  · have hdist : Zeta23.Ndist T (2 * T) ≤ Zeta23.Ncount T (2 * T) :=
      (Zeta23.trivial_chain Zeta23.zetaSeam T (2 * T)).2.2.2.2.2
    calc
      c * (Zeta23.Ndist T (2 * T) : ℝ) ≤
          c * (Zeta23.Ncount T (2 * T) : ℝ) := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdist) hc
      _ ≤ Zeta23.N0star T (2 * T) := hT₀ T hT
  · have hc' : c ≤ 0 := le_of_not_ge hc
    calc
      c * (Zeta23.Ndist T (2 * T) : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc' (Nat.cast_nonneg _)
      _ ≤ Zeta23.N0star T (2 * T) := Nat.cast_nonneg _

/-- Strict-gain form of the imported benchmark with a distinct-zero
denominator and distinct critical-line numerator. -/
theorem externalZeta23_strictlyAboveTwoThirds_distinctDenominator :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2 : ℝ) / 3 + externalZeta23StrictGainOverTwoThirds - ε) *
          (Zeta23.Ndist T (2 * T) : ℝ) ≤
        Zeta23.N0star T (2 * T) := by
  intro ε hε
  have hgain := externalZeta23_strictGainOverTwoThirds_pos
  obtain ⟨T₀, hT₀⟩ := externalZeta23_montgomeryTaylor_distinctDenominator
    (ε + externalZeta23StrictGainOverTwoThirds) (by positivity)
  refine ⟨T₀, fun T hT ↦ ?_⟩
  have h := hT₀ T hT
  convert h using 1
  unfold externalZeta23StrictGainOverTwoThirds
  ring

end

end RiemannGaussian
