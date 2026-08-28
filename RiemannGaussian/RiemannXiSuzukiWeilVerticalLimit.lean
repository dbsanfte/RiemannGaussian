import RiemannGaussian.RiemannXiSuzukiWeilVertical
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The vanishing Suzuki--Weil vertical limit

This file reduces the explicit vertical-boundary majorant to a fixed
constant times a negative real power of `n + 1`, then closes the remaining
quantitative vertical limit in the global Suzuki--Weil meeting theorem.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The explicit real majorant produced by the complete vertical contour
estimate. -/
def suzukiXiWeilVerticalExplicitMajorant
    (A B t : ℝ) (n : ℕ) : ℝ :=
  2 * ((2 * (Real.exp |t| + 1) /
      quantitativeSpectralBoundaryTruncation n ^ 2) *
    (2 * ((2 * (B * (xiCanonicalRadius n + 1) ^ 2)) /
        (xiCanonicalRadius n / 4)) +
      (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) /
          Real.log 2) *
        (4 / xiCanonicalRadius n +
          2 * Real.log (1 + 3 / spectralBoundarySeparation n))))

/-- Fixed base controlling the logarithm of the reciprocal contour gap. -/
def suzukiXiWeilVerticalLogBase (A : ℝ) : ℝ :=
  1 + 9 * (A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2 + 4)

/-- Fixed coefficient controlling the complete logarithmic-derivative
`L¹` norm by `(n+1)^(27/16)`. -/
def suzukiXiWeilVerticalL1AsymptoticConstant (A B : ℝ) : ℝ :=
  784 * B +
    (A * (27 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
      (1 + 16 * (suzukiXiWeilVerticalLogBase A) ^ (1 / 8 : ℝ))

/-- Fixed coefficient in the final negative-power vertical majorant. -/
def suzukiXiWeilVerticalAsymptoticConstant (A B t : ℝ) : ℝ :=
  16 * (Real.exp |t| + 1) *
    suzukiXiWeilVerticalL1AsymptoticConstant A B

lemma rpow_threeHalves_mul_rpow_threeSixteenths
    {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) * x ^ (3 / 16 : ℝ) =
      x ^ (27 / 16 : ℝ) := by
  rw [← Real.rpow_add hx]
  norm_num

lemma rpow_threeHalves_rpow_oneEighth
    {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (3 / 2 : ℝ)) ^ (1 / 8 : ℝ) =
      x ^ (3 / 16 : ℝ) := by
  rw [← Real.rpow_mul hx]
  norm_num

lemma rpow_twentySevenSixteenths_div_sq
    {x : ℝ} (hx : 0 < x) :
    x ^ (27 / 16 : ℝ) / x ^ 2 = x ^ (-(5 / 16 : ℝ)) := by
  rw [← Real.rpow_two, div_eq_mul_inv, ← Real.rpow_neg hx.le,
    ← Real.rpow_add hx]
  norm_num

/-- The complete explicit majorant has a strict negative-power bound.  The
`5/16` margin is what remains after the `3/2` divisor count and the `3/16`
logarithmic allowance are subtracted from Suzuki's quadratic decay. -/
theorem suzukiXiWeilVerticalExplicitMajorant_le_rpow
    {A B : ℝ} (hA : 1 ≤ A)
    (hThreeHalves : ∀ w : ℂ,
      ‖riemannXi w‖ ≤
        Real.exp (A * (‖w‖ + 1) ^ (3 / 2 : ℝ)))
    (hB : 1 ≤ B) (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    suzukiXiWeilVerticalExplicitMajorant A B t n ≤
      suzukiXiWeilVerticalAsymptoticConstant A B t *
        ((n : ℝ) + 1) ^ (-(5 / 16 : ℝ)) := by
  let q : ℝ := (n : ℝ) + 1
  let R := xiCanonicalRadius n
  let T := quantitativeSpectralBoundaryTruncation n
  let xscale : ℝ := 2 * ((n : ℝ) + 2) + 1
  let D : ℝ := A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2 + 4
  let E : ℝ := suzukiXiWeilVerticalLogBase A
  let K : ℝ := suzukiXiWeilVerticalL1AsymptoticConstant A B
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < q := by dsimp [q]; linarith
  have hqone : 1 ≤ q := by dsimp [q]; linarith
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR : 0 < R := by simpa [R] using xiCanonicalRadius_pos n
  have hT : 0 < T := by
    exact (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hTlower : q / 2 ≤ T := by
    have ht := (quantitativeSpectralBoundaryTruncation_spec n).1
    dsimp [q, T]
    linarith
  have hRlower : 4 * q ≤ R := by
    have hr := (xiCanonicalRadius_spec n).1
    dsimp [q, R]
    linarith
  have hRupper : R + 1 ≤ 14 * q := by
    have hr := (xiCanonicalRadius_spec n).2.1
    dsimp [q, R]
    linarith
  have htwoR : 2 * R + 1 ≤ 27 * q := by
    have hr := (xiCanonicalRadius_spec n).2.1
    dsimp [q, R]
    linarith
  have hxscale : xscale ≤ 5 * q := by
    dsimp [xscale, q]
    linarith
  have hqThreeNonneg : 0 ≤ q ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hq.le _
  have hqThreeOne : 1 ≤ q ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow hqone (by norm_num)
  have htwoRpow :
      (2 * R + 1) ^ (3 / 2 : ℝ) ≤
        (27 : ℝ) ^ (3 / 2 : ℝ) * q ^ (3 / 2 : ℝ) := by
    calc
      (2 * R + 1) ^ (3 / 2 : ℝ) ≤
          (27 * q) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) htwoR (by norm_num)
      _ = (27 : ℝ) ^ (3 / 2 : ℝ) * q ^ (3 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hq.le]
  have hxscalePow :
      xscale ^ (3 / 2 : ℝ) ≤
        (5 : ℝ) ^ (3 / 2 : ℝ) * q ^ (3 / 2 : ℝ) := by
    have hxscale0 : 0 ≤ xscale := by
      dsimp [xscale]
      positivity
    calc
      xscale ^ (3 / 2 : ℝ) ≤ (5 * q) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hxscale0 hxscale (by norm_num)
      _ = (5 : ℝ) ^ (3 / 2 : ℝ) * q ^ (3 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hq.le]
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by
    dsimp [E, suzukiXiWeilVerticalLogBase]
    positivity
  have hsepRaw :=
    one_div_spectralBoundarySeparation_le_threeHalves_of_growth
      hA hThreeHalves n
  have hsep :
      1 / spectralBoundarySeparation n ≤
        3 * (D * q ^ (3 / 2 : ℝ)) := by
    calc
      1 / spectralBoundarySeparation n ≤
          3 * (A * xscale ^ (3 / 2 : ℝ) / Real.log 2 + 4) := by
        simpa [xscale] using hsepRaw
      _ ≤ 3 *
          (A * ((5 : ℝ) ^ (3 / 2 : ℝ) * q ^ (3 / 2 : ℝ)) /
              Real.log 2 + 4) := by
        gcongr
      _ = 3 *
          ((A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
              q ^ (3 / 2 : ℝ) + 4) := by ring
      _ ≤ 3 *
          ((A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2 + 4) *
            q ^ (3 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc
          (A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
                q ^ (3 / 2 : ℝ) + 4 ≤
              (A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
                q ^ (3 / 2 : ℝ) + 4 * q ^ (3 / 2 : ℝ) := by
            have h4 : (4 : ℝ) ≤ 4 * q ^ (3 / 2 : ℝ) := by
              nlinarith [hqThreeOne]
            exact add_le_add (le_refl _) h4
          _ = (A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2 + 4) *
                q ^ (3 / 2 : ℝ) := by ring
      _ = 3 * (D * q ^ (3 / 2 : ℝ)) := by rfl
  have harg :
      1 + 3 / spectralBoundarySeparation n ≤
        E * q ^ (3 / 2 : ℝ) := by
    have hthreeSep :
        3 / spectralBoundarySeparation n ≤
          9 * D * q ^ (3 / 2 : ℝ) := by
      calc
        3 / spectralBoundarySeparation n =
            3 * (1 / spectralBoundarySeparation n) := by ring
        _ ≤ 3 * (3 * (D * q ^ (3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hsep (by norm_num)
        _ = 9 * D * q ^ (3 / 2 : ℝ) := by ring
    calc
      1 + 3 / spectralBoundarySeparation n ≤
          q ^ (3 / 2 : ℝ) + 9 * D * q ^ (3 / 2 : ℝ) :=
        add_le_add hqThreeOne hthreeSep
      _ = E * q ^ (3 / 2 : ℝ) := by
        dsimp [E, D, suzukiXiWeilVerticalLogBase]
        ring
  have harg0 : 0 ≤ 1 + 3 / spectralBoundarySeparation n := by
    have hδ := spectralBoundarySeparation_pos n
    positivity
  have hargPow :
      (1 + 3 / spectralBoundarySeparation n) ^ (1 / 8 : ℝ) ≤
        (E * q ^ (3 / 2 : ℝ)) ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow harg0 harg (by norm_num)
  have hlog :
      Real.log (1 + 3 / spectralBoundarySeparation n) ≤
        8 * (E ^ (1 / 8 : ℝ) * q ^ (3 / 16 : ℝ)) := by
    calc
      Real.log (1 + 3 / spectralBoundarySeparation n) ≤
          (1 + 3 / spectralBoundarySeparation n) ^ (1 / 8 : ℝ) /
            (1 / 8 : ℝ) :=
        Real.log_le_rpow_div harg0 (by norm_num)
      _ ≤ (E * q ^ (3 / 2 : ℝ)) ^ (1 / 8 : ℝ) /
            (1 / 8 : ℝ) :=
        div_le_div_of_nonneg_right hargPow (by norm_num)
      _ = 8 * (E ^ (1 / 8 : ℝ) * q ^ (3 / 16 : ℝ)) := by
        rw [Real.mul_rpow hE hqThreeNonneg,
          rpow_threeHalves_rpow_oneEighth hq.le]
        ring
  have hradial : 4 / R ≤ q ^ (3 / 16 : ℝ) := by
    have hfour : 4 / R ≤ 1 / q := by
      rw [div_le_div_iff₀ hR hq]
      simpa using hRlower
    have hinv : 1 / q ≤ 1 := (div_le_one hq).mpr hqone
    exact hfour.trans (hinv.trans
      (Real.one_le_rpow hqone (by norm_num)))
  have hcost :
      4 / R + 2 * Real.log (1 + 3 / spectralBoundarySeparation n) ≤
        (1 + 16 * E ^ (1 / 8 : ℝ)) * q ^ (3 / 16 : ℝ) := by
    calc
      4 / R + 2 * Real.log (1 + 3 / spectralBoundarySeparation n) ≤
          q ^ (3 / 16 : ℝ) +
            2 * (8 * (E ^ (1 / 8 : ℝ) * q ^ (3 / 16 : ℝ))) :=
        add_le_add hradial (mul_le_mul_of_nonneg_left hlog (by norm_num))
      _ = (1 + 16 * E ^ (1 / 8 : ℝ)) * q ^ (3 / 16 : ℝ) := by ring
  have hcount :
      A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2 ≤
        (A * (27 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
          q ^ (3 / 2 : ℝ) := by
    calc
      A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2 ≤
          A * ((27 : ℝ) ^ (3 / 2 : ℝ) * q ^ (3 / 2 : ℝ)) /
            Real.log 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left htwoRpow hA0) hlog2.le
      _ = (A * (27 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
          q ^ (3 / 2 : ℝ) := by ring
  have hcost0 : 0 ≤
      4 / R + 2 * Real.log (1 + 3 / spectralBoundarySeparation n) := by
    have hargOne : 1 ≤ 1 + 3 / spectralBoundarySeparation n := by
      have hδ := spectralBoundarySeparation_pos n
      have : 0 ≤ 3 / spectralBoundarySeparation n := by positivity
      linarith
    exact add_nonneg (by positivity)
      (mul_nonneg (by norm_num) (Real.log_nonneg hargOne))
  have hcanonical :
      (A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2) *
          (4 / R + 2 * Real.log
            (1 + 3 / spectralBoundarySeparation n)) ≤
        ((A * (27 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
          (1 + 16 * E ^ (1 / 8 : ℝ))) * q ^ (27 / 16 : ℝ) := by
    calc
      (A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2) *
          (4 / R + 2 * Real.log
            (1 + 3 / spectralBoundarySeparation n)) ≤
          ((A * (27 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
            q ^ (3 / 2 : ℝ)) *
          ((1 + 16 * E ^ (1 / 8 : ℝ)) *
            q ^ (3 / 16 : ℝ)) := by
        exact mul_le_mul hcount hcost hcost0 (by positivity)
      _ = ((A * (27 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
          (1 + 16 * E ^ (1 / 8 : ℝ))) * q ^ (27 / 16 : ℝ) := by
        rw [← rpow_threeHalves_mul_rpow_threeSixteenths hq]
        ring
  have hresidual :
      2 * ((2 * (B * (R + 1) ^ 2)) / (R / 4)) ≤
        784 * B * q := by
    have hR1sq : (R + 1) ^ 2 ≤ (14 * q) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr hRupper
    have hquot : (R + 1) ^ 2 / R ≤ (14 * q) ^ 2 / (4 * q) :=
      div_le_div₀ (sq_nonneg _) hR1sq (by positivity) hRlower
    calc
      2 * ((2 * (B * (R + 1) ^ 2)) / (R / 4)) =
          16 * B * ((R + 1) ^ 2 / R) := by
        field_simp [hR.ne']
        ring
      _ ≤ 16 * B * ((14 * q) ^ 2 / (4 * q)) :=
        mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = 784 * B * q := by
        field_simp [hq.ne']
        ring
  have hqTotal : q ≤ q ^ (27 / 16 : ℝ) := by
    calc
      q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
      _ ≤ q ^ (27 / 16 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hqone (by norm_num)
  have hL1 :
      2 * ((2 * (B * (R + 1) ^ 2)) / (R / 4)) +
          (A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2) *
            (4 / R + 2 * Real.log
              (1 + 3 / spectralBoundarySeparation n)) ≤
        K * q ^ (27 / 16 : ℝ) := by
    calc
      2 * ((2 * (B * (R + 1) ^ 2)) / (R / 4)) +
          (A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2) *
            (4 / R + 2 * Real.log
              (1 + 3 / spectralBoundarySeparation n)) ≤
          784 * B * q +
            ((A * (27 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
              (1 + 16 * E ^ (1 / 8 : ℝ))) *
                q ^ (27 / 16 : ℝ) :=
        add_le_add hresidual hcanonical
      _ ≤ 784 * B * q ^ (27 / 16 : ℝ) +
            ((A * (27 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
              (1 + 16 * E ^ (1 / 8 : ℝ))) *
                q ^ (27 / 16 : ℝ) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hqTotal (by positivity)) le_rfl
      _ = K * q ^ (27 / 16 : ℝ) := by
        dsimp [K, E, suzukiXiWeilVerticalL1AsymptoticConstant]
        ring
  have hL10 : 0 ≤
      2 * ((2 * (B * (R + 1) ^ 2)) / (R / 4)) +
        (A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2) *
          (4 / R + 2 * Real.log
            (1 + 3 / spectralBoundarySeparation n)) := by
    exact add_nonneg (by positivity)
      (mul_nonneg (by positivity) hcost0)
  have hK : 0 ≤ K := by
    dsimp [K, suzukiXiWeilVerticalL1AsymptoticConstant]
    positivity
  have hTsq : (q / 2) ^ 2 ≤ T ^ 2 :=
    (sq_le_sq₀ (by positivity) hT.le).mpr hTlower
  have hTinv : 1 / T ^ 2 ≤ 4 / q ^ 2 := by
    calc
      1 / T ^ 2 ≤ 1 / (q / 2) ^ 2 :=
        one_div_le_one_div_of_le (sq_pos_of_pos (by positivity)) hTsq
      _ = 4 / q ^ 2 := by
        field_simp [hq.ne']
        ring
  have hM :
      2 * (Real.exp |t| + 1) / T ^ 2 ≤
        8 * (Real.exp |t| + 1) / q ^ 2 := by
    calc
      2 * (Real.exp |t| + 1) / T ^ 2 =
          (2 * (Real.exp |t| + 1)) * (1 / T ^ 2) := by ring
      _ ≤ (2 * (Real.exp |t| + 1)) * (4 / q ^ 2) :=
        mul_le_mul_of_nonneg_left hTinv (by positivity)
      _ = 8 * (Real.exp |t| + 1) / q ^ 2 := by ring
  unfold suzukiXiWeilVerticalExplicitMajorant
  change
    2 * ((2 * (Real.exp |t| + 1) / T ^ 2) *
      (2 * ((2 * (B * (R + 1) ^ 2)) / (R / 4)) +
        (A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2) *
          (4 / R + 2 * Real.log
            (1 + 3 / spectralBoundarySeparation n)))) ≤ _
  calc
    2 * ((2 * (Real.exp |t| + 1) / T ^ 2) *
      (2 * ((2 * (B * (R + 1) ^ 2)) / (R / 4)) +
        (A * (2 * R + 1) ^ (3 / 2 : ℝ) / Real.log 2) *
          (4 / R + 2 * Real.log
            (1 + 3 / spectralBoundarySeparation n)))) ≤
        2 * ((8 * (Real.exp |t| + 1) / q ^ 2) *
          (K * q ^ (27 / 16 : ℝ))) := by
      gcongr
    _ = suzukiXiWeilVerticalAsymptoticConstant A B t *
        q ^ (-(5 / 16 : ℝ)) := by
      rw [show
        2 * ((8 * (Real.exp |t| + 1) / q ^ 2) *
          (K * q ^ (27 / 16 : ℝ))) =
            (16 * (Real.exp |t| + 1) * K) *
              (q ^ (27 / 16 : ℝ) / q ^ 2) by ring,
        rpow_twentySevenSixteenths_div_sq hq]
      rfl

/-- The explicit majorant is nonnegative whenever its two growth constants
are nonnegative. -/
lemma suzukiXiWeilVerticalExplicitMajorant_nonneg
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (t : ℝ) (n : ℕ) :
    0 ≤ suzukiXiWeilVerticalExplicitMajorant A B t n := by
  have hT : 0 < quantitativeSpectralBoundaryTruncation n :=
    (Nat.cast_nonneg n).trans_lt
      (quantitativeSpectralBoundaryTruncation_spec n).1
  have hR : 0 < xiCanonicalRadius n := xiCanonicalRadius_pos n
  have hsep : 0 < spectralBoundarySeparation n :=
    spectralBoundarySeparation_pos n
  have harg : 1 ≤ 1 + 3 / spectralBoundarySeparation n := by
    have hfrac : 0 ≤ 3 / spectralBoundarySeparation n := by positivity
    linarith
  have hlog : 0 ≤ Real.log (1 + 3 / spectralBoundarySeparation n) :=
    Real.log_nonneg harg
  unfold suzukiXiWeilVerticalExplicitMajorant
  positivity

/-- The complete explicit vertical majorant tends to zero.  This is the
real-asymptotic closure of the `5/16` decay margin. -/
theorem tendsto_suzukiXiWeilVerticalExplicitMajorant_zero
    {A B : ℝ} (hA : 1 ≤ A)
    (hThreeHalves : ∀ w : ℂ,
      ‖riemannXi w‖ ≤
        Real.exp (A * (‖w‖ + 1) ^ (3 / 2 : ℝ)))
    (hB : 1 ≤ B) (t : ℝ) :
    Tendsto (fun n : ℕ ↦
      suzukiXiWeilVerticalExplicitMajorant A B t n)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      suzukiXiWeilVerticalExplicitMajorant_nonneg
        (by linarith) (by linarith) t n
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact suzukiXiWeilVerticalExplicitMajorant_le_rpow
      hA hThreeHalves hB t n hn
  · have hbase : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1)
        atTop atTop :=
      tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have hpower : Tendsto
        (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-(5 / 16 : ℝ)))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 16)).comp
        hbase
    have hconstant : Tendsto
        (fun n : ℕ ↦ suzukiXiWeilVerticalAsymptoticConstant A B t *
          ((n : ℝ) + 1) ^ (-(5 / 16 : ℝ)))
        atTop
        (nhds (suzukiXiWeilVerticalAsymptoticConstant A B t * 0)) :=
      tendsto_const_nhds.mul hpower
    simpa using hconstant

/-- Along the quantitatively separated truncation sequence, the literal
two-sided Suzuki--Weil vertical boundary tends to zero for every fixed
proper time and evaluation point. -/
theorem tendsto_suzukiXiWeilVerticalBoundaryIntegral_quantitative
    (t : ℝ) (z : ℂ) :
    Tendsto (fun n : ℕ ↦
      suzukiXiWeilVerticalBoundaryIntegral t z
        (quantitativeSpectralBoundaryTruncation n))
      atTop (nhds 0) := by
  rcases riemannXi_threeHalvesGrowth with ⟨A, hA, hThreeHalves⟩
  rcases riemannXi_quadraticGrowth with ⟨B, hB, hQuadratic⟩
  apply squeeze_zero_norm'
  · filter_upwards
      [tendsto_quantitativeSpectralBoundaryTruncation_atTop.eventually
        (eventually_ge_atTop (2 * |z.re|))] with n hn
    simpa [suzukiXiWeilVerticalExplicitMajorant] using
      norm_suzukiXiWeilVerticalBoundaryIntegral_quantitative_le_of_growth
        hA hThreeHalves hB hQuadratic t z n hn
  · exact tendsto_suzukiXiWeilVerticalExplicitMajorant_zero
      hA hThreeHalves hB t

/-- The arithmetic and spectral positive-proper-time Suzuki functions agree
above height one.  All horizontal and vertical contour limits in this
meeting theorem are now discharged. -/
theorem riemannXiSuzukiArithmeticPPositive_eq_spectral
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 1 < z.im) :
    riemannXiSuzukiArithmeticPPositive t z =
      riemannXiSuzukiSpectralP t z := by
  exact
    riemannXiSuzukiArithmeticPPositive_eq_spectral_of_quantitative_vertical_limit
      ht hz (tendsto_suzukiXiWeilVerticalBoundaryIntegral_quantitative t z)

/-- Analytic continuation extends the contour identity from `Im z > 1` to
Suzuki's complete safe half-plane `Im z > 1/2`. -/
theorem riemannXiSuzukiArithmeticPPositive_eq_spectral_safe
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    riemannXiSuzukiArithmeticPPositive t z =
      riemannXiSuzukiSpectralP t z := by
  have hspectral : AnalyticOnNhd ℂ (riemannXiSuzukiSpectralP t)
      suzukiXiSafeUpperHalfPlane :=
    (differentiableOn_riemannXiSuzukiSpectralP t).analyticOnNhd
      isOpen_suzukiXiSafeUpperHalfPlane
  have hpreconnected : IsPreconnected suzukiXiSafeUpperHalfPlane := by
    simpa [suzukiXiSafeUpperHalfPlane] using
      (convex_halfSpace_im_gt (1 / 2 : ℝ)).isPreconnected
  have htwo : (2 * Complex.I : ℂ) ∈ suzukiXiSafeUpperHalfPlane := by
    simp [suzukiXiSafeUpperHalfPlane]
    norm_num
  have hlocal : Filter.EventuallyEq (nhds (2 * Complex.I))
      (riemannXiSuzukiArithmeticPPositive t)
      (riemannXiSuzukiSpectralP t) :=
    eventuallyEq_of_mem
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
        (by norm_num : (1 : ℝ) < (2 * Complex.I : ℂ).im))
      (fun w hw ↦
        riemannXiSuzukiArithmeticPPositive_eq_spectral ht hw)
  exact
    (analyticOnNhd_riemannXiSuzukiArithmeticPPositive ht).eqOn_of_preconnected_of_eventuallyEq
      hspectral hpreconnected htwo hlocal hz

end

end RiemannGaussian
