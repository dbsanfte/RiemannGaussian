/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldEulerConstant

/-!
# Sharp constants for the higher reciprocal zero masses

Two positive atanh terms give a rational logarithm lower bound. It proves
monotonicity of the twice-corrected harmonic upper sequence, allowing exact
finite arithmetic at order 200 to bound Euler's constant. The same bound
and the proved rational enclosure of pi control its logarithm.
-/

open Real
namespace RiemannGaussian.RosserSchoenfeldSharpConstants
noncomputable section
set_option maxRecDepth 20000

/-- Difference from the first two positive atanh terms. -/
private def gap (x : ℝ) : ℝ :=
  log (1 + x) - (2 * (x / (x + 2)) + (2 / 3) * (x / (x + 2))^3)

/-- The exact derivative is nonnegative on the nonnegative real axis. -/
private theorem gap_deriv {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt gap (x^4 / ((1 + x) * (x + 2)^4)) x := by
  have hp : 1 + x ≠ 0 := by positivity
  have hq : x + 2 ≠ 0 := by positivity
  have hl := ((hasDerivAt_const x 1).add (hasDerivAt_id x)).log hp
  have hg := (hasDerivAt_id x).div ((hasDerivAt_id x).add_const 2) hq
  convert hl.sub ((hg.const_mul 2).add ((hg.pow 3).const_mul (2 / 3))) using 1 <;>
    norm_num [gap] <;> first | rfl | (field_simp; ring)

/-- A cubic rational lower bound for the actual logarithm. -/
theorem log_cubic_lower {x : ℝ} (hx : 0 ≤ x) :
    2 * (x / (x + 2)) + (2 / 3) * (x / (x + 2))^3 ≤ log (1 + x) := by
  have hm : MonotoneOn gap (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t ht => (gap_deriv ht).continuousAt.continuousWithinAt
    · exact fun t ht => (gap_deriv (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(gap_deriv (interior_subset ht)).deriv]
      have ht0 : 0 ≤ t := interior_subset ht
      positivity
  have hh := hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx hx
  simpa [gap] using hh

/-- The harmonic upper sequence with its first two Euler corrections. -/
private def sharp (n : ℕ) : ℝ :=
  Real.eulerMascheroniSeq' (n+1) - 1 / (2 * ((n : ℝ)+1)) +
    1 / (12 * ((n : ℝ)+1)^2)

/-- The cubic logarithm bound pays the corrected harmonic step. -/
private lemma sharp_cell {a : ℝ} (ha : 0 < a) :
    1 / (a+1) + 1/(2*a) - 1/(2*(a+1)) - 1/(12*a^2) + 1/(12*(a+1)^2) ≤
      Real.log (a+1) - Real.log a := by
  have hh := log_cubic_lower (show 0 ≤ 1/a by positivity)
  rw [show 1+1/a=(a+1)/a by field_simp, Real.log_div (by positivity) ha.ne'] at hh
  refine le_trans ?_ hh
  have he : (1/a)/(1/a+2)=1/(2*a+1) := by field_simp; ring
  rw [he]
  have h1 : 0 < a+1 := by positivity
  have h2 : 0 < 2*a+1 := by positivity
  field_simp
  nlinarith [sq_nonneg a]

/-- The twice-corrected harmonic sequence decreases. -/
private lemma sharp_antitone : Antitone sharp := by
  apply antitone_nat_of_succ_le
  intro n
  have hh := sharp_cell (show 0 < (n : ℝ)+1 by positivity)
  simp only [sharp, Real.eulerMascheroniSeq', Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte]
  rw [harmonic_succ (n+1)]
  push_cast
  simp only [one_div] at *
  linarith

/-- Both corrections vanish, preserving the actual Euler constant. -/
private theorem sharp_tendsto : Filter.Tendsto sharp Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have hs := Real.tendsto_eulerMascheroniSeq'.comp (Filter.tendsto_add_atTop_nat 1)
  have hx : Filter.Tendsto (fun n : ℕ => (n : ℝ)+1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
  have hi : Filter.Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hx
  have h1 := hi.div_const 2
  have h2 := (hi.pow 2).div_const 12
  convert (hs.sub h1).add h2 using 1
  · ext n
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    dsimp [sharp]
    field_simp
  · norm_num

/-- A checked nine-decimal upper bound for Euler's constant. -/
theorem euler_upper : Real.eulerMascheroniConstant < (577215666 / 10^9 : ℝ) := by
  have hb := sharp_antitone.le_of_tendsto sharp_tendsto 199
  have he : sharp 199 = (harmonic 200 : ℝ) - Real.log 200 - 1/400 + 1/480000 := by
    norm_num [sharp, Real.eulerMascheroniSeq']
  rw [he] at hb
  have hlog : Real.log (200 : ℝ) = 3 * Real.log 2 + 2 * Real.log 5 := by
    rw [show (200 : ℝ) = 2^3*5^2 by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  rw [hlog] at hb
  have hh : (harmonic 200 : ℝ) < (5878030948122 / 10^12 : ℝ) := by
    set_option maxRecDepth 10000 in norm_num
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

/-- A checked nine-decimal lower bound for the logarithm of pi. -/
theorem log_pi_lower : (1144729883 / 10^9 : ℝ) < Real.log Real.pi := by
  have hh := log_cubic_lower
    (show (0 : ℝ) ≤ (314159265358979323846/10^20)/3-1 by norm_num)
  have he : Real.log (314159265358979323846/10^20 : ℝ) = Real.log 3 +
      Real.log (1+((314159265358979323846/10^20 : ℝ)/3-1)) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have hp : Real.log (314159265358979323846/10^20 : ℝ) < Real.log Real.pi :=
    Real.log_lt_log (by norm_num) (by convert Real.pi_gt_d20 using 1; norm_num)
  rw [he] at hp
  norm_num at hh
  linarith [Real.log_three_gt_d9]

end
end RiemannGaussian.RosserSchoenfeldSharpConstants
