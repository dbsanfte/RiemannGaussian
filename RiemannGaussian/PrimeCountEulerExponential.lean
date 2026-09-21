/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.PrimeCountEuler
import RiemannGaussian.PrimeNewtonThree
import RiemannGaussian.DirichletDyadicBlocks
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The convergent exponential formula for the signed prime-count series

The prime sum and the power sum may be exchanged only after absolute
summability has been proved. This is an Euler-half-plane identity, not an
analyticity assertion across the hypothetical zero.
-/

namespace RiemannGaussian.PrimeCountEuler
noncomputable section
open scoped BigOperators Classical
open PrimeNewtonThree

theorem primeAtom_norm_le_half {s : ℂ} (hs : 1<s.re) (p : ℕ) :
    ‖primeAtom s p‖ ≤ (1/2 : ℝ) := by
  by_cases hp : p.Prime
  · rw [primeAtom, if_pos hp, norm_zetaPrimeFeature, zetaPrimeExpWeight]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hl := Real.log_le_log (by norm_num : (0 : ℝ)<2) hp2
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr
        (by nlinarith [Real.log_pos (by norm_num : (1 : ℝ)<2)])
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  · simp [primeAtom, hp]

private theorem summable_logPowers {f : ℕ → ℂ} (hf : Summable f)
    (hb : ∀ p, ‖f p‖ ≤ (1/2 : ℝ)) :
    Summable (fun v : ℕ × ℕ => f v.2^(v.1+1)/((v.1+1 : ℕ) : ℂ)) := by
  have hg : Summable (fun r : ℕ => (1/2 : ℝ)^r) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hmajor : Summable (fun v : ℕ × ℕ => (1/2 : ℝ)^v.1*‖f v.2‖) :=
    summable_mul_of_summable_norm hg.norm hf.norm.norm
  apply hmajor.of_norm_bounded
  rintro ⟨r,p⟩
  rw [norm_div, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ ‖f p‖^(r+1) := div_le_self (by positivity) (by exact_mod_cast Nat.le_add_left 1 r)
    _ = ‖f p‖^r*‖f p‖ := pow_succ _ _
    _ ≤ (1/2 : ℝ)^r*‖f p‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb p) _) (norm_nonneg _)

/-- The two complete sums have an absolutely summable joint majorant. -/
theorem generating_eq_exp_primeSeries {z s : ℂ} (hz : ‖z‖ ≤ 1) (hs : 1<s.re) :
    generating z s = Complex.exp
      (-(∑' r : ℕ, z^(r+1)*primeSeries (((r+1 : ℕ) : ℂ)*s)/((r+1 : ℕ) : ℂ))) := by
  let f : ℕ → ℂ := fun p => z*primeAtom s p
  have hf : Summable f := (summable_primeAtom hs).mul_left z
  have hb (p : ℕ) : ‖f p‖ ≤ (1/2 : ℝ) := by
    dsimp only [f]
    rw [norm_mul]
    exact (mul_le_mul hz (primeAtom_norm_le_half hs p) (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul _)
  have hpowers := summable_logPowers hf hb
  have hlogs : Summable (fun p => Complex.log (1-f p)) := by
    simpa only [sub_eq_add_neg] using Complex.summable_log_one_add_of_summable hf.neg
  have he : (∑' r : ℕ, z^(r+1)*primeSeries (((r+1 : ℕ) : ℂ)*s)/((r+1 : ℕ) : ℂ)) =
      -(∑' p, Complex.log (1-f p)) := by
    calc
      _ = ∑' r : ℕ, ∑' p : ℕ, f p^(r+1)/((r+1 : ℕ) : ℂ) := by
        apply tsum_congr
        intro r
        have hterm (p : ℕ) : f p^(r+1)/((r+1 : ℕ) : ℂ) =
            z^(r+1)*primeAtom (((r+1 : ℕ) : ℂ)*s) p/((r+1 : ℕ) : ℂ) := by
          dsimp only [f]
          rw [mul_pow, primeAtom_pow s p (r+1) (Nat.succ_ne_zero r)]
        simp_rw [hterm]
        rw [tsum_div_const, tsum_mul_left]
        rfl
      _ = ∑' p : ℕ, ∑' r : ℕ, f p^(r+1)/((r+1 : ℕ) : ℂ) := by
        exact (Summable.tsum_comm (f := fun r p : ℕ => f p^(r+1)/((r+1 : ℕ) : ℂ)) hpowers).symm
      _ = _ := by
        have hsum (p : ℕ) : (∑' r : ℕ, f p^(r+1)/((r+1 : ℕ) : ℂ)) =
            -Complex.log (1-f p) := by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (Complex.hasSum_taylorSeries_neg_log' ((hb p).trans_lt (by norm_num))).tsum_eq
        simp only [hsum, tsum_neg]
  have hn (p : ℕ) : 1-f p ≠ 0 := by
    intro heq
    have hfp : f p = 1 := (sub_eq_zero.mp heq).symm
    have hh := hb p
    rw [hfp, norm_one] at hh
    norm_num at hh
  have hp := Complex.hasProd_of_hasSum_log hn hlogs.hasSum
  have hg : HasProd (fun p : ℕ => 1-f p) (generating z s) := by
    have hi := (hasProd_subtype_iff_mulIndicator (s := {p : ℕ | p.Prime})
      (f := fun p : ℕ => 1-z*(p : ℂ)^(-s))).mp (hasProd_generating hz hs)
    apply hi.congr_fun
    intro p
    by_cases hpp : p.Prime
    · simp only [Set.mulIndicator_apply, Set.mem_ofPred_eq, f, primeAtom, if_pos hpp,
        DirichletDyadicBlocks.feature_eq_cpow s hpp.pos]
    · simp [f, primeAtom, hpp]
  rw [he, neg_neg]
  exact hg.unique hp

end
end RiemannGaussian.PrimeCountEuler
