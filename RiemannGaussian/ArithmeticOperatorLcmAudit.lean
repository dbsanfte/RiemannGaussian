/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit

/-!
# Logarithmic LCM conditional-negativity gate

The actual integer LCM/logarithm identity is retained, but its zero-mean
quadratic is exactly the negative GCD incidence Gram. Its conditional
sign follows for every nonnegative divisor weight. Cancelling a strictly
positive real density deletes all column amplitudes, hence every source.
This does not rule out nonlinear LCM pair kernels or signed density
comparisons with genuinely additional integer-prime input.
-/

namespace RiemannGaussian.ArithmeticOperatorLcmAudit
noncomputable section
open ArithmeticOperatorKummerCutoff ArithmeticOperatorGcdAudit ArithmeticOperatorGramAudit
open scoped BigOperators ComplexConjugate

/-- The logarithmic join kernel with an arbitrary divisor measure.
At actual Mangoldt weights it is exactly log(lcm), on positive integers. -/
def joinKernel (w : ℕ → ℂ) (m n : ℕ) : ℂ :=
  divisorObservation w m+divisorObservation w n-gcdKernel w m n

/-- Full finite conditional quadratic; neither incidence is discarded. -/
def joinQuadratic (X : ℕ) (alpha w : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
    alpha m*conj (alpha n)*joinKernel w m n

/-- Genuine integer product/GCD compatibility, including the logarithms
of all prime-power factors of the two labels. -/
theorem log_lcm_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Real.log (Nat.lcm m n : ℝ) =
      Real.log m+Real.log n-Real.log (Nat.gcd m n) := by
  have he := congrArg (fun a : ℕ => Real.log (a : ℝ)) (Nat.gcd_mul_lcm m n)
  have hg : (Nat.gcd m n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left n hm).ne'
  have hl : (Nat.lcm m n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_pos hm hn).ne'
  simp only [Nat.cast_mul] at he
  rw [Real.log_mul hg hl,Real.log_mul (by exact_mod_cast hm.ne')
    (by exact_mod_cast hn.ne')] at he
  linarith

/-- The actual-prime specialization is the literal LCM kernel, rather
than a declaration that arbitrary weights reproduce log(lcm). -/
theorem joinKernel_mangoldt {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    joinKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) m n =
      (Real.log (Nat.lcm m n : ℝ) : ℂ) := by
  rw [joinKernel,divisorObservation_vonMangoldt,divisorObservation_vonMangoldt,
    gcdKernel_mangoldt,log_lcm_eq hm hn]
  push_cast
  ring

/-- Zero-mean row coefficients remove the two rank-one contributions
exactly. All remaining signed arithmetic is the same GCD Gram. -/
theorem joinQuadratic_zero_mean {X : ℕ} {alpha : ℕ → ℂ}
    (ha : ∑ m ∈ Finset.Icc 1 X, alpha m = 0) (w : ℕ → ℂ) :
    joinQuadratic X alpha w = -gcdQuadratic X alpha w := by
  unfold joinQuadratic joinKernel gcdQuadratic
  have he (m : ℕ) :
      (∑ n ∈ Finset.Icc 1 X,
        alpha m*conj (alpha n)*
          (divisorObservation w m+divisorObservation w n-gcdKernel w m n)) =
      (alpha m*divisorObservation w m)*(conj (∑ n ∈ Finset.Icc 1 X, alpha n))+
        alpha m*(∑ n ∈ Finset.Icc 1 X, conj (alpha n)*divisorObservation w n)-
        ∑ n ∈ Finset.Icc 1 X, alpha m*conj (alpha n)*gcdKernel w m n := by
    simp only [map_sum,Finset.mul_sum]
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp_rw [he,ha,map_zero,mul_zero,zero_add]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul,ha,zero_mul,zero_sub]

/-- The familiar logarithmic-LCM conditional sign has a free-weight
proof and is not an extra inequality excluding positive countermeasures. -/
theorem joinQuadratic_nonpositive {X : ℕ} {alpha : ℕ → ℂ}
    (ha : ∑ m ∈ Finset.Icc 1 X, alpha m = 0) (w : ℕ → ℝ)
    (hw : ∀ d ∈ Finset.Icc 1 X, 0 ≤ w d) :
    (joinQuadratic X alpha (fun d => (w d : ℂ))).re ≤ 0 := by
  rw [joinQuadratic_zero_mean ha,Complex.neg_re]
  linarith [gcdQuadratic_nonnegative X alpha w hw]

/-- Its exact positive-real-density centering is source-blind as well.
This does not assert positivity of the complex twisted pole density. -/
theorem joinQuadratic_density_cancellation_kills_source {X : ℕ}
    {alpha : ℕ → ℂ} (ha : ∑ m ∈ Finset.Icc 1 X, alpha m = 0)
    (density : ℕ → ℝ) (hdensity : ∀ d ∈ Finset.Icc 1 X, 0 < density d)
    (hpole : (joinQuadratic X alpha (fun d => (density d : ℂ))).re = 0)
    (source : ℕ → ℂ) : joinQuadratic X alpha source = 0 := by
  rw [joinQuadratic_zero_mean ha,Complex.neg_re] at hpole
  have hg : (gcdQuadratic X alpha (fun d => (density d : ℂ))).re = 0 := by linarith
  rw [joinQuadratic_zero_mean ha,
    gcdQuadratic_density_cancellation_kills_source X alpha density hdensity hg source,neg_zero]

end
end RiemannGaussian.ArithmeticOperatorLcmAudit
