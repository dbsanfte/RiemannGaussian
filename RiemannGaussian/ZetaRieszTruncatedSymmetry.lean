/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeRieszWindows

/-!
# The exact truncated Selberg--Vaughan symmetry of the Riesz hinge

The convolution defect has a constant interior and an explicit compact
cutoff transition. Both remain inside the signed Mobius--von Mangoldt
sum. No estimate for that sum is inferred from positivity of the kernel.
-/

namespace RiemannGaussian.ZetaRieszTruncatedSymmetry
noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius

/-- The full three-cutoff defect of the positive-part hinge. -/
def defect (L x y : ℝ) : ℝ :=
  max 0 (L-x-y)-max 0 (L-x)-max 0 (L-y)

/-- The transition is exactly a clipped overlap, with its constant
interior retained. Taking only the overlap changes the carrier. -/
theorem defect_eq_overlap {L x y : ℝ} (hL : 0 ≤ L) :
    defect L x y = -L + ZetaSquarefreeRieszWindows.primePairTent x y L := by
  simp only [defect, ZetaSquarefreeRieszWindows.primePairTent, max_eq_right hL]
  ring

/-- The literal truncated convolution identity, with its prime-power
endpoint correction. It is valid for every integer, including zero. -/
theorem log_mul_riesz_eq_convolution (L : ℝ) (n : ℕ) :
    -Real.log n*VaughanLogAverage.riesz L n =
      (∑ d ∈ n.divisors, ∑ ab ∈ d.divisorsAntidiagonal,
        (μ ab.1 : ℝ)*ArithmeticFunction.vonMangoldt ab.2*
          defect L (Real.log ab.1) (Real.log ab.2)) +
        ArithmeticFunction.vonMangoldt n*max 0 (L-Real.log n) := by
  have h := VaughanLogAverage.sum_profile_eq (fun a => max 0 (L-Real.log a)) n
  have he : (∑ d ∈ n.divisors, ∑ ab ∈ d.divisorsAntidiagonal,
      (μ ab.1 : ℝ)*ArithmeticFunction.vonMangoldt ab.2*
        (max 0 (L-Real.log d)-max 0 (L-Real.log ab.1)-max 0 (L-Real.log ab.2))) =
      ∑ d ∈ n.divisors, ∑ ab ∈ d.divisorsAntidiagonal,
        (μ ab.1 : ℝ)*ArithmeticFunction.vonMangoldt ab.2*
          defect L (Real.log ab.1) (Real.log ab.2) := by
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro ab hab
    obtain ⟨ha,hb⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hab
    have hl : Real.log d = Real.log ab.1+Real.log ab.2 := by
      rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, Nat.cast_mul,
        Real.log_mul (by exact_mod_cast ha) (by exact_mod_cast hb)]
    simp only [hl, defect, sub_sub]
  rw [he] at h
  change _ = -Real.log n*VaughanLogAverage.riesz L n - _ at h
  linear_combination -h

/-- On the actual squarefree composite support the prime-power
correction vanishes exactly; the complete signed convolution remains. -/
theorem squarefree_composite_identity (L : ℝ) {n : ℕ} (hn : Squarefree n) (hp : ¬n.Prime) :
    -Real.log n*VaughanLogAverage.riesz L n =
      ∑ d ∈ n.divisors, ∑ ab ∈ d.divisorsAntidiagonal,
        (μ ab.1 : ℝ)*ArithmeticFunction.vonMangoldt ab.2*
          defect L (Real.log ab.1) (Real.log ab.2) := by
  have hz : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (fun h =>
      hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hn,h⟩))
  simpa only [hz, zero_mul, add_zero] using log_mul_riesz_eq_convolution L n

/-- The constant interior collapses to its prime-power endpoint. -/
theorem sum_interior (n : ℕ) :
    (∑ d ∈ n.divisors, ∑ ab ∈ d.divisorsAntidiagonal,
      (μ ab.1 : ℝ)*ArithmeticFunction.vonMangoldt ab.2) =
        ArithmeticFunction.vonMangoldt n := by
  have h : ((μ : ArithmeticFunction ℝ)*ArithmeticFunction.vonMangoldt)*
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = ArithmeticFunction.vonMangoldt := by
    rw [mul_right_comm, ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n) h
  rw [ArithmeticFunction.coe_mul_zeta_apply] at he
  simpa only [ArithmeticFunction.mul_apply,
    ArithmeticFunction.intCoe_apply] using he

/-- The compact overlap form has no constant interior on squarefree
composites. The Mobius sign and every factor constraint remain coupled. -/
theorem squarefree_composite_overlap {L : ℝ} (hL : 0 ≤ L) {n : ℕ}
    (hn : Squarefree n) (hp : ¬n.Prime) :
    -Real.log n*VaughanLogAverage.riesz L n =
      ∑ d ∈ n.divisors, ∑ ab ∈ d.divisorsAntidiagonal,
        (μ ab.1 : ℝ)*ArithmeticFunction.vonMangoldt ab.2*
          ZetaSquarefreeRieszWindows.primePairTent (Real.log ab.1) (Real.log ab.2) L := by
  rw [squarefree_composite_identity L hn hp]
  simp_rw [defect_eq_overlap hL, mul_add, Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul]
  rw [sum_interior]
  have hz : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (fun h =>
      hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hn,h⟩))
  simp only [hz, zero_mul, zero_add]

end
end RiemannGaussian.ZetaRieszTruncatedSymmetry
