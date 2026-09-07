import RiemannGaussian.EtaMoebiusQuotientShells
import RiemannGaussian.EtaMoebiusParityRecurrence

/-!
# Exact parity recurrence inside complete quotient shells

The original term-level parity relation survives restriction to any
complete quotient fibre. Even divisors become odd divisors at the halved
physical cutoff, with the same quotient index. The actual shell cutoff
is kept fixed across the two scales: it is still selected by the original
physical cutoff, rather than recomputed after halving.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The odd-divisor part of one complete quotient block, retaining the original completed terms. -/
def pairedEtaCompletedMoebiusOddQuotientBlock (rho : NontrivialZetaZero) (M q : ℕ) : ℂ :=
  ∑ d ∈ (Finset.Icc 1 M).filter (fun d ↦ Odd d ∧ M / d = q), pairedEtaCompletedMoebiusTerm rho M d

/-- The even part of a complete quotient fibre equals the odd part of the same quotient fibre at half the physical cutoff, with its exact complex multiplier. -/
theorem sum_even_pairedEtaCompletedMoebiusQuotientBlock_eq_half_odd
    (rho : NontrivialZetaZero) (M q : ℕ) :
    (∑ d ∈ (Finset.Icc 1 M).filter (fun d ↦ Even d ∧ M / d = q), pairedEtaCompletedMoebiusTerm rho M d) =
      -(2 : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusOddQuotientBlock rho (M / 2) q := by
  have hfilter : (Finset.Icc 1 M).filter (fun d ↦ Even d ∧ M / d = q) =
      ((Finset.Icc 1 M).filter Even).filter (fun d ↦ M / d = q) := by
    ext d
    simp only [Finset.mem_filter, and_assoc]
  rw [hfilter, Finset.sum_filter,
    sum_even_Icc_eq_sum_half M (fun d ↦ if M / d = q then pairedEtaCompletedMoebiusTerm rho M d else 0)]
  simp only [← Nat.div_div_eq_div_mul, pairedEtaCompletedMoebiusTerm_two_mul,
    pairedEtaCompletedMoebiusOddQuotientBlock, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp_all

/-- Every complete quotient block is the odd block minus its dyadically shifted odd block; no clipped arithmetic endpoint is introduced. -/
theorem pairedEtaCompletedMoebiusQuotientBlock_eq_odd_sub_half
    (rho : NontrivialZetaZero) (M q : ℕ) :
    pairedEtaCompletedMoebiusQuotientBlock rho M q =
      pairedEtaCompletedMoebiusOddQuotientBlock rho M q -
        (2 : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusOddQuotientBlock rho (M / 2) q := by
  have h := Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 M).filter (fun d ↦ M / d = q))
    Odd (pairedEtaCompletedMoebiusTerm rho M)
  have ho : ((Finset.Icc 1 M).filter (fun d ↦ M / d = q)).filter Odd =
      (Finset.Icc 1 M).filter (fun d ↦ Odd d ∧ M / d = q) := by
    ext d
    simp only [Finset.mem_filter]
    tauto
  have he : ((Finset.Icc 1 M).filter (fun d ↦ M / d = q)).filter (fun d ↦ ¬Odd d) =
      (Finset.Icc 1 M).filter (fun d ↦ Even d ∧ M / d = q) := by
    ext d
    simp only [Finset.mem_filter, Nat.not_odd_iff_even]
    tauto
  rw [ho, he, sum_even_pairedEtaCompletedMoebiusQuotientBlock_eq_half_odd,
    sum_pairedEtaCompletedMoebiusTerm_eq_quotientBlock] at h
  simpa only [pairedEtaCompletedMoebiusOddQuotientBlock, neg_mul, ← sub_eq_add_neg] using h.symm

/-- A dyadic shell of odd complete quotient blocks, with its quotient cap specified independently of the physical cutoff. -/
def pairedEtaCompletedMoebiusOddQuotientShell (rho : NontrivialZetaZero) (Q M j : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)),
    if q ≤ Q then pairedEtaCompletedMoebiusOddQuotientBlock rho M q else 0

/-- The exact shell-level parity recurrence keeps the original moving quotient cap on both physical scales. Recomputing the cap after halving would change the carrier. -/
theorem pairedEtaCompletedMoebiusQuotientShell_eq_odd_sub_half
    (rho : NontrivialZetaZero) (D M j : ℕ) :
    pairedEtaCompletedMoebiusQuotientShell rho D M j =
      pairedEtaCompletedMoebiusOddQuotientShell rho (M / (D + 1)) M j -
        (2 : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusOddQuotientShell rho (M / (D + 1)) (M / 2) j := by
  unfold pairedEtaCompletedMoebiusQuotientShell pairedEtaCompletedMoebiusLargeQuotientFamily
    pairedEtaCompletedMoebiusOddQuotientShell
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q ≤ M / (D + 1)
  · simp only [if_pos hq, pairedEtaCompletedMoebiusQuotientBlock_eq_odd_sub_half]
  · simp only [if_neg hq, mul_zero, sub_zero]

/-- The odd quotient prefix retains all of its complete fibres. -/
def pairedEtaCompletedMoebiusOddQuotientAggregate (rho : NontrivialZetaZero) (Q M : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, pairedEtaCompletedMoebiusOddQuotientBlock rho M q

/-- The whole surviving complete-block carrier has the same exact two-scale parity recurrence as its individual shells. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_odd_sub_half
    (rho : NontrivialZetaZero) (M D : ℕ) :
    pairedEtaCompletedMoebiusCompleteQuotientAggregate rho M D =
      pairedEtaCompletedMoebiusOddQuotientAggregate rho (M / (D + 1)) M -
        (2 : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusOddQuotientAggregate rho (M / (D + 1)) (M / 2) := by
  simp only [pairedEtaCompletedMoebiusCompleteQuotientAggregate,
    pairedEtaCompletedMoebiusOddQuotientAggregate, pairedEtaCompletedMoebiusQuotientBlock_eq_odd_sub_half,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

end

end RiemannGaussian
