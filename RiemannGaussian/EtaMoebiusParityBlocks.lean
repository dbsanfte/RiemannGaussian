import RiemannGaussian.EtaMoebiusParityBound

/-!
# Uniform bounds for all four actual Möbius parity blocks

Each entry retains the full complex double sum over its growing pair of
divisor families. Factoring these finite sums connects the rich kernel
to the exact parity aggregates. Only then are the uniform norm bounds
applied, including both completion channels in the signed orientation.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The full physical divisor set for one parity: `true` selects odd
divisors and `false` selects even divisors. -/
def pairedEtaMoebiusParityIndices (M : ℕ) (p : Bool) : Finset ℕ :=
  if p then (Finset.Icc 1 M).filter Odd else (Finset.Icc 1 M).filter Even

/-- Both exact completed parity aggregates in a common two-channel
interface, with their original physical cutoff. -/
def pairedEtaCompletedMoebiusParityAggregate (rho : NontrivialZetaZero)
    (M : ℕ) (p : Bool) : ℂ :=
  if p then pairedEtaCompletedMoebiusOddAggregate rho M
  else pairedEtaCompletedMoebiusEvenAggregate rho M

/-- The parity interface is exactly the original finite arithmetic sum. -/
theorem pairedEtaCompletedMoebiusParityAggregate_eq_sum (rho : NontrivialZetaZero)
    (M : ℕ) (p : Bool) :
    pairedEtaCompletedMoebiusParityAggregate rho M p =
      ∑ d ∈ pairedEtaMoebiusParityIndices M p, pairedEtaCompletedMoebiusTerm rho M d := by
  cases p <;> rfl

/-- The cutoff-independent bound for each parity, retaining the extra
dyadic factor of the even contribution. -/
def pairedEtaCompletedMoebiusParityBound (rho : NontrivialZetaZero) (p : Bool) : ℝ :=
  if p then pairedEtaCompletedMoebiusParityConstant rho
  else ‖(2 : ℂ) ^ (-rho.1)‖ * pairedEtaCompletedMoebiusParityConstant rho

/-- Both explicit parity bounds are nonnegative. -/
theorem pairedEtaCompletedMoebiusParityBound_nonneg (rho : NontrivialZetaZero) (p : Bool) :
    0 ≤ pairedEtaCompletedMoebiusParityBound rho p := by
  cases p
  · exact mul_nonneg (norm_nonneg _) (pairedEtaCompletedMoebiusParityConstant_nonneg rho)
  · exact pairedEtaCompletedMoebiusParityConstant_nonneg rho

/-- A uniform estimate for either entire growing parity family. -/
theorem norm_pairedEtaCompletedMoebiusParityAggregate_le (rho : NontrivialZetaZero)
    (M : ℕ) (p : Bool) :
    ‖pairedEtaCompletedMoebiusParityAggregate rho M p‖ ≤
      pairedEtaCompletedMoebiusParityBound rho p := by
  cases p
  · exact norm_pairedEtaCompletedMoebiusEvenAggregate_le rho M
  · exact norm_pairedEtaCompletedMoebiusOddAggregate_le rho M

/-- One complete quadratic parity block at the common physical cutoff.
Both divisor indices and every complex interaction are retained. -/
def pairedEtaCompletedMoebiusParityBlock (rho : NontrivialZetaZero)
    (M : ℕ) (p q : Bool) : ℂ :=
  ∑ d ∈ pairedEtaMoebiusParityIndices M p, ∑ e ∈ pairedEtaMoebiusParityIndices M q,
    pairedEtaCompletedMoebiusPairKernel rho M d e

/-- Exact factorization of every full complex parity block. This identity
precedes the norm estimate and includes the same-parity interactions. -/
theorem pairedEtaCompletedMoebiusParityBlock_eq_pair (rho : NontrivialZetaZero)
    (M : ℕ) (p q : Bool) :
    pairedEtaCompletedMoebiusParityBlock rho M p q =
      pairedEtaCompletedMoebiusParityAggregate rho M p *
        starRingEnd ℂ (pairedEtaCompletedMoebiusParityAggregate rho M q) := by
  simp only [pairedEtaCompletedMoebiusParityBlock, pairedEtaCompletedMoebiusPairKernel,
    pairedEtaCompletedMoebiusParityAggregate_eq_sum, ← Finset.mul_sum, ← map_sum, ← Finset.sum_mul]

/-- All four complete parity blocks have cutoff-independent bounds.
The sum is taken before its norm; individual pair norms are not summed. -/
theorem norm_pairedEtaCompletedMoebiusParityBlock_le (rho : NontrivialZetaZero)
    (M : ℕ) (p q : Bool) :
    ‖pairedEtaCompletedMoebiusParityBlock rho M p q‖ ≤
      pairedEtaCompletedMoebiusParityBound rho p * pairedEtaCompletedMoebiusParityBound rho q := by
  rw [pairedEtaCompletedMoebiusParityBlock_eq_pair, norm_mul, RCLike.norm_conj]
  exact mul_le_mul (norm_pairedEtaCompletedMoebiusParityAggregate_le rho M p)
    (norm_pairedEtaCompletedMoebiusParityAggregate_le rho M q) (norm_nonneg _)
    (pairedEtaCompletedMoebiusParityBound_nonneg rho p)

/-- A complete parity block of the original signed reflected kernel,
with both completion channels and their conjugation orientation intact. -/
def pairedEtaSignedCompletedMoebiusParityBlock (rho : NontrivialZetaZero)
    (M : ℕ) (p q : Bool) : ℂ :=
  ∑ d ∈ pairedEtaMoebiusParityIndices M p, ∑ e ∈ pairedEtaMoebiusParityIndices M q,
    pairedEtaSignedCompletedMoebiusPairKernel rho M d e

/-- The signed parity block factors into the actual signed completed
pair of whole parity aggregates, before any loss of their complex phase. -/
theorem pairedEtaSignedCompletedMoebiusParityBlock_eq_pair (rho : NontrivialZetaZero)
    (M : ℕ) (p q : Bool) :
    pairedEtaSignedCompletedMoebiusParityBlock rho M p q =
      etaSignedCompletedPair
        (pairedEtaCompletedMoebiusParityAggregate (NontrivialZetaZero.conjugatePartner rho) M p)
        (pairedEtaCompletedMoebiusParityAggregate (NontrivialZetaZero.conjugatePartner rho) M q)
        (pairedEtaCompletedMoebiusParityAggregate rho M p)
        (pairedEtaCompletedMoebiusParityAggregate rho M q) := by
  simp only [pairedEtaSignedCompletedMoebiusParityBlock, pairedEtaSignedCompletedMoebiusPairKernel,
    etaSignedCompletedPair, pairedEtaCompletedMoebiusParityAggregate_eq_sum,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum, ← Finset.sum_mul]

/-- The exact signed block is the reflected block minus the conjugate
original block, preserving both phases for downstream estimates. -/
theorem pairedEtaSignedCompletedMoebiusParityBlock_eq_channels (rho : NontrivialZetaZero)
    (M : ℕ) (p q : Bool) :
    pairedEtaSignedCompletedMoebiusParityBlock rho M p q =
      pairedEtaCompletedMoebiusParityBlock (NontrivialZetaZero.conjugatePartner rho) M p q -
        starRingEnd ℂ (pairedEtaCompletedMoebiusParityBlock rho M p q) := by
  simp only [pairedEtaSignedCompletedMoebiusParityBlock_eq_pair,
    pairedEtaCompletedMoebiusParityBlock_eq_pair, etaSignedCompletedPair, map_mul,
    starRingEnd_self_apply]

/-- The four complete signed parity blocks are uniformly bounded at
every cutoff. This controls the actual growing arithmetic sums, while
the original current's weighted absolute-return estimate remains separate. -/
theorem norm_pairedEtaSignedCompletedMoebiusParityBlock_le (rho : NontrivialZetaZero)
    (M : ℕ) (p q : Bool) :
    ‖pairedEtaSignedCompletedMoebiusParityBlock rho M p q‖ ≤
      pairedEtaCompletedMoebiusParityBound (NontrivialZetaZero.conjugatePartner rho) p *
        pairedEtaCompletedMoebiusParityBound (NontrivialZetaZero.conjugatePartner rho) q +
      pairedEtaCompletedMoebiusParityBound rho p * pairedEtaCompletedMoebiusParityBound rho q := by
  rw [pairedEtaSignedCompletedMoebiusParityBlock_eq_channels]
  calc
    _ ≤ ‖pairedEtaCompletedMoebiusParityBlock (NontrivialZetaZero.conjugatePartner rho) M p q‖ +
        ‖starRingEnd ℂ (pairedEtaCompletedMoebiusParityBlock rho M p q)‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [RCLike.norm_conj]
      exact add_le_add
        (norm_pairedEtaCompletedMoebiusParityBlock_le (NontrivialZetaZero.conjugatePartner rho) M p q)
        (norm_pairedEtaCompletedMoebiusParityBlock_le rho M p q)

end

end RiemannGaussian
