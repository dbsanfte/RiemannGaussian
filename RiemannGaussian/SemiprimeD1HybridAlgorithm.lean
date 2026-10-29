/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HybridPublicReport
import RiemannGaussian.SemiprimeD1BoundaryLeafOriginalRate
import RiemannGaussian.SemiprimeD1BoundaryLeafOriginalReachRate
import RiemannGaussian.SemiprimeD1BoundaryPartitionReachRate
import RiemannGaussian.SemiprimeD1HybridCallReport
import RiemannGaussian.SemiprimeD1HybridOriginalRate

/-! # Public factoring entry with the acquired boundary contraction leaf

The current original-binary algorithm uses its own deterministic partition and
full-jet sorted-record leaf at both recursive stopping sites. Original factor
bytes and all changed retained work contributions are preserved. The uniform
leaf half exponent and the tightened actual call count are separate checked
results; complete primitive-machine bit complexity remains open.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HybridAlgorithm
open SemiprimeBitArithmetic

/-- Current closed original-binary factor execution with the boundary leaf installed. -/
def factor (input : List Bool) : SemiprimeD1WordTapeBinaryFactorExecution.Run :=
  SemiprimeD1HybridPublicExecution.run input

/-- Complete own retained report of that same actual factor execution. -/
def report (input : List Bool) : Nat := SemiprimeD1HybridPublicExecution.work input

/-- Every successful binary output is an ordinary proper factor pair. -/
theorem factor_sound (input left right : List Bool)
    (h : (factor input).factors = some (left, right)) :
    bitValue left * bitValue right = bitValue input ∧ 2 ≤ bitValue left ∧ 2 ≤ bitValue right :=
  SemiprimeD1HybridPublicExecution.run_sound input left right h

/-- All binary semiprimes, including prime squares, return complete factor bytes. -/
theorem factor_complete (input : List Bool) (p q : Nat) (hp : p.Prime) (hq : q.Prime)
    (hsem : bitValue input = p * q) :
    ∃ left right, (factor input).factors = some (left, right) ∧
      bitValue left * bitValue right = bitValue input ∧
      2 ≤ bitValue left ∧ 2 ≤ bitValue right ∧ (bitValue left = p ∨ bitValue left = q) :=
  SemiprimeD1HybridPublicExecution.run_complete input p q hp hq hsem

/-- The installed execution retains the original linear number of count queries. -/
theorem factor_queries (input : List Bool) :
    (factor input).queries ≤ SemiprimePublicAcquiredExecution.wireCount (bitValue input) + 1 :=
  SemiprimeD1HybridPublicExecution.run_queries input

/-- The actual changed native retained report has fixed constants before every
original positive canonical binary input. Primitive-machine lowering is separate. -/
theorem report_rate : ∃ C : Nat, ∀ᶠ ell : Nat in Filter.atTop,
    ∀ input : List Bool, SemiprimeSourceCompactBits.Compact input →
      ∀ _hN : 0 < bitValue input, SemiprimeMacroParameters.bitLength (bitValue input) = ell →
        (report input : Real) ≤ (2 : Real)^((C : Real) * SemiprimeD1OriginalCallRate.inputScale ell) :=
  SemiprimeD1HybridOriginalRate.eventually_public_report_rate

end RiemannGaussian.SemiprimeD1HybridAlgorithm
