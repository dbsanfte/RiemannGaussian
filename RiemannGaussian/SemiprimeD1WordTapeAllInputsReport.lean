/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapeOriginalRate
import RiemannGaussian.SemiprimeD1GlobalRate
import RiemannGaussian.SemiprimeD1CanonicalInput

/-! # Every original canonical input: correctness and quantitative REPORT bound
The finite initial range is absorbed into one family-wide constant. Canonical
word selection below is a proof-side parameterization of supplied binary input,
not preprocessing run by the factoring program. Every actual query and recovery
report is retained. This is deliberately a report theorem: a complete primitive
machine simulation, including native/control/heap costs, remains open.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1WordTapeAllInputsReport
open Filter SemiprimeBitArithmetic SemiprimeSourceCompactBits
open SemiprimeMacroParameters SemiprimeD1OriginalCallRate
attribute [local irreducible] SemiprimeD1WordTapePublicReport.work

/-- Proof-side unique canonical input word representing one original integer. -/
def canonical (N : ℕ) : List Bool :=
  (trim (SemiprimeEncodedRowSelection.digits (bitLength N) N).bits).bits

/-- This input parameterization preserves the original integer exactly. -/
theorem canonical_value (N : ℕ) : bitValue (canonical N)=N := by
  rw [canonical,trim_value,SemiprimeEncodedRowSelection.digits_value _ _ (input_lt_bitLength_power N)]

/-- Every selected input word is canonical, including the zero convention. -/
theorem canonical_compact (N : ℕ) : Compact (canonical N) := trim_compact _

/-- Arbitrary supplied canonical binary input has this same unique word. -/
theorem input_eq_canonical (input : List Bool) (hc:Compact input) : input=canonical (bitValue input) := by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ hc (canonical_compact _)
  rw [canonical_value]

noncomputable section

/-- CLOSED quantitative REPORT rate for EVERY positive canonical original
binary input. The single constant precedes the entire input family. -/
theorem all_positive_report_rate : ∃C:ℕ,∀input:List Bool,Compact input→
    0<bitValue input→(SemiprimeD1WordTapePublicReport.work input:ℝ) ≤
      (2:ℝ)^((C:ℝ)*inputScale (bitLength (bitValue input))) := by
  obtain ⟨C,hC⟩:=SemiprimeD1WordTapeOriginalRate.eventually_public_report_rate
  have h:∀ᶠ ell:ℕ in atTop,∀N:ℕ,0<N→bitLength N=ell→
      (SemiprimeD1WordTapePublicReport.work (canonical N):ℝ) ≤ (2:ℝ)^((C:ℝ)*inputScale ell):=by
    filter_upwards [hC] with ell hlocal
    intro N hN hEll
    have hv:0<bitValue (canonical N):=by rw [canonical_value];exact hN
    have hs:bitLength (bitValue (canonical N))=ell:=by rw [canonical_value,hEll]
    exact hlocal (canonical N) (canonical_compact N) hv hs
  obtain ⟨D,hD⟩:=SemiprimeD1GlobalRate.eventually_to_all
    (fun N=>SemiprimeD1WordTapePublicReport.work (canonical N)) C h
  refine ⟨D,?_⟩
  intro input hc hN
  simpa only [←input_eq_canonical input hc] using hD (bitValue input) hN

/-- The report uses exactly the requested ceiling-logarithm input size and
natural logarithm in the exponent denominator; d=0 already suffices here. -/
theorem all_positive_report_goal_form : ∃C:ℕ,∀input:List Bool,Compact input→
    0<bitValue input→(SemiprimeD1WordTapePublicReport.work input:ℝ) ≤
      (2:ℝ)^((C:ℝ)*(Nat.clog 2 (bitValue input+1):ℝ)/
        Real.sqrt (Real.log (Nat.clog 2 (bitValue input+1)+2:ℕ))) := by
  obtain ⟨C,hC⟩:=all_positive_report_rate
  refine ⟨C,?_⟩
  intro input hc hN
  simpa only [inputScale,SemiprimeD1CanonicalInput.size_eq_clog,mul_div_assoc] using hC input hc hN

/-- The SAME executed original-input program has closed semiprime correctness
and the all-family REPORT bound. This does not assert a primitive bit clock. -/
theorem semiprime_correct_and_report : ∃C:ℕ,∀input:List Bool,Compact input→
    ∀p q:ℕ,p.Prime→q.Prime→bitValue input=p*q→
      ∃left right,(SemiprimeD1WordTapeBinaryFactorExecution.run input).factors=some (left,right) ∧
        bitValue left*bitValue right=bitValue input ∧2 ≤ bitValue left ∧2 ≤ bitValue right ∧
        (bitValue left=p ∨bitValue left=q) ∧
        (SemiprimeD1WordTapePublicReport.work input:ℝ) ≤
          (2:ℝ)^((C:ℝ)*inputScale (bitLength (bitValue input))) := by
  obtain ⟨C,hC⟩:=all_positive_report_rate
  refine ⟨C,?_⟩
  intro input hc p q hp hq hsem
  obtain ⟨left,right,ho,hprod,hl,hr,hpq⟩:=
    SemiprimeD1WordTapeBinaryFactorExecution.run_complete input p q hp hq hsem
  have hN:0<bitValue input:=by rw [hsem];exact Nat.mul_pos hp.pos hq.pos
  exact ⟨left,right,ho,hprod,hl,hr,hpq,hC input hc hN⟩

end
end RiemannGaussian.SemiprimeD1WordTapeAllInputsReport
