/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceOffsetProgramBits
import RiemannGaussian.SemiprimeSourceProgramStorage

/-! # Original-resource bound for the physical source-offset block
The conservative physical width is a magnitude bound. For the actual scheduled
source scales that magnitude is a FIXED polynomial of the original materialized
resources, including U=r^(2Q). No arbitrary input magnitude is assumed polynomial
in its own binary length. Initial encoding and the whole public caller stay separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeSourceOffsetProgramBudget
open SemiprimeRationalBits SemiprimeSourceProgramBits SemiprimeSourceOffsetProgramBits
open SemiprimeSourceOffsetHeight SemiprimeReportPolynomialGrowth

/-- Explicit original-resource majorant of the scheduled scale denominator. -/
def denominatorEnvelope (S : ℕ) : ℕ := S*S*S*(2*S)
/-- Explicit original-resource majorant of the scheduled scale numerator. -/
def numeratorEnvelope (S : ℕ) : ℕ := S*(2*S)+S*(S*S)*S
/-- Actual conservative width bounded after substituting original bank and dimensions. -/
def widthEnvelope (S : ℕ) : ℕ :=
  height (denominatorEnvelope S) (numeratorEnvelope S) S S S S S+1
/-- All twelve actual instruction, operand-scan and persistent-copy reports. -/
def clockEnvelope (S : ℕ) : ℕ := 12*(stepBudget 19 (widthEnvelope S) 4+3)+1

/-- Scheduled scales give a width polynomial in the ORIGINAL resource cap, with
the actual universal bank U retained as a separate input-size resource. -/
theorem scheduled_width_le (M n r Q lam S : ℕ)
    (hM : M ≤ S) (hn : n ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hlam : lam ≤ S)
    (hU : r^(2*Q) ≤ S) :
    width (r*lam*r^(2*Q)*(2*r)) (M*(2*r)+n*(r*lam)*r^(2*Q)) M n r Q ≤ widthEnvelope S := by
  have hd : r*lam*r^(2*Q)*(2*r) ≤ denominatorEnvelope S := by
    unfold denominatorEnvelope
    gcongr
  have hb : M*(2*r)+n*(r*lam)*r^(2*Q) ≤ numeratorEnvelope S := by
    unfold numeratorEnvelope
    gcongr
  unfold width widthEnvelope height
  gcongr

/-- Actual source enumerations discharge the universal-size substitution exactly. -/
theorem caller_width_le {I E : Type} {n r Q : ℕ}
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam S : ℕ)
    (hM : en.incidences.values.length ≤ S) (hn : n ≤ S) (hr : r ≤ S)
    (hQ : Q ≤ S) (hlam : lam ≤ S) (hU : en.types.values.length ≤ S) :
    width (r*lam*r^(2*Q)*(2*r))
      (en.incidences.values.length*(2*r)+n*(r*lam)*r^(2*Q))
      en.incidences.values.length n r Q ≤ widthEnvelope S := by
  apply scheduled_width_le _ _ _ _ _ S hM hn hr hQ hlam
  simpa only [caller_universal_length] using hU

/-- The actual physical offset interpreter has a bound in original resources, once
its seven ORIGINAL input registers have been acquired at the proved width. -/
theorem caller_run_clock {I E : Type} {n r Q : ℕ}
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam S : ℕ)
    (hM : en.incidences.values.length ≤ S) (hn : n ≤ S) (hr : r ≤ S)
    (hQ : Q ≤ S) (hlam : lam ≤ S) (hU : en.types.values.length ≤ S)
    (memory : List RationalWord) (hlen : memory.length=7)
    (hwidth : ∀ w∈memory,Width w (width (r*lam*r^(2*Q)*(2*r))
      (en.incidences.values.length*(2*r)+n*(r*lam)*r^(2*Q)) en.incidences.values.length n r Q)) :
    (run (List.replicate (width (r*lam*r^(2*Q)*(2*r))
      (en.incidences.values.length*(2*r)+n*(r*lam)*r^(2*Q)) en.incidences.values.length n r Q) false)
      code memory).clock ≤ clockEnvelope S := by
  let W := width (r*lam*r^(2*Q)*(2*r))
    (en.incidences.values.length*(2*r)+n*(r*lam)*r^(2*Q)) en.incidences.values.length n r Q
  have hW : 1 ≤ W := by unfold W width; omega
  have hb := run_clock (List.replicate W false) code memory 4
    (by simpa only [List.length_replicate] using hW) (by decide) code_addresses
    (by simpa only [List.length_replicate] using hwidth)
  rw [List.length_replicate,code_length,hlen] at hb
  have hw := caller_width_le en lam S hM hn hr hQ hlam hU
  apply hb.trans
  unfold clockEnvelope stepBudget
  dsimp only [W]
  gcongr

/-- Uniform fixed monomial witnesses for the actual block's original-resource envelope. -/
theorem clockEnvelope_monomial : ∃ C k : ℕ,∀ S,clockEnvelope S ≤ C*(S+1)^k := by
  change Bound (fun S => clockEnvelope S)
  simp only [clockEnvelope,stepBudget,widthEnvelope,height,denominatorEnvelope,numeratorEnvelope]
  boundArithmetic

end RiemannGaussian.SemiprimeSourceOffsetProgramBudget
