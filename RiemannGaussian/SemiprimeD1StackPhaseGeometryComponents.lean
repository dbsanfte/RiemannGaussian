/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryValuation
/-! # Complete literal geometry-plus-valuation source trace -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryComponents
open SemiprimeD1StackPhaseGeometry SemiprimeD1StackPhaseGeometryArithmetic
open SemiprimeD1StackPhaseGeometryPrimitives SemiprimeD1StackProcedureTrace
namespace V
export SemiprimeD1StackPhaseGeometryValuation (scanData scanOrder scanResult)
end V
/-- Exact final bank: original operands retained, binary geometry and counted order acquired. -/
def result (a t : List Bool) : Stack→List Bool :=
  V.scanData a t (magnitude a.length t) [negative a.length t] []
    (valuation (magnitude a.length t)) [decide (SemiprimeBitArithmetic.bitValue (magnitude a.length t)=0)]
/-- A clean physical scan starts from a real preserving copy of the ACTUAL absword. -/
theorem scan_call (a t mag sign : List Bool) :
    Runs program (5*mag.length+4) .scanCopy
      (SemiprimeD1StackPhaseGeometrySubtract.phase a t [] [] mag sign)
      .scan (V.scanData a t mag sign mag 0 []) :=by
  have h:=copy_empty 6 .scanCopy .scan rfl
    (SemiprimeD1StackPhaseGeometrySubtract.phase a t [] [] mag sign) rfl rfl
  have he:Function.update (SemiprimeD1StackPhaseGeometrySubtract.phase a t [] [] mag sign) (copyTarget 6)
      (SemiprimeD1StackPhaseGeometrySubtract.phase a t [] [] mag sign (copySource 6))=
      V.scanData a t mag sign mag 0 []:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h
  exact h
/-- Zero padding changes neither the exact valuation nor the final reset rule. -/
theorem scanOrder_zero (xs : List Bool) : V.scanOrder xs 0=valuation xs :=by
  unfold V.scanOrder
  by_cases h:SemiprimeBitArithmetic.bitValue xs=0
  · simp only [h,ite_true]
    exact (valuation_zero xs h).symm
  · simp only [h,ite_false,Nat.zero_add]
/-- Actual scan and all physical cleanup finish with the exact acquired output bank. -/
theorem valuation_run (a t : List Bool) :
    ∃q≤10*((magnitude a.length t).length+1),
      Runs program q .scan (V.scanData a t (magnitude a.length t) [negative a.length t]
        (magnitude a.length t) 0 []) .done (result a t) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseGeometryValuation.scan_run a t
    (magnitude a.length t) [negative a.length t] (magnitude a.length t) 0
  rw [Nat.mul_zero,Nat.add_zero] at hq
  have he:V.scanResult a t (magnitude a.length t) [negative a.length t] (magnitude a.length t) 0=result a t:=by
    unfold V.scanResult result
    rw [scanOrder_zero]
  rw [he] at hr
  exact ⟨q,hq,hr⟩
/-- Own linear clock in ACTUAL physical original exponent/index bytes. -/
def runBound (a t : List Bool) : Nat :=1000*(a.length+t.length+1)
/-- WHOLE source constructs powers, chooses exact signed subtraction and scans order.
No point, sign, zero test, valuation, answer or clock is a runtime operand. -/
theorem source_trace (a t : List Bool) :
    ∃q,q+1≤ runBound a t ∧ Runs program q .start (input a t) .done (result a t) :=by
  have h0:=SemiprimeD1StackPhaseGeometryPower.source_run a t
  obtain ⟨b,hb,h1⟩:=SemiprimeD1StackPhaseGeometrySubtract.source_run a t
  have h2:=scan_call a t (magnitude a.length t) [negative a.length t]
  obtain ⟨d,hd,h3⟩:=valuation_run a t
  have hh:=join (join (join h0 h1) h2) h3
  refine ⟨_,?_,hh⟩
  have hl:=magnitude_length a.length t
  have hm:max t.length (a.length+1)≤ t.length+a.length+1:=max_le (by omega) (by omega)
  unfold runBound
  omega
end RiemannGaussian.SemiprimeD1StackPhaseGeometryComponents
