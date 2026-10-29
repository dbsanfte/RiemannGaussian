/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowMeaning
/-! # Exact legacy original-row payload, with true geometry and complete raw bytes
Legacy reports occur only in byte/value equivalence. Their clock fields are
never used to bound or execute the literal source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridOriginalStep
open SemiprimeD1StackRecoveryGridView
namespace Model
export SemiprimeD1StackRecoveryGridModel (Payload center alpha node node_original)
end Model
namespace Row
export SemiprimeD1StackRecoveryGridRowMeaning (step work multiplicity index negative numeratorBase denominatorBase numeratorPower denominatorPower reciprocal slope)
export SemiprimeD1StackRecoveryGridRow (order centerBit)
end Row
namespace Old
export SemiprimeD1RecoveryGridBits (GridReport loop index copies_words)
export SemiprimeD1RecoveryWeightRun (geometry geometry_center geometry_size geometry_point multiplicityRun)
end Old
/-- Only the original acquired words/slopes; old report clocks are explicitly excluded. -/
def payload (r:Old.GridReport) :Model.Payload:=⟨r.numerator,r.denominator,r.slopes⟩
/-- Original word-only suffix fold used in exact chronological physical-loop invariants. -/
def loop (a M u n:Nat) (width:List Bool) (qs:List Nat) :Model.Payload:=
  payload (Old.loop width a (SemiprimeD1TaperedLoss.height M u) u n (Old.geometry a n)
    (Model.center a width) (Model.alpha a width) (Old.index a n).word qs)
/-- The actual scanned order equals the exact original finite-fuel order, including q0/order=a. -/
theorem order_original (a n v:Nat) (q:List Bool) (hv:SemiprimeBitArithmetic.bitValue q=v) (hq:v<2^(a+1)) :
    Row.order a q=(SemiprimeD1RecoveryScalarRun.orderFuel (Old.geometry a n).size ((v:Int)-(Old.geometry a n).center).natAbs).value:=by
  have h:=SemiprimeD1StackPhaseGeometryOriginal.orderFuel_original (List.replicate a true) q
    (by simpa only [List.length_replicate,hv] using hq)
  have hb:=SemiprimeD1StackRecoveryGridRow.order_bytes ({}:Words) a 0 q
  change SemiprimeD1StackPhaseGeometryComponents.result (List.replicate a true) q
    (SemiprimeD1StackPhaseGeometry.aux .order)=List.replicate (Row.order a q) true at hb
  rw [hb] at h
  have he:=congrArg List.length h
  simp only [List.length_replicate] at he
  simpa only [Row.order,Old.geometry_size,Old.geometry_point,Old.geometry_center,SemiprimeD1WireKernelOriginal.point,hv] using he
/-- The actual geometry singleton tests the true original center independently of fitted W. -/
theorem center_original (a n v:Nat) (q:List Bool) (hv:SemiprimeBitArithmetic.bitValue q=v) :
    Row.centerBit a q=true↔v=(Old.geometry a n).center.natAbs:=by
  unfold Row.centerBit
  rw [decide_eq_true_eq,SemiprimeD1StackPhaseGeometryArithmetic.magnitude_value,hv,Int.natAbs_eq_zero]
  rw [Old.geometry_center]
  change (v:Int)-(2^a:Nat)=0↔v=2^a
  omega
/-- Exact actual m equals the original multiplicity report value; the report's work field is unused. -/
theorem multiplicity_original (a M u n v:Nat) (q:List Bool)
    (hv:SemiprimeBitArithmetic.bitValue q=v) (hq:v<2^(a+1)) :
    Row.multiplicity a M u q=(Old.multiplicityRun (Old.geometry a n) (SemiprimeD1TaperedLoss.height M u) u v).value:=by
  unfold Row.multiplicity Old.multiplicityRun
  rw [order_original a n v q hv hq]
/-- One actual row payload is EXACT the legacy q::suffix fold, including all raw widths, negative zero, repeats and orientation. -/
theorem step_original (a M u n v:Nat) (t q width:List Bool) (qs:List Nat)
    (ht:SemiprimeBitArithmetic.bitValue t=n) (hn:n<2^(a+1))
    (hqv:SemiprimeBitArithmetic.bitValue q=v) (hql:q.length=a+2) (hq:v<2^(a+1)) :
    Row.step a M u t q width (loop a M u n width qs)=loop a M u n width (v::qs):=by
  have hcenter:=center_original a n v q hqv
  by_cases hc:Row.centerBit a q=true
  · have hskip:v=(Old.geometry a n).center.natAbs∨v=n:=Or.inl (hcenter.mp hc)
    simp only [Row.step,ite_eq_left hc,loop,Old.loop,ite_eq_left hskip,payload]
  · have hnot:v≠(Old.geometry a n).center.natAbs:=by intro he;exact hc (hcenter.mpr he)
    by_cases he:v=n
    · have hskip:v=(Old.geometry a n).center.natAbs∨v=n:=Or.inr he
      simp only [Row.step,ite_eq_right hc,hqv,ht,ite_eq_left he,loop,Old.loop,ite_eq_left hskip,payload]
    · have hskip:¬(v=(Old.geometry a n).center.natAbs∨v=n):=by rintro (hs|hs);exact hnot hs;exact he hs
      simp only [Row.step,ite_eq_right hc,hqv,ht,ite_eq_right he,loop,Old.loop,ite_eq_right hskip,payload]
      have hnode:=Model.node_original a n t ht hn
      have hindex:Row.index q=(Old.index a v).word:=SemiprimeD1StackRecoveryGridRowStart.index_original a v q hql hqv hq
      have hm:=multiplicity_original a M u n v q hqv hq
      dsimp only [Row.work,Row.numeratorPower,Row.denominatorPower,Row.numeratorBase,Row.denominatorBase,Row.reciprocal,Row.slope,Row.negative]
      rw [hnode,hindex,hm,Old.copies_words]
end RiemannGaussian.SemiprimeD1StackRecoveryGridOriginalStep
