/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowStart
import RiemannGaussian.SemiprimeD1StackRecoveryGridCompare
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowWork
/-! # Actual complete original-grid row: true center/node skips or the whole acquired body -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridRow
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridOperationInput SemiprimeD1StackProcedureTrace
namespace Start
export SemiprimeD1StackRecoveryGridRowStart (result runBound row_start_run center_run index_run index)
end Start
namespace Compare
export SemiprimeD1StackRecoveryGridCompare (runBound compare_run after)
end Compare
namespace Work
export SemiprimeD1StackRecoveryGridRowWork (result runBound row_work_run put_nonempty)
end Work
namespace Cleanup
export SemiprimeD1StackRecoveryGridRowCleanup (result runBound cleanup_run)
end Cleanup
/-- Actual bounded order scanned by the real geometry source, only interpreted here for the trace invariant. -/
def order (a:Nat) (q:List Bool) :Nat:=SemiprimeD1StackPhaseGeometryArithmetic.valuation
  (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a q)
/-- Actual singleton center flag from that same physical source. -/
def centerBit (a:Nat) (q:List Bool) :Bool:=decide (SemiprimeBitArithmetic.bitValue
  (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a q)=0)
/-- Actual row state after the physical todo pop and true geometry acquisition. -/
def geometry (w:Words) (a n:Nat) (q:List Bool) :Words:=Start.result w a q n
/-- Actual paid current-index copy after both real skip tests reject. -/
def indexed (w:Words) (a n:Nat) (q:List Bool) :Words:=putReg (geometry w a n q) .index (Start.index q)
/-- Actual complete stopped row, including all physical skip-path or work-path cleanup. -/
def result (w:Words) (width:List Bool) (a h u n:Nat) (q t:List Bool) :Words:=
  if centerBit a q then Cleanup.result (geometry w a n q)
  else if SemiprimeBitArithmetic.bitValue q=SemiprimeBitArithmetic.bitValue t then Cleanup.result (geometry w a n q)
  else Work.result (indexed w a n q) width h u (order a q)
/-- Own conservative row cap pays all real branch components from their actual physical input banks. -/
def runBound (w:Words) (width:List Bool) (a h u n:Nat) (q t:List Bool) :Nat:=
  Start.runBound a q+1+Compare.runBound q t+Cleanup.runBound (geometry w a n q)+(5*q.length+4+2)+
    Work.runBound (indexed w a n q) width h u (order a q)
attribute [local irreducible] result runBound Start.runBound Compare.runBound Cleanup.runBound Work.runBound
/-- Actual geometry order word exactly matches the physically scanned count, including q0 and center0. -/
theorem order_bytes (w:Words) (a n:Nat) (q:List Bool) :
    (geometry w a n q).geometry .order=List.replicate (order a q) true:=by
  change List.replicate (SemiprimeD1StackPhaseGeometryArithmetic.valuation
    (SemiprimeD1StackPhaseGeometryArithmetic.magnitude (List.replicate a true).length q)) true=_
  rw [List.length_replicate]
  rfl
/-- Actual singleton center-test bytes, independent of all fitted coefficients and W. -/
theorem center_bytes (w:Words) (a n:Nat) (q:List Bool) :
    (geometry w a n q).geometry .zero=[centerBit a q]:=by
  change [decide (SemiprimeBitArithmetic.bitValue (SemiprimeD1StackPhaseGeometryArithmetic.magnitude
    (List.replicate a true).length q)=0)]=_
  rw [List.length_replicate]
  rfl
/-- Complete literal row execution acquires geometry and multiplicity internally and preserves both exact skip conditions. -/
theorem row_run (w:Words) (width:List Bool) (a h u n:Nat) (q t:List Bool)
    (htodo:w.auxiliary .todo=List.replicate (n+1) true)
    (ha:w.auxiliary .originalA=List.replicate a true) (hu:w.auxiliary .originalU=List.replicate u true)
    (ht:w.auxiliary .originalT=t) (hq:w.auxiliary .q=q) (hh:w.division .quotient=List.replicate h true)
    (hg:∀k,w.geometry k=[]) (hr:w.rational=emptyRational width)
    (hp:w.product=SemiprimeD1StackUnaryProduct.contents [] [] [] [])
    (hs:w.auxiliary .copyScratch=[]) (hpow:w.auxiliary .powerTodo=[]) (hrep:w.auxiliary .repeatTodo=[])
    (hf:w.auxiliary .frameScratch=[]) (ho:w.auxiliary .orderTodo=[])
    (hi:w.registers (.index,false)=[]) (hid:w.registers (.index,true)=[])
    (hc:w.registers (.center,false)≠[]) (hn:w.registers (.node,false)≠[]) (hal:w.registers (.alpha,false)≠[])
    (hgn:w.registers (.gridNum,false)≠[]) (hgd:w.registers (.gridDen,false)≠[]) :
    ∃time≤ runBound w width a h u n q t,Runs program time (.local .row) (bank w) (.local .advance)
      (bank (result w width a h u n q t)):=by
  have hRipple:∀k,w.rational (SemiprimeD1StackRationalOperation.adderStack k)=[]:=by
    intro k;rw [hr];cases k <;> rfl
  obtain ⟨p,hpBound,h0⟩:=Start.row_start_run w a n q htodo ha hq hg hRipple
  change Runs program p _ _ _ (bank (geometry w a n q)) at h0
  have h1:=Start.center_run (geometry w a n q) (centerBit a q) (center_bytes w a n q)
  cases hb:centerBit a q with
  | true=>
    rw [hb] at h1
    change Runs program 1 _ _ (.local (.clearTransient false 0)) _ at h1
    obtain ⟨s,hsBound,h2⟩:=Cleanup.cleanup_run (geometry w a n q)
    have he:Cleanup.result (geometry w a n q)=result w width a h u n q t:=by unfold result;rw [hb];rfl
    rw [he] at h2
    refine ⟨p+1+s,?_,PTrace.join (PTrace.join h0 h1) h2⟩
    unfold runBound
    omega
  | false=>
    rw [hb] at h1
    change Runs program 1 _ _ (.local .equalQ) _ at h1
    have h2:=Compare.compare_run (geometry w a n q) q t hq ht hRipple hs
    by_cases heq:SemiprimeBitArithmetic.bitValue q=SemiprimeBitArithmetic.bitValue t
    · have halt:Compare.after q t=.local (.clearTransient false 0):=by unfold Compare.after;rw [ite_eq_left heq]
      rw [halt] at h2
      obtain ⟨s,hsBound,h3⟩:=Cleanup.cleanup_run (geometry w a n q)
      have he:Cleanup.result (geometry w a n q)=result w width a h u n q t:=by unfold result;rw [hb];simp only [Bool.false_eq_true,ite_false,ite_eq_left heq]
      rw [he] at h3
      refine ⟨p+1+Compare.runBound q t+s,?_,PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3⟩
      unfold runBound
      omega
    · have halt:Compare.after q t=.local .index:=by unfold Compare.after;rw [ite_eq_right heq]
      rw [halt] at h2
      have h3:=Start.index_run (geometry w a n q) q hq hs hi hid
      change Runs program (5*q.length+4+2) _ _ _ (bank (indexed w a n q)) at h3
      have hidx:(indexed w a n q).registers (.index,false)≠[]:=by
        unfold indexed
        rw [(SemiprimeD1StackRecoveryGridRegisters.putReg_fields (geometry w a n q) .index (Start.index q)).1]
        exact List.cons_ne_nil _ _
      obtain ⟨s,hsBound,h4⟩:=Work.row_work_run (indexed w a n q) width h u (order a q)
        hu (order_bytes w a n q) hh hs hp ho hr hpow hrep hf hidx
        (Work.put_nonempty _ .index _ .center hc) (Work.put_nonempty _ .index _ .node hn)
        (Work.put_nonempty _ .index _ .alpha hal) (Work.put_nonempty _ .index _ .gridNum hgn) (Work.put_nonempty _ .index _ .gridDen hgd)
      have he:Work.result (indexed w a n q) width h u (order a q)=result w width a h u n q t:=by
        unfold result;rw [hb];simp only [Bool.false_eq_true,ite_false,ite_eq_right heq]
      rw [he] at h4
      refine ⟨p+1+Compare.runBound q t+(5*q.length+4+2)+s,?_,
        PTrace.join (PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3) h4⟩
      unfold runBound
      omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridRow
