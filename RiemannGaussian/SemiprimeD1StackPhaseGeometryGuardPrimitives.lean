/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryGuard
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Real geometry, preserving-copy and consuming-comparison calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardPrimitives
open SemiprimeD1StackPhaseGeometryGuard SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- The exact fourteen-role cache acquired by the frozen physical source. -/
def cache (a : Nat) (t : List Bool) : G.Stack→List Bool :=
  SemiprimeD1StackPhaseGeometryComponents.result (List.replicate a true) t
/-- Exact proof-side description of the ACQUIRED order, never a runtime parameter. -/
def order (a : Nat) (t : List Bool) : Nat :=SemiprimeD1StackPhaseGeometryArithmetic.valuation
  (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a t)
/-- Proof-side description of the actual acquired singleton zero flag. -/
def zero (a : Nat) (t : List Bool) : Bool :=decide (SemiprimeBitArithmetic.bitValue
  (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a t)=0)
/-- The whole acquired cache and original u are retained at every guard boundary. -/
def context (a u : Nat) (t left limit valid output : List Bool) : Stack→List Bool :=
  store (cache a t) (words (List.replicate u true) left limit valid output)
/-- Exact byte identity of the physically acquired order counter. -/
theorem cache_order (a : Nat) (t : List Bool) : cache a t (G.aux .order)=List.replicate (order a t) true :=by
  change List.replicate (SemiprimeD1StackPhaseGeometryArithmetic.valuation
    (SemiprimeD1StackPhaseGeometryArithmetic.magnitude (List.replicate a true).length t)) true=_
  rw [List.length_replicate]
  rfl
/-- Exact actual singleton zero flag, including all-zero padded magnitudes. -/
theorem cache_zero (a : Nat) (t : List Bool) : cache a t (G.aux .zero)=[zero a t] :=by
  change [decide (SemiprimeBitArithmetic.bitValue (SemiprimeD1StackPhaseGeometryArithmetic.magnitude
    (List.replicate a true).length t)=0)]=_
  rw [List.length_replicate]
  rfl
/-- Actual order cells are bounded by the paid binary magnitude width. -/
theorem order_le (a : Nat) (t : List Bool) : order a t≤ max t.length (a+1) :=
  (SemiprimeD1StackPhaseGeometryArithmetic.valuation_le _).trans
    (SemiprimeD1StackPhaseGeometryArithmetic.magnitude_length a t).le
/-- Chronological composition retains arbitrary actual caller frames. -/
theorem join {m n : Nat} {pc mid next : Label} {d e f : Stack→List Bool}
    (h : Runs program m pc d mid e) (g : Runs program n mid e next f) :
    Runs program (m+n) pc d next f :=runs_trans program m n pc mid next d e f h g
/-- Whole actual geometry call runs from ONLY original exponent/index fields. -/
theorem geometry_call (a u : Nat) (t : List Bool) :
    ∃q≤1000*(a+t.length+1)+1,Runs program q .start (input a u t) .zero (context a u t [] [] [] []) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseGeometryExecution.source_run (List.replicate a true) t
  have hq':q≤1000*(a+t.length+1):=by
    simpa only [SemiprimeD1StackPhaseGeometryComponents.runBound,List.length_replicate] using hq
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program geometryStack Label.geometry geometry_injective
    G.program .start (fun _=>rfl) .start .zero rfl q
    (SemiprimeD1StackPhaseGeometry.initial (List.replicate a true) t)
    (SemiprimeD1StackPhaseGeometryExecution.done (List.replicate a true) t) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Both copy loops, actual restoration and real call/return are charged. -/
theorem copy_call (kind : Fin 3) (pc next : Label)
    (hc : program pc=.call (.copy kind 0) next) (d : Stack→List Bool)
    (hz : d (aux .scratch)=[]) (ht : d (copyTarget kind)=[]) :
    Runs program (5*(d (copySource kind)).length+4) pc d next
      (Function.update d (copyTarget kind) (d (copySource kind))) :=by
  let xs:=d (copySource kind)
  have hi:Link.DataRel (copyStack kind) d (SemiprimeD1StackCopy.state 0 none xs [] []).store d:=by
    constructor
    · intro k;fin_cases k
      · rfl
      · exact ht
      · exact hz
    · intro k _;rfl
  have ho:=Link.data_update (copyStack kind) (copy_injective kind) _ _ _ hi (1:Fin 3) xs
  have he:Function.update (SemiprimeD1StackCopy.state 0 none xs [] []).store 1 xs=
      (SemiprimeD1StackCopy.done xs xs).store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  have hr:=SemiprimeD1StackCopy.copy_words xs [] none
  rw [List.append_nil] at hr
  exact included_call program (copyStack kind) (Label.copy kind) (copy_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs [] []) (SemiprimeD1StackCopy.done xs xs)
    d _ rfl rfl hr hi ho
/-- The actual finite consuming comparator clears BOTH operands and its spare field. -/
theorem less_call (second : Bool) (a u m d : Nat) (t : List Bool) :
    ∃q≤30*(m+d+1)+11,Runs program q (.compare second)
      (context a u t (List.replicate m true) (List.replicate d true) [] []) (.branch second)
      (context a u t [] [] [decide (m<d)] []) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackUnarySumLessBytecode.compare_run m 0 d
  simp only [Nat.add_zero] at hq hr
  refine ⟨q+1,by omega,?_⟩
  apply included_call program lessStack Label.less less_injective Less.code Less.entry (fun _=>rfl)
    (.compare second) (.branch second) rfl q
    ⟨some Less.entry,none,Less.contents (List.replicate m true) [] (List.replicate d true) []⟩
    ⟨none,none,Less.contents [] [] [] [decide (m<d)]⟩ _ _ rfl rfl hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rfl
      · cases k
        · rfl
        · exact (hk .left rfl).elim
        · exact (hk .right rfl).elim
        · exact (hk .limit rfl).elim
        · exact (hk .valid rfl).elim
        · rfl
        · rfl
end RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardPrimitives
