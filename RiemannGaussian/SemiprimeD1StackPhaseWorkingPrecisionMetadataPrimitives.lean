/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadata
/-! # Real primitive calls and exact bounded-word state views -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives
open SemiprimeD1StackPhaseWorkingPrecisionMetadata SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Description of actual acquired order; never a runtime argument. -/
abbrev order :=SemiprimeD1StackPhaseGeometryGuardPrimitives.order
/-- Description of actual acquired guard verdict, never supplied to the program. -/
abbrev accepted :=SemiprimeD1StackPhaseGeometryGuardComponents.accepted
/-- Proof-only stage coordinates of physical unary fields. None inhabit finite control. -/
structure Counts where
  /-- Actual dividend marker count. -/
  input : Nat:=0
  /-- Actual physically copied divisor marker count. -/
  divisor : Nat:=0
  /-- Actual retained divider quotient marker count. -/
  height : Nat:=0
  /-- Actual temporary divider remainder marker count. -/
  remainder : Nat:=0
  /-- Actual consuming product multiplier marker count. -/
  multiplier : Nat:=0
  /-- Actual product multiplicand marker count. -/
  multiplicand : Nat:=0
  /-- Actual acquired coefficient-block marker count. -/
  q : Nat:=0
  /-- Actual acquired bounded precision-product marker count. -/
  r : Nat:=0
  /-- Actual acquired binary-shift marker count. -/
  delta : Nat:=0
  /-- Actual copied-order subtraction marker count. -/
  subtractWork : Nat:=0
  deriving DecidableEq
/-- Every unary output/work count initially has zero physical cells. -/
def empty : Counts :={}
/-- Literal acquired-cache plus physical unary work/output words and original binary p. -/
def context (a u M : Nat) (t p : List Bool) (c : Counts) : Stack→List Bool :=
  store (SemiprimeD1StackPhaseGeometryGuardComponents.result a u t)
    (D.contents (D.unary c.input) (D.unary c.divisor) [] [] (D.unary c.height) (D.unary c.remainder))
    (words (D.unary M) p (D.unary c.multiplier) (D.unary c.multiplicand) []
      (D.unary c.q) (D.unary c.r) (D.unary c.delta) (D.unary c.subtractWork) [])
/-- Chronological instruction composition retains every real outer return frame. -/
theorem join {m n : Nat} {pc mid next : Label} {d e f : Stack→List Bool}
    (h : Runs program m pc d mid e) (g : Runs program n mid e next f) :
    Runs program (m+n) pc d next f :=runs_trans program m n pc mid next d e f h g
/-- Exact actual source value at each of the nine fixed copy sites. -/
def copyValue (a u M : Nat) (t : List Bool) (kind : Fin 9) (c : Counts) : Nat :=
  if kind=0 then M else if kind=1 then u else if kind=2 then u else if kind=3 then u
  else if kind=4 then order a t else if kind=5 then c.height else if kind=6 then M else a
/-- Exact proof-side result of one paid preserving copy into a physical unary field. -/
def copied (a u M : Nat) (t : List Bool) (kind : Fin 9) (c : Counts) : Counts :=
  let v:=copyValue a u M t kind c
  if kind=0 ∨ kind=1 then {c with input:=v+c.input}
  else if kind=2 then {c with divisor:=v+c.divisor}
  else if kind=3 ∨ kind=7 then {c with multiplicand:=v+c.multiplicand}
  else if kind=4 then {c with subtractWork:=v+c.subtractWork}
  else if kind=5 ∨ kind=6 then {c with multiplier:=v+c.multiplier}
  else {c with delta:=v+c.delta}
/-- Source words are the actual physical caller/acquired words, not decoded operands. -/
theorem source_word (a u M : Nat) (t p : List Bool) (kind : Fin 9) (c : Counts) :
    context a u M t p c (copySource kind)=D.unary (copyValue a u M t kind c) :=by
  fin_cases kind <;> first | rfl | exact SemiprimeD1StackPhaseGeometryGuardPrimitives.cache_order a t
/-- Actual Copy source executes both loops and restores its original operand. -/
theorem copy_call (kind : Fin 9) (pc next : Label)
    (hc : program pc=.call (.copy kind 0) next) (d : Stack→List Bool)
    (hz : d (aux .copyScratch)=[]) :
    Runs program (5*(d (copySource kind)).length+4) pc d next
      (Function.update d (copyTarget kind) (d (copySource kind)++d (copyTarget kind))) :=by
  let xs:=d (copySource kind)
  let ys:=d (copyTarget kind)
  have hi:Link.DataRel (copyStack kind) d (SemiprimeD1StackCopy.state 0 none xs ys []).store d:=by
    constructor
    · intro k;fin_cases k
      · rfl
      · rfl
      · exact hz
    · intro k _;rfl
  have ho:=Link.data_update (copyStack kind) (copy_injective kind) _ _ _ hi (1:Fin 3) (xs++ys)
  have he:Function.update (SemiprimeD1StackCopy.state 0 none xs ys []).store 1 (xs++ys)=
      (SemiprimeD1StackCopy.done xs (xs++ys)).store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack kind) (Label.copy kind) (copy_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs ys []) (SemiprimeD1StackCopy.done xs (xs++ys))
    d _ rfl rfl (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- Every static copy site has its exact actual stage trace and charged source length. -/
theorem copy_context (a u M : Nat) (t p : List Bool) (kind : Fin 9) (c : Counts)
    (pc next : Label) (hc : program pc=.call (.copy kind 0) next) :
    Runs program (5*copyValue a u M t kind c+4) pc (context a u M t p c)
      next (context a u M t p (copied a u M t kind c)) :=by
  have h:=copy_call kind pc next hc (context a u M t p c) rfl
  rw [source_word,D.unary,List.length_replicate] at h
  have he:Function.update (context a u M t p c) (copyTarget kind)
      (D.unary (copyValue a u M t kind c)++context a u M t p c (copyTarget kind))=
      context a u M t p (copied a u M t kind c):=by
    fin_cases kind <;> funext k <;> rcases k with k|k
    all_goals first | rfl | (rcases k with k|k <;> cases k <;> first | rfl | exact (SemiprimeD1StackUnaryDivmod.unary_add _ _).symm)
  change Runs program (5*copyValue a u M t kind c+4) pc (context a u M t p c) next
    (Function.update (context a u M t p c) (copyTarget kind)
      (D.unary (copyValue a u M t kind c)++context a u M t p c (copyTarget kind))) at h
  rw [he] at h
  exact h
/-- Whole real guard call starts ONLY from original physical a/u/M/t/p words. -/
theorem guard_call (a u M : Nat) (t p : List Bool) :
    ∃q≤10000*(a+u+t.length+1)+1,Runs program q .start (input a u M t p) .branch (context a u M t p empty) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseGeometryGuardExecution.source_run a u t
  refine ⟨q+1,by exact Nat.add_le_add_right hq 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program guardStack Label.guard guard_injective
    G.program .start (fun _=>rfl) .start .branch rfl q
    (SemiprimeD1StackPhaseGeometryGuard.initial a u t)
    (SemiprimeD1StackPhaseGeometryGuardExecution.done a u t) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rcases k with k|k <;> cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives
