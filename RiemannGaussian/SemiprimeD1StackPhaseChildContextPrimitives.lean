/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContext
/-! # Actual whole phase/context/copy/frame calls with explicit physical bank views -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextPrimitives
open SemiprimeD1StackPhaseChildContext SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Literal physical existing-ABI UNARY-dimension axis header. -/
def header (axes : List Nat) : List Bool :=SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)
/-- Exact48-role phase cache actually acquired by the whole binary source. -/
def phase (a u edges : Nat) (t p : List Bool) : P.Stack→List Bool :=
  SemiprimeD1StackPhaseWorkingPrecisionComponents.result a u edges t p
/-- Actual bounded coefficient-block dimension, described only for source proofs. -/
abbrev count :=SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic.blocks
/-- Exact actual retained branch singleton from P48. -/
abbrev accepted :=SemiprimeD1StackPhaseWorkingPrecisionComponents.accepted
/-- Exact actual BINARY new precision word; this projection is a proof-side physical bank view. -/
def precision (a u edges : Nat) (t p : List Bool) : List Bool :=phase a u edges t p (P.aux .output)
/-- Physically acquired old/child context result, not a native rank cache supplier. -/
def contextResult (axes : List Nat) (p : List Bool) : J.Stack→List Bool :=
  SemiprimeD1StackJetContextCorrectness.finalData axes p
/-- Only the selected actual15-role context bank is replaced by this stage view. -/
def withContext (child : Bool) (base : Stack→List Bool) (view : J.Stack→List Bool) : Stack→List Bool
  | .inr (.inl k)=>if child then base (.inr (.inl k)) else view k
  | .inr (.inr (.inl k))=>if child then view k else base (.inr (.inr (.inl k)))
  | k=>base k
/-- Chronological execution composition preserves all real outer return frames. -/
theorem join {m n : Nat} {pc mid next : Label} {d e f : Stack→List Bool}
    (h : Runs program m pc d mid e) (g : Runs program n mid e next f) :
    Runs program (m+n) pc d next f :=runs_trans program m n pc mid next d e f h g
/-- Every copy executes both physical loops and preserves its actual source word. -/
theorem copy_call (kind : Fin 3) (pc next : Label) (hc : program pc=.call (.copy kind 0) next)
    (d : Stack→List Bool) (hs : d (aux .scratch)=[]) (ht : d (copyTarget kind)=[]) :
    Runs program (5*(d (copySource kind)).length+4) pc d next
      (Function.update d (copyTarget kind) (d (copySource kind))) :=by
  let xs:=d (copySource kind)
  have hi:Link.DataRel (copyStack kind) d (SemiprimeD1StackCopy.state 0 none xs [] []).store d:=by
    constructor
    · intro k;fin_cases k
      · rfl
      · exact ht
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack kind) (copy_injective kind) _ _ _ hi (1:Fin 3) xs
  have he:Function.update (SemiprimeD1StackCopy.state 0 none xs [] []).store 1 xs=
      (SemiprimeD1StackCopy.done xs xs).store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  have hr:=SemiprimeD1StackCopy.copy_words xs [] none
  rw [List.append_nil] at hr
  exact included_call program (copyStack kind) (Label.copy kind) (copy_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs [] []) (SemiprimeD1StackCopy.done xs xs) d _ rfl rfl hr hi ho
/-- Real Frame prepends the ACTUAL acquired unary-q field and restores all of its source cells. -/
theorem frame_call (d : Stack→List Bool) (hs : d (aux .scratch)=[]) :
    Runs program (6*(d blocks).length+5) .frame d .cons
      (Function.update d (childStack J.axesCache)
        (SemiprimeSourceHistogramKeyBits.frame (d blocks) (d (childStack J.axesCache)))) :=by
  let xs:=d blocks
  let ys:=d (childStack J.axesCache)
  have hi:Link.DataRel frameStack d (SemiprimeD1StackFrame.state 0 none xs ys []).store d:=by
    constructor
    · intro k;fin_cases k
      · rfl
      · rfl
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update frameStack frame_injective _ _ _ hi (1:Fin 3) (SemiprimeSourceHistogramKeyBits.frame xs ys)
  have he:Function.update (SemiprimeD1StackFrame.state 0 none xs ys []).store 1
      (SemiprimeSourceHistogramKeyBits.frame xs ys)=(SemiprimeD1StackFrame.done xs (SemiprimeSourceHistogramKeyBits.frame xs ys)).store:=by
    funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program frameStack Label.framing frame_injective SemiprimeD1StackFrame.code 0 (fun _=>rfl)
    .frame .cons rfl (6*xs.length+4) (SemiprimeD1StackFrame.state 0 none xs ys [])
    (SemiprimeD1StackFrame.done xs (SemiprimeSourceHistogramKeyBits.frame xs ys)) d _ rfl rfl
    (SemiprimeD1StackFrame.frame_words xs ys none) hi ho
/-- Each real context source acquires rank and numerical precision WIDTH from only header/binary precision.
Its cost EXPLICITLY includes VALUE expansion, not only precision-byte length. -/
theorem context_call (child : Bool) (axes : List Nat) (hp : ∀q∈axes,0<q) (p : List Bool)
    (base : Stack→List Bool) :
    ∃q≤SemiprimeD1StackJetContextCorrectness.budget axes p+1,
      Runs program q (if child then .childContext else .oldContext)
        (withContext child base (J.initial (header axes) p).data)
        (if child then .accept else .copyHeader) (withContext child base (contextResult axes p)) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackJetContextCorrectness.source_run axes hp p
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program (if child then childStack else oldStack)
    (Label.context child) (context_injective child) J.program .start (fun _=>rfl)
    (if child then .childContext else .oldContext) (if child then .accept else .copyHeader)
    (by cases child <;> rfl) q (J.initial (header axes) p)
    (⟨none,none,none,contextResult axes p,[]⟩:C.State J.Stack J.Label) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;cases child <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases child <;> rfl
    · intro k hk
      cases child with
      | false=>
        rcases k with k|k
        · rfl
        · rcases k with k|k
          · exact (hk k rfl).elim
          · rcases k with k|k <;> rfl
      | true=>
        rcases k with k|k
        · rfl
        · rcases k with k|k
          · rfl
          · rcases k with k|k
            · exact (hk k rfl).elim
            · rfl
end RiemannGaussian.SemiprimeD1StackPhaseChildContextPrimitives
