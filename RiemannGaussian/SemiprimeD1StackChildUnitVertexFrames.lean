/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildUnitVertexCalls
/-! # Actual table tag, whole table frame and literal empty-scope/vertex tags -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildUnitVertexFrames
open SemiprimeD1StackChildUnitVertex SemiprimeD1StackChildUnitVertexCalls
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Each literal push is an actual transition, independent of transient flags. -/
theorem push_run (pc next : Control) (stack : Stack) (bit : Bool) (data : Stack→List Bool)
    (hc : program (.local pc)=.base (.push stack bit (.local next))) :
    Runs program 1 (.local pc) data (.local next) (Function.update data stack (bit::data stack)) :=
  one_base program (.local pc) (.local next) (.push stack bit (.local next)) _ _ hc rfl rfl
/-- One full restoring frame executes on the acquired table, not on a supplied result. -/
theorem frame_call (data : Stack→List Bool) (word tail : List Bool)
    (hin : ∀i,data (frameStack i)=SemiprimeD1StackFrame.payload word tail [] i) :
    Runs program (6*word.length+5) (.local .frame) data (.local .scope0)
      (Function.update data (aux .record) (frame word tail)) := by
  let source:=SemiprimeD1StackFrame.state 0 none word tail []
  let result:=SemiprimeD1StackFrame.done word (frame word tail)
  have hd : SemiprimeD1StackMultiplierLink.DataRel frameStack data source.store data:=⟨hin,fun _ _=>rfl⟩
  have hu:=SemiprimeD1StackMultiplierLink.data_update frameStack frame_injective data source.store data hd 1 (frame word tail)
  have he : Function.update source.store 1 (frame word tail)=result.store := by
    funext i
    fin_cases i <;> simp [source,result,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.done,
      SemiprimeD1StackFrame.payload,Function.update]
  rw [he] at hu
  exact included_call program frameStack Label.frame frame_injective SemiprimeD1StackFrame.code 0 (fun _=>rfl)
    (.local .frame) (.local .scope0) rfl (6*word.length+4) source result data _ rfl rfl
    (SemiprimeD1StackFrame.frame_words word tail none) hd hu
/-- Exact actual stopped bank after both real producers, before any record bits. -/
def ready (axes : List ℕ) (precision : List Bool) : Stack→List Bool :=
  bank (contextData axes precision) (UC.bank (width axes precision) (rank axes precision) [] []
    (SemiprimeD1TensorTapeCodec.vectorBits (SemiprimeD1JetAffineCoefficient.one (ctx axes precision)).words)) [] []
/-- The table word is acquired by ONE actual FALSE leaf-tag push. -/
def tableWord (axes : List ℕ) (precision : List Bool) : List Bool := false::ready axes precision (unit U.output)
/-- All actual producer fields are retained, with the real leaf tag added to its output. -/
def tagged (axes : List ℕ) (precision : List Bool) : Stack→List Bool :=
  Function.update (ready axes precision) (unit U.output) (tableWord axes precision)
/-- Fixed empty-port frame and vertex tag around the actually acquired table frame. -/
def recordWord (axes : List ℕ) (precision : List Bool) : List Bool :=
  true::true::false::false::frame (tableWord axes precision) [false]
/-- Exact final store: all original producer words, real leaf tag and actual whole record. -/
def result (axes : List ℕ) (precision : List Bool) : Stack→List Bool :=
  Function.update (tagged axes precision) (aux .record) (recordWord axes precision)
/-- The complete real table-field frame and four literal scope/vertex pushes. -/
theorem assemble_run (axes : List ℕ) (precision : List Bool) :
    Runs program (6*(tableWord axes precision).length+11) (.local .leaf) (ready axes precision)
      (.local .done) (result axes precision) := by
  let data:=tagged axes precision
  let seeded:=Function.update data (aux .record) [false]
  let framed:=Function.update data (aux .record) (frame (tableWord axes precision) [false])
  let zero:=Function.update data (aux .record) (false::frame (tableWord axes precision) [false])
  let zeros:=Function.update data (aux .record) (false::false::frame (tableWord axes precision) [false])
  let scope:=Function.update data (aux .record) (true::false::false::frame (tableWord axes precision) [false])
  have h0:=push_run .leaf .eof (unit U.output) false (ready axes precision) rfl
  have h1:=push_run .eof .frame (aux .record) false data rfl
  change Runs program 1 _ _ _ seeded at h1
  have h2:=frame_call seeded (tableWord axes precision) [false]
    (by intro i;fin_cases i <;> rfl)
  change Runs program _ _ _ _ (Function.update seeded (aux .record) (frame (tableWord axes precision) [false])) at h2
  simp only [seeded,Function.update_idem] at h2
  have h3:=push_run .scope0 .scope1 (aux .record) false framed rfl
  have h4:=push_run .scope1 .scopeTag (aux .record) false zero rfl
  have h5:=push_run .scopeTag .vertexTag (aux .record) true zeros rfl
  have h6:=push_run .vertexTag .done (aux .record) true scope rfl
  simp only [framed,zero,zeros,scope,Function.update_self,Function.update_idem] at h3 h4 h5 h6
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0
    (runs_trans program _ _ _ _ _ _ _ _ h1 (runs_trans program _ _ _ _ _ _ _ _ h2
      (runs_trans program _ _ _ _ _ _ _ _ h3 (runs_trans program _ _ _ _ _ _ _ _ h4
        (runs_trans program _ _ _ _ _ _ _ _ h5 h6)))))
  convert h using 1 <;> first | rfl | omega
end RiemannGaussian.SemiprimeD1StackChildUnitVertexFrames
