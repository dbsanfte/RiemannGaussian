/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryView
import RiemannGaussian.SemiprimeD1StackChildTableEntryPrimitives
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Real individual precision reduction, with complete scalar operand framing
Every original and appended-zero coefficient uses this SAME real scalar source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryScalar
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryView SemiprimeD1StackChildTableEntryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace SR
export SemiprimeD1StackPrecisionReduceExecution (input result totalTime source_run totalTime_le)
end SR
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel)
end Link
local notation "ctl"=>Label.local
/-- All eight actual scalar source words, with only input or stopped result nonempty. -/
def scalarBank (input result:List Bool):R.Stack→List Bool:=R.store input [] [] [] [] [] result []
/-- Real scalar input update preserves all seven other reducer roles. -/
theorem scalar_input (input result xs:List Bool):Function.update (scalarBank input result) .input xs=scalarBank xs result:=by
  funext k;cases k <;> rfl
/-- Real scalar result drain restores all eight roles to their actual empty boundary. -/
theorem scalar_result (input result xs:List Bool):Function.update (scalarBank input result) .result xs=scalarBank input xs:=by
  funext k;cases k <;> rfl
/-- Both parsers, actual binary-to-unary NEWp acquisition and actual scalar reducer execute before the real caller return. -/
theorem scalar_call (z:Bool) (word p:List Bool) (old child:J.Stack→List Bool)
    (g:G.Stack→List Bool) (t:T.Stack→List Bool) (a:Aux→List Bool):
    Runs program (SR.totalTime word p+1) (ctl (.reduce z))
      (bank old child g t (scalarBank (SR.input word p) []) a) (ctl (.frame z))
      (bank old child g t (scalarBank [] (SR.result word p)) a):=by
  let start:C.State R.Stack R.Label:=⟨some .start,none,none,scalarBank (SR.input word p) [],[]⟩
  let stop:C.State R.Stack R.Label:=⟨none,none,none,scalarBank [] (SR.result word p),[]⟩
  have hin:Link.DataRel reduce (bank old child g t start.data a) start.data (bank old child g t start.data a):=⟨fun _=>rfl,fun _ _=>rfl⟩
  have hout:Link.DataRel reduce (bank old child g t start.data a) stop.data (bank old child g t stop.data a):=by
    constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k|k|k|k|k
      · rfl
      · rfl
      · rfl
      · rfl
      · exact False.elim (hk k rfl)
      · rfl
  exact SemiprimeD1StackProcedureCallsTrace.included_call program reduce Label.reduce reduce_injective R.program .start
    (fun _=>rfl) (ctl (.reduce z)) (ctl (.frame z)) rfl (SR.totalTime word p) start stop _ _
    rfl rfl rfl rfl (SR.source_run word p) hin hout
/-- Exact sum of real framing, complete scalar-source, logging, reversal and drain costs for one coefficient. -/
def scalarTime (word p:List Bool):Nat:=
  (6*p.length+5)+(6*word.length+5)+(SR.totalTime word p+1)+
    (6*(SR.result word p).length+5)+1+(2*(row (SR.result word p)).length+3)+
    (word.length+1)+((SR.result word p).length+1)
/-- One complete actual individual scalar reduction/logging step; no current coefficient is dropped or lifted in aggregate. -/
theorem scalar_run (z:Bool) (word p:List Bool) (old child:J.Stack→List Bool)
    (g:G.Stack→List Bool) (t:T.Stack→List Bool) (w:Words) (hp:child J.precisionBits=p):
    Runs program (scalarTime word p) (ctl (.precision z))
      (bank old child g t (scalarBank [] []) (words {w with coefficient:=word,buffer:=[],scratch:=[]}))
      (ctl (if z then .zeros else .header))
      (bank old child g t (scalarBank [] [])
        (words {w with coefficient:=[],buffer:=[],scratch:=[],history:=(row (SR.result word p)).reverse++w.history})):=by
  let v:Words:={w with coefficient:=word,buffer:=[],scratch:=[]}
  let b0:=bank old child g t (scalarBank [] []) (words v)
  have h0:=frame_call .precision (.precision z) (.scalar z) rfl b0 p [] (by exact hp) rfl rfl
  change Runs program _ _ _ _ (Function.update b0 (reduce .input) (frame p [])) at h0
  rw [update_reduce,scalar_input] at h0
  have h1:=frame_call .scalar (.scalar z) (.reduce z) rfl
    (bank old child g t (scalarBank (frame p []) []) (words v)) word (frame p []) rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (bank old child g t (scalarBank (frame p []) []) (words v)) (reduce .input) (frame word (frame p []))) at h1
  rw [update_reduce,scalar_input] at h1
  have h2:=scalar_call z word p old child g t (words v)
  have h3:=frame_call .log (.frame z) (.tag z) rfl
    (bank old child g t (scalarBank [] (SR.result word p)) (words v)) (SR.result word p) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update
    (bank old child g t (scalarBank [] (SR.result word p)) (words v)) (aux .buffer) (frame (SR.result word p) [])) at h3
  rw [update_aux,words_update] at h3
  let v1:Words:={v with buffer:=frame (SR.result word p) []}
  have h4:=push_run (.tag z) (ctl (.reverse z)) (aux .buffer) true
    (bank old child g t (scalarBank [] (SR.result word p)) (words v1)) rfl
  rw [update_aux,words_update] at h4
  let v2:Words:={v with buffer:=row (SR.result word p)}
  have h5:=reverse_call false (.reverse z) (.clearCoefficient z) rfl
    (bank old child g t (scalarBank [] (SR.result word p)) (words v2)) (row (SR.result word p)) w.history rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update
    (bank old child g t (scalarBank [] (SR.result word p)) (words v2)) (aux .buffer) [])
      (aux .history) ((row (SR.result word p)).reverse++w.history)) at h5
  rw [update_aux,words_update,update_aux,words_update] at h5
  let v3:Words:={v with history:=(row (SR.result word p)).reverse++w.history}
  have h6:=drain_loop (.clearCoefficient z) (ctl (.clearReduced z)) (aux .coefficient) rfl
    (bank old child g t (scalarBank [] (SR.result word p)) (words v3)) word rfl
  rw [update_aux,words_update] at h6
  let v4:Words:={v3 with coefficient:=[]}
  have h7:=drain_loop (.clearReduced z) (ctl (if z then .zeros else .header)) (reduce .result) rfl
    (bank old child g t (scalarBank [] (SR.result word p)) (words v4)) (SR.result word p) rfl
  rw [update_reduce,scalar_result] at h7
  have h:=join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7
  exact h
end RiemannGaussian.SemiprimeD1StackChildTableEntryScalar
