/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopeView
import RiemannGaussian.SemiprimeD1StackPortScopePrimitives
import RiemannGaussian.SemiprimeD1PortScopeEncoding
/-! # Actual eight original fields and one acquired ID field -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortScopeParse
open SemiprimeD1StackPortScopeRecords SemiprimeD1StackPortScopeComponents
open SemiprimeD1StackPortScopePrimitives SemiprimeD1StackPortScopeView
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual cache prefix after precisely count real field calls. -/
def readPrefix (words:Record) (count:ℕ) : Record := fun j=>if j.val<count then words j else []
/-- Literal still-unconsumed original port fields. -/
def suffix (w:Record) (part:ℕ) (tail:List Bool) : List Bool :=
  if part=0 then frame (w 0) (frame (w 1) (frame (w 2) (frame (w 3) (frame (w 4) (frame (w 5) (frame (w 6) (frame (w 7) tail)))))))
  else if part=1 then frame (w 1) (frame (w 2) (frame (w 3) (frame (w 4) (frame (w 5) (frame (w 6) (frame (w 7) tail))))))
  else if part=2 then frame (w 2) (frame (w 3) (frame (w 4) (frame (w 5) (frame (w 6) (frame (w 7) tail)))))
  else if part=3 then frame (w 3) (frame (w 4) (frame (w 5) (frame (w 6) (frame (w 7) tail))))
  else if part=4 then frame (w 4) (frame (w 5) (frame (w 6) (frame (w 7) tail)))
  else if part=5 then frame (w 5) (frame (w 6) (frame (w 7) tail))
  else if part=6 then frame (w 6) (frame (w 7) tail)
  else if part=7 then frame (w 7) tail else tail
/-- The selected original field is always a physical reader, never a getter callback. -/
def part9 (part:Fin 8) : Fin 9 := ⟨part.val,by omega⟩
/-- Finite original-field continuation, before the actual ID-vector tag is consumed. -/
def nextPort (part:Fin 8) : Label :=
  if h:part.val<7 then .local (.field ⟨part.val+1,by omega⟩) else .local .bankTag
/-- Updating one actual parsed cache slot gives exactly its next prefix. -/
theorem readPrefix_update (words:Record) (part:Fin 9) :
    Function.update (readPrefix words part.val) part (words part)=readPrefix words (part.val+1) := by
  funext j
  by_cases h:j=part
  · subst j;simp [readPrefix,Function.update]
  · have hn:j.val≠part.val:=by intro he;exact h (Fin.ext he)
    simp only [Function.update_of_ne h,readPrefix]
    by_cases hj:j.val<part.val
    · have hj':j.val<part.val+1:=by omega
      simp [hj,hj']
    · have hj':¬j.val<part.val+1:=by omega
      simp [hj,hj']
/-- Literal suffix framing at every original-field stage. -/
theorem suffix_cons (words:Record) (part:Fin 8) (tail:List Bool) :
    suffix words part.val tail=frame (words (part9 part)) (suffix words (part.val+1) tail) := by
  fin_cases part <;> rfl
/-- The original eight fields always read the port reader, not the ID reader. -/
theorem fieldInput_port (part:Fin 8) : fieldInput (part9 part)=aux .readerPorts := by
  fin_cases part <;> rfl
/-- The physical validity pop has the literal correct next original-field continuation. -/
theorem popPort_code (part:Fin 8) :
    program (.local (.popValid (part9 part)))=.base (.pop (aux .valid) (nextPort part) (nextPort part) (nextPort part)) := by
  by_cases h:part.val<7
  · simp [program,nextPort,part9,h]
  · have he:part.val=7:=by omega
    simp [program,nextPort,part9,he]
/-- One actual original field and its actual validity-cell pop. -/
theorem port_step (base:S.Stack→List Bool) (words:Record) (part:Fin 8) (tail ids raw:List Bool) :
    Runs program (8*(words (part9 part)).length+8) (.local (.field (part9 part)))
      (clean base (suffix words part.val tail) ids (readPrefix words part.val) raw)
      (nextPort part) (clean base (suffix words (part.val+1) tail) ids (readPrefix words (part.val+1)) raw) := by
  let before:=clean base (suffix words part.val tail) ids (readPrefix words part.val) raw
  let after:=clean base (suffix words (part.val+1) tail) ids (readPrefix words (part.val+1)) raw
  have hf:=field_call (part9 part) before (words (part9 part)) (suffix words (part.val+1) tail)
    (by rw [fieldInput_port];change suffix words part.val tail=_;exact suffix_cons words part tail)
    (by change readPrefix words part.val (part9 part)=[];simp [readPrefix,part9]) rfl rfl
  rw [fieldInput_port] at hf
  change Runs program _ _ _ _ (Function.update (Function.update (Function.update before
    (aux .readerPorts) (suffix words (part.val+1) tail)) (cache (part9 part)) (words (part9 part))) (aux .valid) [true]) at hf
  rw [clean_ports] at hf
  change Runs program _ _ _ _ (Function.update
    (Function.update (store base (readPrefix words part.val) (cleanWork (suffix words (part.val+1) tail) ids raw))
      (cache (part9 part)) (words (part9 part))) (aux .valid) [true]) at hf
  have hu:Function.update (readPrefix words part.val) (part9 part) (words (part9 part))=
      readPrefix words (part.val+1):=readPrefix_update words (part9 part)
  rw [update_cache,hu] at hf
  change Runs program _ _ before _ (Function.update after (aux .valid) [true]) at hf
  have hp:=pop_run (.local (.popValid (part9 part))) (nextPort part) (aux .valid)
    (Function.update after (aux .valid) [true]) (popPort_code part)
  rw [Function.update_self] at hp
  change Runs program _ _ _ _ (Function.update (Function.update after (aux .valid) [true]) (aux .valid) []) at hp
  rw [Function.update_idem] at hp
  have he:Function.update after (aux .valid) []=after:=by
    have hh:after (aux .valid)=[]:=rfl
    rw [←hh]
    exact Function.update_eq_self _ _
  rw [he] at hp
  simpa only [show (8*(words (part9 part)).length+7)+1=8*(words (part9 part)).length+8 by omega] using hf.trans hp
/-- Actual original-field mass before the bank field is consumed. -/
def portMass (w:Record) : ℕ :=
  (w 0).length+(w 1).length+(w 2).length+(w 3).length+
    (w 4).length+(w 5).length+(w 6).length+(w 7).length
/-- The eight original fields are acquired from this actual physical tape. -/
theorem ports_run (base:S.Stack→List Bool) (words:Record) (tail ids raw:List Bool) :
    Runs program (8*portMass words+64) (.local (.field 0))
      (clean base (suffix words 0 tail) ids (fun _=>[]) raw) (.local .bankTag)
      (clean base tail ids (readPrefix words 8) raw) := by
  have h0:=port_step base words 0 tail ids raw
  have h1:=port_step base words 1 tail ids raw
  have h2:=port_step base words 2 tail ids raw
  have h3:=port_step base words 3 tail ids raw
  have h4:=port_step base words 4 tail ids raw
  have h5:=port_step base words 5 tail ids raw
  have h6:=port_step base words 6 tail ids raw
  have h7:=port_step base words 7 tail ids raw
  have h:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7)))))))
  have hz:readPrefix words 0=(fun _=>[]):=by funext j;simp [readPrefix]
  change Runs program _ _ (clean base (suffix words 0 tail) ids (readPrefix words 0) raw)
    (.local .bankTag) (clean base (suffix words 8 tail) ids (readPrefix words 8) raw) at h
  rw [hz] at h
  have ht:(8*(words 0).length+8+(8*(words 1).length+8+(8*(words 2).length+8+
      (8*(words 3).length+8+(8*(words 4).length+8+(8*(words 5).length+8+
        (8*(words 6).length+8+(8*(words 7).length+8))))))))=8*portMass words+64:=by
    unfold portMass
    omega
  change Runs program (8*(words 0).length+8+(8*(words 1).length+8+(8*(words 2).length+8+
      (8*(words 3).length+8+(8*(words 4).length+8+(8*(words 5).length+8+
        (8*(words 6).length+8+(8*(words 7).length+8)))))))) _ _ _ _ at h
  rw [ht] at h
  exact h
/-- One REAL vector tag pop, ID-field parser and validity pop acquire the actual next ID word. -/
theorem id_run (base:S.Stack→List Bool) (words:Record) (ports tail raw:List Bool) :
    Runs program (8*(words 8).length+9) (.local .bankTag)
      (clean base ports (true::frame (words 8) tail) (readPrefix words 8) raw)
      (.local (.emitFrame 0)) (clean base ports tail words raw) := by
  let before:=clean base ports (true::frame (words 8) tail) (readPrefix words 8) raw
  let parsed:=clean base ports tail words raw
  have h0:Runs program 1 (.local .bankTag) before (.local (.field 8))
      (clean base ports (frame (words 8) tail) (readPrefix words 8) raw):=by
    apply one_base program _ _ (.pop (aux .readerIds) (.local .abort) (.local .abort) (.local (.field 8))) before _ rfl
    · rfl
    · change Function.update before (aux .readerIds) (frame (words 8) tail)=_
      exact clean_ids _ _ _ _ _ _
  have hf:=field_call 8 (clean base ports (frame (words 8) tail) (readPrefix words 8) raw)
    (words 8) tail rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (Function.update
    (clean base ports (frame (words 8) tail) (readPrefix words 8) raw) (aux .readerIds) tail)
      (cache 8) (words 8)) (aux .valid) [true]) at hf
  rw [clean_ids] at hf
  change Runs program _ _ _ _ (Function.update (Function.update
    (store base (readPrefix words 8) (cleanWork ports tail raw)) (cache 8) (words 8)) (aux .valid) [true]) at hf
  have hu:Function.update (readPrefix words 8) (8:Fin 9) (words 8)=readPrefix words 9:=
    readPrefix_update words 8
  rw [update_cache,hu] at hf
  have hall:readPrefix words 9=words:=by funext j;simp [readPrefix,j.isLt]
  rw [hall] at hf
  change Runs program _ _ _ _ (Function.update parsed (aux .valid) [true]) at hf
  have hp:=pop_run (.local (.popValid 8)) (.local (.emitFrame 0)) (aux .valid)
    (Function.update parsed (aux .valid) [true]) rfl
  rw [Function.update_self] at hp
  change Runs program _ _ _ _ (Function.update (Function.update parsed (aux .valid) [true]) (aux .valid) []) at hp
  rw [Function.update_idem] at hp
  have hv:Function.update parsed (aux .valid) []=parsed:=by
    have hh:parsed (aux .valid)=[]:=rfl
    rw [←hh]
    exact Function.update_eq_self _ _
  rw [hv] at hp
  have h:=h0.trans (hf.trans hp)
  simpa only [show 1+(8*(words 8).length+7+1)=8*(words 8).length+9 by omega] using h
end RiemannGaussian.SemiprimeD1StackPortScopeParse
