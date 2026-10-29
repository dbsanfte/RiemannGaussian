/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryPrimitives
/-! # Literal three-count acquisition, actual raw words and physical bound cache -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicCarryAcquire
open SemiprimeD1StackPublicCarry SemiprimeD1StackPublicCarryState SemiprimeD1StackPublicCarryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Exact phase after the actual three literal marker pushes. -/
def seeded (raw : List Bool) : Payload := {raw:=raw,three:=three}
/-- Three actual literal pushes acquire the count; no count is input advice. -/
theorem seed_run (context : T.Stack→List Bool) (raw : List Bool) :
    Runs program 3 (.seed 0) (view context (rawPayload raw)) .vectorCall (view context (seeded raw)) := by
  have h0:=push_aux (.seed 0) (.seed 1) .three true rfl context (rawPayload raw)
  have h1:=push_aux (.seed 1) (.seed 2) .three true rfl context (set (rawPayload raw) .three [true])
  have h2:=push_aux (.seed 2) .vectorCall .three true rfl context (set (rawPayload raw) .three [true,true])
  exact runs_trans program 2 1 _ _ _ _ _ _ (runs_trans program 1 1 _ _ _ _ _ _ h0 h1) h2
/-- Actual raw-word acquisition ONCE, using the acquired modulus-word width and
literal3 count. Every original/reader/cache/vector byte comes from real code. -/
theorem vector_call (context : T.Stack→List Bool) (raw : List Bool) :
    ∃t ≤ SemiprimeD1StackWordVectorExecution.timeBound raw (width context) three+1,
      Runs program t .vectorCall (view context (seeded raw)) (.tag 0) (view context (produced context raw)) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackWordVectorExecution.source_run raw (width context) three
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program vectorStack Label.words vector_injective
    W.program (.control .start) (fun _=>rfl) .vectorCall (.tag 0) rfl t
    (W.initial raw (width context) three) (SemiprimeD1StackWordVectorExecution.done raw (width context) three)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rcases k with k|k <;> fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> fin_cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rfl
      · cases k <;> first | rfl | exact (hk (.inl 0) rfl).elim | exact (hk (.inr 3) rfl).elim
/-- Complete actual framed parser call, with its real output/validity writes. -/
theorem field_call (k : Fin 3) (context : T.Stack→List Bool) (p : Payload) (word tail : List Bool)
    (hi : p.vector=frame word tail) (hs : p.scratch=[]) (hw : get p (wordAux k)=[]) (hv : p.valid=[]) :
    Runs program (8*word.length+7) (.fieldCall k) (view context p) (.parsed k)
      (view context (set (set (set p .vector tail) (wordAux k) word) .valid [true])) := by
  have hin : SemiprimeD1StackMultiplierLink.DataRel (fieldStack k) (view context p)
      (F.initial (frame word tail) []).store (view context p) := by
    constructor
    · intro j;rcases j with j|j
      · cases j
        · exact hi
        · exact hs
        · change view context p (wordRole k)=[]
          rw [wordRole_eq];exact hw
      · cases j;exact hv
    · intro j _;rfl
  have h0:=SemiprimeD1StackMultiplierLink.data_update (fieldStack k) (field_injective k) _ _ _ hin (.inl .input) tail
  have h1:=SemiprimeD1StackMultiplierLink.data_update (fieldStack k) (field_injective k) _ _ _ h0 (.inl .output) word
  have h2:=SemiprimeD1StackMultiplierLink.data_update (fieldStack k) (field_injective k) _ _ _ h1 (.inr ()) [true]
  let finish : SemiprimeD1StackBytecode.State F.Stack F.Label :=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have he : Function.update (Function.update (Function.update (F.initial (frame word tail) []).store
      (.inl .input) tail) (.inl .output) word) (.inr ()) [true]=finish.store := by
    funext j;rcases j with j|j <;> cases j <;> rfl
  rw [he] at h2
  have hout : SemiprimeD1StackMultiplierLink.DataRel (fieldStack k) (view context p) finish.store
      (view context (set (set (set p .vector tail) (wordAux k) word) .valid [true])) := by
    simpa only [fieldStack,wordRole_eq,view_set] using h2
  apply included_call program (fieldStack k) (Label.fields k) (field_injective k) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (.fieldCall k) (.parsed k) rfl (8*word.length+6)
    (F.initial (frame word tail) []) finish _ _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin hout
/-- Actual vector tag, real framed field and actual produced validity pop.
The expected word is only a physical-frame equality in this trace lemma. -/
theorem read_field (k : Fin 3) (context : T.Stack→List Bool) (p : Payload) (word tail : List Bool)
    (hi : p.vector=true::frame word tail) (hs : p.scratch=[]) (hw : get p (wordAux k)=[]) (hv : p.valid=[]) :
    Runs program (8*word.length+9) (.tag k) (view context p) (afterField k)
      (view context (set (set p .vector tail) (wordAux k) word)) := by
  have h0:=pop_aux (.tag k) .bad .bad (.fieldCall k) .vector rfl context p
  change Runs program 1 (.tag k) (view context p)
    (SemiprimeD1StackBytecode.choose .bad .bad (.fieldCall k) p.vector.head?)
    (view context (set p .vector p.vector.tail)) at h0
  rw [hi] at h0
  have hw' : get (set p .vector (frame word tail)) (wordAux k)=[] := by fin_cases k <;> exact hw
  have h1:=field_call k context (set p .vector (frame word tail)) word tail rfl hs hw' hv
  have h2:=pop_aux (.parsed k) .bad .bad (afterField k) .valid rfl context
    (set (set (set (set p .vector (frame word tail)) .vector tail) (wordAux k) word) .valid [true])
  have he : set (set (set (set (set p .vector (frame word tail)) .vector tail) (wordAux k) word) .valid [true]) .valid []=
      set (set p .vector tail) (wordAux k) word := by
    fin_cases k <;> simp [wordAux,SemiprimeD1StackPublicCarryState.set,hv]
  change Runs program 1 (.parsed k) _ (afterField k) (view context
    (set (set (set (set (set p .vector (frame word tail)) .vector tail) (wordAux k) word) .valid [true]) .valid [])) at h2
  rw [he] at h2
  have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  simpa only [show 1+(8*word.length+7)+1=8*word.length+9 by omega] using h
/-- All THREE actual original words are parsed before any numeric guard.
No operand list/vector/word cache is supplied to the executing public entry. -/
theorem parse_run (context : T.Stack→List Bool) (raw : List Bool) :
    Runs program (8*(coefficient context raw).length+9+(8*(previous context raw).length+9)+
      (8*(next context raw).length+9)+1) (.tag 0) (view context (produced context raw))
      .copyBound (view context (parsed context raw)) := by
  let c:=coefficient context raw
  let p:=previous context raw
  let n:=next context raw
  let d0:=produced context raw
  let d1:=set (set d0 .vector (true::frame p (true::frame n [false]))) .coefficient c
  let d2:=set (set d1 .vector (true::frame n [false])) .previous p
  let d3:=set (set d2 .vector [false]) .next n
  have h0 : Runs program (8*c.length+9) (.tag 0) (view context d0) (.tag 1) (view context d1) :=
    read_field 0 context d0 c (true::frame p (true::frame n [false])) rfl rfl rfl rfl
  have h1 : Runs program (8*p.length+9) (.tag 1) (view context d1) (.tag 2) (view context d2) :=
    read_field 1 context d1 p (true::frame n [false]) rfl rfl rfl rfl
  have h2 : Runs program (8*n.length+9) (.tag 2) (view context d2) .vectorEnd (view context d3) :=
    read_field 2 context d2 n [false] rfl rfl rfl rfl
  have h3 : Runs program 1 .vectorEnd (view context d3) .copyBound (view context (parsed context raw)) := by
    have h:=pop_aux .vectorEnd .bad .copyBound .bad .vector rfl context d3
    exact h
  exact runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
/-- A real modulus-word copy followed by real pop/push acquires the bound word.
No positivity/value/low-bit advice is needed to execute this phase. -/
theorem bound_run (context : T.Stack→List Bool) (raw : List Bool) :
    Runs program (5*(width context).length+6) .copyBound (view context (parsed context raw))
      (.guardOperand 0) (view context (ready context raw)) := by
  let p:=parsed context raw
  have h0:=copy_call .bound .copyBound .boundPop rfl context p rfl rfl
  have h1:=pop_aux .boundPop .boundPush .boundPush .boundPush .bound rfl context (set p .bound (width context))
  have h2:=push_aux .boundPush (.guardOperand 0) .bound false rfl context (set p .bound (width context).tail)
  change Runs program 1 .boundPop (view context (set p .bound (width context)))
    (SemiprimeD1StackBytecode.choose .boundPush .boundPush .boundPush (width context).head?)
    (view context (set p .bound (width context).tail)) at h1
  have he : (SemiprimeD1StackBytecode.choose Label.boundPush Label.boundPush Label.boundPush (width context).head?)=Label.boundPush := by
    cases (width context).head? with
    | none=>rfl
    | some b=>cases b <;> rfl
  rw [he] at h1
  have hh:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  change Runs program (5*(width context).length+4+1+1) .copyBound (view context (parsed context raw))
    (.guardOperand 0) (view context (ready context raw)) at hh
  simpa only [show 5*(width context).length+4+1+1=5*(width context).length+6 by omega] using hh
end RiemannGaussian.SemiprimeD1StackPublicCarryAcquire
