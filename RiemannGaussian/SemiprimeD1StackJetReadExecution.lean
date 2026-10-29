/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRead

set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1StackJetReadExecution
open SemiprimeD1StackJetRead SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Actual source trace concatenation. -/
theorem run_append (m n : ℕ) (a b c : C.State Stack Label)
    (hm : C.run program m a=some b) (hn : C.run program n b=some c) : C.run program (m+n) a=some c := by
  rw [SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hn]

/-- Exact physical cache stack update. -/
theorem store_cache (cache reader index parser skipped output valid copy bits : List Bool) :
    Function.update (store cache reader index parser skipped output valid copy) .cache bits=store bits reader index parser skipped output valid copy := by
  funext k
  cases k <;> simp [store,Function.update]

@[simp] theorem store_get_cache (cache reader index parser skipped output valid copy : List Bool) : store cache reader index parser skipped output valid copy .cache=cache := rfl

/-- Exact physical reader stack update. -/
theorem store_reader (cache reader index parser skipped output valid copy bits : List Bool) :
    Function.update (store cache reader index parser skipped output valid copy) .reader bits=store cache bits index parser skipped output valid copy := by
  funext k
  cases k <;> simp [store,Function.update]

@[simp] theorem store_get_reader (cache reader index parser skipped output valid copy : List Bool) : store cache reader index parser skipped output valid copy .reader=reader := rfl

/-- Exact physical index stack update. -/
theorem store_index (cache reader index parser skipped output valid copy bits : List Bool) :
    Function.update (store cache reader index parser skipped output valid copy) .index bits=store cache reader bits parser skipped output valid copy := by
  funext k
  cases k <;> simp [store,Function.update]

@[simp] theorem store_get_index (cache reader index parser skipped output valid copy : List Bool) : store cache reader index parser skipped output valid copy .index=index := rfl

/-- Exact physical parser stack update. -/
theorem store_parser (cache reader index parser skipped output valid copy bits : List Bool) :
    Function.update (store cache reader index parser skipped output valid copy) .parser bits=store cache reader index bits skipped output valid copy := by
  funext k
  cases k <;> simp [store,Function.update]

@[simp] theorem store_get_parser (cache reader index parser skipped output valid copy : List Bool) : store cache reader index parser skipped output valid copy .parser=parser := rfl

/-- Exact physical skipped stack update. -/
theorem store_skipped (cache reader index parser skipped output valid copy bits : List Bool) :
    Function.update (store cache reader index parser skipped output valid copy) .skipped bits=store cache reader index parser bits output valid copy := by
  funext k
  cases k <;> simp [store,Function.update]

@[simp] theorem store_get_skipped (cache reader index parser skipped output valid copy : List Bool) : store cache reader index parser skipped output valid copy .skipped=skipped := rfl

/-- Exact physical output stack update. -/
theorem store_output (cache reader index parser skipped output valid copy bits : List Bool) :
    Function.update (store cache reader index parser skipped output valid copy) .output bits=store cache reader index parser skipped bits valid copy := by
  funext k
  cases k <;> simp [store,Function.update]

@[simp] theorem store_get_output (cache reader index parser skipped output valid copy : List Bool) : store cache reader index parser skipped output valid copy .output=output := rfl

/-- Exact physical valid stack update. -/
theorem store_valid (cache reader index parser skipped output valid copy bits : List Bool) :
    Function.update (store cache reader index parser skipped output valid copy) .valid bits=store cache reader index parser skipped output bits copy := by
  funext k
  cases k <;> simp [store,Function.update]

@[simp] theorem store_get_valid (cache reader index parser skipped output valid copy : List Bool) : store cache reader index parser skipped output valid copy .valid=valid := rfl

/-- Exact physical copy stack update. -/
theorem store_copy (cache reader index parser skipped output valid copy bits : List Bool) :
    Function.update (store cache reader index parser skipped output valid copy) .copy bits=store cache reader index parser skipped output valid bits := by
  funext k
  cases k <;> simp [store,Function.update]

@[simp] theorem store_get_copy (cache reader index parser skipped output valid copy : List Bool) : store cache reader index parser skipped output valid copy .copy=copy := rfl

/-- Every discarded bit executes an actual pop. -/
theorem clear_skipped (cache reader index parser skipped output valid copy : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run program (skipped.length+1) (state (some .clearSkipped) flag rt cache reader index parser skipped output valid copy)=
    some (state (some .loop) none rt cache reader index parser ([]) output valid copy) := by
  induction skipped generalizing flag with
  | nil => simp [C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_skipped]
  | cons bit skipped ih =>
    have hs : C.run program 1 (state (some .clearSkipped) flag rt cache reader index parser (bit::skipped) output valid copy)=
        some (state (some .clearSkipped) (some bit) rt cache reader index parser (skipped) output valid copy) := by
      cases bit <;> simp [C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_skipped]
    have hh:=run_append 1 (skipped.length+1) _ _ _ hs (ih (some bit))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Every discarded bit executes an actual pop. -/
theorem clear_reader (cache reader index parser skipped output valid copy : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run program (reader.length+1) (state (some .clearInput) flag rt cache reader index parser skipped output valid copy)=
    some (state (some .clearIndex) none rt cache ([]) index parser skipped output valid copy) := by
  induction reader generalizing flag with
  | nil => simp [C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_reader]
  | cons bit reader ih =>
    have hs : C.run program 1 (state (some .clearInput) flag rt cache (bit::reader) index parser skipped output valid copy)=
        some (state (some .clearInput) (some bit) rt cache (reader) index parser skipped output valid copy) := by
      cases bit <;> simp [C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_reader]
    have hh:=run_append 1 (reader.length+1) _ _ _ hs (ih (some bit))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Every discarded bit executes an actual pop. -/
theorem clear_index (cache reader index parser skipped output valid copy : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run program (index.length+1) (state (some .clearIndex) flag rt cache reader index parser skipped output valid copy)=
    some (state (some .done) none rt cache reader ([]) parser skipped output valid copy) := by
  induction index generalizing flag with
  | nil => simp [C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_index]
  | cons bit index ih =>
    have hs : C.run program 1 (state (some .clearIndex) flag rt cache reader (bit::index) parser skipped output valid copy)=
        some (state (some .clearIndex) (some bit) rt cache reader (index) parser skipped output valid copy) := by
      cases bit <;> simp [C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_index]
    have hh:=run_append 1 (index.length+1) _ _ _ hs (ih (some bit))
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Actual take field call acquires its word and physical validity flag. -/
theorem parse_take (cache index word tail : List Bool) :
    Runs program (8*word.length+7) .callTake (store cache (frame word tail) index [] [] [] [] [])
      .takeParsed (store cache tail index [] [] word [true] []) := by
  apply included_call program (fieldStack false) (Label.field false) (fieldStack_injective false) Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) .callTake .takeParsed rfl (8*word.length+6)
    (Field.initial (frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:
      SemiprimeD1StackBytecode.State Field.Stack Field.Label)
    (store cache (frame word tail) index [] [] [] [] []) (store cache tail index [] [] word [true] [])
  · rfl
  · rfl
  · exact Field.framed_run word tail []
  · constructor
    · intro k; rcases k with k|k <;> cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      have hi:=hk (.inl .input)
      have ho:=hk (.inl .output)
      have hv:=hk (.inr ())
      cases k <;> simp_all [fieldStack,store]

/-- Actual skip field call acquires its word and physical validity flag. -/
theorem parse_skip (cache index word tail : List Bool) :
    Runs program (8*word.length+7) .callSkip (store cache (frame word tail) index [] [] [] [] [])
      .skipParsed (store cache tail index [] word [] [true] []) := by
  apply included_call program (fieldStack true) (Label.field true) (fieldStack_injective true) Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) .callSkip .skipParsed rfl (8*word.length+6)
    (Field.initial (frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:
      SemiprimeD1StackBytecode.State Field.Stack Field.Label)
    (store cache (frame word tail) index [] [] [] [] []) (store cache tail index [] word [] [true] [])
  · rfl
  · rfl
  · exact Field.framed_run word tail []
  · constructor
    · intro k; rcases k with k|k <;> cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      have hi:=hk (.inl .input)
      have ho:=hk (.inl .output)
      have hv:=hk (.inr ())
      cases k <;> simp_all [fieldStack,store]

/-- Full physically paid cleanup from a consumed vector tag or selected field. -/
theorem cleanup_run (cache reader index output : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run program (reader.length+index.length+3)
      (state (some .clearInput) flag rt cache reader index [] [] output [] [])=
    some (state none none none cache [] [] [] [] output [] []) := by
  have h1:=clear_reader cache reader index [] [] output [] [] flag rt
  have h2:=clear_index cache [] index [] [] output [] [] none rt
  have h3 : C.run program 1 (state (some .done) none rt cache [] [] [] [] output [] [])=
      some (state none none none cache [] [] [] [] output [] []) := rfl
  have hh:=run_append _ _ _ _ _ (run_append _ _ _ _ _ h1 h2) h3
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- A selected nil tag physically yields the empty zero/default word. -/
theorem select_nil (cache : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run program 4 (state (some .selectTag) flag rt cache (vectorBits []) [] [] [] [] [] [])=
    some (state none none none cache [] [] [] [] [] [] []) := by
  have h1 : C.run program 1 (state (some .selectTag) flag rt cache (vectorBits []) [] [] [] [] [] [])=
      some (state (some .clearInput) (some false) rt cache [] [] [] [] [] [] []) := by
    simp [C.run,C.step,C.execute,state,program,vectorBits,SemiprimeD1StackBytecode.choose,store_reader]
  exact run_append 1 3 _ _ _ h1 (cleanup_run cache [] [] [] (some false) rt)

/-- Actual selected-field parse, validity pop and suffix cleanup. -/
theorem select_cons (cache word : List Bool) (words : List (List Bool)) (flag : Option Bool) (rt : Option Label) :
    C.run program (8*word.length+(vectorBits words).length+12)
      (state (some .selectTag) flag rt cache (vectorBits (word::words)) [] [] [] [] [] [])=
    some (state none none none cache [] [] [] [] word [] []) := by
  have h1 : C.run program 1
      (state (some .selectTag) flag rt cache (vectorBits (word::words)) [] [] [] [] [] [])=
      some (state (some .callTake) (some true) rt cache (frame word (vectorBits words)) [] [] [] [] [] []) := by
    simp [C.run,C.step,C.execute,state,program,vectorBits,SemiprimeD1StackBytecode.choose,store_reader]
  obtain ⟨parsed,h2,hAt⟩:=parse_take cache [] word (vectorBits words) []
    (state (some .callTake) (some true) rt cache (frame word (vectorBits words)) [] [] [] [] [] []) ⟨rfl,rfl,rfl⟩
  have heq : parsed=state (some .takeParsed) parsed.flag parsed.returned cache (vectorBits words) [] [] [] word [true] [] := by
    cases parsed
    simp_all [At,state]
  have h2':=h2.trans (congrArg some heq)
  have h3 : C.run program 1
      (state (some .takeParsed) parsed.flag parsed.returned cache (vectorBits words) [] [] [] word [true] [])=
      some (state (some .clearInput) (some true) parsed.returned cache (vectorBits words) [] [] [] word [] []) := by
    simp [C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_valid]
  have h4:=cleanup_run cache (vectorBits words) [] word (some true) parsed.returned
  have hh:=run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ h1 h2') h3) h4
  rw [show 1+(8*word.length+7)+1+((vectorBits words).length+[].length+3)=
    8*word.length+(vectorBits words).length+12 by simp; omega] at hh
  exact hh

/-- Exact actual selected-field stage count. -/
def selectTime : List (List Bool) → ℕ
  | [] => 4
  | word::words => 8*word.length+(vectorBits words).length+12

/-- The actual selected word is the literal first field, with the correct empty default. -/
theorem select_run (cache : List Bool) (words : List (List Bool)) (flag : Option Bool) (rt : Option Label) :
    C.run program (selectTime words) (state (some .selectTag) flag rt cache (vectorBits words) [] [] [] [] [] [])=
    some (state none none none cache [] [] [] [] (words.headD []) [] []) := by
  cases words with
  | nil => exact select_nil cache flag rt
  | cons word words => exact select_cons cache word words flag rt

/-- An exhausted vector physically clears every remaining index cell before returning default zero. -/
theorem skip_nil (cache index : List Bool) (flag : Option Bool) (rt : Option Label) :
    C.run program (index.length+4) (state (some .skipTag) flag rt cache (vectorBits []) index [] [] [] [] [])=
    some (state none none none cache [] [] [] [] [] [] []) := by
  have h1 : C.run program 1 (state (some .skipTag) flag rt cache (vectorBits []) index [] [] [] [] [])=
      some (state (some .clearInput) (some false) rt cache [] index [] [] [] [] []) := by
    simp [C.run,C.step,C.execute,state,program,vectorBits,SemiprimeD1StackBytecode.choose,store_reader]
  have hh:=run_append 1 _ _ _ _ h1 (cleanup_run cache [] index [] (some false) rt)
  rw [show 1+([].length+index.length+3)=index.length+4 by simp; omega] at hh
  exact hh

/-- One skipped coefficient is actually parsed, copied, and then completely cleared. -/
theorem skip_cons (cache index word : List Bool) (words : List (List Bool)) (flag : Option Bool) (rt : Option Label) :
    ∃rr,C.run program (9*word.length+10)
      (state (some .skipTag) flag rt cache (vectorBits (word::words)) index [] [] [] [] [])=
    some (state (some .loop) none rr cache (vectorBits words) index [] [] [] [] []) := by
  have h1 : C.run program 1
      (state (some .skipTag) flag rt cache (vectorBits (word::words)) index [] [] [] [] [])=
      some (state (some .callSkip) (some true) rt cache (frame word (vectorBits words)) index [] [] [] [] []) := by
    simp [C.run,C.step,C.execute,state,program,vectorBits,SemiprimeD1StackBytecode.choose,store_reader]
  obtain ⟨parsed,h2,hAt⟩:=parse_skip cache index word (vectorBits words) []
    (state (some .callSkip) (some true) rt cache (frame word (vectorBits words)) index [] [] [] [] []) ⟨rfl,rfl,rfl⟩
  have heq : parsed=state (some .skipParsed) parsed.flag parsed.returned cache (vectorBits words) index [] word [] [true] [] := by
    cases parsed
    simp_all [At,state]
  have h2':=h2.trans (congrArg some heq)
  have h3 : C.run program 1
      (state (some .skipParsed) parsed.flag parsed.returned cache (vectorBits words) index [] word [] [true] [])=
      some (state (some .clearSkipped) (some true) parsed.returned cache (vectorBits words) index [] word [] [] []) := by
    simp [C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_valid]
  have h4:=clear_skipped cache (vectorBits words) index [] word [] [] [] (some true) parsed.returned
  have hh:=run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ h1 h2') h3) h4
  refine ⟨parsed.returned,?_⟩
  rw [show 1+(8*word.length+7)+1+(word.length+1)=9*word.length+10 by omega] at hh
  exact hh

/-- Exact actual traversal count; only its proof definition sees lists as native values. -/
def loopTime : List Bool → List (List Bool) → ℕ
  | [],words => 1+selectTime words
  | _::index,[] => 1+(index.length+4)
  | _::index,word::words => 1+(9*word.length+10)+loopTime index words

/-- Actual physical index execution computes exactly the original cached-list lookup bytes. -/
theorem loop_run (cache index : List Bool) (words : List (List Bool)) (flag : Option Bool) (rt : Option Label) :
    C.run program (loopTime index words)
      (state (some .loop) flag rt cache (vectorBits words) index [] [] [] [] [])=
    some (state none none none cache [] [] [] [] ((words[index.length]?).getD []) [] []) := by
  induction index generalizing words flag rt with
  | nil =>
    have h1 : C.run program 1 (state (some .loop) flag rt cache (vectorBits words) [] [] [] [] [] [])=
        some (state (some .selectTag) none rt cache (vectorBits words) [] [] [] [] [] []) := by
      simp [C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_index]
    have hh:=run_append _ _ _ _ _ h1 (select_run cache words none rt)
    cases words <;> simpa only [loopTime,List.length_nil,List.getElem?_nil,List.getElem?_cons_zero,
      Option.getD_none,Option.getD_some,List.headD_nil,List.headD_cons] using hh
  | cons marker index ih =>
    have h1 : C.run program 1
        (state (some .loop) flag rt cache (vectorBits words) (marker::index) [] [] [] [] [])=
        some (state (some .skipTag) (some marker) rt cache (vectorBits words) index [] [] [] [] []) := by
      cases marker <;> simp [C.run,C.step,C.execute,state,program,SemiprimeD1StackBytecode.choose,store_index]
    cases words with
    | nil =>
      have hh:=run_append _ _ _ _ _ h1 (skip_nil cache index (some marker) rt)
      simpa only [loopTime,List.getElem?_nil,Option.getD_none] using hh
    | cons word words =>
      obtain ⟨rr,h2⟩:=skip_cons cache index word words (some marker) rt
      have h3:=ih words none rr
      have hh:=run_append _ _ _ _ _ (run_append _ _ _ _ _ h1 h2) h3
      simpa only [loopTime,List.length_cons,List.getElem?_cons_succ,Nat.add_assoc] using hh

/-- Exact whole cache-preserving coefficient read count. -/
def totalTime (index : List Bool) (words : List (List Bool)) : ℕ :=
  (5*(vectorBits words).length+4)+loopTime index words

/-- Closed actual read, preserving the original encoded cache and clearing all query/work data. -/
theorem source_run (index : List Bool) (words : List (List Bool)) :
    C.run program (totalTime index words) (state (some .start) none none (vectorBits words) [] index [] [] [] [] [])=
    some (state none none none (vectorBits words) [] [] [] [] ((words[index.length]?).getD []) [] []) := by
  let d0:=store (vectorBits words) [] index [] [] [] [] []
  let d1:=store (vectorBits words) (vectorBits words) index [] [] [] [] []
  have hc : Runs program (5*(vectorBits words).length+4) .start d0 .loop d1 := by
    apply included_call program copyStack Label.copy copyStack_injective SemiprimeD1StackCopy.code (0:Fin 9)
      (fun _=>rfl) .start .loop rfl (5*(vectorBits words).length+3)
      (SemiprimeD1StackCopy.state 0 none (vectorBits words) [] [])
      (SemiprimeD1StackCopy.done (vectorBits words) (vectorBits words++[])) d0 d1
    · rfl
    · rfl
    · exact SemiprimeD1StackCopy.copy_words (vectorBits words) [] none
    · constructor
      · intro k; fin_cases k <;> rfl
      · intro k hk; rfl
    · constructor
      · intro k; fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,d1]
      · intro k hk
        have hr:=hk 1
        cases k <;> simp_all [copyStack,d0,d1]
  obtain ⟨copied,h1,hAt⟩:=hc [] (state (some .start) none none (vectorBits words) [] index [] [] [] [] []) ⟨rfl,rfl,rfl⟩
  have heq : copied=state (some .loop) copied.flag copied.returned (vectorBits words) (vectorBits words) index [] [] [] [] [] := by
    cases copied
    simp_all [At,state,d1]
  have h1':=h1.trans (congrArg some heq)
  exact run_append _ _ _ _ _ h1' (loop_run (vectorBits words) index words copied.flag copied.returned)

/-- Actual selected-stage time is bounded by the literal encoded input inventory. -/
theorem selectTime_le (words : List (List Bool)) : selectTime words ≤ 10*(vectorBits words).length+12 := by
  cases words with
  | nil => simp [selectTime,vectorBits]
  | cons word words =>
    simp only [selectTime,vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
    omega

/-- Actual traversal bound includes every skipped field, binary word copy and leftover index cell. -/
theorem loopTime_le (index : List Bool) (words : List (List Bool)) :
    loopTime index words ≤ 15*(vectorBits words).length+2*index.length+20 := by
  induction index generalizing words with
  | nil =>
    have h:=selectTime_le words
    simp only [loopTime,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
  | cons marker index ih =>
    cases words with
    | nil => simp [loopTime,vectorBits]; omega
    | cons word words =>
      have h:=ih words
      simp only [loopTime,List.length_cons,vectorBits,SemiprimeSourceHistogramKeyBits.frame_length]
      omega

/-- Fixed linear budget in actual encoded inventory and physical unary query size. -/
def timeBound (I i : ℕ) : ℕ := 30*(I+i+2)

/-- Closed cache read has no supplied coefficient, count, route or runtime answer. -/
theorem totalTime_le (index : List Bool) (words : List (List Bool)) :
    totalTime index words ≤ timeBound (vectorBits words).length index.length := by
  have h:=loopTime_le index words
  unfold totalTime timeBound
  omega

/-- Genuine actual transition certificate for binary coefficient acquisition. -/
def sourceRead (index : List Bool) (words : List (List Bool)) :
    StateTransition.EvalsToInTime (C.step program)
      (state (some .start) none none (vectorBits words) [] index [] [] [] [] [])
      (some (state none none none (vectorBits words) [] [] [] [] ((words[index.length]?).getD []) [] []))
      (timeBound (vectorBits words).length index.length) :=
  ⟨⟨_,source_run index words⟩,totalTime_le index words⟩

/-- Actual fixed finite-stack coefficient read with physically consumed unary query metadata. -/
def machineRead (index : List Bool) (words : List (List Bool)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (state (some .start) none none (vectorBits words) [] index [] [] [] [] []))
      (some (SemiprimeD1StackCalls.configuration
        (state none none none (vectorBits words) [] [] [] [] ((words[index.length]?).getD []) [] [])))
      (timeBound (vectorBits words).length index.length) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) Stack.cache Stack.output Label.start program _ _ _
    (sourceRead index words)

/-- Acquired bytes are exactly the original JetRingBits cached-list read, including raw padding/defaults. -/
theorem output_eq_original (index : List Bool) (words : List (List Bool)) :
    ((words[index.length]?).getD [])=(SemiprimeD1JetRingBits.read words index.length).bits :=
  (SemiprimeD1JetRingBits.read_bits words index.length).symm

/-- Every actual source prefix bounds all eight Boolean stacks and real return frames. -/
theorem prefix_cells (index : List Bool) (words : List (List Bool)) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (state (some .start) none none (vectorBits words) [] index [] [] [] [] [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 9*((vectorBits words).length+index.length+fuel) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel ((vectorBits words).length+index.length)
    _ out (by intro k; cases k <;> simp [state,store]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k:Stack,(out.data k).length) ≤ 8*((vectorBits words).length+index.length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,((vectorBits words).length+index.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = 8*((vectorBits words).length+index.length+fuel) := by
        have hc : Fintype.card Stack=8 := by decide
        simp [hc]
  omega

/-- No successful prefix survives past the actual proved cache-reader halt. -/
theorem prefix_fuel_le (index : List Bool) (words : List (List Bool)) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (state (some .start) none none (vectorBits words) [] index [] [] [] [] [])=some out) :
    fuel ≤ totalTime index words := by
  by_contra hn
  have he : fuel=totalTime index words+(1+(fuel-(totalTime index words+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : C.run program 1 (state none none none (vectorBits words) [] [] [] [] ((words[index.length]?).getD []) [] [])=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- Derived all-prefix storage bound depends only on the actual encoded operand/query sizes. -/
theorem prefix_linear_cells (index : List Bool) (words : List (List Bool)) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (state (some .start) none none (vectorBits words) [] index [] [] [] [] [])=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      9*((vectorBits words).length+index.length+timeBound (vectorBits words).length index.length) := by
  have hf:=(prefix_fuel_le index words fuel out hr).trans (totalTime_le index words)
  exact (prefix_cells index words fuel out hr).trans (by omega)

/-- The same unconditional physical-cell bound holds for actual compiled-machine prefixes. -/
theorem machine_prefix_linear_cells (index : List Bool) (words : List (List Bool)) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (state (some .start) none none (vectorBits words) [] index [] [] [] [] [])))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      9*((vectorBits words).length+index.length+timeBound (vectorBits words).length index.length) := by
  let start:=state (some .start) none none (vectorBits words) [] index [] [] [] [] []
  have he:=SemiprimeD1StackCalls.run_correct Stack.cache Stack.output Label.start program fuel start
  change (C.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:C.run program fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_linear_cells index words fuel out hc

end RiemannGaussian.SemiprimeD1StackJetReadExecution
