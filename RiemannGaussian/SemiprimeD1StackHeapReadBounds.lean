/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackHeapReadExecution

/-! # Actual allocator-history heap dereference resources
Original record bytes and unary references determine the executed scan. The
proof derives field validity from allocator writes, and actual transition and
prefix-space bounds from the literal linked program, without a read oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackHeapReadBounds
open SemiprimeD1StackHeapRead SemiprimeD1StackHeapReadExecution

/-- Proof-side total record payload, used only to bound actual serialized bytes. -/
def wordMass (records:List (List Bool)) : ℕ := (records.map List.length).sum

/-- Every allocator frame contributes its literal tags, data and delimiter. -/
theorem heap_length (records:List (List Bool)) :
    (SemiprimeD1StackHeapAllocate.heapBytes records).length=2*wordMass records+records.length := by
  have h (records:List (List Bool)) (tail:List Bool) :
      (records.foldl (fun bytes record=>SemiprimeSourceHistogramKeyBits.frame record bytes) tail).length=
        tail.length+2*wordMass records+records.length := by
    induction records generalizing tail with
    | nil => simp [wordMass]
    | cons word records ih =>
      rw [List.foldl_cons,ih,SemiprimeSourceHistogramKeyBits.frame_length]
      simp only [wordMass,List.map_cons,List.sum_cons,List.length_cons]
      omega
  simpa only [SemiprimeD1StackHeapAllocate.heapBytes,List.length_nil,Nat.zero_add] using h records []

/-- Reversing actual record order preserves total physical data length. -/
theorem wordMass_reverse (records:List (List Bool)) : wordMass records.reverse=wordMass records := by
  simp [wordMass]

/-- The actual skip-loop transition count includes every parsed/copied/cleared bit. -/
theorem scanTime_eq (records:List (List Bool)) :
    scanTime records=9*wordMass records+10*records.length+1 := by
  induction records with
  | nil => rfl
  | cons word records ih =>
    simp only [scanTime,wordMass,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    omega

/-- Actual full dereference time is linear in heap, counter and reference lengths. -/
theorem readTime_le (before:List (List Bool)) (word:List Bool) (after:List (List Bool)) :
    readTime before word after ≤
      25*((SemiprimeD1StackHeapAllocate.heapBytes (before++word::after)).length+
        (before++word::after).length+before.length+1) := by
  have hm:wordMass (before++word::after)=wordMass before+word.length+wordMass after:=by
    simp only [wordMass,List.map_append,List.map_cons,List.sum_append,List.sum_cons]
    omega
  unfold readTime
  rw [scanTime_eq,wordMass_reverse,List.length_reverse]
  simp only [heap_length,hm,List.length_append,List.length_cons]
  omega

/-- Finite original reference split; its record is read from the original store, not an answer parameter. -/
theorem split_at (records:List (List Bool)) (i:Fin records.length) :
    records.take i.val++records[i.val]::records.drop (i.val+1)=records := by
  rw [←List.drop_eq_getElem_cons i.isLt,List.take_append_drop]

/-- Actual exact transition count at a finite allocator-issued ordinal. -/
def readTimeAt (records:List (List Bool)) (i:Fin records.length) : ℕ :=
  readTime (records.take i.val) records[i.val] (records.drop (i.val+1))

/-- Whole fixed program returns the actual indexed record and preserves the original heap. -/
theorem read_run (records:List (List Bool)) (i:Fin records.length) :
    C.run program (readTimeAt records i)
      (initial (SemiprimeD1StackHeapAllocate.heapBytes records) (List.replicate records.length true)
        (List.replicate i.val true))=
      some (done (SemiprimeD1StackHeapAllocate.heapBytes records) (List.replicate records.length true)
        (List.replicate i.val true) records[i.val]) := by
  have h:=read_split (records.take i.val) records[i.val] (records.drop (i.val+1))
  have ht:(records.take i.val).length=i.val:=by
    simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  rw [split_at records i,ht] at h
  exact h

/-- Closed actual transition cap, with no supplied getter or cost estimate. -/
theorem readTimeAt_le (records:List (List Bool)) (i:Fin records.length) :
    readTimeAt records i ≤25*((SemiprimeD1StackHeapAllocate.heapBytes records).length+records.length+i.val+1) := by
  have h:=readTime_le (records.take i.val) records[i.val] (records.drop (i.val+1))
  have ht:(records.take i.val).length=i.val:=by
    simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  rw [split_at records i,ht] at h
  exact h

/-- Genuine finite-machine heap read, from actual physical allocator data. -/
def readInTime (records:List (List Bool)) (i:Fin records.length) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (SemiprimeD1StackHeapAllocate.heapBytes records) (List.replicate records.length true)
          (List.replicate i.val true)))
      (some (SemiprimeD1StackCalls.configuration
        (done (SemiprimeD1StackHeapAllocate.heapBytes records) (List.replicate records.length true)
          (List.replicate i.val true) records[i.val])))
      (25*((SemiprimeD1StackHeapAllocate.heapBytes records).length+records.length+i.val+1)) := by
  apply SemiprimeD1StackCalls.evalsCorrect Stack.heap Stack.output (.inl .start) program
  exact ⟨⟨readTimeAt records i,read_run records i⟩,readTimeAt_le records i⟩

/-- An actual allocation history starts empty and records real allocator transitions. -/
inductive History : List (List Bool)→List Bool→List Bool→Prop where
  /-- Empty physical heap and counter require no constructor advice. -/
  | empty : History [] [] []
  /-- The successor heap/counter are read from an actual executed allocator result. -/
  | step {records:List (List Bool)} {heap counter:List Bool} (prev:History records heap counter)
      (word:List Bool) (out:SemiprimeD1StackBytecode.State (Fin 6) (Fin 22))
      (executed:SemiprimeD1StackBytecode.run SemiprimeD1StackHeapAllocate.code
        (5*counter.length+6*word.length+7)
        (SemiprimeD1StackHeapAllocate.state 0 none word heap [] counter [] [])=some out) :
      History (records++[word]) (out.store 1) (out.store 3)

/-- Well-formed framing and exact unary counter are derived from the executed allocation history. -/
theorem History.fields {records:List (List Bool)} {heap counter:List Bool} (h:History records heap counter) :
    heap=SemiprimeD1StackHeapAllocate.heapBytes records ∧ counter=List.replicate records.length true := by
  induction h with
  | empty => exact ⟨rfl,rfl⟩
  | @step records heap counter prev word out executed ih =>
    have hr:=SemiprimeD1StackHeapAllocate.allocate_run word heap counter none
    have hout:out=SemiprimeD1StackHeapAllocate.done word (SemiprimeSourceHistogramKeyBits.frame word heap)
        (true::counter) counter:=Option.some.inj (executed.symm.trans hr)
    subst out
    simp only [SemiprimeD1StackHeapAllocate.done,SemiprimeD1StackHeapAllocate.payload,
      show (1:Fin 6)≠0 by decide,ite_false,ite_true,
      show (3:Fin 6)≠0 by decide,show (3:Fin 6)≠1 by decide,show (3:Fin 6)≠2 by decide]
    rw [ih.1,ih.2,SemiprimeD1StackHeapAllocate.heapBytes_append]
    simp only [List.length_append,List.length_cons,List.length_nil,List.replicate_succ,and_self]

/-- History extension itself is acquired by the actual allocator, rather than assumed heap values. -/
theorem History.allocate {records:List (List Bool)} {heap counter:List Bool}
    (h:History records heap counter) (word:List Bool) :
    History (records++[word]) (SemiprimeSourceHistogramKeyBits.frame word heap) (true::counter) := by
  exact History.step h word _ (SemiprimeD1StackHeapAllocate.allocate_run word heap counter none)

/-- Original-history endpoint derives all framing/count facts before the actual read. -/
def readHistoryInTime {records:List (List Bool)} {heap counter:List Bool}
    (history:History records heap counter) (i:Fin records.length) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial heap counter (List.replicate i.val true)))
      (some (SemiprimeD1StackCalls.configuration (done heap counter (List.replicate i.val true) records[i.val])))
      (25*(heap.length+counter.length+i.val+1)) := by
  obtain ⟨rfl,rfl⟩:=history.fields
  simpa only [List.length_replicate] using readInTime records i
/-- Every literal-program prefix bounds each real Boolean data stack. -/
theorem prefix_data_bound (heap counter reference:List Bool) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial heap counter reference)=some out) :
    ∀k,(out.data k).length ≤ heap.length+counter.length+reference.length+fuel := by
  apply SemiprimeD1StackReturnLink.run_data_bound program fuel
    (heap.length+counter.length+reference.length) _ out ?_ hr
  intro k
  cases k <;> simp [initial,input] <;> omega

/-- Count every actual Boolean data and fixed-alphabet return-frame cell at every prefix. -/
theorem prefix_cells (heap counter reference:List Bool) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial heap counter reference)=some out) :
    (out.data .heap).length+(out.data .counter).length+(out.data .reference).length+
      (out.data .reader).length+(out.data .depth).length+(out.data .referenceWork).length+
      (out.data .temporary).length+(out.data .fieldScratch).length+(out.data .output).length+
      (out.data .valid).length+out.frames.length ≤11*(heap.length+counter.length+reference.length+fuel) := by
  have h:=prefix_data_bound heap counter reference fuel out hr
  have h0:=h .heap
  have h1:=h .counter
  have h2:=h .reference
  have h3:=h .reader
  have h4:=h .depth
  have h5:=h .referenceWork
  have h6:=h .temporary
  have h7:=h .fieldScratch
  have h8:=h .output
  have h9:=h .valid
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial heap counter reference) out hr
  change out.frames.length ≤ 0+fuel at hf
  omega

/-- Actual successful execution cannot resume after a halted state. -/
theorem run_halted (n:ℕ) (state:C.State Stack Label) (hpc:state.pc=none) :
    C.run program (n+1) state=none := by
  unfold C.run
  rw [Function.iterate_succ_apply]
  have hs:C.step program state=none:=by simp [C.step,SemiprimeD1StackCalls.step,hpc]
  simp only [Option.bind_some,hs]
  exact Function.iterate_fixed rfl n

/-- A successful actual prefix cannot extend past a proved actual halt. -/
theorem fuel_le_halt (time fuel:ℕ) (state finish out:C.State Stack Label)
    (hh:C.run program time state=some finish) (hp:finish.pc=none)
    (hr:C.run program fuel state=some out) : fuel ≤ time := by
  by_contra h
  have ht:fuel=time+((fuel-time-1)+1):=by omega
  rw [ht,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,run_halted _ finish hp] at hr
  cases hr

/-- The actual well-formed heap-read machine has linear all-visited storage, including return frames. -/
theorem machine_space (records:List (List Bool)) (i:Fin records.length) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (SemiprimeD1StackHeapAllocate.heapBytes records) (List.replicate records.length true)
          (List.replicate i.val true))))=some cfg) :
    (cfg.stk (some Stack.heap)).length+(cfg.stk (some Stack.counter)).length+
      (cfg.stk (some Stack.reference)).length+(cfg.stk (some Stack.reader)).length+
      (cfg.stk (some Stack.depth)).length+(cfg.stk (some Stack.referenceWork)).length+
      (cfg.stk (some Stack.temporary)).length+(cfg.stk (some Stack.fieldScratch)).length+
      (cfg.stk (some Stack.output)).length+(cfg.stk (some Stack.valid)).length+(cfg.stk none).length ≤
      286*((SemiprimeD1StackHeapAllocate.heapBytes records).length+records.length+i.val+1) := by
  let state:=initial (SemiprimeD1StackHeapAllocate.heapBytes records) (List.replicate records.length true)
    (List.replicate i.val true)
  have he:=SemiprimeD1StackCalls.run_correct Stack.heap Stack.output (.inl .start) program fuel state
  change (C.run program fuel state).map SemiprimeD1StackCalls.configuration=
    (fun cfg=>cfg.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration state)) at he
  cases hc:C.run program fuel state with
  | none => rw [hc,hr] at he;cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj he
    rw [←hcfg]
    have hspace:=prefix_cells (SemiprimeD1StackHeapAllocate.heapBytes records)
      (List.replicate records.length true) (List.replicate i.val true) fuel out hc
    have hf:=fuel_le_halt (readTimeAt records i) fuel state _ out (read_run records i) rfl hc
    have ht:=readTimeAt_le records i
    simp only [List.length_replicate] at hspace
    change (out.data .heap).length+(out.data .counter).length+(out.data .reference).length+
      (out.data .reader).length+(out.data .depth).length+(out.data .referenceWork).length+
      (out.data .temporary).length+(out.data .fieldScratch).length+(out.data .output).length+
      (out.data .valid).length+out.frames.length ≤ _
    omega

/-- Issued references originate in an actual allocator result, then persist across appends. -/
inductive Issued : List (List Bool)→List Bool→Prop where
  /-- The reference bytes are read from the actual allocator's returned pointer stack. -/
  | fresh {records:List (List Bool)} {heap counter:List Bool} (prev:History records heap counter)
      (word:List Bool) (out:SemiprimeD1StackBytecode.State (Fin 6) (Fin 22))
      (executed:SemiprimeD1StackBytecode.run SemiprimeD1StackHeapAllocate.code
        (5*counter.length+6*word.length+7)
        (SemiprimeD1StackHeapAllocate.state 0 none word heap [] counter [] [])=some out) :
      Issued (records++[word]) (out.store 4)
  /-- The actual append-only allocator preserves every previously issued reference. -/
  | keep {records:List (List Bool)} {reference:List Bool} (prev:Issued records reference)
      (word:List Bool) : Issued (records++[word]) reference

/-- Unary form and index validity are derived from actual reference issuance. -/
theorem Issued.valid {records:List (List Bool)} {reference:List Bool} (h:Issued records reference) :
    reference=List.replicate reference.length true ∧ reference.length < records.length := by
  induction h with
  | @fresh records heap counter prev word out executed =>
    have hr:=SemiprimeD1StackHeapAllocate.allocate_run word heap counter none
    have hout:out=SemiprimeD1StackHeapAllocate.done word (SemiprimeSourceHistogramKeyBits.frame word heap)
        (true::counter) counter:=Option.some.inj (executed.symm.trans hr)
    subst out
    have hc:=prev.fields.2
    simp only [SemiprimeD1StackHeapAllocate.done,SemiprimeD1StackHeapAllocate.payload,
      show (4:Fin 6)≠0 by decide,show (4:Fin 6)≠1 by decide,show (4:Fin 6)≠2 by decide,
      show (4:Fin 6)≠3 by decide,ite_false,ite_true]
    rw [hc]
    simp only [List.length_replicate,List.length_append,List.length_cons,List.length_nil]
    exact ⟨trivial,by omega⟩
  | @keep records reference prev word ih =>
    refine ⟨ih.1,?_⟩
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega

/-- Final original-history/issued-reference endpoint: no desired record or validity answer input. -/
def readIssuedInTime {records:List (List Bool)} {heap counter reference:List Bool}
    (history:History records heap counter) (issued:Issued records reference) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial heap counter reference))
      (some (SemiprimeD1StackCalls.configuration
        (done heap counter reference (records.get ⟨reference.length,issued.valid.2⟩))))
      (25*(heap.length+counter.length+reference.length+1)) := by
  have href:=issued.valid.1
  have h:=readHistoryInTime history (⟨reference.length,issued.valid.2⟩:Fin records.length)
  simpa only [←href,List.get_eq_getElem] using h
/-- Actual allocator histories and issued bytes close the all-visited memory bound directly. -/
theorem machine_history_space {records:List (List Bool)} {heap counter reference:List Bool}
    (history:History records heap counter) (issued:Issued records reference)
    (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial heap counter reference)))=some cfg) :
    (cfg.stk (some Stack.heap)).length+(cfg.stk (some Stack.counter)).length+
      (cfg.stk (some Stack.reference)).length+(cfg.stk (some Stack.reader)).length+
      (cfg.stk (some Stack.depth)).length+(cfg.stk (some Stack.referenceWork)).length+
      (cfg.stk (some Stack.temporary)).length+(cfg.stk (some Stack.fieldScratch)).length+
      (cfg.stk (some Stack.output)).length+(cfg.stk (some Stack.valid)).length+(cfg.stk none).length ≤
      286*(heap.length+counter.length+reference.length+1) := by
  obtain ⟨rfl,rfl⟩:=history.fields
  have href:=issued.valid.1
  have h:=machine_space records (⟨reference.length,issued.valid.2⟩:Fin records.length) fuel cfg
    (by simpa only [←href] using hr)
  simpa only [List.length_replicate] using h
end RiemannGaussian.SemiprimeD1StackHeapReadBounds
