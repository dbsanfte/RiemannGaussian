/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackHeapReadComponents
import RiemannGaussian.SemiprimeD1StackHeapAllocate

/-! # Original allocator-history dereference execution
Every counter/reference bit and every skipped record is visited by the actual
fixed program. The logical store is used only to prove the meaning of bytes
created by the actual allocator, never as a runtime getter or read answer.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackHeapReadExecution
open SemiprimeD1StackHeapRead SemiprimeD1StackHeapReadComponents
open SemiprimeSourceHistogramKeyBits (frame)

/-- Exact physical payload at all top-level protocol boundaries. -/
def payload (heap counter reference reader depth work output valid:List Bool) : Stack→List Bool
  | .heap => heap
  | .counter => counter
  | .reference => reference
  | .reader => reader
  | .depth => depth
  | .referenceWork => work
  | .output => output
  | .valid => valid
  | _ => []

/-- Three actual included copies preserve heap/counter/reference and acquire their work copies. -/
theorem prepare (heap counter reference:List Bool) :
    Runs (5*heap.length+5*counter.length+5*reference.length+12) (.inl .start)
      (payload heap counter reference [] [] [] [] []) (.inl .afterReference)
      (payload heap counter reference heap counter reference [] []) := by
  have h0:=copy_call 0 (payload heap counter reference [] [] [] [] []) rfl
    (.inl .start) (.inl .afterHeap) rfl
  have hd0:Function.update (payload heap counter reference [] [] [] [] []) Stack.reader heap=
      payload heap counter reference heap [] [] [] []:=by funext k;cases k <;> simp [payload,Function.update]
  simp only [copyInput,copyOutput,payload,List.append_nil,ite_true] at h0
  rw [hd0] at h0
  have h1:=copy_call 1 (payload heap counter reference heap [] [] [] []) rfl
    (.inl .afterHeap) (.inl .afterCounter) rfl
  have hd1:Function.update (payload heap counter reference heap [] [] [] []) Stack.depth counter=
      payload heap counter reference heap counter [] [] []:=by funext k;cases k <;> simp [payload,Function.update]
  simp only [copyInput,copyOutput,payload,show ¬((1:Fin 3)=0) by decide,ite_false,ite_true,List.append_nil] at h1
  rw [hd1] at h1
  have h2:=copy_call 2 (payload heap counter reference heap counter [] [] []) rfl
    (.inl .afterCounter) (.inl .afterReference) rfl
  have hd2:Function.update (payload heap counter reference heap counter [] [] []) Stack.referenceWork reference=
      payload heap counter reference heap counter reference [] []:=by funext k;cases k <;> simp [payload,Function.update]
  simp only [copyInput,copyOutput,payload,show ¬((2:Fin 3)=0) by decide,
    show ¬((2:Fin 3)=1) by decide,ite_false,List.append_nil] at h2
  rw [hd2] at h2
  have h:=h0.trans (h1.trans h2)
  convert h using 1
  omega

/-- An actual pair of unary work-stack pops decreases both lengths once. -/
theorem reference_pair (heap counter reference reader depth work:List Bool) :
    Runs 2 (.inl .referenceLoop) (payload heap counter reference reader (true::depth) (true::work) [] [])
      (.inl .referenceLoop) (payload heap counter reference reader depth work [] []) := by
  have h0:Runs 1 (.inl .referenceLoop) (payload heap counter reference reader (true::depth) (true::work) [] [])
      (.inl .referenceStep) (payload heap counter reference reader (true::depth) work [] []):=by
    apply one_base _ _ (.pop .referenceWork (.inl .scan) (.inl .referenceStep) (.inl .referenceStep)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,SemiprimeD1StackBytecode.execute,payload,Function.update]
  have h1:Runs 1 (.inl .referenceStep) (payload heap counter reference reader (true::depth) work [] [])
      (.inl .referenceLoop) (payload heap counter reference reader depth work [] []):=by
    apply one_base _ _ (.pop .depth (.inl .bad) (.inl .referenceLoop) (.inl .referenceLoop)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,SemiprimeD1StackBytecode.execute,payload,Function.update]
  exact h0.trans h1

/-- The actual unary-reference loop computes the residual depth without native subtraction. -/
theorem reference_loop (i d:ℕ) (heap counter reference reader:List Bool) :
    Runs (2*i+1) (.inl .referenceLoop)
      (payload heap counter reference reader (List.replicate (i+d) true) (List.replicate i true) [] [])
      (.inl .scan) (payload heap counter reference reader (List.replicate d true) [] [] []) := by
  induction i with
  | zero =>
    apply one_base _ _ (.pop .referenceWork (.inl .scan) (.inl .referenceStep) (.inl .referenceStep)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,SemiprimeD1StackBytecode.execute,payload,Function.update]
  | succ i ih =>
    have h:=reference_pair heap counter reference reader (List.replicate (i+d) true) (List.replicate i true)
    have hh:=h.trans ih
    simpa only [Nat.succ_add,List.replicate_succ,show 2+ (2*i+1)=2*(i+1)+1 by omega] using hh

/-- Physical newest-record adjustment followed by the actual unary-reference scan. -/
theorem acquire_depth (i d:ℕ) (heap counter reference reader:List Bool) :
    Runs (2*i+2) (.inl .afterReference)
      (payload heap counter reference reader (List.replicate (i+d+1) true) (List.replicate i true) [] [])
      (.inl .scan) (payload heap counter reference reader (List.replicate d true) [] [] []) := by
  have h0:Runs 1 (.inl .afterReference)
      (payload heap counter reference reader (true::List.replicate (i+d) true) (List.replicate i true) [] [])
      (.inl .referenceLoop)
      (payload heap counter reference reader (List.replicate (i+d) true) (List.replicate i true) [] []):=by
    apply one_base _ _ (.pop .depth (.inl .bad) (.inl .referenceLoop) (.inl .referenceLoop)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,SemiprimeD1StackBytecode.execute,payload,Function.update]
  have h:=h0.trans (reference_loop i d heap counter reference reader)
  simpa only [List.replicate_succ,show 1+(2*i+1)=2*i+2 by omega] using h
/-- Parser store refinement for the bytes actually written by the allocator. -/
theorem parsed_frame (heap counter reference word tail depth work valid:List Bool) :
    parsed (payload heap counter reference (frame word tail) depth work [] valid)=
      payload heap counter reference tail depth work word (true::valid) := by
  have h:=SemiprimeSourceHistogramKeyBits.split_frame word tail
  funext k
  cases k <;> simp [parsed,payload,h.1,h.2.1,h.2.2]

/-- Actual included parser call on a real frame, with no supplied parse answer. -/
theorem parse_field (heap counter reference word tail depth work valid:List Bool)
    (pc next:Label) (hcall:program pc=.call (fieldLabel (Field.active .tagPop (none,false))) next) :
    Runs (8*word.length+7) pc (payload heap counter reference (frame word tail) depth work [] valid)
      next (payload heap counter reference tail depth work word (true::valid)) := by
  have h:=field_call (payload heap counter reference (frame word tail) depth work [] valid) rfl rfl pc next hcall
  rw [parsed_frame] at h
  simpa only [payload,SemiprimeD1TensorTapeFieldBounds.fieldSteps_frame] using h

/-- Every skipped field's actual copied bits are physically popped. -/
theorem clear_skipped (word heap counter reference reader depth work:List Bool) :
    Runs (word.length+1) (.inl .clearSkipped) (payload heap counter reference reader depth work word [])
      (.inl .scan) (payload heap counter reference reader depth work [] []) := by
  induction word with
  | nil =>
    apply one_base _ _ (.pop .output (.inl .scan) (.inl .clearSkipped) (.inl .clearSkipped)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,payload,Function.update]
  | cons bit word ih =>
    have h0:Runs 1 (.inl .clearSkipped) (payload heap counter reference reader depth work (bit::word) [])
        (.inl .clearSkipped) (payload heap counter reference reader depth work word []):=by
      apply one_base _ _ (.pop .output (.inl .scan) (.inl .clearSkipped) (.inl .clearSkipped)) _ _ rfl
      · cases bit <;> rfl
      · funext k;cases k <;> simp [B.execute,payload,Function.update]
    have h:=h0.trans ih
    convert h using 1
    simp only [List.length_cons]
    omega

/-- The final reader suffix is physically cleared, preserving heap and returned record. -/
theorem clear_reader (reader heap counter reference output:List Bool) :
    Runs (reader.length+1) (.inl .clearReader) (payload heap counter reference reader [] [] output [true])
      (.inl .halt) (payload heap counter reference [] [] [] output [true]) := by
  induction reader with
  | nil =>
    apply one_base _ _ (.pop .reader (.inl .halt) (.inl .clearReader) (.inl .clearReader)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,payload,Function.update]
  | cons bit reader ih =>
    have h0:Runs 1 (.inl .clearReader) (payload heap counter reference (bit::reader) [] [] output [true])
        (.inl .clearReader) (payload heap counter reference reader [] [] output [true]):=by
      apply one_base _ _ (.pop .reader (.inl .halt) (.inl .clearReader) (.inl .clearReader)) _ _ rfl
      · cases bit <;> rfl
      · funext k;cases k <;> simp [B.execute,payload,Function.update]
    have h:=h0.trans ih
    convert h using 1
    simp only [List.length_cons]
    omega

/-- Physical newest-first framing of a finite record list with an existing byte tail. -/
def tape (records:List (List Bool)) (tail:List Bool) : List Bool := records.foldr frame tail

/-- Exact executed scan budget; no native budget is an instruction operand. -/
def scanTime : List (List Bool)→ℕ
  | [] => 1
  | word::words => 9*word.length+10+scanTime words

/-- Actual skip loop scans, verifies and clears each newer allocator-produced record. -/
theorem scan_fields (newer:List (List Bool)) (tail heap counter reference:List Bool) :
    Runs (scanTime newer) (.inl .scan)
      (payload heap counter reference (tape newer tail) (List.replicate newer.length true) [] [] [])
      (.inl .finalCall) (payload heap counter reference tail [] [] [] []) := by
  induction newer with
  | nil =>
    apply one_base _ _ (.pop .depth (.inl .finalCall) (.inl .skipCall) (.inl .skipCall)) _ _ rfl
    · rfl
    · funext k;cases k <;> simp [B.execute,payload,tape,Function.update]
  | cons word newer ih =>
    let rest:=tape newer tail
    let depth:=List.replicate newer.length true
    have h0:Runs 1 (.inl .scan) (payload heap counter reference (frame word rest) (true::depth) [] [] [])
        (.inl .skipCall) (payload heap counter reference (frame word rest) depth [] [] []):=by
      apply one_base _ _ (.pop .depth (.inl .finalCall) (.inl .skipCall) (.inl .skipCall)) _ _ rfl
      · rfl
      · funext k;cases k <;> simp [B.execute,payload,Function.update]
    have h1:=parse_field heap counter reference word rest depth [] [] (.inl .skipCall) (.inl .afterSkip) rfl
    have h2:Runs 1 (.inl .afterSkip) (payload heap counter reference rest depth [] word [true])
        (.inl .clearSkipped) (payload heap counter reference rest depth [] word []):=by
      apply one_base _ _ (.pop .valid (.inl .bad) (.inl .bad) (.inl .clearSkipped)) _ _ rfl
      · rfl
      · funext k;cases k <;> simp [B.execute,payload,Function.update]
    have h3:=clear_skipped word heap counter reference rest depth []
    have h:=h0.trans (h1.trans (h2.trans (h3.trans ih)))
    change Runs (scanTime (word::newer)) (.inl .scan)
      (payload heap counter reference (frame word rest) (List.replicate (newer.length+1) true) [] [] [])
      (.inl .finalCall) (payload heap counter reference tail [] [] [] [])
    rw [List.replicate_succ]
    convert h using 1
    simp only [scanTime]
    omega

/-- Actual final parse, validity inspection and complete reader clearing. -/
theorem final_field (word older heap counter reference:List Bool) :
    Runs (8*word.length+older.length+9) (.inl .finalCall)
      (payload heap counter reference (frame word older) [] [] [] [])
      (.inl .halt) (payload heap counter reference [] [] [] word [true]) := by
  have h0:=parse_field heap counter reference word older [] [] [] (.inl .finalCall) (.inl .afterFinal) rfl
  have h1:Runs 1 (.inl .afterFinal) (payload heap counter reference older [] [] word [true])
      (.inl .clearReader) (payload heap counter reference older [] [] word [true]):=by
    apply one_base _ _ (.peek .valid (.inl .bad) (.inl .bad) (.inl .clearReader)) _ _ rfl
    · rfl
    · rfl
  have h2:=clear_reader older heap counter reference word
  have h:=h0.trans (h1.trans h2)
  convert h using 1
  omega
/-- Actual allocator bytes expose newer records in newest-first order. -/
theorem heap_decomposition (before:List (List Bool)) (word:List Bool) (after:List (List Bool)) :
    SemiprimeD1StackHeapAllocate.heapBytes (before++word::after)=
      tape after.reverse (frame word (SemiprimeD1StackHeapAllocate.heapBytes before)) := by
  simp only [SemiprimeD1StackHeapAllocate.heapBytes,List.foldl_append,List.foldl_cons,tape,List.foldr_reverse]

/-- Exact executed dereference time, assembled from actual component and local-loop costs. -/
def readTime (before:List (List Bool)) (word:List Bool) (after:List (List Bool)) : ℕ :=
  let heap:=SemiprimeD1StackHeapAllocate.heapBytes (before++word::after)
  (5*heap.length+5*(before++word::after).length+5*before.length+12)+
    ((2*before.length+2)+(scanTime after.reverse+
      (8*word.length+(SemiprimeD1StackHeapAllocate.heapBytes before).length+9)))+1

/-- Exact actual successful heap-read output, with every work stack cleared. -/
def done (heap counter reference word:List Bool) : C.State Stack Label :=
  ⟨none,none,none,payload heap counter reference [] [] [] word [true],[]⟩

/-- Exact actual dereference of a record in the original allocator's append order. -/
theorem read_split (before:List (List Bool)) (word:List Bool) (after:List (List Bool)) :
    C.run program (readTime before word after)
      (initial (SemiprimeD1StackHeapAllocate.heapBytes (before++word::after))
        (List.replicate (before++word::after).length true) (List.replicate before.length true))=
      some (done (SemiprimeD1StackHeapAllocate.heapBytes (before++word::after))
        (List.replicate (before++word::after).length true) (List.replicate before.length true) word) := by
  let heap:=SemiprimeD1StackHeapAllocate.heapBytes (before++word::after)
  let counter:=List.replicate (before++word::after).length true
  let reference:=List.replicate before.length true
  have h0:=prepare heap counter reference
  have h1:=acquire_depth before.length after.length heap counter reference heap
  have hc:counter=List.replicate (before.length+after.length+1) true:=by
    dsimp only [counter]
    congr 1
    simp only [List.length_append,List.length_cons]
    omega
  have hd:List.replicate after.length true=List.replicate after.reverse.length true:=by simp
  rw [←hc,hd] at h1
  have hheap:heap=tape after.reverse (frame word (SemiprimeD1StackHeapAllocate.heapBytes before)):=
    heap_decomposition before word after
  have h2:=scan_fields after.reverse (frame word (SemiprimeD1StackHeapAllocate.heapBytes before)) heap counter reference
  rw [←hheap] at h2
  have h3:=final_field word (SemiprimeD1StackHeapAllocate.heapBytes before) heap counter reference
  have h:=h0.trans (h1.trans (h2.trans h3))
  let time:=(5*heap.length+5*counter.length+5*reference.length+12)+
    ((2*before.length+2)+(scanTime after.reverse+
      (8*word.length+(SemiprimeD1StackHeapAllocate.heapBytes before).length+9)))
  have hs:At (.inl .start) (payload heap counter reference [] [] [] [] []) [] (initial heap counter reference):=by
    refine ⟨rfl,?_,rfl⟩
    funext k;cases k <;> rfl
  obtain ⟨finish,hfinish,hout⟩:=h [] (initial heap counter reference) hs
  have he:time+1=readTime before word after:=by
    simp only [time,readTime,counter,reference,heap,List.length_replicate]
  rw [←he,SemiprimeD1StackReturnLink.run_add]
  change (C.run program time (initial heap counter reference)).bind (C.run program 1)=_
  have ht:time=(5*heap.length+5*counter.length+5*reference.length+12)+
      ((2*before.length+2)+(scanTime after.reverse+
        (8*word.length+(SemiprimeD1StackHeapAllocate.heapBytes before).length+9))):=rfl
  rw [ht,hfinish,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step program finish=some (done heap counter reference word)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,
    hdata,hframes,done]
end RiemannGaussian.SemiprimeD1StackHeapReadExecution
