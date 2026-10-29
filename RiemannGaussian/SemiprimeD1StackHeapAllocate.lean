/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFrame

/-! # Actual stable-reference framed heap allocation
The fixed program copies the unary allocation counter, increments that actual
counter, and writes the supplied Boolean record. Numerical record contents
remain binary. Oldest-first logical addresses survive newest-first physical
framing; no native allocator or list operation is a machine instruction.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackHeapAllocate
open SemiprimeD1StackBytecode
open SemiprimeD1StackCopy (run_add)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Fixed allocation program, before every record, address and heap input. -/
def code (label:Fin 22) : Instruction (Fin 6) (Fin 22) :=
  if label=0 then .pop 3 3 1 2
  else if label=1 then .push 5 false 0
  else if label=2 then .push 5 true 0
  else if label=3 then .pop 5 10 4 5
  else if label=4 then .push 3 false 7
  else if label=5 then .push 3 true 8
  else if label=7 then .push 4 false 3
  else if label=8 then .push 4 true 3
  else if label=10 then .push 3 true 11
  else if label=11 then .pop 0 14 12 13
  else if label=12 then .push 2 false 11
  else if label=13 then .push 2 true 11
  else if label=14 then .push 1 false 15
  else if label=15 then .pop 2 21 16 17
  else if label=16 then .push 0 false 18
  else if label=17 then .push 0 true 19
  else if label=18 then .push 1 false 20
  else if label=19 then .push 1 true 20
  else if label=20 then .push 1 true 15
  else .halt

/-- Actual record, heap, record-scratch, counter, reference and counter-scratch stacks. -/
def payload (record heap scratch counter reference temporary:List Bool) : Fin 6→List Bool :=
  fun k=>if k=0 then record else if k=1 then heap else if k=2 then scratch
    else if k=3 then counter else if k=4 then reference else temporary

/-- State at an actual fixed allocation label. -/
def state (label:Fin 22) (flag:Option Bool)
    (record heap scratch counter reference temporary:List Bool) : State (Fin 6) (Fin 22) :=
  ⟨some label,flag,payload record heap scratch counter reference temporary⟩

/-- Actual clean allocation return, with two empty scratch stacks. -/
def done (record heap counter reference:List Bool) : State (Fin 6) (Fin 22) :=
  ⟨none,none,payload record heap [] counter reference []⟩

/-- Physical first counter loop, one actual bit at a time. -/
theorem counter_move_bit (b:Bool) (rec hp rs cs ptr tmp:List Bool) (flag:Option Bool) :
    run code 2 (state 0 flag rec hp rs (b::cs) ptr tmp)=
      some (state 0 (some b) rec hp rs cs ptr (b::tmp)) := by
  cases b <;> simp [run,Function.iterate_succ_apply,step,execute,code,state,payload,
    choose,Function.update] <;> funext k <;> fin_cases k <;> rfl

/-- Physical second counter loop restores and copies one actual bit. -/
theorem counter_copy_bit (b:Bool) (rec hp rs cs ptr tmp:List Bool) (flag:Option Bool) :
    run code 3 (state 3 flag rec hp rs cs ptr (b::tmp))=
      some (state 3 (some b) rec hp rs (b::cs) (b::ptr) tmp) := by
  cases b <;> simp [run,Function.iterate_succ_apply,step,execute,code,state,payload,
    choose,Function.update] <;> funext k <;> fin_cases k <;> rfl

/-- The actual counter move loop, including its empty branch. -/
theorem counter_move (cs rec hp rs ptr tmp:List Bool) (flag:Option Bool) :
    run code (2*cs.length+1) (state 0 flag rec hp rs cs ptr tmp)=
      some (state 3 none rec hp rs [] ptr (cs.reverse++tmp)) := by
  induction cs generalizing tmp flag with
  | nil => simp [run,step,execute,code,state,payload,choose]
  | cons b cs ih =>
    rw [show 2*(b::cs).length+1=2+(2*cs.length+1) by simp; omega,run_add,counter_move_bit]
    simp only [Option.bind_some]
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

/-- The actual counter-copy loop stops at the literal increment instruction. -/
theorem counter_copy (tmp rec hp rs cs ptr:List Bool) (flag:Option Bool) :
    run code (3*tmp.length+1) (state 3 flag rec hp rs cs ptr tmp)=
      some (state 10 none rec hp rs (tmp.reverse++cs) (tmp.reverse++ptr) []) := by
  induction tmp generalizing cs ptr flag with
  | nil => simp [run,step,execute,code,state,payload,choose]
  | cons b tmp ih =>
    rw [show 3*(b::tmp).length+1=3+(3*tmp.length+1) by simp; omega,run_add,counter_copy_bit]
    simp only [Option.bind_some]
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

/-- Actual acquired counter copy; the old ordinal is not supplied as an answer. -/
theorem counter_run (cs rec hp rs ptr:List Bool) (flag:Option Bool) :
    run code (5*cs.length+2) (state 0 flag rec hp rs cs ptr [])=
      some (state 10 none rec hp rs cs (cs++ptr) []) := by
  rw [show 5*cs.length+2=(2*cs.length+1)+(3*cs.reverse.length+1) by simp; omega,run_add,counter_move]
  simp only [List.append_nil,Option.bind_some]
  rw [counter_copy,List.reverse_reverse,List.append_nil]

/-- Actual record move instruction pair, preserving counter and returned reference. -/
theorem record_move_bit (b:Bool) (rec hp rs cs ptr tmp:List Bool) (flag:Option Bool) :
    run code 2 (state 11 flag (b::rec) hp rs cs ptr tmp)=
      some (state 11 (some b) rec hp (b::rs) cs ptr tmp) := by
  cases b <;> simp [run,Function.iterate_succ_apply,step,execute,code,state,payload,
    choose,Function.update] <;> funext k <;> fin_cases k <;> rfl

/-- Actual framed record-bit construction, including continuation tag. -/
theorem record_copy_bit (b:Bool) (rec hp rs cs ptr tmp:List Bool) (flag:Option Bool) :
    run code 4 (state 15 flag rec hp (b::rs) cs ptr tmp)=
      some (state 15 (some b) (b::rec) (true::b::hp) rs cs ptr tmp) := by
  cases b <;> simp [run,Function.iterate_succ_apply,step,execute,code,state,payload,
    choose,Function.update] <;> funext k <;> fin_cases k <;> rfl

/-- Full actual record move, with every input bit visited. -/
theorem record_move (rec hp rs cs ptr tmp:List Bool) (flag:Option Bool) :
    run code (2*rec.length+1) (state 11 flag rec hp rs cs ptr tmp)=
      some (state 14 none [] hp (rec.reverse++rs) cs ptr tmp) := by
  induction rec generalizing rs flag with
  | nil => simp [run,step,execute,code,state,payload,choose]
  | cons b rec ih =>
    rw [show 2*(b::rec).length+1=2+(2*rec.length+1) by simp; omega,run_add,record_move_bit]
    simp only [Option.bind_some]
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

/-- Record restoration and writing are actual loop execution, not frame evaluation. -/
theorem record_copy (rs rec hp cs ptr:List Bool) (flag:Option Bool) :
    run code (4*rs.length+2) (state 15 flag rec hp rs cs ptr [])=
      some (done (rs.reverse++rec) (rs.reverse.foldr (fun b rest=>true::b::rest) hp) cs ptr) := by
  induction rs generalizing rec hp flag with
  | nil => simp [run,Function.iterate_succ_apply,step,execute,code,state,done,payload,choose,Function.update]
  | cons b rs ih =>
    rw [show 4*(b::rs).length+2=4+(4*rs.length+2) by simp; omega,run_add,record_copy_bit]
    simp only [Option.bind_some]
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append,List.foldr_append,List.foldr_cons,List.foldr_nil]

/-- Actual physical record acquisition with an already computed counter/reference. -/
theorem record_run (rec hp cs ptr:List Bool) (flag:Option Bool) :
    run code (6*rec.length+4) (state 11 flag rec hp [] cs ptr [])=
      some (done rec (frame rec hp) cs ptr) := by
  rw [show 6*rec.length+4=(2*rec.length+1)+(1+(4*rec.reverse.length+2)) by simp; omega,run_add,record_move]
  simp only [List.append_nil,Option.bind_some]
  rw [run_add]
  have hs:run code 1 (state 14 none [] hp rec.reverse cs ptr [])=
      some (state 15 none [] (false::hp) rec.reverse cs ptr []):=by
    simp [run,step,execute,code,state,payload]
    funext k
    fin_cases k <;> rfl
  rw [hs,Option.bind_some,record_copy,List.reverse_reverse,List.append_nil,SemiprimeD1StackFrame.frame_fold]

/-- Complete actual allocation: physically copied old counter, real increment and record write. -/
theorem allocate_run (rec hp cs:List Bool) (flag:Option Bool) :
    run code (5*cs.length+6*rec.length+7) (state 0 flag rec hp [] cs [] [])=
      some (done rec (frame rec hp) (true::cs) cs) := by
  rw [show 5*cs.length+6*rec.length+7=(5*cs.length+2)+(1+(6*rec.length+4)) by omega,run_add,counter_run]
  simp only [List.append_nil,Option.bind_some]
  rw [run_add]
  have hs:run code 1 (state 10 none rec hp [] cs cs [])=
      some (state 11 none rec hp [] (true::cs) cs []):=by
    simp [run,step,execute,code,state,payload]
    funext k
    fin_cases k <;> rfl
  rw [hs,Option.bind_some,record_run]

/-- One fixed actual finite allocator machine, independent of all records and heaps. -/
def machine : Turing.FinTM2 := SemiprimeD1StackBytecode.machine 0 4 0 code

/-- Actual finite-machine allocation certificate, charging each executed stack operation. -/
def allocateInTime (rec hp cs:List Bool) (flag:Option Bool) :
    StateTransition.EvalsToInTime machine.step (configuration (state 0 flag rec hp [] cs [] []))
      (some (configuration (done rec (frame rec hp) (true::cs) cs)))
      (5*cs.length+6*rec.length+7) := by
  apply evalsCorrect 0 4 0 code
  exact ⟨⟨5*cs.length+6*rec.length+7,allocate_run rec hp cs flag⟩,le_refl _⟩
/-- Mathematical bytes of an oldest-first append-only logical store. -/
def heapBytes (records:List (List Bool)) : List Bool :=
  records.foldl (fun bytes record=>frame record bytes) []

/-- Logical append is exactly the physical newest-first framed write. -/
theorem heapBytes_append (records:List (List Bool)) (record:List Bool) :
    heapBytes (records++[record])=frame record (heapBytes records) := by
  simp only [heapBytes,List.foldl_append,List.foldl_cons,List.foldl_nil]

/-- An old ordinal reference keeps exactly the same meaning after allocation. -/
theorem old_reference_stable (records:List (List Bool)) (record:List Bool) (address:ℕ)
    (h:address < records.length) : (records++[record])[address]?=records[address]? :=
  List.getElem?_append_left h

/-- The physically acquired reference denotes the newly appended record. -/
theorem new_reference (records:List (List Bool)) (record:List Bool) :
    (records++[record])[records.length]?=some record := by
  simp only [List.getElem?_append_right (le_refl _),Nat.sub_self,List.getElem?_cons_zero]

/-- Original heap/counter invariant is preserved by actual allocation, with no encoded answer input. -/
theorem allocate_heap (records:List (List Bool)) (record:List Bool) (flag:Option Bool) :
    run code (5*records.length+6*record.length+7)
      (state 0 flag record (heapBytes records) [] (List.replicate records.length true) [] [])=
      some (done record (heapBytes (records++[record]))
        (List.replicate (records.length+1) true) (List.replicate records.length true)) := by
  simpa only [List.length_replicate,heapBytes_append,List.replicate_succ] using
    allocate_run record (heapBytes records) (List.replicate records.length true) flag

/-- Every reached actual allocation stack has a bound from initial real payload and steps. -/
theorem prefix_bound (rec hp cs:List Bool) (flag:Option Bool) (fuel:ℕ)
    (out:State (Fin 6) (Fin 22))
    (hr:run code fuel (state 0 flag rec hp [] cs [] [])=some out) :
    ∀k,(out.store k).length ≤ rec.length+hp.length+cs.length+fuel := by
  apply SemiprimeD1StackCopy.run_bound code fuel (rec.length+hp.length+cs.length) _ out ?_ hr
  intro k
  fin_cases k <;> simp [state,payload] <;> omega

/-- Six-stack allocation has an actual all-prefix total payload bound. -/
theorem machine_prefix_cells (rec hp cs:List Bool) (flag:Option Bool) (fuel:ℕ)
    (cfg:Turing.TM2.Cfg (fun _:Fin 6=>Bool) (Fin 22) (Option Bool))
    (hr:(fun cfg=>cfg.bind machine.step)^[fuel]
      (some (configuration (state 0 flag rec hp [] cs [] [])))=some cfg) :
    (cfg.stk 0).length+(cfg.stk 1).length+(cfg.stk 2).length+
      (cfg.stk 3).length+(cfg.stk 4).length+(cfg.stk 5).length ≤
      6*(rec.length+hp.length+cs.length+fuel) := by
  have he:=run_correct 0 4 0 code fuel (state 0 flag rec hp [] cs [] [])
  change (run code fuel (state 0 flag rec hp [] cs [] [])).map configuration=
    (fun cfg=>cfg.bind machine.step)^[fuel] (some (configuration (state 0 flag rec hp [] cs [] []))) at he
  cases hc:run code fuel (state 0 flag rec hp [] cs [] []) with
  | none => rw [hc,hr] at he;cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg:configuration out=cfg:=Option.some.inj he
    rw [←hcfg]
    have h:=prefix_bound rec hp cs flag fuel out hc
    have h0:=h 0
    have h1:=h 1
    have h2:=h 2
    have h3:=h 3
    have h4:=h 4
    have h5:=h 5
    change (out.store 0).length+(out.store 1).length+(out.store 2).length+
      (out.store 3).length+(out.store 4).length+(out.store 5).length ≤ _
    omega
end RiemannGaussian.SemiprimeD1StackHeapAllocate
