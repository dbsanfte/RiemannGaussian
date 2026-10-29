/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseBankRestoreExecution

/-! # Linear actual phase-cache access, including all fifty-eight roles and real returns
The actual stored heap, counter and issued reference pay for the whole read and
all forty-eight field parses. No decoded-bank, selected-record-size or address
oracle is a runtime operand or a resource premise.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPhaseBankRestoreBounds
open SemiprimeD1StackPhaseBankRestore SemiprimeD1StackPhaseBankRestoreFields
open SemiprimeD1StackPhaseBankRestoreExecution
open SemiprimeD1StackCalls (run configuration)
local notation "ctl" => (Sum.inl : Control→Label)
/-- Total physical input bytes plus one, including the actual issued-reference word. -/
def resource (heap counter reference:List Bool) :Nat :=heap.length+counter.length+reference.length+1
/-- Actual prepared-source input size, not a price assigned to a semantic bank lookup. -/
def inputSize (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :Nat :=
  resource (SemiprimeD1StackHeapAllocate.heapBytes (records banks))
    (List.replicate banks.length true) (List.replicate i.val true)
/-- One fixed linear whole-consumer clock from the actual physical input bytes. -/
def linearBound (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :Nat :=1000*inputSize banks i
/-- Generic consecutive field framing has its literal data and delimiter byte count. -/
theorem frames_length (ks:List P.Stack) (bank:P.Stack→List Bool) :
    (ks.foldr (fun k tail=>SemiprimeSourceHistogramKeyBits.frame (bank k) tail) []).length=
      2*(ks.map (fun k=>(bank k).length)).sum+ks.length :=by
  induction ks with
  | nil=>rfl
  | cons k ks ih=>
    simp only [List.foldr_cons,SemiprimeSourceHistogramKeyBits.frame_length,ih,
      List.map_cons,List.sum_cons,List.length_cons]
    omega
/-- The complete phase record contains every actual restored word, not just the useful operands. -/
theorem record_length (bank:P.Stack→List Bool) :
    (record bank).length=2*mass bank 0+48 :=by
  have h:=frames_length I.roles bank
  simpa only [record,mass,List.drop_zero,I.roles_length] using h
/-- Any actual stored record's payload is bounded by the complete original allocation history. -/
theorem member_mass (rows:List (List Bool)) (word:List Bool) (hw:word∈rows) :
    word.length ≤ SemiprimeD1StackHeapReadBounds.wordMass rows :=by
  induction rows with
  | nil=>simp only [List.not_mem_nil] at hw
  | cons row rows ih=>
    rcases List.mem_cons.mp hw with h|h
    · subst word
      simp only [SemiprimeD1StackHeapReadBounds.wordMass,List.map_cons,List.sum_cons]
      omega
    · have ht:=ih h
      simp only [SemiprimeD1StackHeapReadBounds.wordMass,List.map_cons,List.sum_cons]
      unfold SemiprimeD1StackHeapReadBounds.wordMass at ht
      omega
/-- Complete selected word mass is paid by the actual physical heap; no selected-size cap is supplied. -/
theorem selected_mass_le (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :
    mass banks[i.val] 0 ≤ (SemiprimeD1StackHeapAllocate.heapBytes (records banks)).length :=by
  have hm:record banks[i.val]∈records banks:=List.mem_map.mpr ⟨banks[i.val],List.getElem_mem i.isLt,rfl⟩
  have h:=member_mass (records banks) (record banks[i.val]) hm
  rw [record_length] at h
  rw [SemiprimeD1StackHeapReadBounds.heap_length]
  omega
/-- The SAME actual dereference/restore trace fits one fixed linear input-byte clock. -/
theorem runBound_le (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :
    runBound banks i ≤ linearBound banks i :=by
  have hr:=SemiprimeD1StackHeapReadBounds.readTimeAt_le (records banks) (index banks i)
  have hm:=selected_mass_le banks i
  have hl:(records banks).length=banks.length:=by simp only [records,List.length_map]
  have hv:(index banks i).val=i.val:=rfl
  unfold runBound linearBound inputSize resource
  simp only [List.length_replicate]
  omega
/-- Real whole source execution with its physical-input linear cap. -/
theorem source_run_linear (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :
    ∃q ≤ linearBound banks i,run program q (source banks i)=some (target banks i) :=
  ⟨runBound banks i,runBound_le banks i,run_exact banks i⟩
/-- Each initialized word contains only one of the actual three physical input tapes. -/
theorem initial_length (heap counter reference:List Bool) (k:Stack) :
    ((initial heap counter reference).data k).length ≤ resource heap counter reference :=by
  rcases k with k|k
  · exact Nat.zero_le _
  · cases k <;> simp only [initial,data,SemiprimeD1StackHeapRead.input,
      Sum.elim_inr,List.length_nil,resource] <;> omega
/-- Successful prefixes cannot pass the SAME program's actual bounded final halt. -/
theorem prefix_fuel (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (source banks i)=some out) :
    fuel ≤ linearBound banks i :=by
  have he:=run_exact banks i
  have hh:run program 1 (target banks i)=none:=rfl
  have hf:fuel ≤ runBound banks i:=by
    by_contra hn
    have h:fuel=runBound banks i+(1+(fuel-(runBound banks i+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans (runBound_le banks i)
/-- Abstract finite-bank summation avoids reducing any concrete source or cache during elaboration. -/
theorem word_sum_le {K:Type} [Fintype K] (words:K→List Bool) (B:Nat)
    (h:∀k,(words k).length ≤ B) :(∑k:K,(words k).length) ≤ Fintype.card K*B :=by
  calc
    _ ≤ ∑_k:K,B:=Finset.sum_le_sum (fun k _=>h k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- All fifty-eight Boolean data words and every actual return cell are counted at every prefix. -/
theorem prefix_cells (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (source banks i)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤60000*inputSize banks i :=by
  have hi:∀k,((source banks i).data k).length ≤ inputSize banks i:=
    initial_length (SemiprimeD1StackHeapAllocate.heapBytes (records banks))
      (List.replicate banks.length true) (List.replicate i.val true)
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize banks i) (source banks i) out hi hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (source banks i) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:=word_sum_le out.data (inputSize banks i+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel banks i fuel out hr
  unfold linearBound at ht
  omega
/-- Actual compiled finite-machine certificate uses the same physical linear clock. -/
noncomputable def restoreBoundedInTime (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :
    StateTransition.EvalsToInTime machine.step (configuration (source banks i))
      (some (configuration (target banks i))) (linearBound banks i) :=by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (ctl .start) program
  exact ⟨⟨runBound banks i,run_exact banks i⟩,runBound_le banks i⟩
/-- Every reached compiled configuration counts the complete restored bank and actual return stack. -/
theorem machine_prefix_cells (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (configuration (source banks i)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤60000*inputSize banks i :=by
  have he:=SemiprimeD1StackCalls.run_correct originalInput output (ctl .start) program fuel (source banks i)
  have hh:=he.trans hr
  cases hout:run program fuel (source banks i) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells banks i fuel out hout
/-- Every actual transition expands into at most four fundamental machine commands. -/
theorem compile_depth (pc:Label) :SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤4 :=
  SemiprimeD1StackCalls.compile_depth (ctl .start) (program pc)
end RiemannGaussian.SemiprimeD1StackPhaseBankRestoreBounds
