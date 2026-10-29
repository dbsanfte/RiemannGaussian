/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordOriginal
/-! # Actual non-Boolean descriptor branch for a complete catalogue sweep
The unchanged fixed parser and dispatch code consumes original arithmetic
descriptors without logging a Boolean row. No native family filter executes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordReject
open SemiprimeD1StackBooleanDescriptorRecord SemiprimeD1StackBooleanDescriptorRecordEncoding
open SemiprimeD1StackBooleanDescriptorRecordExecution SemiprimeD1StackBooleanDescriptorRecordPrimitives
open SemiprimeD1StackProcedureFragments (Runs)
/-- Literal arithmetic-family dispatch reaches the actual abort halt, retaining
the real descriptor fields and complete record substore without a row write. -/
theorem rejected_run (code : Fin 18) (hc:code.val<8) (w : Record)
    (htag:w 0=List.replicate code.val true) (base : R.Stack→List Bool) (tail : List Bool) :
    C.run program (8*mass w+6*code.val+46)
      (⟨some (.local (.field 0)),none,none,clean base (fun _=>[]) (record w tail),[]⟩:C.State Stack Label)=
      some ⟨none,none,none,clean base w tail,[]⟩ := by
  have h0:=all_fields base w tail
  have h1:=copy_tag base w tail
  rw [htag,List.length_replicate] at h1
  have h2:=decode_run code.val 0 (by omega) base w tail
  have he:(⟨0+code.val,by omega⟩:Fin 18)=code:=by
    apply Fin.ext
    change 0+code.val=code.val
    omega
  have hd:dispatch code=.local .abort:=by
    have h8:code.val≠8:=by omega
    have h9:code.val≠9:=by omega
    have h10:¬10≤code.val:=by omega
    simp [dispatch,h8,h9,h10]
  rw [he,hd] at h2
  have h:=h0.trans (h1.trans h2)
  obtain ⟨finish,hr,ho⟩:=h []
    (⟨some (.local (.field 0)),none,none,clean base (fun _=>[]) (record w tail),[]⟩:C.State Stack Label)
    ⟨rfl,rfl,rfl⟩
  have ht:8*mass w+6*code.val+46=(8*mass w+40)+((5*code.val+4)+(code.val+1))+1:=by omega
  rw [ht,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  rcases ho with ⟨hp,hd,hf⟩
  change C.step program finish=some (⟨none,none,none,clean base w tail,[]⟩:C.State Stack Label)
  simp only [C.step,SemiprimeD1StackCalls.step,hp,Option.map_some,program,C.execute,hd,hf]
/-- Complete original arithmetic complement to the ten proved Boolean cases. -/
theorem arithmetic_tag {r t digits : Nat} (v : SemiprimeMacroGraph.Vertex r t digits)
    (hm:SemiprimeD1StackBooleanDescriptorRecordOriginal.originalMode (.inl v)=none) :
    ∃code : Fin 18,code.val<8 ∧
      SemiprimeD1EdgeCatalogueEncoding.vertex (.inl v) 0=List.replicate code.val true := by
  cases v with
  | input side i=>exact ⟨0,by decide,rfl⟩
  | first tr j=>exact ⟨1,by decide,rfl⟩
  | scale tr j k=>exact ⟨2,by decide,rfl⟩
  | second tr k=>exact ⟨3,by decide,rfl⟩
  | product i=>exact ⟨4,by decide,rfl⟩
  | carryInitial=>exact ⟨5,by decide,rfl⟩
  | carry i=>exact ⟨6,by decide,rfl⟩
  | carryTerminal=>exact ⟨7,by decide,rfl⟩
  | orGate side j=>cases hm
  | inputCheck side=>cases hm
end RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordReject
