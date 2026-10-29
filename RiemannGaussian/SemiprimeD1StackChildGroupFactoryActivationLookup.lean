/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationView
/-! # Actual whole activation source block, with its complete115-word boundary -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLookup
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
open SemiprimeD1StackChildGroupFactoryActivation SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Sum of the same literal component/cleanup clocks; no clock is a runtime operand. -/
def budget (i:Inputs) (key:List Bool) (selected:List Bool) (unread:List Bool) (environment:List (List Bool×List Bool)):Nat:=((5*(key).length+4))+((5*(i.environment).length+4))+((SemiprimeD1StackOwnerLookupExecution.loopTime key environment+2))+(1)+((5*(selected).length+4))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+(((key).length+1))+(((unread).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+((([]:List Bool).length+1))+(((selected).length+1))
/-- Complete actual block; its trace and real returns come from the literal source. -/
theorem source_trace (i:Inputs) (todo key hist map:List Bool) (environment:List (List Bool×List Bool)) (selected unread:List Bool) (he:i.environment=SemiprimeD1StackOwnerLookup.records environment []) (hget:SemiprimeD1StackOwnerLookup.result key environment []=(true::selected,unread)):
    ∃t≤budget i key selected unread environment,Runs program t (.local 0 4) (data i todo key hist map) (.local 0 20) (selectedData i todo key hist map selected):=by
  let b0:Stack→List Bool:=data i todo key hist map
  let b1:Stack→List Bool:=Function.update b0 (lookup (.inr .query)) (key++[])
  have h0:Runs program (5*(key).length+4) (.local 0 4) b0 (.local 0 5) b1:=
    copy_call 2 (.local 0 4) (.local 0 5) rfl b0 key [] (by simp [b0,data,aux,lookup,copyStack,copyPorts]) (by simp [b0,data,input,aux,lookup,copyStack,copyPorts]) (by simp [b0,data,input,aux,copyStack])
  let b2:Stack→List Bool:=Function.update b1 (lookup (.inr .reader)) (i.environment++[])
  have h1:Runs program (5*(i.environment).length+4) (.local 0 5) b1 (.local 0 6) b2:=
    copy_call 3 (.local 0 5) (.local 0 6) rfl b1 i.environment [] (by simp [b0,b1,data,input,aux,lookup,copyStack,copyPorts,he]) (by simp [b0,b1,data,input,aux,lookup,copyStack,copyPorts]) (by simp [b0,b1,data,input,aux,lookup,copyStack])
  let b3:Stack→List Bool:=withLookup b2 (SemiprimeD1StackOwnerLookup.done key environment []).data
  have h2:Runs program (SemiprimeD1StackOwnerLookupExecution.loopTime key environment+2) (.local 0 6) b2 (.local 0 7) b3:=
    lookup_call (.local 0 6) (.local 0 7) rfl b2 key environment [] (by
      intro k;rcases k with k|k <;> cases k <;> simp [b0,b1,b2,data,input,lookup,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackOwnerLookup.initial,SemiprimeD1StackAdder.store,he])
  let b4:Stack→List Bool:=Function.update b3 (lookup (.inr .output)) selected
  have h3a:=pop_run (.local 0 7) (.local 15 14) (.local 15 14) (.local 0 8) (lookup (.inr .output)) b3 (true::selected) rfl (by simp [b0,b1,b2,b3,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,he,hget])
  have h3:Runs program 1 (.local 0 7) b3 (.local 0 8) b4:=by
    simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] using h3a
  let b5:Stack→List Bool:=Function.update b4 (aux .selectedID) (selected++[])
  have h4:Runs program (5*(selected).length+4) (.local 0 8) b4 (.local 0 9) b5:=
    copy_call 4 (.local 0 8) (.local 0 9) rfl b4 selected [] (by simp [b0,b1,b2,b3,b4,aux,lookup,copyStack,copyPorts,SemiprimeD1StackOwnerLookup.done,he,hget]) (by simp [b0,b1,b2,b3,b4,data,input,aux,lookup,copyStack,copyPorts,withLookup,SemiprimeD1StackOwnerLookup.done,he,hget]) (by simp [b0,b1,b2,b3,b4,data,input,aux,lookup,copyStack,withLookup,SemiprimeD1StackOwnerLookup.done,he,hget])
  let b6:Stack→List Bool:=Function.update b5 (lookup (.inl .left)) []
  have h5:Runs program (([]).length+1) (.local 0 9) b5 (.local 0 10) b6:=
    drain_loop (.local 0 9) (.local 0 10) (lookup (.inl .left)) rfl b5 [] (by simp [b0,b1,b2,b3,b4,b5,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackAdder.store,he,hget])
  let b7:Stack→List Bool:=Function.update b6 (lookup (.inl .right)) []
  have h6:Runs program (([]).length+1) (.local 0 10) b6 (.local 0 11) b7:=
    drain_loop (.local 0 10) (.local 0 11) (lookup (.inl .right)) rfl b6 [] (by simp [b0,b1,b2,b3,b4,b5,b6,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackAdder.store,he,hget])
  let b8:Stack→List Bool:=Function.update b7 (lookup (.inl .scratch)) []
  have h7:Runs program (([]).length+1) (.local 0 11) b7 (.local 0 12) b8:=
    drain_loop (.local 0 11) (.local 0 12) (lookup (.inl .scratch)) rfl b7 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackAdder.store,he,hget])
  let b9:Stack→List Bool:=Function.update b8 (lookup (.inl .output)) []
  have h8:Runs program (([]).length+1) (.local 0 12) b8 (.local 0 13) b9:=
    drain_loop (.local 0 12) (.local 0 13) (lookup (.inl .output)) rfl b8 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,SemiprimeD1StackAdder.store,he,hget])
  let b10:Stack→List Bool:=Function.update b9 (lookup (.inr .query)) []
  have h9:Runs program ((key).length+1) (.local 0 13) b9 (.local 0 14) b10:=
    drain_loop (.local 0 13) (.local 0 14) (lookup (.inr .query)) rfl b9 key (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,he,hget])
  let b11:Stack→List Bool:=Function.update b10 (lookup (.inr .reader)) []
  have h10:Runs program ((unread).length+1) (.local 0 14) b10 (.local 0 15) b11:=
    drain_loop (.local 0 14) (.local 0 15) (lookup (.inr .reader)) rfl b10 unread (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,he,hget])
  let b12:Stack→List Bool:=Function.update b11 (lookup (.inr .fieldScratch)) []
  have h11:Runs program (([]).length+1) (.local 0 15) b11 (.local 0 16) b12:=
    drain_loop (.local 0 15) (.local 0 16) (lookup (.inr .fieldScratch)) rfl b11 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,he,hget])
  let b13:Stack→List Bool:=Function.update b12 (lookup (.inr .valid)) []
  have h12:Runs program (([]).length+1) (.local 0 16) b12 (.local 0 17) b13:=
    drain_loop (.local 0 16) (.local 0 17) (lookup (.inr .valid)) rfl b12 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,he,hget])
  let b14:Stack→List Bool:=Function.update b13 (lookup (.inr .copyScratch)) []
  have h13:Runs program (([]).length+1) (.local 0 17) b13 (.local 0 18) b14:=
    drain_loop (.local 0 17) (.local 0 18) (lookup (.inr .copyScratch)) rfl b13 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,he,hget])
  let b15:Stack→List Bool:=Function.update b14 (lookup (.inr .discard)) []
  have h14:Runs program (([]).length+1) (.local 0 18) b14 (.local 0 19) b15:=
    drain_loop (.local 0 18) (.local 0 19) (lookup (.inr .discard)) rfl b14 [] (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,SemiprimeD1StackOwnerLookup.data,he,hget])
  let b16:Stack→List Bool:=Function.update b15 (lookup (.inr .output)) []
  have h15:Runs program ((selected).length+1) (.local 0 19) b15 (.local 0 20) b16:=
    drain_loop (.local 0 19) (.local 0 20) (lookup (.inr .output)) rfl b15 selected (by simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,aux,lookup,SemiprimeD1StackOwnerLookup.done,he,hget])
  have hfinal:b16=(selectedData i todo key hist map selected):=by
    funext k
    rcases k with k|k|k|k|k|k
    · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,data,input,aux,lookup,SemiprimeD1StackOwnerLookup.done,selectedData,he,hget]
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,data,input,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,selectedData,he,hget]
      · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,data,input,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,selectedData,he,hget]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,data,input,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,selectedData,he,hget]
    · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,data,input,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,selectedData,he,hget]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,data,input,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,selectedData,he,hget]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,data,input,aux,lookup,withLookup,SemiprimeD1StackOwnerLookup.done,selectedData,he,hget]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 (join h7 (join h8 (join h9 (join h10 (join h11 (join h12 (join h13 (join h14 (h15)))))))))))))))
  rw [hfinal] at hwhole
  refine ⟨_,?_,hwhole⟩
  dsimp only [budget]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLookup
