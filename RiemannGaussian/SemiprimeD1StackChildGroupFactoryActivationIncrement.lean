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
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationIncrement
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
open SemiprimeD1StackChildGroupFactoryActivation SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Sum of the same literal component/cleanup clocks; no clock is a runtime operand. -/
def budget (key:List Bool):Nat:=((5*(key).length+4))+(1)+((3*(max (key).length ((true::[])).length+1)+2*((SemiprimeBitArithmetic.addBits key [true] false).bits).length+3))+(((key).length+1))+((5*((SemiprimeBitArithmetic.addBits key [true] false).bits).length+4))+((((SemiprimeBitArithmetic.addBits key [true] false).bits).length+1))
/-- Complete actual block; its trace and real returns come from the literal source. -/
theorem source_trace (i:Inputs) (todo key hist map:List Bool):
    ∃t≤budget key,Runs program t (.local 2 10) (data i todo key hist map) (.local 0 3) (data i todo (SemiprimeBitArithmetic.addBits key [true] false).bits hist map):=by
  let b0:Stack→List Bool:=data i todo key hist map
  let b1:Stack→List Bool:=Function.update b0 (arithmetic .left) (key++[])
  have h0:Runs program (5*(key).length+4) (.local 2 10) b0 (.local 2 11) b1:=
    copy_call 12 (.local 2 10) (.local 2 11) rfl b0 key [] (by simp [b0,data,aux,arithmetic,copyStack,copyPorts]) (by simp [b0,data,input,aux,arithmetic,copyStack,copyPorts]) (by simp [b0,data,input,aux,copyStack])
  let b2:Stack→List Bool:=Function.update b1 (arithmetic .right) (true::[])
  have h1p:b1 (arithmetic .right)=[]:=(by simp [b0,b1,data,input,arithmetic])
  have h1a:=push_run (.local 2 11) (.local 2 12) (arithmetic .right) true b1 rfl
  have h1:Runs program 1 (.local 2 11) b1 (.local 2 12) b2:=by
    simpa only [h1p] using h1a
  let b3:Stack→List Bool:=withArithmetic b2 (SemiprimeD1StackAdder.store [] [] [] (SemiprimeBitArithmetic.addBits key [true] false).bits)
  have h2:Runs program (3*(max (key).length ((true::[])).length+1)+2*((SemiprimeBitArithmetic.addBits key [true] false).bits).length+3) (.local 2 12) b2 (.local 2 13) b3:=
    add_call (.local 2 12) (.local 2 13) rfl b2 key (true::[]) (by intro k;cases k <;> simp [b0,b1,b2,data,input,arithmetic,SemiprimeD1StackAdder.store])
  let b4:Stack→List Bool:=Function.update b3 (aux .vertexKey) []
  have h3:Runs program ((key).length+1) (.local 2 13) b3 (.local 2 14) b4:=
    drain_loop (.local 2 13) (.local 2 14) (aux .vertexKey) rfl b3 key (by simp [b0,b1,b2,b3,data,aux,arithmetic,withArithmetic])
  let b5:Stack→List Bool:=Function.update b4 (aux .vertexKey) ((SemiprimeBitArithmetic.addBits key [true] false).bits++[])
  have h4:Runs program (5*((SemiprimeBitArithmetic.addBits key [true] false).bits).length+4) (.local 2 14) b4 (.local 2 15) b5:=
    copy_call 13 (.local 2 14) (.local 2 15) rfl b4 (SemiprimeBitArithmetic.addBits key [true] false).bits [] (by simp [b0,b1,b2,b3,b4,aux,arithmetic,copyStack,copyPorts,withArithmetic,SemiprimeD1StackAdder.store]) (by simp [b0,b1,b2,b3,b4,aux,arithmetic,copyStack,copyPorts]) (by simp [b0,b1,b2,b3,b4,data,input,aux,arithmetic,copyStack,withArithmetic])
  let b6:Stack→List Bool:=Function.update b5 (arithmetic .output) []
  have h5:Runs program (((SemiprimeBitArithmetic.addBits key [true] false).bits).length+1) (.local 2 15) b5 (.local 0 3) b6:=
    drain_loop (.local 2 15) (.local 0 3) (arithmetic .output) rfl b5 (SemiprimeBitArithmetic.addBits key [true] false).bits (by simp [b0,b1,b2,b3,b4,b5,aux,arithmetic,withArithmetic,SemiprimeD1StackAdder.store])
  have hfinal:b6=(data i todo (SemiprimeBitArithmetic.addBits key [true] false).bits hist map):=by
    funext k
    rcases k with k|k|k|k|k|k
    · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,data,input,aux,arithmetic,withArithmetic]
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,data,input,aux,arithmetic,withArithmetic]
      · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,data,input,aux,arithmetic,withArithmetic]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,data,input,aux,arithmetic,withArithmetic,SemiprimeD1StackAdder.store]
    · rcases k with k|k <;> cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,data,input,aux,arithmetic,withArithmetic]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,data,input,aux,arithmetic,withArithmetic]
    · cases k <;> simp [b0,b1,b2,b3,b4,b5,b6,data,input,aux,arithmetic,withArithmetic]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 (h5)))))
  rw [hfinal] at hwhole
  refine ⟨_,?_,hwhole⟩
  dsimp only [budget]
  simp only [List.length_cons,List.length_nil]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationIncrement
