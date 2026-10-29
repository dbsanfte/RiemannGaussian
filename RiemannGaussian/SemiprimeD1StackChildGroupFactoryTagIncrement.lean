/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCalls
/-! # Real per-vertex first-index binary successor
The actual counter starts at zero and advances only after a same-vertex child
has a different whole raw tag. It counts physical filtered positions.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagIncrement
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
/-- Actual full binary add-one result. -/
def successor (position:List Bool):List Bool:=(SemiprimeBitArithmetic.addBits position [true] false).bits
/-- All copies, actual adder, old-counter erase, result copy and result erase. -/
def timeBound (position:List Bool):Nat:=
  (5*position.length+4)+1+(3*(max position.length 1+1)+2*(successor position).length+3)+
    (position.length+1)+(5*(successor position).length+4)+((successor position).length+1)
/-- Complete actual increment with all four arithmetic tapes restored to empty. -/
theorem source_trace (before:Stack→List Bool) (position:List Bool)
    (hp:before (aux .localPosition)=position) (hc:before (aux .copyScratch)=[])
    (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound position) (.local 13 13) before (.local 12 30)
      (Function.update before (aux .localPosition) (successor position)):=by
  simp only [aux] at hp hc
  have hal:=ha .left
  have har:=ha .right
  have has:=ha .scratch
  have hao:=ha .output
  simp only [arithmetic] at hal har has hao
  let b1:=Function.update before (arithmetic .left) position
  have h0:=copy_call 34 (.local 13 13) (.local 13 14) rfl before position []
    (by simpa [copyStack,copyPorts,aux] using hp)
    (by simpa [copyStack,copyPorts,arithmetic] using hal) (by simpa [copyStack,aux] using hc)
  simp only [List.append_nil] at h0
  change Runs program _ _ before _ b1 at h0
  let b2:=Function.update b1 (arithmetic .right) [true]
  have h1a:=push_run (.local 13 14) (.local 13 15) (arithmetic .right) true b1 rfl
  have hr:b1 (arithmetic .right)=[]:=by simp [b1,arithmetic,har]
  have h1:Runs program 1 (.local 13 14) b1 (.local 13 15) b2:=by simpa only [hr] using h1a
  let b3:=withArithmetic b2 (SemiprimeD1StackAdder.store [] [] [] (successor position))
  have h2:=add_call (.local 13 15) (.local 13 16) rfl b2 position [true]
    (by intro k;cases k <;> simp [b2,b1,arithmetic,SemiprimeD1StackAdder.store,has,hao])
  change Runs program _ _ b2 _ b3 at h2
  let b4:=Function.update b3 (aux .localPosition) []
  have h3:=drain_loop (.local 13 16) (.local 13 17) (aux .localPosition) rfl b3 position
    (by simpa [b3,b2,b1,withArithmetic,aux,arithmetic] using hp)
  change Runs program _ _ b3 _ b4 at h3
  let b5:=Function.update b4 (aux .localPosition) (successor position)
  have h4:=copy_call 35 (.local 13 17) (.local 13 18) rfl b4 (successor position) []
    (by simp [b4,b3,withArithmetic,copyStack,copyPorts,aux,arithmetic,SemiprimeD1StackAdder.store])
    (by simp [b4,copyStack,copyPorts])
    (by simpa [b4,b3,b2,b1,withArithmetic,copyStack,aux,arithmetic] using hc)
  simp only [List.append_nil] at h4
  change Runs program _ _ b4 _ b5 at h4
  let b6:=Function.update b5 (arithmetic .output) []
  have h5:=drain_loop (.local 13 18) (.local 12 30) (arithmetic .output) rfl b5 (successor position)
    (by simp [b5,b4,b3,withArithmetic,aux,arithmetic,SemiprimeD1StackAdder.store])
  change Runs program _ _ b5 _ b6 at h5
  have hout:b6=Function.update before (aux .localPosition) (successor position):=by
    funext k
    rcases k with k|k|k|k|k|k
    · rfl
    · rfl
    · cases k <;> simp [b6,b5,b4,b3,withArithmetic,aux,arithmetic,SemiprimeD1StackAdder.store,hal,har,has,hao]
    · rfl
    · rfl
    · cases k <;> simp [b6,b5,b4,b3,b2,b1,withArithmetic,aux,arithmetic]
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 h5))))
  rw [hout] at hwhole
  simpa only [timeBound,successor,List.length_cons,List.length_nil,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagIncrement
