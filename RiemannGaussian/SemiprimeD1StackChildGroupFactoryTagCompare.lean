/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCalls
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyEncoding
/-! # Real whole-raw-tag comparison, with two physically appended sentinels
Numeric equality is used only AFTER actual trailing TRUE writes and copies.
The exact original tag words and every other physical tape are preserved.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagCompare
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
/-- The actual result selects emit or the physical five-word cleanup. -/
def next (tag candidate:List Bool):Label:=if tag=candidate then .local 13 19 else .local 13 12
/-- All literal pushes/copies, actual numeric equality and result-pop clock. -/
def timeBound (tag candidate:List Bool):Nat:=
  1+(5*tag.length+4)+1+(5*candidate.length+4)+
    (SemiprimeD1StackWordEqualExecution.executionTime (tag++[true]) (candidate++[true])+1)+1
/-- No classification flag is an input: the real sentinel comparison chooses the next tag site. -/
theorem source_trace (before:Stack→List Bool) (tag candidate:List Bool)
    (hs:before (aux .tagWord)=tag) (hp:before (aux .candidateTag)=candidate)
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound tag candidate) (.local 13 6) before (next tag candidate) before:=by
  simp only [aux] at hs hp hc
  have hal:=ha .left
  have har:=ha .right
  have has:=ha .scratch
  have hao:=ha .output
  simp only [arithmetic] at hal har has hao
  let b1:=Function.update before (arithmetic .left) [true]
  have h0:=push_run (.local 13 6) (.local 13 7) (arithmetic .left) true before rfl
  simp only [arithmetic,hal] at h0
  change Runs program 1 (.local 13 6) before (.local 13 7) b1 at h0
  let b2:=Function.update b1 (arithmetic .left) (tag++[true])
  have h1:=copy_call 32 (.local 13 7) (.local 13 8) rfl b1 tag [true]
    (by simpa [b1,copyStack,copyPorts,aux,arithmetic] using hs)
    (by simp [b1,copyStack,copyPorts]) (by simpa [b1,copyStack,aux,arithmetic] using hc)
  change Runs program _ _ b1 _ b2 at h1
  let b3:=Function.update b2 (arithmetic .right) [true]
  have h2:=push_run (.local 13 8) (.local 13 9) (arithmetic .right) true b2 rfl
  have hb2:b2 (arithmetic .right)=[]:=by simp [b2,b1,arithmetic,har]
  rw [hb2] at h2
  change Runs program 1 _ b2 _ b3 at h2
  let b4:=Function.update b3 (arithmetic .right) (candidate++[true])
  have h3:=copy_call 33 (.local 13 9) (.local 13 10) rfl b3 candidate [true]
    (by simpa [b3,b2,b1,copyStack,copyPorts,aux,arithmetic] using hp)
    (by simp [b3,copyStack,copyPorts]) (by simpa [b3,b2,b1,copyStack,aux,arithmetic] using hc)
  change Runs program _ _ b3 _ b4 at h3
  have h4:=equal_call (.local 13 10) (.local 13 11) rfl b4 (tag++[true]) (candidate++[true])
    (by intro k;cases k <;> simp [b4,b3,b2,b1,arithmetic,SemiprimeD1StackAdder.store,has,hao])
  have heq:bitValue (tag++[true])=bitValue (candidate++[true]) ↔ tag=candidate:=
    SemiprimeD1StackSourceKeyFrequencyEncoding.encoded_eq tag candidate
  simp only [heq] at h4
  let b5:=withArithmetic b4 (SemiprimeD1StackAdder.store [] [] [] [decide (tag=candidate)])
  change Runs program _ _ b4 _ b5 at h4
  have h5a:=pop_run (.local 13 11) abort (.local 13 12) (.local 13 19) (arithmetic .output)
    b5 [decide (tag=candidate)] rfl rfl
  have hout:Function.update b5 (arithmetic .output) []=before:=by
    funext k
    rcases k with k|k|k|k|k|k
    · rfl
    · rfl
    · cases k <;> simp [b5,withArithmetic,arithmetic,SemiprimeD1StackAdder.store,hal,har,has,hao]
    · rfl
    · rfl
    · rfl
  have h5:Runs program 1 (.local 13 11) b5 (next tag candidate) before:=by
    by_cases h:tag=candidate <;>
      simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose,hout,next,
        h,decide_true,decide_false,ite_true,ite_false] using h5a
  have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 h5))))
  simpa only [timeBound,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagCompare
