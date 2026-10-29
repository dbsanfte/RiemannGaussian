/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCalls
/-! # Actual numeric vertex comparison at the three literal source sites
Original binary vertex keys may retain high-zero padding; the acquired numeric
counter need not share their raw bytes. No decoded vertex or verdict is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexCompare
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
/-- Three finite static code families, never additional runtime modes. -/
def pc (site:Fin 3) (slot:Fin 4):Label:=match site.val,slot.val with
  | 0,0=>.local 10 5 | 0,1=>.local 10 6 | 0,2=>.local 10 7 | 0,3=>.local 10 8
  | 1,0=>.local 11 18 | 1,1=>.local 11 19 | 1,2=>.local 11 20 | 1,3=>.local 11 21
  | 2,0=>.local 12 26 | 2,1=>.local 12 27 | 2,2=>.local 12 28 | 2,3=>.local 12 29
  | _,_=>.local 10 5
/-- Actual nonmatching continuations. -/
def different (site:Fin 3):Label:=match site.val with
  | 0=>.local 10 9 | 1=>.local 14 6 | _=>.local 12 30
/-- Actual matching continuations. -/
def matched (site:Fin 3):Label:=match site.val with
  | 0=>.local 10 15 | 1=>.local 11 22 | _=>.local 13 4
/-- Only the actual computed numeric result selects the literal continuation. -/
def next (site:Fin 3) (query target:List Bool):Label:=
  if bitValue query=bitValue target then matched site else different site
/-- Two actual preserving copies, numeric equality and real output pop. -/
def timeBound (query target:List Bool):Nat:=
  (5*query.length+4)+(5*target.length+4)+SemiprimeD1StackWordEqualExecution.executionTime query target+1+1
/-- Full actual comparison, restoring every arithmetic word and retaining the entire115-word bank. -/
theorem source_trace (site:Fin 3) (before:Stack→List Bool) (query target:List Bool)
    (hq:before (aux .ownerKey)=query) (ht:before (aux .vertexKey)=target)
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]):
    Runs program (timeBound query target) (pc site 0) before (next site query target) before:=by
  simp only [aux] at hq ht hc
  have hal:=ha .left
  have har:=ha .right
  have has:=ha .scratch
  have hao:=ha .output
  simp only [arithmetic] at hal har has hao
  let b1:=Function.update before (arithmetic .left) query
  have h0:=copy_call 27 (pc site 0) (pc site 1) (by fin_cases site <;> rfl) before query []
    (by simpa [copyStack,copyPorts,aux] using hq)
    (by simpa [copyStack,copyPorts,arithmetic] using hal) (by simpa [copyStack,aux] using hc)
  simp only [List.append_nil] at h0
  change Runs program _ _ before _ b1 at h0
  let b2:=Function.update b1 (arithmetic .right) target
  have h1:=copy_call 28 (pc site 1) (pc site 2) (by fin_cases site <;> rfl) b1 target []
    (by simpa [b1,copyStack,copyPorts,aux,arithmetic] using ht)
    (by simp [b1,copyStack,copyPorts,arithmetic,har])
    (by simpa [b1,copyStack,aux,arithmetic] using hc)
  simp only [List.append_nil] at h1
  change Runs program _ _ b1 _ b2 at h1
  have h2:=equal_call (pc site 2) (pc site 3) (by fin_cases site <;> rfl) b2 query target
    (by intro k;cases k <;> simp [b2,b1,arithmetic,SemiprimeD1StackAdder.store,has,hao])
  let b3:=withArithmetic b2 (SemiprimeD1StackAdder.store [] [] [] [decide (bitValue query=bitValue target)])
  change Runs program _ _ b2 _ b3 at h2
  have h3a:=pop_run (pc site 3) abort (different site) (matched site) (arithmetic .output) b3
    [decide (bitValue query=bitValue target)] (by fin_cases site <;> rfl) rfl
  have hout:Function.update b3 (arithmetic .output) []=before:=by
    funext k
    rcases k with k|k|k|k|k|k
    · rfl
    · rfl
    · cases k <;> simp [b3,withArithmetic,arithmetic,SemiprimeD1StackAdder.store,hal,har,has,hao]
    · rfl
    · rfl
    · rfl
  have h3:Runs program 1 (pc site 3) b3 (next site query target) before:=by
    by_cases h:bitValue query=bitValue target <;>
      simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose,hout,next,
        h,decide_true,decide_false,ite_true,ite_false] using h3a
  have hwhole:=join h0 (join h1 (join h2 h3))
  simpa only [timeBound,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexCompare
