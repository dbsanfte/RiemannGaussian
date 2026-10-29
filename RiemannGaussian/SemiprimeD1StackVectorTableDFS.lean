/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVectorTableLeaf
import RiemannGaussian.SemiprimeD1StackVectorTableDFSParts
/-! # Complete actual static-checker truth-table DFS and every leaf's own bit clock
Both real recursive calls restore depth/prefix physically. Every scalar comes
from the fixed embedded checker, then ALL of its physical roles are drained.
The resulting tape has EXACT old first-port-outermost, false-first order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackVectorTableDFS
open SemiprimeD1StackVectorTable SemiprimeD1StackVectorTableSpec
open SemiprimeD1StackVectorTableLeaf SemiprimeD1StackVectorTableDFSParts
open SemiprimeD1StackProcedureTrace SemiprimeD1StackProcedureReturns
open SemiprimeD1TensorTapeCodec (tape)
open SemiprimeD1StackVectorTableEmit (leaf_bytes)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : Static K L)
omit [Fintype K] in
/-- Prepend a literal body trace to a proved physical caller-frame return. -/
theorem returns_after {m n : ℕ} {pc mid : Label L s.roles.length} {input middle output : Stack K→List Bool}
    (h : Runs (program s) m pc input mid middle) (g : Returns (program s) n mid middle output) :
    Returns (program s) (m+n) pc input output := by
  intro next frames before hb
  obtain ⟨between,hr,hm⟩:=h (next::frames) before hb
  obtain ⟨finish,hfinish,hout⟩:=g next frames between hm
  refine ⟨finish,?_,hout⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,hfinish]
/-- All leaves in a subtree have the SAME total physical assignment width. -/
def weight (original : K→List Bool) (budget : Nat→Nat) (width : Nat) : Nat :=
  leafBound s original budget width+20
/-- COMPLETE actual recursive visit, not an assumed evaluator/callback.
The same closed fixed code executes one actual public checker per real leaf,
both finite-label calls per fork, and all byte writes/restores/cleanup/returns. -/
theorem visit_returns (original : K→List Bool) (hraw : original s.raw=[])
    (answer : List Bool→List (List Bool)) (budget : Nat→Nat) (hc : CheckerTrace s original answer budget)
    (bank : List Bool) (n : Nat) (front hist : List Bool) :
    ∃t,t+10≤ weight s original budget (front.length+n)*2^n ∧ Returns (program s) t .visit
      (data original bank n front hist)
      (data original bank n front ((tape (tree answer front.reverse n)).reverse++hist)) := by
  induction n generalizing front hist with
  | zero=>
    obtain ⟨t,ht,hret⟩:=leaf_returns s original hraw answer budget hc bank front hist
    rw [leaf_bytes] at hret
    have h:=returns_after s (visit_zero s original bank front hist) hret
    refine ⟨1+t,?_,h⟩
    simp only [Nat.add_zero,pow_zero,Nat.mul_one,weight]
    omega
  | succ n ih=>
    let lowBytes:=tape (tree answer (front.reverse++[false]) n)
    let highBytes:=tape (tree answer (front.reverse++[true]) n)
    obtain ⟨tl,hl,hleft⟩:=ih (false::front) (true::hist)
    obtain ⟨tr,hr,hright⟩:=ih (true::front) (lowBytes.reverse++true::hist)
    simp only [List.reverse_cons] at hleft hright
    have h0:=visit_succ s original bank n front hist
    have h1:=fork_push s original bank n front hist
    have h2:=low_push s original bank n front (true::hist)
    have h3:=SemiprimeD1StackProcedureReturns.call (program s) tl .high .visit .afterLow
      _ _ rfl hleft
    have h4:=low_pop s original bank n front (lowBytes.reverse++true::hist)
    have h5:=high_push s original bank n front (lowBytes.reverse++true::hist)
    have h6:=SemiprimeD1StackProcedureReturns.call (program s) tr .afterHigh .visit .restore
      _ _ rfl hright
    have h7:=high_pop s original bank n front (highBytes.reverse++(lowBytes.reverse++true::hist))
    have h8:=depth_restore s original bank n front (highBytes.reverse++(lowBytes.reverse++true::hist))
    have h:=runs_trans (program s) _ _ _ _ _ _ _ _ h0
      (runs_trans (program s) _ _ _ _ _ _ _ _ h1
        (runs_trans (program s) _ _ _ _ _ _ _ _ h2
          (runs_trans (program s) _ _ _ _ _ _ _ _ h3
            (runs_trans (program s) _ _ _ _ _ _ _ _ h4
              (runs_trans (program s) _ _ _ _ _ _ _ _ h5
                (runs_trans (program s) _ _ _ _ _ _ _ _ h6
                  (runs_trans (program s) _ _ _ _ _ _ _ _ h7 h8)))))))
    have hlog:highBytes.reverse++(lowBytes.reverse++true::hist)=
        (tape (tree answer front.reverse (n+1))).reverse++hist := by
      change highBytes.reverse++(lowBytes.reverse++true::hist)=(true::(lowBytes++highBytes)).reverse++hist
      simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.singleton_append]
    rw [hlog] at h
    have hret:=of_runs (program s) _ .visit .leafReturn _ _ h rfl
    refine ⟨_,?_,hret⟩
    have hw:(false::front).length+n=front.length+(n+1) := by simp only [List.length_cons];omega
    have hw':(true::front).length+n=front.length+(n+1) := by simp only [List.length_cons];omega
    rw [hw] at hl
    rw [hw'] at hr
    rw [pow_succ,←Nat.mul_assoc]
    omega
end RiemannGaussian.SemiprimeD1StackVectorTableDFS
