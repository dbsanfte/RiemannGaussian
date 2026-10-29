/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableLeaf
import RiemannGaussian.SemiprimeD1StackProductTableDFSParts
/-! # Complete actual product truth-table DFS and every leaf's own bit clock
Both real recursive calls restore depth/prefix physically. Every scalar comes
from the embedded original-N product checker, then ALL76 roles are drained.
The resulting tape has EXACT old first-port-outermost, false-first order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableDFS
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableState SemiprimeD1StackProductTableSpec
open SemiprimeD1StackProductTableLeaf SemiprimeD1StackProductTableDFSParts
open SemiprimeD1StackProcedureTrace SemiprimeD1StackProcedureReturns
open SemiprimeD1TensorTapeCodec (tape)
/-- Prepend a literal body trace to a proved physical caller-frame return. -/
theorem returns_after {m n : ℕ} {pc mid : Label} {input middle output : Stack→List Bool}
    (h : Runs program m pc input mid middle) (g : Returns program n mid middle output) :
    Returns program (m+n) pc input output := by
  intro next frames before hb
  obtain ⟨between,hr,hm⟩:=h (next::frames) before hb
  obtain ⟨finish,hfinish,hout⟩:=g next frames between hm
  refine ⟨finish,?_,hout⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,hfinish]
/-- All leaves in a subtree have the SAME total physical assignment width. -/
def weight (bits : List Bool) (width : ℕ) : ℕ :=1000000000000000000*(bits.length+width+2)^3+20
/-- COMPLETE actual recursive visit, not an assumed evaluator/callback.
The same closed fixed code executes one actual public checker per real leaf,
both finite-label calls per fork, and all byte writes/restores/cleanup/returns. -/
theorem visit_returns (bits : List Bool) (hb : bits≠[]) (n : ℕ) (front hist : List Bool) :
    ∃t,t+10≤weight bits (front.length+n)*2^n ∧ Returns program t .visit (data bits n front hist)
      (data bits n front ((tape (tree bits front.reverse n)).reverse++hist)) := by
  induction n generalizing front hist with
  | zero=>
    obtain ⟨t,ht,hret⟩:=leaf_returns bits front hist hb
    rw [leaf_bytes] at hret
    have h:=returns_after (visit_zero bits front hist) hret
    refine ⟨1+t,?_,h⟩
    simp only [Nat.add_zero,pow_zero,Nat.mul_one,weight]
    unfold leafBound at ht
    omega
  | succ n ih=>
    let lowBytes:=tape (tree bits (front.reverse++[false]) n)
    let highBytes:=tape (tree bits (front.reverse++[true]) n)
    obtain ⟨tl,hl,hleft⟩:=ih (false::front) (true::hist)
    obtain ⟨tr,hr,hright⟩:=ih (true::front) (lowBytes.reverse++true::hist)
    simp only [List.reverse_cons] at hleft hright
    have h0:=visit_succ bits n front hist
    have h1:=fork_push bits n front hist
    have h2:=low_push bits n front (true::hist)
    have h3:=SemiprimeD1StackProcedureReturns.call program tl .high .visit .afterLow
      _ _ rfl hleft
    have h4:=low_pop bits n front (lowBytes.reverse++true::hist)
    have h5:=high_push bits n front (lowBytes.reverse++true::hist)
    have h6:=SemiprimeD1StackProcedureReturns.call program tr .afterHigh .visit .restore
      _ _ rfl hright
    have h7:=high_pop bits n front (highBytes.reverse++(lowBytes.reverse++true::hist))
    have h8:=depth_restore bits n front (highBytes.reverse++(lowBytes.reverse++true::hist))
    have h:=chain h0 (chain h1 (chain h2 (chain h3 (chain h4 (chain h5 (chain h6 (chain h7 h8)))))))
    have hlog:highBytes.reverse++(lowBytes.reverse++true::hist)=
        (tape (tree bits front.reverse (n+1))).reverse++hist := by
      change highBytes.reverse++(lowBytes.reverse++true::hist)=(true::(lowBytes++highBytes)).reverse++hist
      simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.singleton_append]
    rw [hlog] at h
    have hret:=of_runs program _ .visit .leafReturn _ _ h rfl
    refine ⟨_,?_,hret⟩
    have hw:(false::front).length+n=front.length+(n+1) := by simp only [List.length_cons];omega
    have hw':(true::front).length+n=front.length+(n+1) := by simp only [List.length_cons];omega
    rw [hw] at hl
    rw [hw'] at hr
    rw [pow_succ,←Nat.mul_assoc]
    omega
end RiemannGaussian.SemiprimeD1StackProductTableDFS
