/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceInner
/-! # Actual full ordered M² occurrence traversal without a count or pair supplier -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceOuter
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidencePrimitives SemiprimeD1StackSourceIncidenceLoopView
open SemiprimeD1StackSourceIncidenceParse SemiprimeD1StackSourceIncidenceAddition
open SemiprimeD1StackSourceIncidenceInner SemiprimeD1StackProcedureTrace
/-- Proof-side result of a remaining outer suffix; every iteration traverses the SAME complete acquired inner stream. -/
def outerResult (i:Inputs) (rows:List (List Bool×List Bool)) (acc:List Bool) :List Bool :=
  rows.foldl (fun sum row=>Spec.inner i.ids i.square i.cube i.fourth row i.rows sum) acc
/-- Recursive actual outer clock pays parsing, retained-source copy, whole inner scan, EOF check and cleanup. -/
def outerClock (i:Inputs) :List (List Bool×List Bool)→List Bool→Nat
  | [],_=>1
  | (lo,lf)::rows,acc=>8*(lo.length+lf.length)+17+(5*(tape i).length+4)+innerClock i lo lf i.rows acc+
      1+((lo.length+1)+(lf.length+1))+
        outerClock i rows (Spec.inner i.ids i.square i.cube i.fourth (lo,lf) i.rows acc)
/-- A paid preserving copy rereads the retained actual occurrence stream exactly once for each actual outer record. -/
theorem copy_inner (i:Inputs) (outer lo lf acc:List Bool) :
    Runs program (5*(tape i).length+4) .copyInner (bank i outer [] lo lf [] [] [] [] [] [] acc) .innerHeader
      (bank i outer (tape i) lo lf [] [] [] [] [] [] acc) :=by
  have h:=copy_call .inner .copyInner .innerHeader rfl (bank i outer [] lo lf [] [] [] [] [] [] acc) rfl rfl
  change Runs program _ _ _ _ (Function.update (bank i outer [] lo lf [] [] [] [] [] [] acc)
    (aux .innerReader) (tape i)) at h
  rw [update_inner] at h
  exact h
/-- Every actual outer record calls the complete same inner scan; no ordered diagonal/repetition is omitted. -/
theorem outer_run (i:Inputs) (rows:List (List Bool×List Bool)) (acc:List Bool) :
    ∃ q ≤ outerClock i rows acc,
      Runs program q .outerHeader (bank i (Records.records rows []) [] [] [] [] [] [] [] [] [] acc) .outerEOF
        (bank i [] [] [] [] [] [] [] [] [] [] (outerResult i rows acc)) :=by
  induction rows generalizing acc with
  | nil=>
    have h:=pop_run .outerHeader .abort .outerEOF (.parse false .owner) (aux .outerReader)
      (bank i (Records.records [] []) [] [] [] [] [] [] [] [] [] acc) [false] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i (Records.records [] []) [] [] [] [] [] [] [] [] [] acc)
      (aux .outerReader) []) at h
    rw [update_outer] at h
    exact ⟨1,le_rfl,h⟩
  | cons row rows ih=>
    rcases row with ⟨lo,lf⟩
    have h0:=read_outer i lo lf acc rows
    have h1:=copy_inner i (Records.records rows []) lo lf acc
    obtain ⟨q,hq,h2⟩:=inner_run i (Records.records rows []) lo lf i.rows acc
    have h3:=inner_finish i (Records.records rows []) lo lf (Spec.inner i.ids i.square i.cube i.fourth (lo,lf) i.rows acc)
    have h4:=clear_outer i (Records.records rows []) (Spec.inner i.ids i.square i.cube i.fourth (lo,lf) i.rows acc) lo lf
    obtain ⟨u,hu,h5⟩:=ih (Spec.inner i.ids i.square i.cube i.fourth (lo,lf) i.rows acc)
    refine ⟨_,?_,join (join (join (join (join h0 h1) h2) h3) h4) h5⟩
    dsimp only [outerClock]
    omega
end RiemannGaussian.SemiprimeD1StackSourceIncidenceOuter
