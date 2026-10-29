/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformFinite
/-! # Original public transform entry refinement on every finite assignment -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformPublic
open SemiprimeD1StackPublicTransformMetadata SemiprimeD1StackPublicTransformFinite
open SemiprimeD1StackPublicTransformFiniteWords SemiprimeD1StackPublicTransformOriginal
open SemiprimeBitArithmetic SemiprimeMacroParameters SemiprimeMacroGraph SemiprimeMacroEntryBitCheck
/-- Erased finite-size transport, preserving every original word and loop slot. -/
theorem transform_cast (p : SemiprimeMacroGraphSemantics.Config) (tr : Transform) (stride : ℕ)
    (factor : SemiprimeMacroEntryBitPrimitives.Expr) {n m : ℕ} (h : n=m) (a b : Fin m→List Bool) :
    transformRun p tr stride factor (fun j : Fin n=>a (Fin.cast h j)) (fun j : Fin n=>b (Fin.cast h j))=
      transformRun p tr stride factor a b := by subst m;rfl
/-- Complete original FIRST transform verdict, for all original raw assignments;
fixed row descriptor j affects acquisition elsewhere, not this local DFT. -/
theorem first_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.first (t:=secondAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    verdict bits (List.ofFn assignment) false (SemiprimeD1StackPublicScaleFinite.selector tr)=
      (publicBitEntry (bitValue bits) hN (.first tr j) assignment).accepted := by
  let p:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
  let inverse:=SemiprimeD1StackPublicScaleFinite.selector tr
  let α:=firstInput bits hc hN tr j assignment
  have hn : size bits false=p.t :=first_size bits hc hN
  have hs : size bits (!false)=p.r :=second_size bits hc hN
  have ha : input bits (List.ofFn α) false=
      fun k : Fin (size bits false)=>localWord (fun b=>assignment
        (localSlotFinEquiv (.first tr j) (.inl (Fin.cast hn k,b)))) := by
    funext k
    exact (acquired_halves bits false α k).1.trans (first_words bits hc hN tr j assignment k).1
  have hb : output bits (List.ofFn α) false=
      fun k : Fin (size bits false)=>localWord (fun b=>assignment
        (localSlotFinEquiv (.first tr j) (.inr (Fin.cast hn k,b)))) := by
    funext k
    exact (acquired_halves bits false α k).2.trans (first_words bits hc hN tr j assignment k).2
  rw [←first_raw bits hc hN tr j assignment,transform_original bits _ false inverse hc hN,ha,hb]
  change (transformRun p (transform inverse) (size bits (!false)) SemiprimeMacroEntryBitPrimitives.oneExpr _ _).accepted=_
  rw [hs]
  have hcast:=transform_cast p (transform inverse) p.r SemiprimeMacroEntryBitPrimitives.oneExpr hn
    (fun k : Fin p.t=>localWord (fun b=>assignment (localSlotFinEquiv (.first tr j) (.inl (k,b)))))
    (fun k : Fin p.t=>localWord (fun b=>assignment (localSlotFinEquiv (.first tr j) (.inr (k,b)))))
  have hr : transformRun p (transform inverse) p.r SemiprimeMacroEntryBitPrimitives.oneExpr
      (fun k=>localWord (fun b=>assignment (localSlotFinEquiv (.first tr j) (.inl (k,b)))))
      (fun k=>localWord (fun b=>assignment (localSlotFinEquiv (.first tr j) (.inr (k,b)))))=
    entryRun p (configTargets p) (.first tr j) assignment := by
    cases tr with
    | inl side=>cases side;rfl
    | inr u=>cases u;rfl
  have he := congrArg SemiprimeMacroEntryBitPrimitives.CheckRun.accepted hcast
  have hh := congrArg SemiprimeMacroEntryBitPrimitives.CheckRun.accepted hr
  exact he.trans (hh.trans ((entryRun_correct p (configTargets p) (.first tr j) assignment).trans
    (publicBitEntry_correct (bitValue bits) hN (.first tr j) assignment).symm))
/-- Complete original SECOND transform verdict, for all original raw assignments;
fixed column descriptor j affects acquisition elsewhere, not this local DFT. -/
theorem second_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : Transform) (j : Fin (secondAxis (bitLength (bitValue bits))))
    (assignment : Fin (arity (Vertex.second (r:=firstAxis (bitLength (bitValue bits)))
      (digits:=digitCount (bitLength (bitValue bits))) tr j))→Bool) :
    verdict bits (List.ofFn assignment) true (SemiprimeD1StackPublicScaleFinite.selector tr)=
      (publicBitEntry (bitValue bits) hN (.second tr j) assignment).accepted := by
  let p:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
  let inverse:=SemiprimeD1StackPublicScaleFinite.selector tr
  let α:=secondInput bits hc hN tr j assignment
  have hn : size bits true=p.r :=second_size bits hc hN
  have hs : size bits (!true)=p.t :=first_size bits hc hN
  have ha : input bits (List.ofFn α) true=
      fun k : Fin (size bits true)=>localWord (fun b=>assignment
        (localSlotFinEquiv (.second tr j) (.inl (Fin.cast hn k,b)))) := by
    funext k
    exact (acquired_halves bits true α k).1.trans (second_words bits hc hN tr j assignment k).1
  have hb : output bits (List.ofFn α) true=
      fun k : Fin (size bits true)=>localWord (fun b=>assignment
        (localSlotFinEquiv (.second tr j) (.inr (Fin.cast hn k,b)))) := by
    funext k
    exact (acquired_halves bits true α k).2.trans (second_words bits hc hN tr j assignment k).2
  rw [←second_raw bits hc hN tr j assignment,transform_original bits _ true inverse hc hN,ha,hb]
  change (transformRun p (transform inverse) (size bits (!true)) (normalizationExpr p (transform inverse)) _ _).accepted=_
  rw [hs]
  have hcast:=transform_cast p (transform inverse) p.t (normalizationExpr p (transform inverse)) hn
    (fun k : Fin p.r=>localWord (fun b=>assignment (localSlotFinEquiv (.second tr j) (.inl (k,b)))))
    (fun k : Fin p.r=>localWord (fun b=>assignment (localSlotFinEquiv (.second tr j) (.inr (k,b)))))
  have hr : transformRun p (transform inverse) p.t (normalizationExpr p (transform inverse))
      (fun k=>localWord (fun b=>assignment (localSlotFinEquiv (.second tr j) (.inl (k,b)))))
      (fun k=>localWord (fun b=>assignment (localSlotFinEquiv (.second tr j) (.inr (k,b)))))=
    entryRun p (configTargets p) (.second tr j) assignment := by
    cases tr with
    | inl side=>cases side;rfl
    | inr u=>cases u;rfl
  have he := congrArg SemiprimeMacroEntryBitPrimitives.CheckRun.accepted hcast
  have hh := congrArg SemiprimeMacroEntryBitPrimitives.CheckRun.accepted hr
  exact he.trans (hh.trans ((entryRun_correct p (configTargets p) (.second tr j) assignment).trans
    (publicBitEntry_correct (bitValue bits) hN (.second tr j) assignment).symm))
end RiemannGaussian.SemiprimeD1StackPublicTransformPublic
