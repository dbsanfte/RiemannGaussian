/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformState
import RiemannGaussian.SemiprimeD1StackPublicTransformMetadata
/-! # Actual selector and original-metadata physical copies -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformSetup
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState
open SemiprimeD1StackProcedureTrace
/-- Selected physical original cache and raw payload, not a runtime source argument. -/
def bare (root : R.Stack→List Bool) (raw : List Bool) : Parts :=
  {root:=root,auxiliary:=fun k=>match k with | .raw=>raw | _=>[]}
/-- Two physical singleton descriptor flags before actual selector reads. -/
def flags (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  {root:=root,auxiliary:=fun k=>match k with | .raw=>raw | .second=>[second] | .inverse=>[inverse] | _=>[]}
/-- Real descriptor pops; finite Boolean modes enter control only after their reads. -/
theorem select_run (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program 2 .selectSecond (data (flags root raw second inverse)) (.rootCode second inverse) (data (bare root raw)) := by
  let p0:=flags root raw second inverse
  let p1:=set p0 (.aux .second) []
  let p2:=set p1 (.aux .inverse) []
  have h0:=SemiprimeD1StackPublicTransformPrimitives.pop .selectSecond .bad (.selectInverse false) (.selectInverse true)
    (.aux .second) rfl (data p0)
  have h1:=SemiprimeD1StackPublicTransformPrimitives.pop (.selectInverse second) .bad (.rootCode second false) (.rootCode second true)
    (.aux .inverse) rfl (data p1)
  have hv0 : data p0 (.aux .second)=[second] := rfl
  have hv1 : data p1 (.aux .inverse)=[inverse] := rfl
  rw [hv0,←data_set] at h0
  rw [hv1,←data_set] at h1
  have h0' : Runs program 1 .selectSecond (data p0) (.selectInverse second) (data p1) := by
    cases second <;> exact h0
  have h1' : Runs program 1 (.selectInverse second) (data p1) (.rootCode second inverse) (data p2) := by
    cases inverse <;> exact h1
  have he : data p2=data (bare root raw) := by
    funext k;cases k <;> first | rfl | (rename_i k;cases k <;> rfl)
  have h:=runs_trans program 1 1 _ _ _ _ _ _ h0' h1'
  rw [he] at h
  exact h
/-- Complete literal metadata-copy result; proof image only. -/
def metadataParts (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  let p0:=bare root raw
  let p1:=copied p0 (.root inverse)
  let p2:=copied p1 (.modulus 0)
  let p3:=copied p2 (.modulus 1)
  let p4:=copied p3 (.modulus 2)
  let p5:=copied p4 (.modulus 3)
  let p6:=copied p5 (.modulus 4)
  let p7:=copied p6 (.axis second 0)
  let p8:=copied p7 (.axis second 1)
  let p9:=copied p8 (.axis second 2)
  let p10:=copied p9 (.axis second 3)
  p10
/-- Every original source byte, cached width and axis marker copied here is paid. -/
def metadataBudget (root : R.Stack→List Bool) (second inverse : Bool) : ℕ :=
  (5*(root (.inr (if inverse then .root else .forwardRoot))).length+4)+
    5*(5*(root (.inl R.modulusKey)).length+4)+3*(5*(root (axisRole second)).length+4)+
    (5*(root (axisRole (!second))).length+4)
/-- Ten literal real preserving copies instantiate source/M/n/stride caches.
There is no native metadata/axis/source-word answer or component clock premise. -/
theorem metadata_run (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program (metadataBudget root second inverse) (.rootCode second inverse) (data (bare root raw))
      (.normalization second inverse) (data (metadataParts root raw second inverse)) := by
  let p0:=bare root raw
  let p1:=copied p0 (.root inverse)
  let p2:=copied p1 (.modulus 0)
  let p3:=copied p2 (.modulus 1)
  let p4:=copied p3 (.modulus 2)
  let p5:=copied p4 (.modulus 3)
  let p6:=copied p5 (.modulus 4)
  let p7:=copied p6 (.axis second 0)
  let p8:=copied p7 (.axis second 1)
  let p9:=copied p8 (.axis second 2)
  let p10:=copied p9 (.axis second 3)
  have h0:=copy_run (.root inverse) (.rootCode second inverse) (.moduli second inverse 0) rfl p0 rfl rfl
  have h1:=copy_run (.modulus 0) (.moduli second inverse 0) (.moduli second inverse 1) rfl p1 rfl rfl
  have h2:=copy_run (.modulus 1) (.moduli second inverse 1) (.moduli second inverse 2) rfl p2 rfl rfl
  have h3:=copy_run (.modulus 2) (.moduli second inverse 2) (.moduli second inverse 3) rfl p3 rfl rfl
  have h4:=copy_run (.modulus 3) (.moduli second inverse 3) (.moduli second inverse 4) rfl p4 rfl rfl
  have h5:=copy_run (.modulus 4) (.moduli second inverse 4) (.axes second inverse 0) rfl p5 rfl rfl
  have h6:=copy_run (.axis second 0) (.axes second inverse 0) (.axes second inverse 1) rfl p6 rfl rfl
  have h7:=copy_run (.axis second 1) (.axes second inverse 1) (.axes second inverse 2) rfl p7 rfl rfl
  have h8:=copy_run (.axis second 2) (.axes second inverse 2) (.axes second inverse 3) rfl p8 rfl rfl
  have h9:=copy_run (.axis second 3) (.axes second inverse 3) (.normalization second inverse) rfl p9 rfl rfl
  have h:=(runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  change Runs program ((5*(root (.inr (if inverse then .root else .forwardRoot))).length+4)+(5*(root (.inl R.modulusKey)).length+4)+(5*(root (.inl R.modulusKey)).length+4)+(5*(root (.inl R.modulusKey)).length+4)+(5*(root (.inl R.modulusKey)).length+4)+(5*(root (.inl R.modulusKey)).length+4)+(5*(root (axisRole second)).length+4)+(5*(root (axisRole second)).length+4)+(5*(root (axisRole second)).length+4)+(5*(root (axisRole (!second))).length+4)) (.rootCode second inverse) (data (bare root raw))
    (.normalization second inverse) (data (metadataParts root raw second inverse)) at h
  have ht : (5*(root (.inr (if inverse then .root else .forwardRoot))).length+4)+(5*(root (.inl R.modulusKey)).length+4)+(5*(root (.inl R.modulusKey)).length+4)+(5*(root (.inl R.modulusKey)).length+4)+(5*(root (.inl R.modulusKey)).length+4)+(5*(root (.inl R.modulusKey)).length+4)+(5*(root (axisRole second)).length+4)+(5*(root (axisRole second)).length+4)+(5*(root (axisRole second)).length+4)+(5*(root (axisRole (!second))).length+4)=metadataBudget root second inverse := by unfold metadataBudget;omega
  rw [ht] at h
  exact h
/-- Actual normalized payload: a literal one, or the acquired canonical word. -/
def normalizedParts (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) : Parts :=
  set (metadataParts root raw second inverse) (.aux .normalizer)
    (if second && inverse then root (.inl (SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr true))) else [true])
/-- The actual normalization copy/push count, before the whole source family. -/
def normalizationBudget (root : R.Stack→List Bool) (second inverse : Bool) : ℕ :=
  if second && inverse then 5*(root (.inl (SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr true)))).length+4 else 1
/-- Physical normalization construction uses the acquired word only in the
inverse SECOND stage; all other stages execute the literal one-cell push. -/
theorem normalization_run (root : R.Stack→List Bool) (raw : List Bool) (second inverse : Bool) :
    Runs program (normalizationBudget root second inverse) (.normalization second inverse)
      (data (metadataParts root raw second inverse)) .copyRawInput (data (normalizedParts root raw second inverse)) := by
  cases second <;> cases inverse
  · have h:=SemiprimeD1StackPublicTransformPrimitives.push (.normalization false false) .copyRawInput (.aux .normalizer) true rfl
      (data (metadataParts root raw false false))
    have hz : data (metadataParts root raw false false) (.aux .normalizer)=[] := rfl
    rw [hz,←data_set] at h;exact h
  · have h:=SemiprimeD1StackPublicTransformPrimitives.push (.normalization false true) .copyRawInput (.aux .normalizer) true rfl
      (data (metadataParts root raw false true))
    have hz : data (metadataParts root raw false true) (.aux .normalizer)=[] := rfl
    rw [hz,←data_set] at h;exact h
  · have h:=SemiprimeD1StackPublicTransformPrimitives.push (.normalization true false) .copyRawInput (.aux .normalizer) true rfl
      (data (metadataParts root raw true false))
    have hz : data (metadataParts root raw true false) (.aux .normalizer)=[] := rfl
    rw [hz,←data_set] at h;exact h
  · exact copy_run .normalizer (.normalization true true) .copyRawInput rfl
      (metadataParts root raw true true) rfl rfl
/-- Complete original-input selector/metadata/normalization setup, with actual
root acquisition ONCE and every real source/count/cache copy retained. -/
theorem acquire_run (bits raw : List Bool) (second inverse : Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1StackRootSourceBounds.timeBound bits+1+2+
      metadataBudget (SemiprimeD1StackPublicTransformMetadata.rootData bits) second inverse+
        normalizationBudget (SemiprimeD1StackPublicTransformMetadata.rootData bits) second inverse,
      Runs program t .start (initial bits raw second inverse).data .copyRawInput
        (data (normalizedParts (SemiprimeD1StackPublicTransformMetadata.rootData bits) raw second inverse)) := by
  obtain ⟨t,ht,h0⟩:=roots_call bits raw second inverse hb
  have h1:=select_run (SemiprimeD1StackPublicTransformMetadata.rootData bits) raw second inverse
  have h2:=metadata_run (SemiprimeD1StackPublicTransformMetadata.rootData bits) raw second inverse
  have h3:=normalization_run (SemiprimeD1StackPublicTransformMetadata.rootData bits) raw second inverse
  have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
  rw [initial_data] at h
  exact ⟨_,by omega,h⟩
end RiemannGaussian.SemiprimeD1StackPublicTransformSetup
