/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScorePhysicalSearch

/-! # Original source caller using physical integer-count selection
Original enumeration cardinalities discharge the averaging-bank identity. No
offset or rational scale is constructed by this caller: all comparisons are
driven by physical integer counts and weights. Finite original labels and their
descriptor construction retain the documented native metadata representation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeSourceScorePhysicalCaller
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords

/-- Exact scheduled rational x used only to state original-caller refinement. -/
def originalX {I E : Type} {n r Q : ℕ}
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) : ℚ :=
  (1/((r*lam:ℕ):ℚ))*(en.incidences.values.length:ℚ)/(en.types.values.length:ℚ)

/-- Construct descriptors and physical integer scores from the actual source inputs. -/
def computed {I E : Type} [DecidableEq E] {n r Q : ℕ}
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) :
    Run (List (Word r Q)) :=
  SemiprimeSourceScorePhysicalSearch.computedList owner factor en.incidences.values.length n lam
    en.wordFirst en.wordTail en.terms.values en.indices.values

/-- All source-size and score-order conditions follow from original inputs.
The offset is proof-side and may be ANY constant shared by candidates. -/
theorem computed_refines {I E : Type} [DecidableEq E] {n r Q : ℕ} [NeZero r]
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) (hlam : 0 < lam)
    (offset : ℚ) :
    (computed owner factor en lam).value =
      (SemiprimeMaterializedSourceWords.computedList owner factor en.wordFirst en.wordTail
        en.terms.values en.indices.values (originalX en lam) ((n:ℚ)/(2*(r:ℚ))) offset).value := by
  have hcard : (en.wordFirst::en.wordTail).length^4=(r^(2*Q))^2 := by
    simpa only [SemiprimeSourceOffsetHeight.caller_universal_length] using
      SemiprimeSourceScoreCountOrder.caller_cardinality en
  have hx : originalX en lam=
      (en.incidences.values.length:ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ)) := by
    simp only [originalX,SemiprimeSourceOffsetHeight.caller_universal_length]
    exact SemiprimeSourceScoreCancellation.scheduled_x _ _ _ _
  rw [hx]
  exact SemiprimeSourceScorePhysicalSearch.computedList_refines owner factor _ n lam
    en.wordFirst en.wordTail en.terms.values en.indices.values offset (NeZero.pos r) hlam hcard

/-- Acquire the original incidence-label producer from the actual integer search once. -/
def producer {I E : Type} [DecidableEq E] {n r Q : ℕ}
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) :
    SemiprimeMaterializedSourceUniversal.Run
      (I → SemiprimeMaterializedSourceUniversal.Run (UniversalType r Q 1)) :=
  let labels := computed owner factor en lam
  ⟨fun i => SemiprimeMaterializedSourceWords.labelAt owner factor en.wordFirst
    en.indices.values labels.value i,labels.work+1⟩

/-- Exact original incidence labels from the acquired physical-count source path. -/
theorem producer_refines {I E : Type} [Fintype I] [DecidableEq E] {n r Q : ℕ} [NeZero r]
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) (hlam : 0 < lam)
    (i : I) :
    ((producer owner factor en lam).value i).value=
      ((SemiprimeMaterializedSourceWords.producer owner factor en.wordFirst en.wordTail
        en.terms.values en.indices.values (originalX en lam) ((n:ℚ)/(2*(r:ℚ)))).value i).value := by
  simp only [producer,SemiprimeMaterializedSourceWords.producer,Fintype.card_fin]
  rw [computed_refines owner factor en lam hlam]

end RiemannGaussian.SemiprimeSourceScorePhysicalCaller
