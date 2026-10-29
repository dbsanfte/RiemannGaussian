/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSourceAcquisition
import RiemannGaussian.SemiprimeMaterializedSourceWords

/-! # Original computed words to actual cached source arrays
No producer, coefficient, packing address, or rank answer is an input. Finite
network enumerations remain explicit; their initial construction is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedOriginalSource
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking SqrtLog
open SemiprimeMaterializedSourceUniversal SemiprimeJetArray
variable {I E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
variable {n r Q : ℕ}

/-- Original conditional-expectation acquisition followed by actual complete source acquisition. -/
def acquire (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ) :
    Run (Array (Array (Array ℚ))) :=
  let x := eps*(en.incidences.values.length : ℚ)/(en.types.values.length : ℚ)
  let y := (n : ℚ)/(2*(r : ℚ))
  let producer := SemiprimeMaterializedSourceWords.producer owner factor en.wordFirst en.wordTail
    en.terms.values en.indices.values x y
  let out := SemiprimeMaterializedSourceAcquisition.acquire R en.incidences.values owner en.types.values producer.value
  ⟨out.value,producer.work+out.work+en.incidences.values.length+en.types.values.length+9⟩

omit [DecidableEq E] in
/-- Literal-list scale computation is the original source incidence score scale. -/
theorem scale_eq (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) :
    eps*(en.incidences.values.length : ℚ)/(en.types.values.length : ℚ)=
      eps*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ) := by
  rw [en.incidences.length_eq_card,en.types.length_eq_card]

/-- The concrete computed label program is the original searched packing label. -/
theorem label_value (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (i : I) :
    ((SemiprimeMaterializedSourceWords.producer owner factor en.wordFirst en.wordTail
      en.terms.values en.indices.values
      (eps*(en.incidences.values.length : ℚ)/(en.types.values.length : ℚ))
      ((n : ℚ)/(2*(r : ℚ)))).value i).value=
      (SemiprimeFiniteEnumerations.searchPacking owner factor en eps).label i := by
  rw [SemiprimeMaterializedSourceWords.producer_value,scale_eq]
  simp only [SemiprimeFiniteEnumerations.searchPacking,Packing.computedPacking,Fintype.card_fin]

/-- All acquired original coefficients equal the already proved builtLayout rows. -/
theorem acquire_coefficient (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ)
    (i : I) (v : Fin n) (k : ℕ) (hk : k≤R) :
    coefficient (SemiprimeSourceArrayAcquisition.read en.incidences
      (acquire owner factor en eps R).value i v) k=
      ((SemiprimeSourceLayout.builtLayout owner factor en eps R).row i v).coeff k := by
  let producer := SemiprimeMaterializedSourceWords.producer owner factor en.wordFirst en.wordTail
    en.terms.values en.indices.values
    (eps*(en.incidences.values.length : ℚ)/(en.types.values.length : ℚ)) ((n : ℚ)/(2*(r : ℚ)))
  have h := SemiprimeMaterializedSourceAcquisition.acquire_coefficient
    (SemiprimeFiniteEnumerations.searchPacking owner factor en eps) R owner producer.value
    (label_value owner factor en eps) i v k (by omega)
  change coefficient (SemiprimeSourceArrayAcquisition.read en.incidences
    (SemiprimeMaterializedSourceAcquisition.acquire R en.incidences.values owner en.types.values producer.value).value i v) k=
    ((SemiprimeSourceLayout.builtLayout owner factor en eps R).row i v).coeff k at h
  exact h

/-- All original score, label-read, packing, universal, interpolation and pullback scalar work. -/
def budget (M n A D T N Q R start : ℕ) : ℕ :=
  SemiprimeMaterializedSourceWords.producerBudget A T N Q+
    SemiprimeMaterializedSourceAcquisition.budget R Q M n D start (4*N+6*(N+1)^2+7)+M+D+9

/-- Whole attached source ledger has no supplied terminal/label/coefficient budget. -/
theorem acquire_work (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ) :
    (acquire owner factor en eps R).work≤
      budget en.incidences.values.length n en.wordTail.length en.types.values.length
        en.terms.values.length en.indices.values.length Q R
          (SemiprimeMaterializedSourcePullback.centered r Q R) := by
  let x := eps*(en.incidences.values.length : ℚ)/(en.types.values.length : ℚ)
  let y := (n : ℚ)/(2*(r : ℚ))
  let producer := SemiprimeMaterializedSourceWords.producer owner factor en.wordFirst en.wordTail
    en.terms.values en.indices.values x y
  have hp := SemiprimeMaterializedSourceWords.producer_work owner factor en.wordFirst en.wordTail
    en.terms.values en.indices.values x y
  have ho := SemiprimeMaterializedSourceAcquisition.acquire_work
    (SemiprimeFiniteEnumerations.searchPacking owner factor en eps) R owner producer.value
    (label_value owner factor en eps) (4*en.indices.values.length+6*(en.indices.values.length+1)^2+7)
    (SemiprimeMaterializedSourceWords.producer_label_work owner factor en.wordFirst en.wordTail
      en.terms.values en.indices.values x y)
  unfold acquire budget
  dsimp only
  change producer.work+_+_+_+9≤_
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hp ho) _) _) 9

end RiemannGaussian.SemiprimeMaterializedOriginalSource
