/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryNodeBits

/-! # Original-input physical weight-array refinement
All coefficients, cached powers and inverse words used below are acquired by
the actual constructor. Original scalar/array values are proof specifications,
never runtime suppliers or an assumed correct trace.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1RecoveryNodeBitsCorrectness
open SemiprimeRationalBits SemiprimeJetBits SemiprimeJetArray SemiprimeBitArithmetic
open SemiprimeD1RecoveryScalarRun SemiprimeD1RecoveryWeightRun
open SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid
open SemiprimeD1RecoveryNodeBits

/-- Actual coefficient access lists retain exactly the stored array order. -/
theorem coefficient_list (a : Array ℚ) :
    (List.range a.size).map (coefficient a)=a.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have h : i < a.size := by simpa using hi
    simp [coefficient,h]

/-- Physical array legality transfers to its actual finite memory representation. -/
theorem toList_valid (a : Array RationalWord) (ha : Valid a) : ∀x∈a.toList,x.Valid := by
  intro x hx
  obtain ⟨i,hi,he⟩:=Array.mem_iff_getElem.mp (show x∈a by simpa using hx)
  have h:=ha i hi
  rwa [he] at h

/-- Physical array widths transfer to the actual list-memory slots. -/
theorem toList_bounded (a : Array RationalWord) (W : ℕ) (ha : Bounded a W) : ∀x∈a.toList,Width x W := by
  intro x hx
  obtain ⟨i,hi,he⟩:=Array.mem_iff_getElem.mp (show x∈a by simpa using hx)
  have h:=ha i hi
  rwa [he] at h

/-- Every actual retained-index word has its original value and canonical
components; no supplied canonical row/height/trace answer is accepted. -/
theorem weights_correct (template : List Bool) (a h u : ℕ) (t : Fin (size a))
    (scalar : RationalWord) (inverse powers : List RationalWord)
    (hs : scalar.value=SemiprimeD1JetRecoveryGrid.Ezero a h u t.val) (hsv : scalar.Valid)
    (hi : inverse.map RationalWord.value=(SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients.toList)
    (hp : powers.map RationalWord.value=
      (powersRun (SemiprimeD1WeightPrecision.argument a t.val) (nodeMultiplicity a h u t.val)).value.toList)
    (hiv : ∀x∈inverse,x.Valid) (hpv : ∀x∈powers,x.Valid)
    (hW : SemiprimeD1RecoveryWeightRunState.sumExponent a h u t.val < template.length)
    (hWW : SemiprimeD1HermiteWeightBits.weightExponent a h u t.val < template.length)
    (js : List ℕ) (hj : ∀j∈js,j < nodeMultiplicity a h u t.val) :
    let out:=weights template (nodeMultiplicity a h u t.val) scalar inverse powers
      (indices (nodeMultiplicity a h u t.val)).value js
    let target:=fun j => coefficient (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).weights j
    out.words.map RationalWord.value=js.map target ∧
      (∀x∈out.words,x.Valid) ∧ (∀x∈out.words,Width x template.length) ∧
      out.words.map (fun x => (x.numerator.value,bitValue x.denominator))=
        js.map (fun j => ((target j).num,(target j).den)) := by
  dsimp only
  induction js with
  | nil => exact ⟨rfl,by simp [weights],by simp [weights],rfl⟩
  | cons j js ih =>
    have old:=ih (fun j hj' => hj j (List.mem_cons_of_mem _ hj'))
    have cur:=SemiprimeD1RecoveryScalarWeightBits.weight_correct template a h u t j (hj j List.mem_cons_self)
      scalar inverse powers hs hsv hi hp hiv hpv hW hWW
    refine ⟨?_,?_,?_,?_⟩
    · simp only [weights,List.map_cons,cur.1,old.1]
    · intro x hx
      simp only [weights,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact cur.2.1
      · exact old.2.1 x hx
    · intro x hx
      simp only [weights,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact cur.2.2.1
      · exact old.2.2.1 x hx
    · simp only [weights,List.map_cons,cur.2.2.2.1,cur.2.2.2.2,old.2.2.2]

/-- The actual constructor's word path uses the original acquired multiplicity. -/
theorem acquireAt_words (template : List Bool) (a M u : ℕ) (t : Fin (size a)) :
    let grid:=SemiprimeD1RecoveryGridBits.acquire template a M u t
    let q:=nodeMultiplicity a (height M u) u t.val
    let den:=SemiprimeAffineJetBits.build template q grid.grid.slopes
    let inv:=SemiprimeNormalizedInverseBits.build template den.words q
    let memory:=SemiprimeSourceMemoryBits.copyMemory inv.words.toList
    let keys:=indices q
    let powers:=SemiprimeD1RecoveryScalarWeightBits.powers template grid.argument keys.value
    (acquireAt template a M u t).words=(weights template q grid.scalar memory.words powers.words keys.value keys.value).words := by
  simp only [acquireAt,multiplicityRun_value a (height M u) u t.val t.val t.isLt]

/-- COMPLETE actual original physical node acquisition, including canonical row
payloads, refines the original scalar/array producer. Every runtime input is
original metadata; all caches and capacities are acquired/derived internally. -/
theorem acquireAt_correct (template : List Bool) (a M u : ℕ) (t : Fin (size a))
    (hM : u ≤ M) (hW : width a M ≤ template.length) :
    let out:=acquireAt template a M u t
    let native:=SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val
    out.words.map RationalWord.value=native.weights.toList ∧
      (∀x∈out.words,x.Valid) ∧ (∀x∈out.words,Width x template.length) ∧
      out.words.map (fun x => (x.numerator.value,bitValue x.denominator))=
        native.weights.toList.map (fun x => (x.num,x.den)) := by
  dsimp only
  let q:=nodeMultiplicity a (height M u) u t.val
  let grid:=SemiprimeD1RecoveryGridBits.acquire template a M u t
  let den:=SemiprimeAffineJetBits.build template q grid.grid.slopes
  let inv:=SemiprimeNormalizedInverseBits.build template den.words q
  let memory:=SemiprimeSourceMemoryBits.copyMemory inv.words.toList
  let keys:=(indices q).value
  let powers:=SemiprimeD1RecoveryScalarWeightBits.powers template grid.argument keys
  have hgW:=(grid_width_le a M u hM).trans hW
  have hs:=SemiprimeD1RecoveryGridBits.acquire_scalar_correct template a M u t hgW
  have hx:=SemiprimeD1RecoveryGridBits.acquire_argument_correct template a M u t hgW
  have hi:=SemiprimeD1RecoveryNodeBits.inverse_correct template a M u t hM hW
  have scaps:=scalar_caps a M u t.val hM
  have hpWidth : (a+1)*q+1 ≤ template.length := scaps.2.2.trans hW
  have hk : ∀k∈keys,k ≤ q := by simp only [keys,indices_value,List.mem_range]; exact fun k h => h.le
  have hp:=SemiprimeD1RecoveryScalarWeightBits.powers_correct template a (height M u) u t
    grid.argument hx.1 hx.2.1 hpWidth keys hk
  have hpower:=SemiprimeD1RecoveryScalarWeightBits.powers_original template a (height M u) u t
    grid.argument hx.1 hx.2.1 hpWidth
  have hmem : memory.words.map RationalWord.value=
      (SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val).inverse.coefficients.toList := by
    rw [SemiprimeSourceMemoryBits.copyMemory_words]
    have hh:=congrArg Array.toList hi.1
    simpa only [decode,Array.toList_map] using hh
  have hiv : ∀x∈memory.words,x.Valid := by
    rw [SemiprimeSourceMemoryBits.copyMemory_words]
    exact toList_valid inv.words hi.2.1
  have hjs : ∀j∈keys,j < q := by simp only [keys,indices_value,List.mem_range]; exact fun k h => h
  have hw:=weights_correct template a (height M u) u t grid.scalar memory.words powers.words
    hs.1 hs.2.1 hmem hpower hiv hp.2.1 (scaps.1.trans_le hW) (scaps.2.1.trans_le hW) keys hjs
  have hlist : keys.map (coefficient (SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val).weights)=
      (SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val).weights.toList := by
    rw [← coefficient_list]
    simp only [keys,indices_value,SemiprimeD1JetRecoveryWeights.acquire_weights_size]
    rfl
  rw [acquireAt_words]
  refine ⟨hw.1.trans hlist,hw.2.1,hw.2.2.1,?_⟩
  rw [hw.2.2.2]
  simpa only [List.map_map,Function.comp_def] using congrArg (List.map fun x:ℚ => (x.num,x.den)) hlist

/-- ORIGINAL entry point derives its own template, with no width/Fits advice. -/
theorem acquire_correct (a M u : ℕ) (t : Fin (size a)) (hM : u ≤ M) :
    let out:=SemiprimeD1RecoveryNodeBits.acquire a M u t
    let native:=SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t.val
    out.words.map RationalWord.value=native.weights.toList ∧
      (∀x∈out.words,x.Valid) ∧ (∀x∈out.words,Width x (width a M)) ∧
      out.words.map (fun x => (x.numerator.value,bitValue x.denominator))=
        native.weights.toList.map (fun x => (x.num,x.den)) := by
  have h:=acquireAt_correct (List.replicate (width a M) false) a M u t hM (by simp)
  simpa only [SemiprimeD1RecoveryNodeBits.acquire,widthRun_value,List.length_replicate] using h

/-- Exact canonical-row refinement to the frozen fully acquired native producer,
not a different mathematical coefficient array. -/
theorem acquire_canonical (a M u : ℕ) (t : Fin (size a)) (hM : u ≤ M) :
    (SemiprimeD1RecoveryNodeBits.acquire a M u t).words.map (fun x => (x.numerator.value,bitValue x.denominator))=
      (SemiprimeD1RecoveryWeightRun.acquire a M u t).rows.map (fun x => (x.numerator,x.denominator)) := by
  have h:=(acquire_correct a M u t hM).2.2.2
  rw [SemiprimeD1RecoveryWeightRun.acquire_original_rows]
  simpa only [List.map_map,Function.comp_def] using h

end RiemannGaussian.SemiprimeD1RecoveryNodeBitsCorrectness
