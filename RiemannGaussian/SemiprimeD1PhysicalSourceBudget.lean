/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalModeAcquisition

/-! # Original acquired source report in actual menu size
The sparse packet selector/replay and complete catalogue/enumerator reports are
retained. No capacity, accepted guard, desired tuple list or source-work answer
is assumed. This is the actual mixed native/physical source report.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1PhysicalSourceBudget

/-- Explicit source polynomial with the actual observed packet/menu counts. -/
def budget (n F r a M u i p packets P modes : ℕ) : ℕ :=
  SemiprimeD1PacketReplayBudget.budget n F r a M+
  SemiprimeD1WeightedCardinality.modeFactor (packets*2^(i+1)) P*modes+
  SemiprimeD1WeightedCardinality.modeOverhead (packets*2^(i+1)) P+
  M+packets+a+i+u+p+20

/-- The acquired real port inventory has the literal original incidence count. -/
theorem placements_length (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F)×Fin (arity e)) → Fin n) :
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length=∑e,arity e := by
  have h:=congrArg List.length (SemiprimeD1PacketReplayOriginal.sources n F r a arity owner)
  simpa only [List.length_map,SemiprimeD1IncidenceAcquisitionBounds.keys_length] using h

/-- Every actual source supplier call is bounded in its ACTUAL output menu size.
Later resource substitution must retain this factor every time the caller
repeats the source/header report, rather than charging acquisition once. -/
theorem acquire_work (n F r a u i p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F)×Fin (arity e)) → Fin n) :
    let source:=SemiprimeD1OriginalModeAcquisition.acquire n F r a u i p arity owner
    source.work ≤ budget n F r a (∑e,arity e) u i p
      source.packets.state.packets.length (source.precision-1) source.modes.values.length := by
  let packets:=SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner
  let P:=SemiprimeD1ModeRate.workingPrecision packets.placements.length u a i p-1
  have hr:=SemiprimeD1PacketReplayBudget.acquire_work n F r a arity owner
  have hm:=SemiprimeD1ModeCatalog.acquireModes_work_le packets.state.packets.length (2^(i+1)) P
  have hlen:=placements_length n F r a arity owner
  change packets.state.clock+
      (SemiprimeD1ModeCatalog.acquireModes packets.state.packets.length (2^(i+1)) P).work+
      packets.placements.length+packets.state.packets.length+a+i+u+p+20 ≤ _
  change _ ≤ SemiprimeD1PacketReplayBudget.budget n F r a (∑e,arity e)+
    SemiprimeD1WeightedCardinality.modeFactor (packets.state.packets.length*2^(i+1)) P*
      (SemiprimeD1ModeCatalog.acquireModes packets.state.packets.length (2^(i+1)) P).values.length+
    SemiprimeD1WeightedCardinality.modeOverhead (packets.state.packets.length*2^(i+1)) P+
    (∑e,arity e)+packets.state.packets.length+a+i+u+p+20
  change packets.state.clock ≤ _ at hr
  change packets.placements.length=∑e,arity e at hlen
  simp only [SemiprimeD1WeightedCardinality.modeFactor,
    SemiprimeD1WeightedCardinality.modeOverhead] at ⊢
  omega

/-- Positive weighted degree bounds each actual retained tuple coordinate. -/
theorem exponent_le_degree (ws es : List ℕ) (hw : ∀ w ∈ ws, 0 < w)
    (hl : es.length=ws.length) (e : ℕ) (he : e ∈ es) :
    e ≤ SemiprimeD1WeightedTuples.degree ws es := by
  induction ws generalizing es with
  | nil => cases es <;> simp_all
  | cons w ws ih =>
    cases es with
    | nil => simp at he
    | cons x xs =>
      have hwt : ∀ y ∈ ws, 0 < y := fun y hy => hw y (by simp [hy])
      have hlt : xs.length=ws.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl
      simp only [List.mem_cons] at he
      simp only [SemiprimeD1WeightedTuples.degree]
      rcases he with he|he
      · subst e
        have hm:=Nat.mul_le_mul_right x (show 1 ≤ w from hw w (by simp))
        simp only [Nat.one_mul] at hm
        omega
      · have ht:=ih xs hwt hlt he
        omega

/-- Actual acquired modes have original catalogue length and bounded exponents;
no mode/count/vector answer or coordinate-width advice is supplied. -/
theorem mode_bounds (n F r a u i p : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F)×Fin (arity e)) → Fin n) (beta : List ℕ)
    (hb : beta ∈ (SemiprimeD1OriginalModeAcquisition.acquire n F r a u i p arity owner).modes.values) :
    let source:=SemiprimeD1OriginalModeAcquisition.acquire n F r a u i p arity owner
    beta.length=(source.precision-1)*(source.packets.state.packets.length*2^(i+1)) ∧
      ∀ b ∈ beta, b ≤ source.precision-1 := by
  let source:=SemiprimeD1OriginalModeAcquisition.acquire n F r a u i p arity owner
  let slots:=source.packets.state.packets.length*2^(i+1)
  let P:=source.precision-1
  have hm : beta ∈ (SemiprimeD1ModeCatalog.acquireModes source.packets.state.packets.length
      (2^(i+1)) P).values := hb
  have ha:=(SemiprimeD1ModeCatalog.acquireModes_correct source.packets.state.packets.length
    (2^(i+1)) P beta).1.mp hm
  have hl : beta.length=P*slots := by
    simpa only [SemiprimeD1ModeCatalog.weights,List.length_map,
      SemiprimeD1ModeCatalog.catalog_length] using ha.1
  refine ⟨hl,?_⟩
  intro b hb
  exact (exponent_le_degree _ beta (SemiprimeD1ModeCatalog.weights_positive slots P) ha.1 b hb).trans ha.2

end RiemannGaussian.SemiprimeD1PhysicalSourceBudget
