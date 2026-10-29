/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdEnvironment
import RiemannGaussian.SemiprimeSourceScorePredicateBitsBounds

/-! # Actual physical ID environment costs
Every key/ID comparison and copy is charged. The only premises bound original
finite metadata/payload lists, not truth, fits or unknown callback work.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeSourceWordIdEnvironmentBounds
open SemiprimeRationalBits SemiprimeMaterializedWords SemiprimeSourceWordIdEnvironment
open SemiprimeSourceOffsetInputsCore SemiprimeReportPolynomialGrowth

/-- Actual stored variable keys retain an original physical width cap. -/
def KeysBound (K : ℕ) (env : Env) : Prop := ∀ p∈env.overrides,p.1.length ≤ K
/-- Actual stored candidate payloads have a finite acquired-menu width cap. -/
def PayloadBound (B : ℕ) (env : Env) : Prop :=
  env.defaultID.length ≤ B ∧ (∀ id∈env.fixedIDs,id.length ≤ B) ∧
    ∀ p∈env.overrides,p.2.length ≤ B

/-- Original acquired-menu membership supplies all candidate-ID payload bounds. -/
theorem valid_payload (menu : List ID) (env : Env) (B : ℕ)
    (he : ValidIds menu env) (hm : ∀ id∈menu,id.length ≤ B) : PayloadBound B env :=
  ⟨hm _ he.1,fun id hi => hm id (he.2.1 id hi),fun p hp => hm _ (he.2.2 p hp)⟩

/-- Physical acquired keys have the actual natural-encoding length bound. -/
theorem acquireKey_length (n : ℕ) : (acquireKey n).value.length ≤ n+1 := natBits_length n

/-- One denominator-one key has exactly its original Boolean payload width. -/
theorem idWord_width (id : ID) (W : ℕ) (hW : 1 ≤ W) (hi : id.length ≤ W) : Width (idWord id) W :=
  ⟨hi,by simpa only [idWord,List.length_cons,List.length_nil] using hW⟩

/-- Actual double signed comparison and key record construction. -/
def eqBudget (W : ℕ) : ℕ := 400*(W+1)^2+6

/-- Key equality cost is derived from actual bit payloads, not numeric ID values. -/
theorem equalID_work (a b : ID) (W : ℕ) (hW : 1 ≤ W)
    (ha : a.length ≤ W) (hb : b.length ≤ W) :
    (equalID a b).work ≤ eqBudget W := by
  have h := SemiprimeSourceScorePredicateBitsBounds.equalWord_work (idWord a) (idWord b) W
    (idWord_width a W hW ha) (idWord_width b W hW hb)
  unfold equalID eqBudget SemiprimeSourceScorePredicateBitsBounds.equalityBudget at *
  dsimp only at *
  omega

/-- Full returned candidate-ID copy. -/
def idCopyBudget (B : ℕ) : ℕ := 4*B+2
/-- Actual finite reverse-prefix key acquisition. -/
def keyBudget (N : ℕ) : ℕ := 20*(N+1)^2+2
/-- A conservative original-metadata budget for either fixed or override visits. -/
def scanStep (K N B : ℕ) : ℕ :=
  keyBudget N+idCopyBudget K+eqBudget (K+N+2)+idCopyBudget B+N+10
/-- Both original finite scans plus their actual selected/default ID copy. -/
def readBudget (K N B s : ℕ) : ℕ := (N+s)*scanStep K N B+idCopyBudget B

/-- Physical reverse-prefix lookup pays every actual key producer, comparison and copy. -/
theorem readFixed_work (defaultID : ID) (fixedIDs : List ID) (target : ID) (K N B : ℕ)
    (hd : defaultID.length ≤ B) (hf : ∀ id∈fixedIDs,id.length ≤ B)
    (hn : fixedIDs.length ≤ N) (ht : target.length ≤ K) :
    (readFixed defaultID fixedIDs target).work ≤ fixedIDs.length*scanStep K N B+idCopyBudget B := by
  induction fixedIDs with
  | nil =>
    simpa only [readFixed,List.length_nil,Nat.zero_mul,Nat.zero_add,idCopyBudget] using
      (SemiprimeSourceChoiceBits.copyID_work defaultID).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hd) 2)
  | cons id ids ih =>
    have hlen : ids.length ≤ N := by simp only [List.length_cons] at hn;omega
    have htail := ih (fun v hv => hf v (List.mem_cons_of_mem id hv)) hlen
    have hk := (acquireKey_work ids.length).trans
      (show 20*(ids.length+1)^2+2 ≤ keyBudget N by unfold keyBudget;gcongr)
    have heq := equalID_work target (acquireKey ids.length).value (K+N+2) (by omega)
      (by omega) ((acquireKey_length ids.length).trans (by omega))
    have hv := (SemiprimeSourceChoiceBits.copyID_work id).trans
      (show 4*id.length+2 ≤ idCopyBudget B by unfold idCopyBudget;gcongr;exact hf id List.mem_cons_self)
    simp only [readFixed,List.length_cons]
    unfold scanStep at htail ⊢
    split_ifs <;> dsimp only <;> nlinarith

/-- Physical newest-override lookup retains both possible scan paths honestly. -/
theorem readOverrides_work (defaultID : ID) (fixedIDs : List ID) (target : ID)
    (ps : List (ID × ID)) (K N B : ℕ)
    (hd : defaultID.length ≤ B) (hf : ∀ id∈fixedIDs,id.length ≤ B) (hn : fixedIDs.length ≤ N)
    (ht : target.length ≤ K) (hk : ∀ p∈ps,p.1.length ≤ K) (hv : ∀ p∈ps,p.2.length ≤ B) :
    (readOverrides defaultID fixedIDs target ps).work ≤
      ps.length*scanStep K N B+fixedIDs.length*scanStep K N B+idCopyBudget B := by
  induction ps with
  | nil => simpa only [readOverrides,List.length_nil,Nat.zero_mul,Nat.zero_add] using
      readFixed_work defaultID fixedIDs target K N B hd hf hn ht
  | cons p ps ih =>
    have htail := ih (fun v hv => hk v (List.mem_cons_of_mem p hv))
      (fun v hp => hv v (List.mem_cons_of_mem p hp))
    have hkey := (SemiprimeSourceChoiceBits.copyID_work p.1).trans
      (show 4*p.1.length+2 ≤ idCopyBudget K by unfold idCopyBudget;gcongr;exact hk p List.mem_cons_self)
    have heq := equalID_work (SemiprimeSourceChoiceBits.copyID p.1).value target (K+N+2) (by omega)
      (by rw [SemiprimeSourceChoiceBits.copyID_value];have := hk p List.mem_cons_self;omega) (by omega)
    have hout := (SemiprimeSourceChoiceBits.copyID_work p.2).trans
      (show 4*p.2.length+2 ≤ idCopyBudget B by unfold idCopyBudget;gcongr;exact hv p List.mem_cons_self)
    simp only [readOverrides,List.length_cons]
    unfold scanStep at htail ⊢
    split_ifs <;> dsimp only <;> nlinarith

/-- Original finite environment caps close actual read work, with no decoder callback. -/
theorem read_work (env : Env) (target : ID) (K N B s : ℕ)
    (hp : PayloadBound B env) (hk : KeysBound K env)
    (hf : env.fixedIDs.length ≤ N) (ho : env.overrides.length ≤ s) (ht : target.length ≤ K) :
    (read env target).work ≤ readBudget K N B s := by
  have h := readOverrides_work env.defaultID env.fixedIDs target env.overrides K N B
    hp.1 hp.2.1 hf ht hk hp.2.2
  apply h.trans
  unfold readBudget
  have hm := Nat.add_le_add (Nat.mul_le_mul_right (scanStep K N B) ho)
    (Nat.mul_le_mul_right (scanStep K N B) hf)
  nlinarith

/-- Actual count pushes preserve the physical variable-key cap. -/
theorem extend_keys (env : Env) (key id : ID) (K : ℕ)
    (he : KeysBound K env) (hk : key.length ≤ K) : KeysBound K (extend env key id).value := by
  simp only [KeysBound,extend,SemiprimeSourceChoiceBits.copyID_value]
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl|hp
  · exact hk
  · exact he p hp

/-- The ORIGINAL fixed prefix is unchanged by a local branch push. -/
theorem extend_fixed_length (env : Env) (key id : ID) :
    (extend env key id).value.fixedIDs.length=env.fixedIDs.length := rfl

/-- Exactly one actual override pair is added by the local branch push. -/
theorem extend_override_length (env : Env) (key id : ID) :
    (extend env key id).value.overrides.length=env.overrides.length+1 := rfl

end RiemannGaussian.SemiprimeSourceWordIdEnvironmentBounds
