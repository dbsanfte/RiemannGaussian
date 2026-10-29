/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScorePredicateBits
import RiemannGaussian.SemiprimeSourceChoiceBits

/-! # Physical candidate-ID environments
The runtime stores ONLY Boolean candidate IDs and Boolean variable keys.
Original Word functions/CachedWord arrays appear solely in decode specifications.
Reverse-prefix keys are actually acquired by natBits; natural length/control
metadata remains explicit. Every selected ID and pushed key/ID is physically copied.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeSourceWordIdEnvironment
open SemiprimeRationalBits SemiprimeMaterializedWords
open SemiprimeBitArithmetic SemiprimeBitIndexClipping
open SemiprimeSourceScorePredicateBits SemiprimeSourceOffsetInputsCore
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- Physical Boolean word used as a candidate ID or variable key. -/
abbrev ID := List Bool

/-- A Boolean natural word can be compared without semantic integer extraction. -/
def idWord (id : ID) : RationalWord := ⟨⟨false,id⟩,[true]⟩

/-- The denominator-one physical key is always valid. -/
theorem idWord_valid (id : ID) : (idWord id).Valid := by
  change 0<(1:ℕ)
  decide

/-- Mathematical interpretation of an acquired key, used only by the specification. -/
theorem idWord_value (id : ID) : (idWord id).value=(bitValue id:ℚ) := by
  simp [idWord,RationalWord.value,SignedWord.value,bitValue,bitNat]

/-- Actual physical numeric key equality, including unequal padding. -/
def equalID (a b : ID) : Run Bool :=
  let out := equalWord (idWord a) (idWord b)
  ⟨out.value,out.work+3⟩

/-- Actual physical equality agrees with numeric key identity. -/
theorem equalID_correct (a b : ID) : (equalID a b).value=true ↔ bitValue a=bitValue b := by
  rw [show (equalID a b).value=(equalWord (idWord a) (idWord b)).value from rfl,
    equalWord_correct _ _ (idWord_valid a) (idWord_valid b),idWord_value,idWord_value]
  exact_mod_cast Iff.rfl

/-- Acquire a real Boolean key from an original finite natural metadata counter. -/
def acquireKey (n : ℕ) : Run ID :=
  let out := natBits n
  ⟨out.bits,out.clock+2⟩

/-- No key-value oracle is used by the actual key producer. -/
theorem acquireKey_value (n : ℕ) : bitValue (acquireKey n).value=n := natBits_value n

/-- Runtime environment contains no source Word function or original cached array. -/
structure Env where
  /-- Actual fallback candidate ID. -/
  defaultID : ID
  /-- Actual reverse-prefix candidate IDs. -/
  fixedIDs : List ID
  /-- Newest-first physical variable-key/candidate-ID overrides. -/
  overrides : List (ID × ID)

/-- Acquire original finite prefix payloads through actual physical copies. -/
def initial (defaultID : ID) (fixedIDs : List ID) : Run Env :=
  let d := SemiprimeSourceChoiceBits.copyID defaultID
  let f := SemiprimeSourceChoiceBits.copyIDs fixedIDs
  ⟨⟨d.value,f.value,[]⟩,d.work+f.work+4⟩

/-- Push an actual copied key and ID; existing immutable cache references are reused. -/
def extend (env : Env) (key id : ID) : Run Env :=
  let k := SemiprimeSourceChoiceBits.copyID key
  let v := SemiprimeSourceChoiceBits.copyID id
  ⟨⟨env.defaultID,env.fixedIDs,(k.value,v.value)::env.overrides⟩,k.work+v.work+5⟩

/-- Every candidate ID in the actual environment belongs to the acquired menu. -/
def ValidIds (menu : List ID) (env : Env) : Prop :=
  env.defaultID∈menu ∧ (∀ id∈env.fixedIDs,id∈menu) ∧
    ∀ p∈env.overrides,p.2∈menu

/-- Initialization preserves the actual acquired-menu invariant. -/
theorem initial_valid (menu : List ID) (defaultID : ID) (fixedIDs : List ID)
    (hd : defaultID∈menu) (hf : ∀ id∈fixedIDs,id∈menu) :
    ValidIds menu (initial defaultID fixedIDs).value := by
  simpa only [initial,SemiprimeSourceChoiceBits.copyID_value,SemiprimeSourceChoiceBits.copyIDs_value,
    ValidIds,List.not_mem_nil,false_implies,implies_true,and_true] using And.intro hd hf

/-- Every actual valid branch push preserves acquired-menu membership. -/
theorem extend_valid (menu : List ID) (env : Env) (key id : ID)
    (he : ValidIds menu env) (hi : id∈menu) : ValidIds menu (extend env key id).value := by
  simp only [extend,SemiprimeSourceChoiceBits.copyID_value,ValidIds] at ⊢
  refine ⟨he.1,he.2.1,?_⟩
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl|hp
  · exact hi
  · exact he.2.2 p hp

/-- Reverse-prefix lookup acquires each visited finite key and copies its selected ID. -/
def readFixed (defaultID : ID) : List ID → ID → Run ID
  | [],_ => SemiprimeSourceChoiceBits.copyID defaultID
  | id::ids,target =>
    let key := acquireKey ids.length
    let same := equalID target key.value
    if same.value then
      let out := SemiprimeSourceChoiceBits.copyID id
      ⟨out.value,key.work+same.work+out.work+ids.length+4⟩
    else
      let rest := readFixed defaultID ids target
      ⟨rest.value,key.work+same.work+rest.work+ids.length+4⟩

/-- Newest-first override scan, with actual physical key copy and lazy fallback. -/
def readOverrides (defaultID : ID) (fixedIDs : List ID) (target : ID) :
    List (ID × ID) → Run ID
  | [] => readFixed defaultID fixedIDs target
  | p::ps =>
    let key := SemiprimeSourceChoiceBits.copyID p.1
    let same := equalID key.value target
    if same.value then
      let out := SemiprimeSourceChoiceBits.copyID p.2
      ⟨out.value,key.work+same.work+out.work+4⟩
    else
      let rest := readOverrides defaultID fixedIDs target ps
      ⟨rest.value,key.work+same.work+rest.work+4⟩

/-- Runtime lookup depends only on actual Boolean key tests, never bitValue. -/
def read (env : Env) (key : ID) : Run ID :=
  readOverrides env.defaultID env.fixedIDs key env.overrides

/-- Exact original fixed-prefix finite lookup at the interpreted key. -/
theorem readFixed_value (defaultID : ID) (fixedIDs : List ID) (key : ID) :
    (readFixed defaultID fixedIDs key).value=
      (SemiprimeMaterializedWordSearch.readRun defaultID fixedIDs (bitValue key)).value := by
  induction fixedIDs with
  | nil => exact SemiprimeSourceChoiceBits.copyID_value defaultID
  | cons id ids ih =>
    have hs : (equalID key (acquireKey ids.length).value).value=true ↔ bitValue key=ids.length := by
      rw [equalID_correct,acquireKey_value]
    by_cases h : bitValue key=ids.length
    · simp only [readFixed,hs.mpr h,ite_true,SemiprimeSourceChoiceBits.copyID_value,
        SemiprimeMaterializedWordSearch.readRun,h]
    · have hn := Bool.eq_false_of_not_eq_true (fun hh => h (hs.mp hh))
      simpa only [readFixed,hn,Bool.false_eq_true,ite_false,
        SemiprimeMaterializedWordSearch.readRun,h] using ih

/-- Reference finite override lookup; this is never called by the runtime read. -/
def referenceOverrides (defaultID : ID) (fixedIDs : List ID) (i : ℕ) : List (ID × ID) → ID
  | [] => (SemiprimeMaterializedWordSearch.readRun defaultID fixedIDs i).value
  | p::ps => if bitValue p.1=i then p.2 else referenceOverrides defaultID fixedIDs i ps

/-- Actual physical override precedence refines the exact original finite lookup. -/
theorem readOverrides_value (defaultID : ID) (fixedIDs : List ID) (key : ID) (ps : List (ID × ID)) :
    (readOverrides defaultID fixedIDs key ps).value=referenceOverrides defaultID fixedIDs (bitValue key) ps := by
  induction ps with
  | nil => exact readFixed_value defaultID fixedIDs key
  | cons p ps ih =>
    have hs : (equalID p.1 key).value=true ↔ bitValue p.1=bitValue key := equalID_correct _ _
    by_cases h : bitValue p.1=bitValue key
    · simp only [readOverrides,SemiprimeSourceChoiceBits.copyID_value,hs.mpr h,ite_true,
        referenceOverrides,h]
    · have hn := Bool.eq_false_of_not_eq_true (fun hh => h (hs.mp hh))
      simpa only [readOverrides,SemiprimeSourceChoiceBits.copyID_value,hn,Bool.false_eq_true,ite_false,
        referenceOverrides,h] using ih

/-- Every selected physical ID is still an actual acquired menu member. -/
theorem read_valid (menu : List ID) (env : Env) (key : ID) (he : ValidIds menu env) :
    (read env key).value∈menu := by
  have hf (ids : List ID) (hs : ∀ id∈ids,id∈menu) : (readFixed env.defaultID ids key).value∈menu := by
    induction ids with
    | nil => simpa only [readFixed,SemiprimeSourceChoiceBits.copyID_value] using he.1
    | cons id ids ih =>
      have ht := ih (fun v hv => hs v (List.mem_cons_of_mem id hv))
      simp only [readFixed]
      split_ifs
      · simpa only [SemiprimeSourceChoiceBits.copyID_value] using hs id List.mem_cons_self
      · exact ht
  have ho (ps : List (ID × ID)) (hs : ∀ p∈ps,p.2∈menu) :
      (readOverrides env.defaultID env.fixedIDs key ps).value∈menu := by
    induction ps with
    | nil => exact hf env.fixedIDs he.2.1
    | cons p ps ih =>
      have ht := ih (fun v hv => hs v (List.mem_cons_of_mem p hv))
      simp only [readOverrides]
      split_ifs
      · simpa only [SemiprimeSourceChoiceBits.copyID_value] using hs p List.mem_cons_self
      · exact ht
  exact ho env.overrides he.2.2

/-- Original environment is a PROOF-SIDE interpretation, never runtime advice. -/
def decodeEnvironment {r Q : ℕ} (decode : ID → Word r Q) (env : Env) :
    SemiprimeMaterializedScoreEnvironment.Environment r Q :=
  ⟨SemiprimeMaterializedScoreEnvironment.cacheWord (decode env.defaultID),
    env.fixedIDs.map (fun id => SemiprimeMaterializedScoreEnvironment.cacheWord (decode id)),
    env.overrides.map (fun p => (bitValue p.1,SemiprimeMaterializedScoreEnvironment.cacheWord (decode p.2)))⟩

/-- Acquired base IDs decode to the ORIGINAL default/reverse-prefix environment. -/
theorem initial_decode {r Q : ℕ} (decode : ID → Word r Q) (defaultID : ID) (fixedIDs : List ID) :
    decodeEnvironment decode (initial defaultID fixedIDs).value=
      SemiprimeMaterializedScoreEnvironment.baseEnvironment (decode defaultID) (fixedIDs.map decode) := by
  simp only [initial,SemiprimeSourceChoiceBits.copyID_value,SemiprimeSourceChoiceBits.copyIDs_value,
    decodeEnvironment,SemiprimeMaterializedScoreEnvironment.baseEnvironment,List.map_map]
  rfl

/-- The actual physical push is exactly ORIGINAL newest-first override extension. -/
theorem extend_decode {r Q : ℕ} (decode : ID → Word r Q) (env : Env) (key id : ID) :
    decodeEnvironment decode (extend env key id).value=
      SemiprimeMaterializedScoreEnvironment.extend (decodeEnvironment decode env) (bitValue key) (decode id) := by
  simp only [extend,SemiprimeSourceChoiceBits.copyID_value,decodeEnvironment,
    SemiprimeMaterializedScoreEnvironment.extend,List.map_cons]

/-- Actual menu-valid environment relation used by the count refinement. -/
def Rel {r Q : ℕ} (menu : List ID) (decode : ID → Word r Q) (physical : Env)
    (original : SemiprimeMaterializedScoreEnvironment.Environment r Q) : Prop :=
  ValidIds menu physical ∧ original=decodeEnvironment decode physical

/-- The concrete physical branch push preserves ORIGINAL count environments. -/
theorem extend_rel {r Q : ℕ} (menu : List ID) (decode : ID → Word r Q)
    (physical : Env) (original : SemiprimeMaterializedScoreEnvironment.Environment r Q)
    (key id : ID) (h : Rel menu decode physical original) (hi : id∈menu) :
    Rel menu decode (extend physical key id).value
      (SemiprimeMaterializedScoreEnvironment.extend original (bitValue key) (decode id)) := by
  refine ⟨extend_valid menu physical key id h.1 hi,?_⟩
  rw [h.2,extend_decode]

/-- Mapping original fixed-prefix values commutes with its literal finite scan. -/
theorem readRun_decode {r Q : ℕ} (decode : ID → Word r Q) (defaultID : ID)
    (fixedIDs : List ID) (i : ℕ) :
    (SemiprimeMaterializedWordSearch.readRun
      (SemiprimeMaterializedScoreEnvironment.cacheWord (decode defaultID))
      (fixedIDs.map (fun id => SemiprimeMaterializedScoreEnvironment.cacheWord (decode id))) i).value=
      SemiprimeMaterializedScoreEnvironment.cacheWord
        (decode (SemiprimeMaterializedWordSearch.readRun defaultID fixedIDs i).value) := by
  induction fixedIDs with
  | nil => rfl
  | cons id ids ih =>
    simp only [List.map_cons,SemiprimeMaterializedWordSearch.readRun,List.length_map]
    split_ifs <;> simp only [ih]

/-- Original override precedence commutes with the proof-side ID decoding. -/
theorem overrides_decode {r Q : ℕ} (decode : ID → Word r Q) (defaultID : ID)
    (fixedIDs : List ID) (i : ℕ) (ps : List (ID × ID)) :
    (SemiprimeMaterializedScoreEnvironment.readOverrides
      (SemiprimeMaterializedScoreEnvironment.cacheWord (decode defaultID))
      (fixedIDs.map (fun id => SemiprimeMaterializedScoreEnvironment.cacheWord (decode id))) i
      (ps.map (fun p => (bitValue p.1,SemiprimeMaterializedScoreEnvironment.cacheWord (decode p.2))))).value=
      SemiprimeMaterializedScoreEnvironment.cacheWord (decode (referenceOverrides defaultID fixedIDs i ps)) := by
  induction ps with
  | nil => exact readRun_decode decode defaultID fixedIDs i
  | cons p ps ih =>
    simp only [List.map_cons,SemiprimeMaterializedScoreEnvironment.readOverrides,referenceOverrides]
    split_ifs <;> simp only [ih]

/-- The ACTUAL selected physical ID denotes exactly the ORIGINAL environment read. -/
theorem read_decode {r Q : ℕ} (decode : ID → Word r Q) (env : Env) (key : ID) :
    SemiprimeMaterializedScoreEnvironment.wordAt
      (SemiprimeMaterializedScoreEnvironment.readEnv (decodeEnvironment decode env) (bitValue key)).value=
        decode (read env key).value := by
  rw [show (read env key).value=referenceOverrides env.defaultID env.fixedIDs (bitValue key) env.overrides from
    readOverrides_value env.defaultID env.fixedIDs key env.overrides]
  change SemiprimeMaterializedScoreEnvironment.wordAt
    (SemiprimeMaterializedScoreEnvironment.readOverrides _ _ _ _).value=_
  dsimp only [decodeEnvironment]
  rw [overrides_decode,SemiprimeMaterializedScoreEnvironment.wordAt_cacheWord]

/-- Actual physical key/ID copies pay the complete branch-push report. -/
theorem extend_work (env : Env) (key id : ID) :
    (extend env key id).work ≤ 4*key.length+4*id.length+9 := by
  have hk := SemiprimeSourceChoiceBits.copyID_work key
  have hi := SemiprimeSourceChoiceBits.copyID_work id
  simp only [extend]
  omega

/-- Actual initial prefix copies have a bound in original finite ID payloads. -/
theorem initial_work (defaultID : ID) (fixedIDs : List ID) (B : ℕ)
    (hf : ∀ id∈fixedIDs,id.length ≤ B) :
    (initial defaultID fixedIDs).work ≤ 4*defaultID.length+fixedIDs.length*(4*B+4)+7 := by
  have hd := SemiprimeSourceChoiceBits.copyID_work defaultID
  have hp := SemiprimeSourceChoiceBits.copyIDs_work fixedIDs B hf
  simp only [initial]
  omega

/-- Finite metadata key acquisition executes the actual Boolean-adder producer. -/
theorem acquireKey_work (n : ℕ) : (acquireKey n).work ≤ 20*(n+1)^2+2 := by
  have h := natBits_clock n
  simp only [acquireKey]
  omega

end RiemannGaussian.SemiprimeSourceWordIdEnvironment
