/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreCountBitsCore
import RiemannGaussian.SemiprimeSourceScoreCountsObjective

/-! # Physical candidate-ID completion counts
The internal push/terminal interfaces are fixed to concrete physical environment
operations by the original-bank caller. No Word-valued override is constructed
by this runtime recursion.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceWordIdCountsCore
open SemiprimeMaterializedWords SemiprimeSourceOffsetInputsCore SemiprimeBitArithmetic
open SemiprimeSourceScoreCountBitsCore
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedScoreEnvironment

/-- Acquire physical keys from the actual finite native active-ID scan. -/
def acquireKeys : List ℕ→ Run (List (List Bool))
  | [] => ⟨[],1⟩
  | i::is => let key:=natBits i
             let rest:=acquireKeys is
             ⟨key.bits::rest.value,key.clock+rest.work+key.bits.length+3⟩

/-- The acquired keys are exactly the original numeric IDs, in the same order. -/
theorem acquireKeys_values (is : List ℕ) : (acquireKeys is).value.map bitValue=is := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [acquireKeys,List.map_cons,natBits_value,ih]

/-- No hidden key enumeration or extra completion level is introduced. -/
theorem acquireKeys_length (is : List ℕ) : (acquireKeys is).value.length=is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [acquireKeys,List.length_cons,ih]

/-- Actual finite-key acquisition has a polynomial original-ID budget. -/
theorem acquireKeys_work (is : List ℕ) (N : ℕ) (h : ∀ i∈is,i≤ N) :
    (acquireKeys is).work≤ is.length*(20*(N+1)^2+N+4)+1 := by
  induction is with
  | nil => simp [acquireKeys]
  | cons i is ih =>
    have hi:=h i List.mem_cons_self
    have ht:=ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have hc:=(natBits_clock i).trans (show 20*(i+1)^2≤20*(N+1)^2 from by gcongr)
    have hl:=natBits_length i
    simp only [acquireKeys,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Every acquired physical key has its ORIGINAL numeric-ID width. -/
theorem acquireKeys_bound (is : List ℕ) (N : ℕ) (h : ∀ i∈is,i≤ N) :
    ∀ key∈(acquireKeys is).value,key.length≤ N+1 := by
  induction is with
  | nil => simp [acquireKeys]
  | cons i is ih =>
    intro key hk
    simp only [acquireKeys,List.mem_cons] at hk
    rcases hk with rfl|hk
    · exact (natBits_length i).trans (Nat.add_le_add_right (h i List.mem_cons_self) 1)
    · exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) key hk

/-- Count actual Boolean terminal outputs over acquired physical IDs and keys.
The pushed environment and EVERY push/child/adder report are cached and retained. -/
def count {σ : Type*} (ids : List (List Bool))
    (push : σ→ List Bool→ List Bool→ Run σ) (terminal : σ→ Run Bool) :
    List (List Bool)→σ→ NatRun
  | [],env => let out:=terminal env
              ⟨if out.value then [true] else [],out.work+2⟩
  | key::keys,env =>
    let out:=sumBits (fun id =>
      let next:=push env key id
      let child:=count ids push terminal keys next.value
      ⟨child.bits,next.work+child.clock+3⟩) ids
    ⟨out.bits,out.clock+ids.length+3⟩

/-- Internal refinement theorem. The concrete bank/environment endpoint discharges
both obligations; no truth/count callback premise remains there. -/
theorem count_value {σ : Type*} {r Q : ℕ} (ids : List (List Bool))
    (push : σ→ List Bool→ List Bool→ Run σ) (terminal : σ→ Run Bool)
    (decode : List Bool→ Word r Q) (p : ScoreProgram Q)
    (Rel : σ→ Environment r Q→ Prop)
    (ht : ∀ env native,Rel env native→(terminal env).value=(SemiprimeSourceScoreCounts.hit p native).value)
    (hp : ∀ env native key id,Rel env native→ id∈ids→
      Rel (push env key id).value (extend native (bitValue key) (decode id)))
    (keys : List (List Bool)) (env : σ) (native : Environment r Q) (hrel : Rel env native) :
    bitValue (count ids push terminal keys env).bits=
      (SemiprimeSourceScoreCounts.count (ids.map decode) p (keys.map bitValue) native).value := by
  induction keys generalizing env native with
  | nil =>
    simp only [count,SemiprimeSourceScoreCounts.count,List.map_nil,ht env native hrel]
    split <;> simp [bitValue,bitNat]
  | cons key keys ih =>
    simp only [count,sumBits_value,SemiprimeSourceScoreCounts.count,
      SemiprimeSourceScoreCounts.sumCount_value,List.map_cons,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro id hid
    exact ih (push env key id).value (extend native (bitValue key) (decode id))
      (hp env native key id hrel hid)

/-- Structural count-word width, independent of any desired answer or Fits. -/
theorem count_length {σ : Type*} (ids : List (List Bool))
    (push : σ→ List Bool→ List Bool→ Run σ) (terminal : σ→ Run Bool)
    (keys : List (List Bool)) (env : σ) :
    (count ids push terminal keys env).bits.length≤1+keys.length*ids.length := by
  induction keys generalizing env with
  | nil => simp only [count,List.length_nil,Nat.zero_mul];split <;> simp
  | cons key keys ih =>
    have h:=sumBits_length (fun id =>
      let next:=push env key id
      let child:=count ids push terminal keys next.value
      (⟨child.bits,next.work+child.clock+3⟩:NatRun)) ids (1+keys.length*ids.length)
      (fun id _ => ih (push env key id).value)
    simpa only [count,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using h

/-- Acquire the original active keys once, then count and pad using only physical IDs. -/
def padded {σ : Type*} {Q : ℕ} (ids : List (List Bool))
    (push : σ→ List Bool→ List Bool→ Run σ) (terminal : σ→ Run Bool)
    (p : ScoreProgram Q) (remaining : List ℕ) (env : σ) : NatRun :=
  let active:=activeRun (support p) remaining
  let keys:=acquireKeys active.value
  let raw:=count ids push terminal keys.value env
  let pad:=unaryPower ids.length (4-active.value.length)
  let encoded:=natBits pad.cells.length
  let out:=mulBits raw.bits encoded.bits
  ⟨out.bits,active.work+keys.work+raw.clock+pad.clock+pad.cells.length+encoded.clock+bitCost out+20⟩

/-- Acquired physical keys introduce no native Word-valued extension. -/
theorem padded_value {σ : Type*} {r Q : ℕ} (ids : List (List Bool))
    (push : σ→ List Bool→ List Bool→ Run σ) (terminal : σ→ Run Bool)
    (decode : List Bool→ Word r Q) (p : ScoreProgram Q)
    (Rel : σ→ Environment r Q→ Prop)
    (ht : ∀ env native,Rel env native→(terminal env).value=(SemiprimeSourceScoreCounts.hit p native).value)
    (hp : ∀ env native key id,Rel env native→ id∈ids→
      Rel (push env key id).value (extend native (bitValue key) (decode id)))
    (remaining : List ℕ) (env : σ) (native : Environment r Q) (hrel : Rel env native) :
    bitValue (padded ids push terminal p remaining env).bits=
      (SemiprimeSourceScoreCountsPadding.paddedLocal (ids.map decode) p remaining native).value := by
  simp only [padded,mulBits_correct,natBits_value,unaryPower_length,
    count_value ids push terminal decode p Rel ht hp _ env native hrel,acquireKeys_values,
    SemiprimeSourceScoreCountsPadding.paddedLocal,
    (SemiprimeSourceScoreCountsPadding.power_spec _ _).1,List.length_map]

/-- Actual two physical count lanes and retained branch work. -/
structure Counts where
  /-- Incidence multiplicities. -/
  incidence : List Bool
  /-- Head multiplicities. -/
  head : List Bool
  /-- Every executed local count and lane adder. -/
  clock : ℕ

/-- Evaluate original score descriptors over physical ID environments. -/
def evaluate {σ : Type*} {Q : ℕ} (ids : List (List Bool))
    (push : σ→ List Bool→ List Bool→ Run σ) (terminal : ScoreProgram Q→σ→ Run Bool) :
    List (ScoreProgram Q)→ List ℕ→σ→ Counts
  | [],_,_ => ⟨[],[],1⟩
  | p::programs,remaining,env =>
    let this:=padded ids push (terminal p) p remaining env
    let rest:=evaluate ids push terminal programs remaining env
    match p with
    | .incidence _ _ _ _ =>
      let out:=addBits this.bits rest.incidence false
      ⟨out.bits,rest.head,this.clock+rest.clock+bitCost out+8⟩
    | .head _ _ _ =>
      let out:=addBits this.bits rest.head false
      ⟨rest.incidence,out.bits,this.clock+rest.clock+bitCost out+8⟩

/-- Internal lane refinement from the actual pushed environment relation. -/
theorem evaluate_value {σ : Type*} {r Q : ℕ} (ids : List (List Bool))
    (push : σ→ List Bool→ List Bool→ Run σ) (terminal : ScoreProgram Q→σ→ Run Bool)
    (decode : List Bool→ Word r Q) (Rel : σ→ Environment r Q→ Prop)
    (ht : ∀ p env native,Rel env native→(terminal p env).value=(SemiprimeSourceScoreCounts.hit p native).value)
    (hp : ∀ env native key id,Rel env native→ id∈ids→
      Rel (push env key id).value (extend native (bitValue key) (decode id)))
    (programs : List (ScoreProgram Q)) (remaining : List ℕ) (env : σ)
    (native : Environment r Q) (hrel : Rel env native) :
    bitValue (evaluate ids push terminal programs remaining env).incidence=
      (SemiprimeSourceScoreCountsObjective.evaluateCounts (ids.map decode) programs remaining native).value.incidence ∧
    bitValue (evaluate ids push terminal programs remaining env).head=
      (SemiprimeSourceScoreCountsObjective.evaluateCounts (ids.map decode) programs remaining native).value.head := by
  induction programs with
  | nil => exact ⟨rfl,rfl⟩
  | cons p programs ih =>
    have ht':=padded_value ids push (terminal p) decode p Rel (ht p) hp remaining env native hrel
    cases p <;> simp only [evaluate,SemiprimeSourceScoreCountsObjective.evaluateCounts,
      addBits_correct,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero,ht',ih.1,ih.2,and_self]

end RiemannGaussian.SemiprimeSourceWordIdCountsCore
