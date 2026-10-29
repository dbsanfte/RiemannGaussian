/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHeadCountBitsBounds
import RiemannGaussian.SemiprimeSourceIncidenceCountBits
import RiemannGaussian.SemiprimeSourceIncidenceNamespaces
import RiemannGaussian.SemiprimeSourceWordIdCounts

/-! # Complete source-score callback using classified physical collision counts
Both local counters copy acquired powers and execute only the needed fixed tests.
No completion enumeration, unary count padding or native count answer is used.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceClassifiedCounts
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedScoreEnvironment (ScoreProgram)
open SemiprimeSourceWordBank (Bank)
open SemiprimeSourceWordIdEnvironment (Env Rel ValidIds)
open SemiprimeSourceCountPowers (Powers)
open SemiprimeSourceWordIdCountsCore (Counts)
open SemiprimeSourceOffsetInputsCore SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeSourceIncidenceNamespaces (Separated)

/-- Dispatch the original descriptor to its actual classified physical counter. -/
def localCount {Q : ℕ} (bank : Bank) (powers : Powers) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Env) : NatRun :=
  match p with
  | .incidence a b c d => SemiprimeSourceIncidenceCountBits.count env powers a b c d remaining
  | .head q a b => SemiprimeSourceHeadCountBits.count bank env powers q a b remaining

/-- Every compiled separated local descriptor gives its ACTUAL original padded count. -/
theorem local_original (r Q : ℕ) [NeZero r] (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Env)
    (original : SemiprimeMaterializedScoreEnvironment.Environment r Q)
    (hn : remaining.Nodup)
    (he : Rel (SemiprimeSourceWordBank.acquire r Q).ids
      (SemiprimeSourceWordBankSemantics.decode r Q) env original) (hp : Separated p) :
    bitValue (localCount (SemiprimeSourceWordBank.acquire r Q)
      (SemiprimeSourceCountPowers.acquire r Q) p remaining env).bits=
      (SemiprimeSourceScoreCountsPadding.paddedLocal (SemiprimeFiniteEnumerations.words r Q).values
        p remaining original).value := by
  cases p with
  | incidence a b c d =>
    exact SemiprimeSourceIncidenceCountBits.count_original r Q env original a b c d remaining hn he
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  | head q a b => exact SemiprimeSourceHeadCountBits.count_original r Q env original q a b remaining hn he

/-- Both optimized local counters return copies bounded by the actual acquired cache. -/
theorem local_length (r Q : ℕ) (p : ScoreProgram Q) (remaining : List ℕ) (env : Env) :
    (localCount (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      p remaining env).bits.length ≤ SemiprimeSourceCountPowers.width r Q := by
  cases p with
  | incidence a b c d => exact SemiprimeSourceIncidenceCountBits.acquired_length r Q env a b c d remaining
  | head q a b => exact SemiprimeSourceHeadCountBits.acquired_length r Q env q a b remaining

/-- Evaluate each original descriptor once and accumulate its correct physical lane. -/
def evaluate {Q : ℕ} (bank : Bank) (powers : Powers) :
    List (ScoreProgram Q) → List ℕ → Env → Counts
  | [],_,_ => ⟨[],[],1⟩
  | p::programs,remaining,env =>
    let this := localCount bank powers p remaining env
    let rest := evaluate bank powers programs remaining env
    match p with
    | .incidence _ _ _ _ =>
      let out := addBits this.bits rest.incidence false
      ⟨out.bits,rest.head,this.clock+rest.clock+bitCost out+8⟩
    | .head _ _ _ =>
      let out := addBits this.bits rest.head false
      ⟨rest.incidence,out.bits,this.clock+rest.clock+bitCost out+8⟩

/-- Actual original finite counts, for all separated descriptors and original environments. -/
theorem evaluate_original (r Q : ℕ) [NeZero r] (programs : List (ScoreProgram Q))
    (remaining : List ℕ) (env : Env)
    (original : SemiprimeMaterializedScoreEnvironment.Environment r Q)
    (hn : remaining.Nodup)
    (he : Rel (SemiprimeSourceWordBank.acquire r Q).ids
      (SemiprimeSourceWordBankSemantics.decode r Q) env original)
    (hp : ∀ p∈programs,Separated p) :
    bitValue (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      programs remaining env).incidence=
      (SemiprimeSourceScoreCountsObjective.evaluateCounts (SemiprimeFiniteEnumerations.words r Q).values
        programs remaining original).value.incidence ∧
    bitValue (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      programs remaining env).head=
      (SemiprimeSourceScoreCountsObjective.evaluateCounts (SemiprimeFiniteEnumerations.words r Q).values
        programs remaining original).value.head := by
  induction programs with
  | nil => exact ⟨rfl,rfl⟩
  | cons p programs ih =>
    have ht := local_original r Q p remaining env original hn he (hp p List.mem_cons_self)
    have hrest := ih (fun p h => hp p (List.mem_cons_of_mem _ h))
    cases p <;> simp only [evaluate,SemiprimeSourceScoreCountsObjective.evaluateCounts,
      addBits_correct,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero,ht,hrest.1,hrest.2,and_self]

/-- Every lane/suffix width is the acquired local width plus actual adder count, not L^4. -/
theorem evaluate_length (r Q : ℕ) (programs : List (ScoreProgram Q)) (remaining : List ℕ) (env : Env) :
    (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      programs remaining env).incidence.length ≤ SemiprimeSourceCountPowers.width r Q+programs.length ∧
    (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      programs remaining env).head.length ≤ SemiprimeSourceCountPowers.width r Q+programs.length := by
  induction programs with
  | nil => simp [evaluate]
  | cons p programs ih =>
    have ht := local_length r Q p remaining env
    have hi := (addBits_counts
      (localCount (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) p remaining env).bits
      (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) programs remaining env).incidence false).2.2.2.2
    have hh := (addBits_counts
      (localCount (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) p remaining env).bits
      (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) programs remaining env).head false).2.2.2.2
    cases p <;> simp only [evaluate,List.length_cons] <;> constructor <;> omega

/-- Lane interpretation agrees with the prior actually executed physical count evaluator. -/
theorem evaluate_eq (r Q : ℕ) [NeZero r] (programs : List (ScoreProgram Q))
    (remaining : List ℕ) (env : Env) (hn : remaining.Nodup)
    (he : ValidIds (SemiprimeSourceWordBank.acquire r Q).ids env)
    (hp : ∀ p∈programs,Separated p) :
    bitValue (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      programs remaining env).incidence=
      bitValue (SemiprimeSourceWordIdCounts.evaluate (SemiprimeSourceWordBank.acquire r Q) programs remaining env).incidence ∧
    bitValue (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      programs remaining env).head=
      bitValue (SemiprimeSourceWordIdCounts.evaluate (SemiprimeSourceWordBank.acquire r Q) programs remaining env).head := by
  have hnew := evaluate_original r Q programs remaining env
    (SemiprimeSourceWordIdEnvironment.decodeEnvironment (SemiprimeSourceWordBankSemantics.decode r Q) env)
    hn ⟨he,rfl⟩ hp
  have hold := SemiprimeSourceWordIdCounts.evaluate_original r Q programs remaining env he
  exact ⟨hnew.1.trans hold.1.symm,hnew.2.trans hold.2.symm⟩

/-- Copy the actual ID prefix, then use classified counts on the original remaining range. -/
def sequential {Q : ℕ} (bank : Bank) (powers : Powers) (defaultID : List Bool)
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool)) : Counts :=
  let initial := SemiprimeSourceWordIdEnvironment.initial defaultID fixedIDs
  let out := evaluate bank powers programs (List.range' fixedIDs.length n) initial.value
  ⟨out.incidence,out.head,initial.work+out.clock+fixedIDs.length+n+8⟩

/-- Exact prior sequential count values for every reachable acquired-ID prefix. -/
theorem sequential_eq (r Q : ℕ) [NeZero r] (defaultID : List Bool) (programs : List (ScoreProgram Q))
    (n : ℕ) (fixedIDs : List (List Bool))
    (hd : defaultID∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hf : ∀ id∈fixedIDs,id∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hp : ∀ p∈programs,Separated p) :
    bitValue (sequential (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      defaultID programs n fixedIDs).incidence=
      bitValue (SemiprimeSourceWordIdCounts.sequential (SemiprimeSourceWordBank.acquire r Q)
        defaultID programs n fixedIDs).incidence ∧
    bitValue (sequential (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      defaultID programs n fixedIDs).head=
      bitValue (SemiprimeSourceWordIdCounts.sequential (SemiprimeSourceWordBank.acquire r Q)
        defaultID programs n fixedIDs).head := by
  exact evaluate_eq r Q programs (List.range' fixedIDs.length n)
    (SemiprimeSourceWordIdEnvironment.initial defaultID fixedIDs).value List.nodup_range'
    (SemiprimeSourceWordIdEnvironment.initial_valid _ defaultID fixedIDs hd hf) hp

/-- Actual optimized count words drive the existing cached integer weighting circuits. -/
def score {Q : ℕ} (bank : Bank) (powers : Powers) (weights : SemiprimeSourceScoreWeightBits.Weights)
    (defaultID : List Bool) (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool)) : RationalReport :=
  let counts := sequential bank powers defaultID programs n fixedIDs
  let out := SemiprimeSourceScoreWeightBits.combine weights counts.incidence counts.head
  ⟨⟨⟨false,out.bits⟩,[true]⟩,counts.clock+out.clock+5⟩

/-- A literal denominator-one output is valid without Fits or count-value advice. -/
theorem score_valid {Q : ℕ} (bank : Bank) (powers : Powers) (weights : SemiprimeSourceScoreWeightBits.Weights)
    (defaultID : List Bool) (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool)) :
    (score bank powers weights defaultID programs n fixedIDs).word.Valid := by
  change 0<(1:ℕ)
  decide

/-- The actual new score agrees with the previous physical score on every original
separated program family and acquired-ID prefix. No clock equality is asserted. -/
theorem score_eq (r Q : ℕ) [NeZero r] (weights : SemiprimeSourceScoreWeightBits.Weights)
    (defaultID : List Bool) (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool))
    (hd : defaultID∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hf : ∀ id∈fixedIDs,id∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hp : ∀ p∈programs,Separated p) :
    (score (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) weights
      defaultID programs n fixedIDs).word.value=
      (SemiprimeSourceWordIdCounts.score (SemiprimeSourceWordBank.acquire r Q) weights
        defaultID programs n fixedIDs).word.value := by
  have h := sequential_eq r Q defaultID programs n fixedIDs hd hf hp
  change (SemiprimeSourceScoreWeightBits.scoreWord weights
    (sequential (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      defaultID programs n fixedIDs).incidence
    (sequential (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      defaultID programs n fixedIDs).head).value=
    (SemiprimeSourceScoreWeightBits.scoreWord weights
      (SemiprimeSourceWordIdCounts.sequential (SemiprimeSourceWordBank.acquire r Q) defaultID programs n fixedIDs).incidence
      (SemiprimeSourceWordIdCounts.sequential (SemiprimeSourceWordBank.acquire r Q) defaultID programs n fixedIDs).head).value
  rw [SemiprimeSourceScoreWeightBits.scoreWord_value,SemiprimeSourceScoreWeightBits.scoreWord_value,h.1,h.2]

end RiemannGaussian.SemiprimeSourceClassifiedCounts
