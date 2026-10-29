/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdCountsCore
import RiemannGaussian.SemiprimeSourceWordIdPredicate
import RiemannGaussian.SemiprimeSourceWordBankIndexed
import RiemannGaussian.SemiprimeSourceScoreCountOrder

/-! # Original acquired-bank collision counts over physical candidate IDs
The runtime accepts no source Word function, cached source Word, truth callback,
count answer or decoded menu. The only native descriptors are the original
at-most-four support keys and finite score-program metadata.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceWordIdCounts
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords SemiprimeRationalBits SemiprimeBitArithmetic
open SemiprimeMaterializedScoreEnvironment (ScoreProgram)
open SemiprimeSourceWordBank (Bank)
open SemiprimeSourceWordIdEnvironment (Env)
open SemiprimeSourceWordIdCountsCore (Counts)

/-- Concrete physical-bank evaluator: no terminal or push callback is supplied. -/
def evaluate {Q : ℕ} (bank : Bank) (programs : List (ScoreProgram Q))
    (remaining : List ℕ) (env : Env) : Counts :=
  SemiprimeSourceWordIdCountsCore.evaluate bank.ids SemiprimeSourceWordIdEnvironment.extend
    (fun p env => SemiprimeSourceWordIdPredicate.terminal bank env p) programs remaining env

/-- Copy the actual default/prefix IDs and complete only acquired physical active keys. -/
def sequential {Q : ℕ} (bank : Bank) (defaultID : List Bool) (programs : List (ScoreProgram Q))
    (n : ℕ) (fixedIDs : List (List Bool)) : Counts :=
  let initial:=SemiprimeSourceWordIdEnvironment.initial defaultID fixedIDs
  let result:=evaluate bank programs (List.range' fixedIDs.length n) initial.value
  ⟨result.incidence,result.head,initial.work+result.clock+fixedIDs.length+n+8⟩

/-- Actual acquired physical count words drive the existing cached weighted circuits. -/
def score {Q : ℕ} (bank : Bank) (weights : SemiprimeSourceScoreWeightBits.Weights)
    (defaultID : List Bool) (programs : List (ScoreProgram Q))
    (n : ℕ) (fixedIDs : List (List Bool)) : RationalReport :=
  let counts:=sequential bank defaultID programs n fixedIDs
  let out:=SemiprimeSourceScoreWeightBits.combine weights counts.incidence counts.head
  ⟨⟨⟨false,out.bits⟩,[true]⟩,counts.clock+out.clock+5⟩

/-- The concrete callback is always a legal denominator-one word. -/
theorem score_valid {Q : ℕ} (bank : Bank) (weights : SemiprimeSourceScoreWeightBits.Weights)
    (defaultID : List Bool) (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool)) :
    (score bank weights defaultID programs n fixedIDs).word.Valid := by
  change 0<(1:ℕ)
  decide

/-- The original acquired bank discharges the INTERNAL truth/push relations.
No supplied truth, count, bank-representation or decoded-menu premise remains. -/
theorem evaluate_original (r Q : ℕ) [NeZero r] (programs : List (ScoreProgram Q))
    (remaining : List ℕ) (env : Env)
    (hv : SemiprimeSourceWordIdEnvironment.ValidIds (SemiprimeSourceWordBank.acquire r Q).ids env) :
    bitValue (evaluate (SemiprimeSourceWordBank.acquire r Q) programs remaining env).incidence=
      (SemiprimeSourceScoreCountsObjective.evaluateCounts (SemiprimeFiniteEnumerations.words r Q).values
        programs remaining (SemiprimeSourceWordIdEnvironment.decodeEnvironment
          (SemiprimeSourceWordBankSemantics.decode r Q) env)).value.incidence ∧
    bitValue (evaluate (SemiprimeSourceWordBank.acquire r Q) programs remaining env).head=
      (SemiprimeSourceScoreCountsObjective.evaluateCounts (SemiprimeFiniteEnumerations.words r Q).values
        programs remaining (SemiprimeSourceWordIdEnvironment.decodeEnvironment
          (SemiprimeSourceWordBankSemantics.decode r Q) env)).value.head := by
  have h:=SemiprimeSourceWordIdCountsCore.evaluate_value
    (SemiprimeSourceWordBank.acquire r Q).ids SemiprimeSourceWordIdEnvironment.extend
    (fun p env => SemiprimeSourceWordIdPredicate.terminal (SemiprimeSourceWordBank.acquire r Q) env p)
    (SemiprimeSourceWordBankSemantics.decode r Q)
    (SemiprimeSourceWordIdEnvironment.Rel (SemiprimeSourceWordBank.acquire r Q).ids
      (SemiprimeSourceWordBankSemantics.decode r Q))
    (fun p env native h => SemiprimeSourceWordIdPredicate.terminal_rel r Q env native p h)
    (fun env native key id h hi => SemiprimeSourceWordIdEnvironment.extend_rel _ _ env native key id h hi)
    programs remaining env (SemiprimeSourceWordIdEnvironment.decodeEnvironment
      (SemiprimeSourceWordBankSemantics.decode r Q) env) ⟨hv,rfl⟩
  simpa only [evaluate,SemiprimeSourceWordBankSemantics.ids_decode] using h

/-- Acquired physical defaults/prefixes decode to the ACTUAL original count environment. -/
theorem sequential_original (r Q : ℕ) [NeZero r] (defaultID : List Bool)
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool))
    (hd : defaultID∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hf : ∀ id∈fixedIDs,id∈(SemiprimeSourceWordBank.acquire r Q).ids) :
    bitValue (sequential (SemiprimeSourceWordBank.acquire r Q) defaultID programs n fixedIDs).incidence=
      (SemiprimeSourceScoreCountsObjective.evaluateCounts (SemiprimeFiniteEnumerations.words r Q).values
        programs (List.range' fixedIDs.length n)
        (SemiprimeMaterializedScoreEnvironment.baseEnvironment (SemiprimeSourceWordBankSemantics.decode r Q defaultID)
          (fixedIDs.map (SemiprimeSourceWordBankSemantics.decode r Q)))).value.incidence ∧
    bitValue (sequential (SemiprimeSourceWordBank.acquire r Q) defaultID programs n fixedIDs).head=
      (SemiprimeSourceScoreCountsObjective.evaluateCounts (SemiprimeFiniteEnumerations.words r Q).values
        programs (List.range' fixedIDs.length n)
        (SemiprimeMaterializedScoreEnvironment.baseEnvironment (SemiprimeSourceWordBankSemantics.decode r Q defaultID)
          (fixedIDs.map (SemiprimeSourceWordBankSemantics.decode r Q)))).value.head := by
  have h:=evaluate_original r Q programs (List.range' fixedIDs.length n)
    (SemiprimeSourceWordIdEnvironment.initial defaultID fixedIDs).value
    (SemiprimeSourceWordIdEnvironment.initial_valid _ defaultID fixedIDs hd hf)
  simpa only [sequential,SemiprimeSourceWordIdEnvironment.initial_decode] using h

/-- Exact ORIGINAL indexed zero-first menu, not a permutation/coverage promise. -/
theorem sequential_indexed (n F r Q : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (programs : List (ScoreProgram Q)) (s : ℕ) (fixedIDs : List (List Bool))
    (hf : ∀ id∈fixedIDs,id∈(SemiprimeSourceWordBank.acquire r Q).ids) :
    let en:=(SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    let fixed:=fixedIDs.map (SemiprimeSourceWordBankSemantics.decode r Q)
    bitValue (sequential (SemiprimeSourceWordBank.acquire r Q) SemiprimeSourceWordBank.defaultID programs s fixedIDs).incidence=
      (SemiprimeSourceScoreCountsObjective.sequentialCounts en.wordFirst en.wordTail programs s fixed).value.incidence ∧
    bitValue (sequential (SemiprimeSourceWordBank.acquire r Q) SemiprimeSourceWordBank.defaultID programs s fixedIDs).head=
      (SemiprimeSourceScoreCountsObjective.sequentialCounts en.wordFirst en.wordTail programs s fixed).value.head := by
  have h:=sequential_original r Q SemiprimeSourceWordBank.defaultID programs s fixedIDs
    (SemiprimeSourceWordBankIndexed.default_mem r Q) hf
  have hm:=(SemiprimeSourceWordMenuOrder.indexed_menu n F r Q arity).symm
  have hz : (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordFirst=(fun _ => 0) := by
    rw [SemiprimePaidFiniteEnumerations.indexed_value]
    rfl
  rw [hm,SemiprimeSourceWordBankIndexed.decode_default] at h
  simpa only [SemiprimeSourceScoreCountsObjective.sequentialCounts,List.length_map,hz] using h

/-- Complete score refinement on actual ORIGINAL acquired bank and indexed menu.
Only reachable-prefix ID membership is a condition, supplied by the physical controller. -/
theorem score_indexed (n F r Q : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (weights : SemiprimeSourceScoreWeightBits.Weights) (programs : List (ScoreProgram Q))
    (s : ℕ) (fixedIDs : List (List Bool))
    (hf : ∀ id∈fixedIDs,id∈(SemiprimeSourceWordBank.acquire r Q).ids) :
    let en:=(SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    let fixed:=fixedIDs.map (SemiprimeSourceWordBankSemantics.decode r Q)
    (score (SemiprimeSourceWordBank.acquire r Q) weights SemiprimeSourceWordBank.defaultID programs s fixedIDs).word.value=
      ((bitValue weights.incidence*(SemiprimeSourceScoreCountsObjective.sequentialCounts
          en.wordFirst en.wordTail programs s fixed).value.incidence+
        bitValue weights.head*(SemiprimeSourceScoreCountsObjective.sequentialCounts
          en.wordFirst en.wordTail programs s fixed).value.head:ℕ):ℚ) := by
  have h:=sequential_indexed n F r Q arity programs s fixedIDs hf
  change (SemiprimeSourceScoreWeightBits.scoreWord weights
    (sequential (SemiprimeSourceWordBank.acquire r Q) SemiprimeSourceWordBank.defaultID programs s fixedIDs).incidence
    (sequential (SemiprimeSourceWordBank.acquire r Q) SemiprimeSourceWordBank.defaultID programs s fixedIDs).head).value=_
  rw [SemiprimeSourceScoreWeightBits.scoreWord_value,h.1,h.2]

end RiemannGaussian.SemiprimeSourceWordIdCounts
