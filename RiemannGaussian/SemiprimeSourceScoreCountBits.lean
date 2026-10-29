/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreCountBitsCore
import RiemannGaussian.SemiprimeSourceScorePredicateBits
import RiemannGaussian.SemiprimeSourceScoreCountsObjective

/-! # Actual physical two-lane source counts and weighted score callback
The original physical terminal supplies each leaf bit. Every branch, normalization
and lane accumulation uses Boolean arithmetic, with no natural count answer input.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceScoreCountBits
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceOffsetInputsCore SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeSourceScoreWeightBits

/-- Actual unsigned lanes and their retained physical/control report. -/
structure Counts where
  /-- Original incidence multiplicity bits. -/
  incidence : List Bool
  /-- Original head-collision multiplicity bits. -/
  head : List Bool
  /-- All branch, terminal and lane-accumulator reports. -/
  clock : ℕ

/-- Original normalized local completion count with a concrete physical terminal. -/
def localCount {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) : NatRun :=
  SemiprimeSourceScoreCountBitsCore.padded alphabet p
    (fun env => SemiprimeSourceScorePredicateBits.terminal_original env p) remaining env

/-- The original concrete terminal discharges the internal count refinement. -/
theorem localCount_value {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) :
    bitValue (localCount alphabet p remaining env).bits=
      (SemiprimeSourceScoreCountsPadding.paddedLocal alphabet p remaining env).value := by
  exact SemiprimeSourceScoreCountBitsCore.padded_value alphabet p _
    (fun env => SemiprimeSourceScorePredicateBits.terminal_original_value env p) remaining env

/-- Original score instructions are evaluated in order and accumulated physically. -/
def evaluate {r Q : ℕ} (alphabet : List (Word r Q)) :
    List (ScoreProgram Q) → List ℕ → Environment r Q → Counts
  | [],_,_ => ⟨[],[],1⟩
  | p::programs,remaining,env =>
    let this := localCount alphabet p remaining env
    let rest := evaluate alphabet programs remaining env
    match p with
    | .incidence _ _ _ _ =>
      let out := addBits this.bits rest.incidence false
      ⟨out.bits,rest.head,this.clock+rest.clock+bitCost out+5⟩
    | .head _ _ _ =>
      let out := addBits this.bits rest.head false
      ⟨rest.incidence,out.bits,this.clock+rest.clock+bitCost out+5⟩

/-- Both acquired bit lanes are exactly the original finite collision counts. -/
theorem evaluate_value {r Q : ℕ} (alphabet : List (Word r Q)) (programs : List (ScoreProgram Q))
    (remaining : List ℕ) (env : Environment r Q) :
    bitValue (evaluate alphabet programs remaining env).incidence=
      (SemiprimeSourceScoreCountsObjective.evaluateCounts alphabet programs remaining env).value.incidence ∧
    bitValue (evaluate alphabet programs remaining env).head=
      (SemiprimeSourceScoreCountsObjective.evaluateCounts alphabet programs remaining env).value.head := by
  induction programs with
  | nil => exact ⟨rfl,rfl⟩
  | cons p programs ih =>
    have ht := localCount_value alphabet p remaining env
    cases p <;> simp only [evaluate,SemiprimeSourceScoreCountsObjective.evaluateCounts,
      addBits_correct,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero,ht,ih.1,ih.2,and_self]

/-- Explicit physical lane widths cover all program suffixes and repeated instructions. -/
theorem evaluate_length {r Q : ℕ} (alphabet : List (Word r Q)) (programs : List (ScoreProgram Q))
    (remaining : List ℕ) (env : Environment r Q) (hL : 0<alphabet.length) (hr : remaining.Nodup) :
    (evaluate alphabet programs remaining env).incidence.length ≤
      3+8*alphabet.length+alphabet.length^4+programs.length ∧
    (evaluate alphabet programs remaining env).head.length ≤
      3+8*alphabet.length+alphabet.length^4+programs.length := by
  induction programs with
  | nil => simp [evaluate]
  | cons p programs ih =>
    have ht := SemiprimeSourceScoreCountBitsCore.padded_length alphabet p
      (fun env => SemiprimeSourceScorePredicateBits.terminal_original env p) remaining env hL hr
    change (localCount alphabet p remaining env).bits.length ≤ _ at ht
    have hi := (addBits_counts (localCount alphabet p remaining env).bits
      (evaluate alphabet programs remaining env).incidence false).2.2.2.2
    have hh := (addBits_counts (localCount alphabet p remaining env).bits
      (evaluate alphabet programs remaining env).head false).2.2.2.2
    cases p <;> simp only [evaluate,List.length_cons] <;> constructor <;> omega

/-- Acquire the original prefix environment and remaining range, retaining setup. -/
def sequential {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixed : List (Word r Q)) : Counts :=
  let out := evaluate (a::tail) programs (List.range' fixed.length n) (baseEnvironment a fixed)
  ⟨out.incidence,out.head,out.clock+2*(Q+1)*(fixed.length+1)+fixed.length+n+2⟩

/-- Every physical original search-prefix lane has the exact original count value. -/
theorem sequential_value {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixed : List (Word r Q)) :
    bitValue (sequential a tail programs n fixed).incidence=
      (SemiprimeSourceScoreCountsObjective.sequentialCounts a tail programs n fixed).value.incidence ∧
    bitValue (sequential a tail programs n fixed).head=
      (SemiprimeSourceScoreCountsObjective.sequentialCounts a tail programs n fixed).value.head :=
  evaluate_value (a::tail) programs (List.range' fixed.length n) (baseEnvironment a fixed)

/-- Actual weighted callback reuses cached original weights and produced count bits. -/
def score {r Q : ℕ} (w : Weights) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixed : List (Word r Q)) : RationalReport :=
  let counts := sequential a tail programs n fixed
  let out := combine w counts.incidence counts.head
  ⟨⟨⟨false,out.bits⟩,[true]⟩,counts.clock+out.clock+4⟩

/-- The actual score callback is always a valid denominator-one physical word. -/
theorem score_valid {r Q : ℕ} (w : Weights) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixed : List (Word r Q)) :
    (score w a tail programs n fixed).word.Valid := by
  change 0<(1:ℕ)
  decide

/-- All physical truth/count/weight stages identify the two actual original counts. -/
theorem score_value {r Q : ℕ} (w : Weights) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixed : List (Word r Q)) :
    (score w a tail programs n fixed).word.value=
      ((bitValue w.incidence*
        (SemiprimeSourceScoreCountsObjective.sequentialCounts a tail programs n fixed).value.incidence+
        bitValue w.head*
        (SemiprimeSourceScoreCountsObjective.sequentialCounts a tail programs n fixed).value.head:ℕ):ℚ) := by
  have h := scoreWord_value w (sequential a tail programs n fixed).incidence
    (sequential a tail programs n fixed).head
  change (scoreWord w (sequential a tail programs n fixed).incidence
    (sequential a tail programs n fixed).head).value = _
  simpa only [(sequential_value a tail programs n fixed).1,
    (sequential_value a tail programs n fixed).2] using h

end RiemannGaussian.SemiprimeSourceScoreCountBits
