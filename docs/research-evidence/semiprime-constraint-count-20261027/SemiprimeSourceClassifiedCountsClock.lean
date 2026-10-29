/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceClassifiedCounts
import RiemannGaussian.SemiprimeSourceIncidenceCountBitsBounds

/-! # Actual complete classified-score report
All optimized locals, lane adders, prefix copies and final weighting are paid.
No candidate completion or unary cardinality/count expansion occurs.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
namespace RiemannGaussian.SemiprimeSourceClassifiedCountsClock
open SemiprimeMaterializedScoreEnvironment (ScoreProgram support)
open SemiprimeSourceWordIdEnvironment (Env ValidIds)
open SemiprimeSourceWordIdEnvironmentBounds (KeysBound)
open SemiprimeSourceClassifiedCounts SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeReportPolynomialGrowth

/-- Structural lane width from acquired cached power width and actual program count. -/
def laneWidth (r Q T : ℕ) : ℕ := SemiprimeSourceCountPowers.width r Q+T
/-- Actual input width for the final two multipliers and adder. -/
def operandWidth (r Q T K : ℕ) : ℕ := K+laneWidth r Q T

/-- Both physical sequential lane widths follow actual acquired cache/adder growth. -/
theorem sequential_length (r Q : ℕ) (defaultID : List Bool) (programs : List (ScoreProgram Q))
    (n : ℕ) (fixedIDs : List (List Bool)) :
    (sequential (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      defaultID programs n fixedIDs).incidence.length ≤ laneWidth r Q programs.length ∧
    (sequential (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      defaultID programs n fixedIDs).head.length ≤ laneWidth r Q programs.length :=
  evaluate_length r Q programs (List.range' fixedIDs.length n)
    (SemiprimeSourceWordIdEnvironment.initial defaultID fixedIDs).value

/-- Final physical score width has no L^4 term or desired-count premise. -/
theorem score_width (r Q : ℕ) (weights : SemiprimeSourceScoreWeightBits.Weights)
    (defaultID : List Bool) (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool)) (K : ℕ)
    (ha : weights.incidence.length ≤ K) (hb : weights.head.length ≤ K) :
    Width (score (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      weights defaultID programs n fixedIDs).word (3*operandWidth r Q programs.length K+1) := by
  have h := sequential_length r Q defaultID programs n fixedIDs
  have hw := SemiprimeSourceScoreWeightBits.combine_length weights
    (sequential (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      defaultID programs n fixedIDs).incidence
    (sequential (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      defaultID programs n fixedIDs).head (operandWidth r Q programs.length K)
    (ha.trans (by unfold operandWidth;omega)) (hb.trans (by unfold operandWidth;omega))
    (h.1.trans (by unfold operandWidth;omega)) (h.2.trans (by unfold operandWidth;omega))
  exact ⟨hw,by change 1 ≤ 3*operandWidth r Q programs.length K+1;omega⟩

/-- Conservative joint cap of the two actual constant-classifier local branches. -/
def localBudget (r Q L N s : ℕ) : ℕ :=
  SemiprimeSourceHeadCountBitsBounds.budget r Q L N s+
    SemiprimeSourceIncidenceCountBitsBounds.countBudget r Q L N s

/-- Every local report follows from concrete acquired bank/cache and finite metadata. -/
theorem local_clock (r Q : ℕ) [NeZero r] (p : ScoreProgram Q) (remaining : List ℕ) (env : Env) (N s : ℕ)
    (he : ValidIds (SemiprimeSourceWordBank.acquire r Q).ids env)
    (hf : env.fixedIDs.length ≤ N) (ho : env.overrides.length ≤ s) (hk : KeysBound (N+1) env)
    (hn : remaining.length ≤ N) (hp : ∀ i∈support p,i ≤ N) :
    (localCount (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      p remaining env).clock ≤ localBudget r Q (r^Q) N s := by
  cases p with
  | incidence a b c d =>
    have h := SemiprimeSourceIncidenceCountBitsBounds.count_work r Q env a b c d remaining N s he hf ho hk hn
      (hp a (by simp [support])) (hp b (by simp [support]))
      (hp c (by simp [support])) (hp d (by simp [support]))
    exact h.trans (by unfold localBudget;omega)
  | head q a b =>
    have h := SemiprimeSourceHeadCountBitsBounds.count_original_clock r Q env q a b remaining N s
      he hf ho hk hn (hp a (by simp [support])) (hp b (by simp [support]))
    exact h.trans (by unfold localBudget;omega)

/-- Actual finite lane accumulation and all local classifiers. -/
def evaluateBudget (r Q L N s T : ℕ) : ℕ :=
  T*(localBudget r Q L N s+11*laneWidth r Q T+12)+1

/-- Every actual program suffix has the classified physical report bound. -/
theorem evaluate_clock (r Q : ℕ) [NeZero r] (programs : List (ScoreProgram Q))
    (remaining : List ℕ) (env : Env) (N s : ℕ)
    (he : ValidIds (SemiprimeSourceWordBank.acquire r Q).ids env)
    (hf : env.fixedIDs.length ≤ N) (ho : env.overrides.length ≤ s) (hk : KeysBound (N+1) env)
    (hn : remaining.length ≤ N) (hp : ∀ p∈programs,∀ i∈support p,i ≤ N) :
    (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      programs remaining env).clock ≤ evaluateBudget r Q (r^Q) N s programs.length := by
  induction programs with
  | nil => simp [evaluate,evaluateBudget]
  | cons p programs ih =>
    have ht := local_clock r Q p remaining env N s he hf ho hk hn (hp p List.mem_cons_self)
    have hc := ih (fun p h => hp p (List.mem_cons_of_mem _ h))
    have hl := evaluate_length r Q programs remaining env
    have hloc := local_length r Q p remaining env
    have ci := addBits_cost
      (localCount (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) p remaining env).bits
      (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) programs remaining env).incidence false
    have ch := addBits_cost
      (localCount (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) p remaining env).bits
      (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) programs remaining env).head false
    have mi : max
        (localCount (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) p remaining env).bits.length
        (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) programs remaining env).incidence.length ≤
        laneWidth r Q programs.length := by apply max_le <;> unfold laneWidth <;> omega
    have mh : max
        (localCount (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) p remaining env).bits.length
        (evaluate (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) programs remaining env).head.length ≤
        laneWidth r Q programs.length := by apply max_le <;> unfold laneWidth <;> omega
    cases p <;> simp only [evaluate,evaluateBudget,List.length_cons,laneWidth] at * <;> nlinarith

/-- Original prefix-ID copy and all classifiers; no free-variable pushes occur. -/
def sequentialBudget (r Q N L T : ℕ) : ℕ :=
  8*L+N*(8*L+4)+7+evaluateBudget r Q L N 0 T+2*N+8

/-- Concrete original prefix metadata closes the entire classified sequential report. -/
theorem sequential_clock (r Q : ℕ) [NeZero r] (defaultID : List Bool)
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool)) (N : ℕ)
    (hd : defaultID∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hf : ∀ id∈fixedIDs,id∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hlen : fixedIDs.length+n ≤ N) (hp : ∀ p∈programs,∀ i∈support p,i ≤ N) :
    (sequential (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      defaultID programs n fixedIDs).clock ≤ sequentialBudget r Q N (r^Q) programs.length := by
  have he := SemiprimeSourceWordIdEnvironment.initial_valid _ defaultID fixedIDs hd hf
  have hc := evaluate_clock r Q programs (List.range' fixedIDs.length n)
    (SemiprimeSourceWordIdEnvironment.initial defaultID fixedIDs).value N 0 he
    (by simpa only [SemiprimeSourceWordIdEnvironment.initial,SemiprimeSourceChoiceBits.copyIDs_value] using
      (show fixedIDs.length ≤ N by omega))
    (by simp [SemiprimeSourceWordIdEnvironment.initial])
    (by simp [KeysBound,SemiprimeSourceWordIdEnvironment.initial])
    (by simp only [List.length_range'];omega) hp
  have hi := SemiprimeSourceWordIdEnvironment.initial_work defaultID fixedIDs (2*r^Q)
    (fun id hid => SemiprimeSourceWordBankAcquisitionBudget.acquire_ids_bounded r Q id (hf id hid))
  have hdw := SemiprimeSourceWordBankAcquisitionBudget.acquire_ids_bounded r Q defaultID hd
  have hinit : (SemiprimeSourceWordIdEnvironment.initial defaultID fixedIDs).work ≤
      8*r^Q+N*(8*r^Q+4)+7 := by
    apply hi.trans
    calc
      _ ≤ 4*(2*r^Q)+N*(4*(2*r^Q)+4)+7 := by gcongr;omega
      _ = 8*r^Q+N*(8*r^Q+4)+7 := by ring
  simp only [sequential,sequentialBudget]
  omega

/-- Complete callback work from cached powers/weights and actual physical lanes. -/
def scoreBudget (r Q N L T K : ℕ) : ℕ :=
  sequentialBudget r Q N L T+SemiprimeSourceScoreWeightBits.combineBudget (operandWidth r Q T K)+5

/-- Original bank/weights/prefix metadata derive all actual score operations. -/
theorem score_clock (r Q : ℕ) [NeZero r] (weights : SemiprimeSourceScoreWeightBits.Weights)
    (defaultID : List Bool) (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool)) (N K : ℕ)
    (hd : defaultID∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hf : ∀ id∈fixedIDs,id∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hlen : fixedIDs.length+n ≤ N) (hp : ∀ p∈programs,∀ i∈support p,i ≤ N)
    (ha : weights.incidence.length ≤ K) (hb : weights.head.length ≤ K) :
    (score (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q)
      weights defaultID programs n fixedIDs).clock ≤ scoreBudget r Q N (r^Q) programs.length K := by
  have hs := sequential_clock r Q defaultID programs n fixedIDs N hd hf hlen hp
  have hl := sequential_length r Q defaultID programs n fixedIDs
  have hc := SemiprimeSourceScoreWeightBits.combine_clock weights
    (sequential (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) defaultID programs n fixedIDs).incidence
    (sequential (SemiprimeSourceWordBank.acquire r Q) (SemiprimeSourceCountPowers.acquire r Q) defaultID programs n fixedIDs).head
    (operandWidth r Q programs.length K)
    (ha.trans (by unfold operandWidth;omega)) (hb.trans (by unfold operandWidth;omega))
    (hl.1.trans (by unfold operandWidth;omega)) (hl.2.trans (by unfold operandWidth;omega))
  simp only [score,scoreBudget]
  omega
/-- Pure six-resource monotonicity, independent of all actual source expressions. -/
theorem scoreBudget_mono {r Q N L T K r' Q' N' L' T' K' : ℕ}
    (hr : r ≤ r') (hQ : Q ≤ Q') (hN : N ≤ N') (hL : L ≤ L')
    (hT : T ≤ T') (hK : K ≤ K') :
    scoreBudget r Q N L T K ≤ scoreBudget r' Q' N' L' T' K' := by
  simp only [scoreBudget,sequentialBudget,evaluateBudget,localBudget,operandWidth,laneWidth,
    SemiprimeSourceCountPowers.width,SemiprimeSourceScoreWeightBits.combineBudget,
    SemiprimeSourceHeadCountBitsBounds.budget,SemiprimeSourceIncidenceCountBitsBounds.countBudget,
    SemiprimeSourceIncidenceCountBitsBounds.edgeBudget,
    SemiprimeSourceWordIdPredicateBounds.terminalBudget,
    SemiprimeSourceWordIdPredicateBounds.programBudget,
    SemiprimeSourceWordIdPredicateBounds.terminalStepBudget,
    SemiprimeSourceWordIdPredicateBounds.bankReadBudget,
    SemiprimeSourceWordIdPredicateBounds.colourReadBudget,
    SemiprimeSourceWordIdEnvironmentBounds.readBudget,
    SemiprimeSourceWordIdEnvironmentBounds.scanStep,
    SemiprimeSourceWordIdEnvironmentBounds.keyBudget,
    SemiprimeSourceWordIdEnvironmentBounds.idCopyBudget,
    SemiprimeSourceWordIdEnvironmentBounds.eqBudget,
    SemiprimeSourceScorePredicateBitsBounds.copyBudget,
    SemiprimeSourceScorePredicateBitsBounds.equalityBudget]
  gcongr

/-- Fixed constants precede the whole original materialized-resource family. -/
theorem scoreBudget_monomial : ∃ C k : ℕ,∀ S,scoreBudget S S S S S S ≤ C*(S+1)^k := by
  change Bound (fun S => scoreBudget S S S S S S)
  simp only [scoreBudget,sequentialBudget,evaluateBudget,localBudget,operandWidth,laneWidth,
    SemiprimeSourceCountPowers.width,SemiprimeSourceScoreWeightBits.combineBudget,
    SemiprimeSourceHeadCountBitsBounds.budget,SemiprimeSourceIncidenceCountBitsBounds.countBudget,
    SemiprimeSourceIncidenceCountBitsBounds.edgeBudget,
    SemiprimeSourceWordIdPredicateBounds.terminalBudget,
    SemiprimeSourceWordIdPredicateBounds.programBudget,
    SemiprimeSourceWordIdPredicateBounds.terminalStepBudget,
    SemiprimeSourceWordIdPredicateBounds.bankReadBudget,
    SemiprimeSourceWordIdPredicateBounds.colourReadBudget,
    SemiprimeSourceWordIdEnvironmentBounds.readBudget,
    SemiprimeSourceWordIdEnvironmentBounds.scanStep,
    SemiprimeSourceWordIdEnvironmentBounds.keyBudget,
    SemiprimeSourceWordIdEnvironmentBounds.idCopyBudget,
    SemiprimeSourceWordIdEnvironmentBounds.eqBudget,
    SemiprimeSourceScorePredicateBitsBounds.copyBudget,
    SemiprimeSourceScorePredicateBitsBounds.equalityBudget]
  boundArithmetic

end RiemannGaussian.SemiprimeSourceClassifiedCountsClock
