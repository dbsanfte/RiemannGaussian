/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreCountBitsBudget
import RiemannGaussian.SemiprimeSourceScorePredicateBitsBounds

/-! # Original metadata bounds for the physical collision-score callback -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace RiemannGaussian.SemiprimeSourceScoreCountBitsBounds
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes LocalExpectation
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceOffsetInputsCore SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeSourceScoreCountBitsCore SemiprimeSourceScoreCountBitsBudget
open SemiprimeSourceScoreCountBits SemiprimeSourceScoreWeightBits
open SemiprimeSourceScorePredicateBitsBounds SemiprimeReportPolynomialGrowth

/-- Physical local count width, independent of any desired numerical answer. -/
def localWidth (L : ℕ) : ℕ := 3+8*L+L^4

/-- Actual unary-pad acquisition and Boolean product, excluding truth traversal. -/
def paddingBudget (L : ℕ) : ℕ :=
  2+4*(L*(3*L^4+3)+L^4+5)+L^4+20*(L^4+1)^2+
    (12*localWidth L*(2*localWidth L+2)+1)+8

/-- Actual active scan, at most four completion levels, and physical padding. -/
def localBudget (r Q N L : ℕ) : ℕ :=
  12*N+1+countBudget L Q (terminalBudget r Q N 4) 4+paddingBudget L

/-- Program-lane accumulation, charging every physical local count and adder. -/
def evaluateBudget (r Q N L T : ℕ) : ℕ :=
  T*(localBudget r Q N L+11*(localWidth L+T)+9)+1

/-- Original prefix-cache acquisition plus all original programs. -/
def sequentialBudget (r Q N L T : ℕ) : ℕ :=
  evaluateBudget r Q N L T+2*(Q+1)*(N+1)+2*N+2

/-- Common original-data operand width for the final two multipliers and adder. -/
def scoreOperandWidth (L T K : ℕ) : ℕ := K+localWidth L+T

/-- Complete score callback budget with cached original weights. -/
def scoreBudget (r Q N L T K : ℕ) : ℕ :=
  sequentialBudget r Q N L T+combineBudget (scoreOperandWidth L T K)+4
/-- All actual extension leaves obey the original ID/override metadata cap. -/
theorem terminal_cap {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) (N s : ℕ)
    (hf : env.fixed.length ≤ N) (ho : env.overrides.length+remaining.length ≤ s)
    (hk : ∀ pair∈env.overrides,pair.1 ≤ N)
    (hi : ∀ i∈remaining,i ≤ N) (hp : ∀ i∈support p,i ≤ N) :
    TerminalCap alphabet (fun env => SemiprimeSourceScorePredicateBits.terminal_original env p)
      (terminalBudget r Q N s) remaining env := by
  induction remaining generalizing env with
  | nil =>
    apply terminal_original_work env p N s hf (by simpa using ho) hk hp
  | cons i remaining ih =>
    intro w _
    apply ih (extend env i w)
    · exact hf
    · simp only [extend,List.length_cons]
      simp only [List.length_cons] at ho
      omega
    · intro pair hpair
      simp only [extend,List.mem_cons] at hpair
      rcases hpair with rfl|hpair
      · exact hi i List.mem_cons_self
      · exact hk pair hpair
    · intro j hj
      exact hi j (List.mem_cons_of_mem i hj)

/-- Actual local padding and truth counts have an original-metadata bound. -/
theorem localCount_clock {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) (N : ℕ)
    (hL : 0<alphabet.length) (hr : remaining.Nodup) (hn : remaining.length ≤ N)
    (hf : env.fixed.length ≤ N) (ho : env.overrides=[]) (hi : ∀ i∈remaining,i ≤ N)
    (hp : ∀ i∈support p,i ≤ N) :
    (localCount alphabet p remaining env).clock ≤ localBudget r Q N alphabet.length := by
  let active := (activeRun (support p) remaining).value
  have ha : active.length ≤ 4 := SemiprimeSourceScoreCountsPadding.active_length p remaining hr
  have hi' : ∀ i∈active,i ≤ N := by
    intro i h
    dsimp only [active] at h
    rw [activeRun_value] at h
    exact hi i (List.mem_of_mem_filter h)
  have cap := terminal_cap alphabet p active env N 4 hf
    (by simp only [ho,List.length_nil,Nat.zero_add];exact ha)
    (by simp [ho]) hi' hp
  have hc := count_clock alphabet
    (fun env => SemiprimeSourceScorePredicateBits.terminal_original env p)
    (terminalBudget r Q N 4) active env cap
  have hc' := hc.trans (countBudget_le_four alphabet.length Q (terminalBudget r Q N 4)
    active.length hL ha)
  have hw := count_length alphabet
    (fun env => SemiprimeSourceScorePredicateBits.terminal_original env p) active env
  have rawWidth : (count alphabet
      (fun env => SemiprimeSourceScorePredicateBits.terminal_original env p) active env).bits.length ≤
      localWidth alphabet.length := by
    unfold localWidth
    have ht : active.length*alphabet.length ≤ 4*alphabet.length := Nat.mul_le_mul_right _ ha
    omega
  have he := natBits_length (unaryPower alphabet.length (4-active.length)).cells.length
  have hec := natBits_clock (unaryPower alphabet.length (4-active.length)).cells.length
  simp only [unaryPower_length] at he hec
  have hpow : alphabet.length^(4-active.length) ≤ alphabet.length^4 :=
    Nat.pow_le_pow_right hL (by omega)
  have encodedWidth : (natBits (unaryPower alphabet.length (4-active.length)).cells.length).bits.length ≤
      localWidth alphabet.length := by
    simp only [unaryPower_length]
    unfold localWidth
    omega
  have hm := mul_cost_le
    (count alphabet (fun env => SemiprimeSourceScorePredicateBits.terminal_original env p) active env).bits
    (natBits (unaryPower alphabet.length (4-active.length)).cells.length).bits
    (localWidth alphabet.length) rawWidth encodedWidth
  have hb := unaryPower_clock alphabet.length 2 hL (4-active.length) (by omega)
  have hb' : (unaryPower alphabet.length (4-active.length)).clock ≤
      2+4*(alphabet.length*(3*alphabet.length^4+3)+alphabet.length^4+5) := by
    apply hb.trans
    gcongr
    omega
  have hec' : (natBits (unaryPower alphabet.length (4-active.length)).cells.length).clock ≤
      20*(alphabet.length^4+1)^2 := by
    rw [unaryPower_length]
    apply hec.trans
    gcongr
  have has := activeRun_work (support p) remaining
  have hs := support_length p
  have has' : (activeRun (support p) remaining).work ≤ 12*N+1 := by
    apply has.trans
    nlinarith
  dsimp only [localCount,padded]
  change _ ≤ localBudget r Q N alphabet.length
  unfold localBudget paddingBudget
  simp only [unaryPower_length]
  simp only [unaryPower_length] at hm hec'
  dsimp only [active] at hc' hm hb' hec' hpow
  omega
/-- Every original program suffix is evaluated physically with the same metadata bounds. -/
theorem evaluate_clock {r Q : ℕ} (alphabet : List (Word r Q)) (programs : List (ScoreProgram Q))
    (remaining : List ℕ) (env : Environment r Q) (N : ℕ)
    (hL : 0<alphabet.length) (hr : remaining.Nodup) (hn : remaining.length ≤ N)
    (hf : env.fixed.length ≤ N) (ho : env.overrides=[]) (hi : ∀ i∈remaining,i ≤ N)
    (hp : ∀ p∈programs,∀ i∈support p,i ≤ N) :
    (evaluate alphabet programs remaining env).clock ≤
      evaluateBudget r Q N alphabet.length programs.length := by
  induction programs with
  | nil => simp [SemiprimeSourceScoreCountBits.evaluate,evaluateBudget]
  | cons p programs ih =>
    have ht := localCount_clock alphabet p remaining env N hL hr hn hf ho hi
      (hp p List.mem_cons_self)
    have hc := ih (fun p h => hp p (List.mem_cons_of_mem _ h))
    have hl := evaluate_length alphabet programs remaining env hL hr
    have hpw := SemiprimeSourceScoreCountBitsCore.padded_length alphabet p
      (fun env => SemiprimeSourceScorePredicateBits.terminal_original env p) remaining env hL hr
    change (localCount alphabet p remaining env).bits.length ≤ localWidth alphabet.length at hpw
    have ci := addBits_cost (localCount alphabet p remaining env).bits
      (evaluate alphabet programs remaining env).incidence false
    have ch := addBits_cost (localCount alphabet p remaining env).bits
      (evaluate alphabet programs remaining env).head false
    have mi : max (localCount alphabet p remaining env).bits.length
        (evaluate alphabet programs remaining env).incidence.length ≤ localWidth alphabet.length+programs.length := by
      apply max_le <;> unfold localWidth at * <;> omega
    have mh : max (localCount alphabet p remaining env).bits.length
        (evaluate alphabet programs remaining env).head.length ≤ localWidth alphabet.length+programs.length := by
      apply max_le <;> unfold localWidth at * <;> omega
    cases p <;> simp only [SemiprimeSourceScoreCountBits.evaluate,evaluateBudget,List.length_cons] at * <;> nlinarith

/-- All actual original prefix frames have the closed sequential budget. -/
theorem sequential_clock {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixed : List (Word r Q)) (N : ℕ)
    (hn : fixed.length+n ≤ N) (hp : ∀ p∈programs,∀ i∈support p,i ≤ N) :
    (sequential a tail programs n fixed).clock ≤
      sequentialBudget r Q N (a::tail).length programs.length := by
  have h := evaluate_clock (a::tail) programs (List.range' fixed.length n)
    (baseEnvironment a fixed) N (by simp) List.nodup_range'
    (by simp only [List.length_range'];omega)
    (by simp only [baseEnvironment,List.length_map];omega) rfl
    (by intro i hi;simp only [List.mem_range'] at hi;omega) hp
  simp only [SemiprimeSourceScoreCountBits.sequential,sequentialBudget]
  have hf : fixed.length ≤ N := by omega
  have hn' : n ≤ N := by omega
  have hm := Nat.mul_le_mul_left (2*(Q+1)) (Nat.add_le_add_right hf 1)
  omega

/-- Physical score-word width follows only cached weight and original list sizes. -/
theorem score_width {r Q : ℕ} (w : Weights) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixed : List (Word r Q)) (K : ℕ)
    (ha : w.incidence.length ≤ K) (hb : w.head.length ≤ K) :
    Width (score w a tail programs n fixed).word
      (3*scoreOperandWidth (a::tail).length programs.length K+1) := by
  have hl := evaluate_length (a::tail) programs (List.range' fixed.length n)
    (baseEnvironment a fixed) (by simp) List.nodup_range'
  have h := combine_length w (sequential a tail programs n fixed).incidence
    (sequential a tail programs n fixed).head
    (scoreOperandWidth (a::tail).length programs.length K)
    (ha.trans (by unfold scoreOperandWidth;omega))
    (hb.trans (by unfold scoreOperandWidth;omega))
    (by unfold scoreOperandWidth localWidth;exact hl.1.trans (by omega))
    (by unfold scoreOperandWidth localWidth;exact hl.2.trans (by omega))
  constructor
  · exact h
  · change 1 ≤ 3*scoreOperandWidth (a::tail).length programs.length K+1
    omega

/-- Closed callback clock with actual physical truth/count/weight execution.
The only weight premise is its original cached bit-array length, not its value or Fits. -/
theorem score_clock {r Q : ℕ} (w : Weights) (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixed : List (Word r Q)) (N K : ℕ)
    (hn : fixed.length+n ≤ N) (hp : ∀ p∈programs,∀ i∈support p,i ≤ N)
    (ha : w.incidence.length ≤ K) (hb : w.head.length ≤ K) :
    (score w a tail programs n fixed).clock ≤
      scoreBudget r Q N (a::tail).length programs.length K := by
  have hs := sequential_clock a tail programs n fixed N hn hp
  have hl := evaluate_length (a::tail) programs (List.range' fixed.length n)
    (baseEnvironment a fixed) (by simp) List.nodup_range'
  have hc := combine_clock w (sequential a tail programs n fixed).incidence
    (sequential a tail programs n fixed).head
    (scoreOperandWidth (a::tail).length programs.length K)
    (ha.trans (by unfold scoreOperandWidth;omega))
    (hb.trans (by unfold scoreOperandWidth;omega))
    (by unfold scoreOperandWidth localWidth;exact hl.1.trans (by omega))
    (by unfold scoreOperandWidth localWidth;exact hl.2.trans (by omega))
  simp only [score,scoreBudget]
  omega
/-- Pure numeric monotonicity, isolated from all original source runtime terms. -/
theorem scoreBudget_mono {r Q N L T K r' Q' N' L' T' K' : ℕ}
    (hr : r ≤ r') (hQ : Q ≤ Q') (hN : N ≤ N') (hL : L ≤ L')
    (hT : T ≤ T') (hK : K ≤ K') :
    scoreBudget r Q N L T K ≤ scoreBudget r' Q' N' L' T' K' := by
  simp only [scoreBudget,sequentialBudget,evaluateBudget,localBudget,paddingBudget,localWidth,
    scoreOperandWidth,combineBudget,countBudget,SemiprimeSourceScorePredicateBitsBounds.terminalBudget,
    SemiprimeSourceScorePredicateBitsBounds.acquisitionBudget,terminalStepBudget,workingWidth,
    wordBudget,idBudget,readBudget,rowEqualityBudget,coordinateBudget,equalityBudget,copyBudget,scanStep]
  gcongr

/-- All constants are fixed before the original materialized dimensions. -/
theorem scoreBudget_monomial : ∃ C k : ℕ,∀ S,scoreBudget S S S S S S ≤ C*(S+1)^k := by
  change Bound (fun S => scoreBudget S S S S S S)
  simp only [scoreBudget,sequentialBudget,evaluateBudget,localBudget,paddingBudget,localWidth,
    scoreOperandWidth,combineBudget,countBudget,SemiprimeSourceScorePredicateBitsBounds.terminalBudget,
    SemiprimeSourceScorePredicateBitsBounds.acquisitionBudget,terminalStepBudget,workingWidth,
    wordBudget,idBudget,readBudget,rowEqualityBudget,coordinateBudget,equalityBudget,copyBudget,scanStep]
  boundArithmetic

end RiemannGaussian.SemiprimeSourceScoreCountBitsBounds
