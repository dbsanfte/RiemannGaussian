/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdCountsBounds
import RiemannGaussian.SemiprimeSourceWordIdPredicateBounds

/-! # Original-input clock for the actual physical-ID score callback -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourceWordIdCountsClock
open SemiprimeMaterializedWords (Run activeRun activeRun_value activeRun_work)
open SemiprimeMaterializedScoreEnvironment (ScoreProgram support support_length)
open SemiprimeSourceOffsetInputsCore SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeSourceWordBank (acquire)
open SemiprimeSourceWordIdEnvironment (Env ValidIds)
open SemiprimeSourceWordIdEnvironmentBounds (KeysBound)
open SemiprimeSourceWordIdCountsCore

/-- Copy both acquired key and menu-ID words at every branch. -/
def pushBudget (N L : ℕ) : ℕ := 4*(N+1)+8*L+9

/-- All actual pushes/leaves satisfy the generic cap from ORIGINAL bank and metadata. -/
theorem cap_original (r Q : ℕ) [NeZero r] (p : ScoreProgram Q) (N : ℕ)
    (keys : List (List Bool)) (env : Env)
    (he : ValidIds (acquire r Q).ids env) (hf : env.fixedIDs.length≤ N)
    (ho : env.overrides.length+keys.length≤4) (hk : KeysBound (N+1) env)
    (hkeys : ∀ key∈keys,key.length≤ N+1) (hp : ∀ i∈support p,i≤ N) :
    SemiprimeSourceWordIdCountsBudget.Cap (acquire r Q).ids SemiprimeSourceWordIdEnvironment.extend
      (fun env => SemiprimeSourceWordIdPredicate.terminal (acquire r Q) env p)
      (pushBudget N (r^Q)) (SemiprimeSourceWordIdPredicateBounds.terminalBudget r Q (r^Q) N 4) keys env := by
  induction keys generalizing env with
  | nil =>
    exact SemiprimeSourceWordIdPredicateBounds.terminal_work r Q env p N 4 he hf
      (by simpa only [List.length_nil,Nat.add_zero] using ho) hk hp
  | cons key keys ih =>
    intro id hid
    have hi:=SemiprimeSourceWordBankAcquisitionBudget.acquire_ids_bounded r Q id hid
    have hkey:=hkeys key List.mem_cons_self
    constructor
    · apply (SemiprimeSourceWordIdEnvironment.extend_work env key id).trans
      unfold pushBudget
      omega
    · apply ih (SemiprimeSourceWordIdEnvironment.extend env key id).value
      · exact SemiprimeSourceWordIdEnvironment.extend_valid _ env key id he hid
      · simpa only [SemiprimeSourceWordIdEnvironmentBounds.extend_fixed_length] using hf
      · rw [SemiprimeSourceWordIdEnvironmentBounds.extend_override_length]
        simp only [List.length_cons] at ho
        omega
      · exact SemiprimeSourceWordIdEnvironmentBounds.extend_keys env key id (N+1) hk hkey
      · exact fun key hkey => hkeys key (List.mem_cons_of_mem _ hkey)

/-- Actual acquired physical local-count multiplier work, apart from truth completion. -/
def paddingBudget (L : ℕ) : ℕ :=
  2+4*(L*(3*L^4+3)+L^4+5)+L^4+20*(L^4+1)^2+
    (12*(3+8*L+L^4)*(2*(3+8*L+L^4)+2)+1)+20

/-- Active scan, physical key acquisition, all copied pushes/leaves, and padding. -/
def localBudget (r Q N L : ℕ) : ℕ :=
  12*N+1+4*(20*(N+1)^2+N+4)+1+
    SemiprimeSourceWordIdCountsBudget.budget L (pushBudget N L)
      (SemiprimeSourceWordIdPredicateBounds.terminalBudget r Q L N 4) 4+paddingBudget L

/-- Actual local completion has no terminal, copied-state, count or Fits budget oracle. -/
theorem padded_clock (r Q : ℕ) [NeZero r] (p : ScoreProgram Q) (remaining : List ℕ)
    (env : Env) (N : ℕ) (hr : remaining.Nodup) (hn : remaining.length≤ N)
    (he : ValidIds (acquire r Q).ids env) (hf : env.fixedIDs.length≤ N)
    (ho : env.overrides=[]) (hi : ∀ i∈remaining,i≤ N) (hp : ∀ i∈support p,i≤ N) :
    (padded (acquire r Q).ids SemiprimeSourceWordIdEnvironment.extend
      (fun env => SemiprimeSourceWordIdPredicate.terminal (acquire r Q) env p) p remaining env).clock≤
      localBudget r Q N (r^Q) := by
  let ids:=(acquire r Q).ids
  let active:=(activeRun (support p) remaining).value
  let keys:=acquireKeys active
  let terminal:=fun env => SemiprimeSourceWordIdPredicate.terminal (acquire r Q) env p
  have hL : ids.length=r^Q := (SemiprimeSourceWordBank.acquire_ids_length r Q).trans
    (SemiprimeSourceWordBankIndexed.acquire_length r Q)
  have hpos : 0< ids.length := by rw [hL];exact pow_pos (NeZero.pos r) _
  have ha : active.length≤4 := SemiprimeSourceScoreCountsPadding.active_length p remaining hr
  have hia : ∀ i∈active,i≤ N := by
    intro i h
    dsimp only [active] at h
    rw [activeRun_value] at h
    exact hi i (List.mem_of_mem_filter h)
  have hka:=acquireKeys_bound active N hia
  have hkc:=acquireKeys_work active N hia
  have hc:=SemiprimeSourceWordIdCountsBudget.count_clock ids SemiprimeSourceWordIdEnvironment.extend terminal
    (pushBudget N (r^Q)) (SemiprimeSourceWordIdPredicateBounds.terminalBudget r Q (r^Q) N 4) keys.value env
    (cap_original r Q p N keys.value env he hf
      (by rw [ho];simp only [List.length_nil,Nat.zero_add];simpa only [keys,acquireKeys_length] using ha)
      (by simp only [KeysBound,ho,List.not_mem_nil,false_implies,implies_true]) hka hp)
  have hc':=hc.trans (SemiprimeSourceWordIdCountsBudget.budget_le_four ids.length _ _ keys.value.length hpos
    (by simpa only [keys,acquireKeys_length] using ha))
  have hw:=count_length ids SemiprimeSourceWordIdEnvironment.extend terminal keys.value env
  rw [show keys.value.length=active.length from acquireKeys_length active] at hw
  have rawWidth : (count ids SemiprimeSourceWordIdEnvironment.extend terminal keys.value env).bits.length≤
      3+8*ids.length+ids.length^4 := by
    have ht:=Nat.mul_le_mul_right ids.length ha
    omega
  have en:=natBits_length (unaryPower ids.length (4-active.length)).cells.length
  have enc:=natBits_clock (unaryPower ids.length (4-active.length)).cells.length
  simp only [unaryPower_length] at en enc
  have hpow : ids.length^(4-active.length)≤ ids.length^4 := Nat.pow_le_pow_right hpos (by omega)
  have encodedWidth : (natBits (unaryPower ids.length (4-active.length)).cells.length).bits.length≤
      3+8*ids.length+ids.length^4 := by rw [unaryPower_length];omega
  have hm:=SemiprimeSourceScoreWeightBits.mul_cost_le
    (count ids SemiprimeSourceWordIdEnvironment.extend terminal keys.value env).bits
    (natBits (unaryPower ids.length (4-active.length)).cells.length).bits
    (3+8*ids.length+ids.length^4) rawWidth encodedWidth
  have hb:=unaryPower_clock ids.length 2 hpos (4-active.length) (by omega)
  have hb' : (unaryPower ids.length (4-active.length)).clock≤
      2+4*(ids.length*(3*ids.length^4+3)+ids.length^4+5) := by
    apply hb.trans
    gcongr
    omega
  have enc' : (natBits (unaryPower ids.length (4-active.length)).cells.length).clock≤
      20*(ids.length^4+1)^2 := by rw [unaryPower_length];apply enc.trans;gcongr
  have has:=activeRun_work (support p) remaining
  have hs:=support_length p
  have has' : (activeRun (support p) remaining).work≤12*N+1 := by
    apply has.trans
    nlinarith
  have hkc' : keys.work≤4*(20*(N+1)^2+N+4)+1 :=
    hkc.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ha) 1)
  change (padded ids SemiprimeSourceWordIdEnvironment.extend terminal p remaining env).clock≤_
  simp only [padded]
  change (activeRun (support p) remaining).work+keys.work+
    (count ids SemiprimeSourceWordIdEnvironment.extend terminal keys.value env).clock+
    (unaryPower ids.length (4-active.length)).clock+(unaryPower ids.length (4-active.length)).cells.length+
    (natBits (unaryPower ids.length (4-active.length)).cells.length).clock+
    bitCost (mulBits (count ids SemiprimeSourceWordIdEnvironment.extend terminal keys.value env).bits
      (natBits (unaryPower ids.length (4-active.length)).cells.length).bits)+20≤_
  unfold localBudget paddingBudget
  rw [← hL]
  rw [← hL] at hc'
  simp only [unaryPower_length] at hm enc' ⊢
  omega

/-- Physical lane adders and all complete local counts. -/
def evaluateBudget (r Q N L T : ℕ) : ℕ :=
  T*(localBudget r Q N L+11*(3+8*L+L^4+T)+12)+1

/-- Every original descriptor is evaluated once, with actual physical accumulator reports. -/
theorem evaluate_clock (r Q : ℕ) [NeZero r] (programs : List (ScoreProgram Q))
    (remaining : List ℕ) (env : Env) (N : ℕ) (hr : remaining.Nodup) (hn : remaining.length≤ N)
    (he : ValidIds (acquire r Q).ids env) (hf : env.fixedIDs.length≤ N)
    (ho : env.overrides=[]) (hi : ∀ i∈remaining,i≤ N)
    (hp : ∀ p∈programs,∀ i∈support p,i≤ N) :
    (SemiprimeSourceWordIdCounts.evaluate (acquire r Q) programs remaining env).clock≤
      evaluateBudget r Q N (r^Q) programs.length := by
  have hL : (acquire r Q).ids.length=r^Q := (SemiprimeSourceWordBank.acquire_ids_length r Q).trans
    (SemiprimeSourceWordBankIndexed.acquire_length r Q)
  have hpos : 0<(acquire r Q).ids.length := by rw [hL];exact pow_pos (NeZero.pos r) _
  induction programs with
  | nil => simp [SemiprimeSourceWordIdCounts.evaluate,evaluate,evaluateBudget]
  | cons p programs ih =>
    have ht:=padded_clock r Q p remaining env N hr hn he hf ho hi (hp p List.mem_cons_self)
    have hc:=ih (fun p h => hp p (List.mem_cons_of_mem _ h))
    have hl:=SemiprimeSourceWordIdCountsBudget.evaluate_length (acquire r Q).ids SemiprimeSourceWordIdEnvironment.extend
      (fun p env => SemiprimeSourceWordIdPredicate.terminal (acquire r Q) env p)
      programs remaining env hpos hr
    have hthis:=SemiprimeSourceWordIdCountsBudget.padded_length (acquire r Q).ids SemiprimeSourceWordIdEnvironment.extend
      (fun env => SemiprimeSourceWordIdPredicate.terminal (acquire r Q) env p) p remaining env hpos hr
    have ai:=addBits_cost (padded (acquire r Q).ids SemiprimeSourceWordIdEnvironment.extend
      (fun env => SemiprimeSourceWordIdPredicate.terminal (acquire r Q) env p) p remaining env).bits
      (SemiprimeSourceWordIdCounts.evaluate (acquire r Q) programs remaining env).incidence false
    have ah:=addBits_cost (padded (acquire r Q).ids SemiprimeSourceWordIdEnvironment.extend
      (fun env => SemiprimeSourceWordIdPredicate.terminal (acquire r Q) env p) p remaining env).bits
      (SemiprimeSourceWordIdCounts.evaluate (acquire r Q) programs remaining env).head false
    rw [hL] at hl hthis
    have mi : max _ (SemiprimeSourceWordIdCounts.evaluate (acquire r Q) programs remaining env).incidence.length≤
        3+8*r^Q+(r^Q)^4+programs.length := max_le (hthis.trans (by omega)) hl.1
    have mh : max _ (SemiprimeSourceWordIdCounts.evaluate (acquire r Q) programs remaining env).head.length≤
        3+8*r^Q+(r^Q)^4+programs.length := max_le (hthis.trans (by omega)) hl.2
    cases p <;> simp only [SemiprimeSourceWordIdCounts.evaluate,evaluate,evaluateBudget,List.length_cons] at * <;> nlinarith

/-- Copy original ID prefix once before count completion. -/
def sequentialBudget (r Q N L T : ℕ) : ℕ :=
  8*L+N*(8*L+4)+7+evaluateBudget r Q N L T+2*N+8

/-- Full concrete physical-ID sequential callback from ORIGINAL acquired data. -/
theorem sequential_clock (r Q : ℕ) [NeZero r] (defaultID : List Bool)
    (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool)) (N : ℕ)
    (hd : defaultID∈(acquire r Q).ids) (hf : ∀ id∈fixedIDs,id∈(acquire r Q).ids)
    (hlen : fixedIDs.length+n≤ N) (hp : ∀ p∈programs,∀ i∈support p,i≤ N) :
    (SemiprimeSourceWordIdCounts.sequential (acquire r Q) defaultID programs n fixedIDs).clock≤
      sequentialBudget r Q N (r^Q) programs.length := by
  have hv:=SemiprimeSourceWordIdEnvironment.initial_valid _ defaultID fixedIDs hd hf
  have hc:=evaluate_clock r Q programs (List.range' fixedIDs.length n)
    (SemiprimeSourceWordIdEnvironment.initial defaultID fixedIDs).value N List.nodup_range'
    (by simp only [List.length_range'];omega) hv
    (by simpa only [SemiprimeSourceWordIdEnvironment.initial,SemiprimeSourceChoiceBits.copyIDs_value] using (show fixedIDs.length≤ N by omega))
    rfl (by intro i hi;simp only [List.mem_range'] at hi;omega) hp
  have hi:=SemiprimeSourceWordIdEnvironment.initial_work defaultID fixedIDs (2*r^Q)
    (fun id hid => SemiprimeSourceWordBankAcquisitionBudget.acquire_ids_bounded r Q id (hf id hid))
  have hdw:=SemiprimeSourceWordBankAcquisitionBudget.acquire_ids_bounded r Q defaultID hd
  have hinit : (SemiprimeSourceWordIdEnvironment.initial defaultID fixedIDs).work≤8*r^Q+N*(8*r^Q+4)+7 := by
    apply hi.trans
    calc
      _≤4*(2*r^Q)+N*(4*(2*r^Q)+4)+7 := by gcongr;omega
      _=8*r^Q+N*(8*r^Q+4)+7 := by ring
  simp only [SemiprimeSourceWordIdCounts.sequential,sequentialBudget]
  omega

/-- Actual final weighted arithmetic from cached original weight arrays. -/
def scoreBudget (r Q N L T K : ℕ) : ℕ :=
  sequentialBudget r Q N L T+
    SemiprimeSourceScoreWeightBits.combineBudget (SemiprimeSourceWordIdCountsBounds.operandWidth L T K)+5

/-- Actual concrete score clock; no terminal, count, push, Fits or encoded-menu advice. -/
theorem score_clock (r Q : ℕ) [NeZero r] (weights : SemiprimeSourceScoreWeightBits.Weights)
    (defaultID : List Bool) (programs : List (ScoreProgram Q)) (n : ℕ) (fixedIDs : List (List Bool)) (N K : ℕ)
    (hd : defaultID∈(acquire r Q).ids) (hf : ∀ id∈fixedIDs,id∈(acquire r Q).ids)
    (hlen : fixedIDs.length+n≤ N) (hp : ∀ p∈programs,∀ i∈support p,i≤ N)
    (ha : weights.incidence.length≤ K) (hb : weights.head.length≤ K) :
    (SemiprimeSourceWordIdCounts.score (acquire r Q) weights defaultID programs n fixedIDs).clock≤
      scoreBudget r Q N (r^Q) programs.length K := by
  have hc:=sequential_clock r Q defaultID programs n fixedIDs N hd hf hlen hp
  have hl:=SemiprimeSourceWordIdCountsBounds.sequential_length (acquire r Q) defaultID programs n fixedIDs
    (SemiprimeSourceWordIdCountsBounds.acquired_ids_pos r Q)
  have hidlen : (acquire r Q).ids.length=r^Q := (SemiprimeSourceWordBank.acquire_ids_length r Q).trans
    (SemiprimeSourceWordBankIndexed.acquire_length r Q)
  rw [hidlen] at hl
  have hm:=SemiprimeSourceScoreWeightBits.combine_clock weights
    (SemiprimeSourceWordIdCounts.sequential (acquire r Q) defaultID programs n fixedIDs).incidence
    (SemiprimeSourceWordIdCounts.sequential (acquire r Q) defaultID programs n fixedIDs).head
    (SemiprimeSourceWordIdCountsBounds.operandWidth (r^Q) programs.length K)
    (ha.trans (by unfold SemiprimeSourceWordIdCountsBounds.operandWidth;omega))
    (hb.trans (by unfold SemiprimeSourceWordIdCountsBounds.operandWidth;omega))
    (hl.1.trans (by unfold SemiprimeSourceWordIdCountsBounds.operandWidth;omega))
    (hl.2.trans (by unfold SemiprimeSourceWordIdCountsBounds.operandWidth;omega))
  simp only [SemiprimeSourceWordIdCounts.score,scoreBudget]
  omega

end RiemannGaussian.SemiprimeSourceWordIdCountsClock
