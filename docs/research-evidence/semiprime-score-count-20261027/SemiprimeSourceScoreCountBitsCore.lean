/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreWeightAcquisition
import RiemannGaussian.SemiprimeSourceScoreCountsPadding

/-! # Physical branch-word additions for original finite source counts
The internal terminal parameter is discharged by the concrete physical original
predicate in the caller module; no integer count answer drives this recursion.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceScoreCountBitsCore
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceOffsetInputsCore SemiprimeBitArithmetic

/-- Right-recursive actual addition of the acquired unsigned branch words. -/
def sumBits {α : Type*} (f : α→NatRun) : List α→NatRun
  | [] => ⟨[],1⟩
  | a::as =>
    let first := f a
    let rest := sumBits f as
    let out := addBits first.bits rest.bits false
    ⟨out.bits,first.clock+rest.clock+bitCost out+3⟩

/-- Branch words sum in the same original order, including repeated labels. -/
theorem sumBits_value {α : Type*} (f : α→NatRun) (xs : List α) :
    bitValue (sumBits f xs).bits=(xs.map (fun a => bitValue (f a).bits)).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [sumBits,addBits_correct,ih,bitNat,Bool.false_eq_true,
      ite_false,Nat.add_zero,List.map_cons,List.sum_cons]

/-- Actual count recursion: physical terminal then Boolean additions, never a Nat sum. -/
def count {r Q : ℕ} (alphabet : List (Word r Q))
    (terminal : Environment r Q→Run Bool) : List ℕ→Environment r Q→NatRun
  | [],env => let out := terminal env
              ⟨if out.value then [true] else [],out.work+2⟩
  | i::remaining,env =>
    let out := sumBits (fun w =>
      let child := count alphabet terminal remaining (extend env i w)
      ⟨child.bits,child.clock+Q+2⟩) alphabet
    ⟨out.bits,out.clock+alphabet.length+3⟩

/-- The internal terminal refinement identifies every actual branch with the
original finite integer count. The concrete caller discharges this premise. -/
theorem count_value {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (terminal : Environment r Q→Run Bool)
    (ht : ∀ env,(terminal env).value=(SemiprimeSourceScoreCounts.hit p env).value)
    (remaining : List ℕ) (env : Environment r Q) :
    bitValue (count alphabet terminal remaining env).bits=
      (SemiprimeSourceScoreCounts.count alphabet p remaining env).value := by
  induction remaining generalizing env with
  | nil =>
    simp only [count,SemiprimeSourceScoreCounts.count,ht]
    split <;> simp [bitValue,bitNat]
  | cons i remaining ih =>
    simp only [count,sumBits_value,SemiprimeSourceScoreCounts.count,
      SemiprimeSourceScoreCounts.sumCount_value]
    congr 1
    apply List.map_congr_left
    intro w _
    exact ih (extend env i w)

/-- All recursive branch-addition outputs have an explicit physical width. -/
theorem sumBits_length {α : Type*} (f : α→NatRun) (xs : List α) (K : ℕ)
    (h : ∀ a∈xs,(f a).bits.length ≤ K) :
    (sumBits f xs).bits.length ≤ K+xs.length := by
  induction xs with
  | nil => simp [sumBits]
  | cons a as ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have hw := (addBits_counts (f a).bits (sumBits f as).bits false).2.2.2.2
    simp only [sumBits,List.length_cons]
    omega

/-- Actual right-recursive adders and child reports have a closed finite-loop bound. -/
theorem sumBits_clock {α : Type*} (f : α→NatRun) (xs : List α) (K B : ℕ)
    (hl : ∀ a∈xs,(f a).bits.length ≤ K) (hc : ∀ a∈xs,(f a).clock ≤ B) :
    (sumBits f xs).clock ≤ xs.length*(B+11*(K+xs.length)+7)+1 := by
  induction xs with
  | nil => simp [sumBits]
  | cons a as ih =>
    have ha := hc a List.mem_cons_self
    have ht := ih (fun a ha => hl a (List.mem_cons_of_mem _ ha))
      (fun a ha => hc a (List.mem_cons_of_mem _ ha))
    have hw := sumBits_length f as K (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    have hla := hl a List.mem_cons_self
    have had := addBits_cost (f a).bits (sumBits f as).bits false
    have hm : max (f a).bits.length (sumBits f as).bits.length ≤ K+as.length := by
      apply max_le <;> omega
    simp only [sumBits,List.length_cons]
    nlinarith

/-- Count word width, covering every branch frame without any desired-count bound. -/
theorem count_length {r Q : ℕ} (alphabet : List (Word r Q))
    (terminal : Environment r Q→Run Bool) (remaining : List ℕ) (env : Environment r Q) :
    (count alphabet terminal remaining env).bits.length ≤ 1+remaining.length*alphabet.length := by
  induction remaining generalizing env with
  | nil => simp only [count,List.length_nil,Nat.zero_mul,Nat.add_zero];split <;> simp
  | cons i remaining ih =>
    have h := sumBits_length (fun w =>
      let child := count alphabet terminal remaining (extend env i w)
      (⟨child.bits,child.clock+Q+2⟩:NatRun)) alphabet (1+remaining.length*alphabet.length)
      (fun w _ => ih (extend env i w))
    simpa only [count,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using h

/-- Original active list and actual acquired padding word followed by a product. -/
def padded {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (terminal : Environment r Q→Run Bool) (remaining : List ℕ) (env : Environment r Q) : NatRun :=
  let active := activeRun (support p) remaining
  let raw := count alphabet terminal active.value env
  let pad := unaryPower alphabet.length (4-active.value.length)
  let encoded := natBits pad.cells.length
  let out := mulBits raw.bits encoded.bits
  ⟨out.bits,active.work+raw.clock+pad.clock+pad.cells.length+encoded.clock+bitCost out+8⟩

/-- Padding uses a physically acquired multiplier, not a power/count-answer word. -/
theorem padded_value {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (terminal : Environment r Q→Run Bool)
    (ht : ∀ env,(terminal env).value=(SemiprimeSourceScoreCounts.hit p env).value)
    (remaining : List ℕ) (env : Environment r Q) :
    bitValue (padded alphabet p terminal remaining env).bits=
      (SemiprimeSourceScoreCountsPadding.paddedLocal alphabet p remaining env).value := by
  simp only [padded,mulBits_correct,natBits_value,unaryPower_length,count_value alphabet p terminal ht,
    SemiprimeSourceScoreCountsPadding.paddedLocal,
    (SemiprimeSourceScoreCountsPadding.power_spec _ _).1]
/-- Width of every actual normalized local word, derived from active support and
original alphabet size rather than the desired count value. -/
theorem padded_length {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (terminal : Environment r Q→Run Bool) (remaining : List ℕ) (env : Environment r Q)
    (hL : 0<alphabet.length) (hr : remaining.Nodup) :
    (padded alphabet p terminal remaining env).bits.length ≤
      3+8*alphabet.length+alphabet.length^4 := by
  have ha := SemiprimeSourceScoreCountsPadding.active_length p remaining hr
  have hc := count_length alphabet terminal (activeRun (support p) remaining).value env
  have he := natBits_length (unaryPower alphabet.length
    (4-(activeRun (support p) remaining).value.length)).cells.length
  rw [unaryPower_length] at he
  have hp : alphabet.length^(4-(activeRun (support p) remaining).value.length) ≤
      alphabet.length^4 := Nat.pow_le_pow_right hL (by omega)
  have hm := mulBits_length
    (count alphabet terminal (activeRun (support p) remaining).value env).bits
    (natBits (unaryPower alphabet.length (4-(activeRun (support p) remaining).value.length)).cells.length).bits
  simp only [unaryPower_length] at hm
  have hc' : (count alphabet terminal (activeRun (support p) remaining).value env).bits.length ≤
      1+4*alphabet.length := hc.trans (by gcongr)
  simp only [padded,unaryPower_length]
  omega

end RiemannGaussian.SemiprimeSourceScoreCountBitsCore
