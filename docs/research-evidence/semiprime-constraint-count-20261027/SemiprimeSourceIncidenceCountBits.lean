/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceIncidenceCountFormula
import RiemannGaussian.SemiprimeSourceCountPowers
import RiemannGaussian.SemiprimeSourceWordIdPredicateBounds

/-! # Physical constant-size classification of original incidence completions
Each fixed equality uses actual physical ID reads and comparison. A free
equality contributes a proved degree loss, without enumerating any completion.
Native descriptor equality/membership and report stages remain explicit.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceIncidenceCountBits
open SemiprimeMaterializedWords SemiprimeSourceOffsetInputsCore SemiprimeBitArithmetic
open SemiprimeSourceWordIdEnvironment
open SemiprimeSourceCountPowers (Powers)
open SemiprimeSourceIncidenceCountFormula

/-- One actually evaluated equality constraint and its remaining free degree. -/
structure Edge where
  /-- Whether fixed anchors permit this equality. -/
  possible : Bool
  /-- Whether a nonloop equality consumes one free word choice. -/
  drop : Bool
  /-- Actual key/ID reads, physical comparison and native membership reports. -/
  clock : ℕ

/-- Classify one original equality, inspecting anchors only when both ends are fixed. -/
def edge (env : Env) (a c : ℕ) (remaining : List ℕ) : Edge :=
  if a=c then ⟨true,false,3⟩ else
    let ma := memberRun a remaining
    let mc := memberRun c remaining
    if ma.value || mc.value then ⟨true,true,ma.work+mc.work+5⟩ else
      let ka := acquireKey a
      let kc := acquireKey c
      let va := read env ka.value
      let vc := read env kc.value
      let same := equalID va.value vc.value
      ⟨same.value,false,ma.work+mc.work+ka.work+kc.work+va.work+vc.work+same.work+9⟩

/-- The actual physical equality is the original environment-word equality. -/
theorem read_equal_original (r Q : ℕ) [NeZero r] (env : Env)
    (original : SemiprimeMaterializedScoreEnvironment.Environment r Q) (a c : ℕ)
    (he : Rel (SemiprimeSourceWordBank.acquire r Q).ids
      (SemiprimeSourceWordBankSemantics.decode r Q) env original) :
    (equalID (read env (acquireKey a).value).value
      (read env (acquireKey c).value).value).value=
      decide (SemiprimeMaterializedScoreEnvironment.denote original a=
        SemiprimeMaterializedScoreEnvironment.denote original c) := by
  have ha := read_valid (SemiprimeSourceWordBank.acquire r Q).ids env (acquireKey a).value he.1
  have hc := read_valid (SemiprimeSourceWordBank.acquire r Q).ids env (acquireKey c).value he.1
  have h := SemiprimeSourceWordIdPredicate.equalID_decoded r Q _ _ ha hc
  rw [SemiprimeSourceWordIdPredicate.decoded_read,SemiprimeSourceWordIdPredicate.decoded_read] at h
  simpa only [SemiprimeMaterializedScoreEnvironment.denote,he.2] using h

/-- Concrete ID operations produce exactly the proved edge predicates. -/
theorem edge_original (r Q : ℕ) [NeZero r] (env : Env)
    (original : SemiprimeMaterializedScoreEnvironment.Environment r Q) (a c : ℕ)
    (remaining : List ℕ)
    (he : Rel (SemiprimeSourceWordBank.acquire r Q).ids
      (SemiprimeSourceWordBankSemantics.decode r Q) env original) :
    (edge env a c remaining).possible=
        decide (pairOK remaining (SemiprimeMaterializedScoreEnvironment.denote original) a c) ∧
      (edge env a c remaining).drop=decide (pairActive remaining a c) := by
  have h := read_equal_original r Q env original a c he
  by_cases hac : a=c
  · simp [edge,hac,pairOK,pairActive]
  · by_cases ha : a∈remaining <;> by_cases hc : c∈remaining <;>
      simp [edge,hac,ha,hc,memberRun_value,pairOK,pairActive,h]

/-- Two physical edge classifiers select an actually copied cached count word. -/
def count (env : Env) (powers : Powers) (a b c d : ℕ) (remaining : List ℕ) : NatRun :=
  let first := edge env a c remaining
  let second := edge env b d remaining
  if first.possible && second.possible then
    if first.drop && second.drop then
      let out := SemiprimeSourceChoiceBits.copyID powers.square
      ⟨out.value,first.clock+second.clock+out.work+7⟩
    else if first.drop || second.drop then
      let out := SemiprimeSourceChoiceBits.copyID powers.cube
      ⟨out.value,first.clock+second.clock+out.work+9⟩
    else
      let out := SemiprimeSourceChoiceBits.copyID powers.fourth
      ⟨out.value,first.clock+second.clock+out.work+9⟩
  else ⟨[],first.clock+second.clock+5⟩

/-- Every output branch contains only its actual cached physical payload. -/
theorem count_bits (env : Env) (powers : Powers) (a b c d : ℕ) (remaining : List ℕ) :
    (count env powers a b c d remaining).bits=
      if (edge env a c remaining).possible && (edge env b d remaining).possible then
        if (edge env a c remaining).drop && (edge env b d remaining).drop then powers.square
        else if (edge env a c remaining).drop || (edge env b d remaining).drop then powers.cube
        else powers.fourth
      else [] := by
  unfold count
  split_ifs <;> simp_all only [SemiprimeSourceChoiceBits.copyID_value,ite_true,ite_false,Bool.false_eq_true]

/-- Output widths follow actual branch payloads, not a decoded count bound. -/
theorem count_length (env : Env) (powers : Powers) (a b c d : ℕ) (remaining : List ℕ) :
    (count env powers a b c d remaining).bits.length ≤
      max powers.square.length (max powers.cube.length powers.fourth.length) := by
  rw [count_bits]
  split_ifs
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · simp

/-- Original cache acquisition supplies every output width. -/
theorem acquired_length (r Q : ℕ) (env : Env) (a b c d : ℕ) (remaining : List ℕ) :
    (count env (SemiprimeSourceCountPowers.acquire r Q) a b c d remaining).bits.length ≤
      SemiprimeSourceCountPowers.width r Q := by
  apply (count_length _ _ _ _ _ _ _).trans
  have h := SemiprimeSourceCountPowers.acquire_length r Q
  exact max_le h.1 (max_le h.2.1 h.2.2.1)

/-- Exact original padded incidence count from physical classifiers and copies.
Original descriptor compilation discharges every namespace inequality. -/
theorem count_original (r Q : ℕ) [NeZero r] (env : Env)
    (original : SemiprimeMaterializedScoreEnvironment.Environment r Q) (a b c d : ℕ)
    (remaining : List ℕ) (hn : remaining.Nodup)
    (he : Rel (SemiprimeSourceWordBank.acquire r Q).ids
      (SemiprimeSourceWordBankSemantics.decode r Q) env original)
    (hab : a≠b) (had : a≠d) (hcb : c≠b) (hcd : c≠d) :
    bitValue (count env (SemiprimeSourceCountPowers.acquire r Q) a b c d remaining).bits=
      (SemiprimeSourceScoreCountsPadding.paddedLocal
        (SemiprimeFiniteEnumerations.words r Q).values
        (.incidence a b c d) remaining original).value := by
  have hfirst := edge_original r Q env original a c remaining he
  have hsecond := edge_original r Q env original b d remaining he
  have hp := SemiprimeSourceCountPowers.acquire_value r Q
  have hsquare : bitValue (SemiprimeSourceCountPowers.acquire r Q).square=(r^Q)^2 := by
    rw [hp.1,←pow_mul]
    congr 1
    omega
  have hcube : bitValue (SemiprimeSourceCountPowers.acquire r Q).cube=(r^Q)^3 := by
    rw [hp.2.1,←pow_mul]
    congr 1
    omega
  have hfourth : bitValue (SemiprimeSourceCountPowers.acquire r Q).fourth=(r^Q)^4 := by
    rw [hp.2.2.1,←pow_mul]
    congr 1
    omega
  have hv := paddedLocal_formula r Q (NeZero.pos r) a b c d remaining original hn hab had hcb hcd
  simp only [SemiprimeSourceHeadCountFormula.alphabet] at hv
  rw [count_bits,hfirst.1,hfirst.2,hsecond.1,hsecond.2,hv]
  simp only [classifiedCount,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  split_ifs <;> simp only [hsquare,hcube,hfourth,bitValue]

end RiemannGaussian.SemiprimeSourceIncidenceCountBits
