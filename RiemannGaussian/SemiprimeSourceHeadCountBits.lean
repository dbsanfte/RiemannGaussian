/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceCountPowers
import RiemannGaussian.SemiprimeSourceHeadCountFormula
import RiemannGaussian.SemiprimeSourceWordIdPredicateBounds

/-! # Closed-form physical padded head-collision counter
Only actual cached Boolean powers are copied. The one fixed/fixed test uses the
actual acquired-bank predicate. Native descriptor equality and membership scans
retain their explicit metadata-stage ledger, not a whole primitive-bit claim.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHeadCountBits
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords SemiprimeSourceOffsetInputsCore SemiprimeBitArithmetic
open SemiprimeSourceCountPowers (Powers)
open SemiprimeSourceWordBank (Bank)
open SemiprimeSourceWordIdEnvironment (Env Rel)

/-- Execute the physical head-count shortcut with cached original power payloads.
The cache acquisition work belongs to the once-per-caller initializer. -/
def count (bank : Bank) (env : Env) (powers : Powers) {Q : ℕ} (q : Fin Q)
    (a b : ℕ) (remaining : List ℕ) : NatRun :=
  if a=b then
    let out := SemiprimeSourceChoiceBits.copyID powers.fourth
    ⟨out.value,out.work+3⟩
  else
    let ma := memberRun a remaining
    let mb := memberRun b remaining
    if ma.value || mb.value then
      let out := SemiprimeSourceChoiceBits.copyID powers.head
      ⟨out.value,ma.work+mb.work+out.work+5⟩
    else
      let truth := SemiprimeSourceWordIdPredicate.terminal bank env (.head q a b)
      if truth.value then
        let out := SemiprimeSourceChoiceBits.copyID powers.fourth
        ⟨out.value,ma.work+mb.work+truth.work+out.work+7⟩
      else ⟨[],ma.work+mb.work+truth.work+5⟩

/-- Exact branch payloads; no numerical count is encoded or supplied. -/
theorem count_bits (bank : Bank) (env : Env) (powers : Powers) {Q : ℕ} (q : Fin Q)
    (a b : ℕ) (remaining : List ℕ) :
    (count bank env powers q a b remaining).bits=
      if a=b then powers.fourth else if a∈remaining ∨ b∈remaining then powers.head
      else if (SemiprimeSourceWordIdPredicate.terminal bank env (.head q a b)).value then powers.fourth else [] := by
  by_cases hab : a=b
  · simp [count,hab,SemiprimeSourceChoiceBits.copyID_value]
  · by_cases ha : a∈remaining <;> by_cases hb : b∈remaining <;>
      simp [count,hab,ha,hb,memberRun_value,SemiprimeSourceChoiceBits.copyID_value]
    split_ifs <;> rfl

/-- Structural output width covers every branch, independent of truth or count value. -/
theorem count_length (bank : Bank) (env : Env) (powers : Powers) {Q : ℕ} (q : Fin Q)
    (a b : ℕ) (remaining : List ℕ) :
    (count bank env powers q a b remaining).bits.length ≤
      max powers.fourth.length powers.head.length := by
  rw [count_bits]
  split_ifs <;> simp

/-- Actual original cache acquisition supplies all output widths internally. -/
theorem acquired_length (r Q : ℕ) (env : Env) (q : Fin Q) (a b : ℕ) (remaining : List ℕ) :
    (count (SemiprimeSourceWordBank.acquire r Q) env (SemiprimeSourceCountPowers.acquire r Q)
      q a b remaining).bits.length ≤ SemiprimeSourceCountPowers.width r Q := by
  apply (count_length _ _ _ q a b remaining).trans
  exact max_le (SemiprimeSourceCountPowers.acquire_length r Q).2.2.1
    (SemiprimeSourceCountPowers.acquire_length r Q).2.2.2

/-- The optimized physical count equals the ACTUAL original padded head counter.
The original bank and power cache are concretely acquired, with no count/Fits advice. -/
theorem count_original (r Q : ℕ) [NeZero r] (env : Env)
    (original : SemiprimeMaterializedScoreEnvironment.Environment r Q)
    (q : Fin Q) (a b : ℕ) (remaining : List ℕ) (hn : remaining.Nodup)
    (he : Rel (SemiprimeSourceWordBank.acquire r Q).ids
      (SemiprimeSourceWordBankSemantics.decode r Q) env original) :
    bitValue (count (SemiprimeSourceWordBank.acquire r Q) env
      (SemiprimeSourceCountPowers.acquire r Q) q a b remaining).bits=
      (SemiprimeSourceScoreCountsPadding.paddedLocal (SemiprimeFiniteEnumerations.words r Q).values
        (.head q a b) remaining original).value := by
  have ht := SemiprimeSourceWordIdPredicate.terminal_rel r Q env original (.head q a b) he
  change (SemiprimeSourceWordIdPredicate.terminal (SemiprimeSourceWordBank.acquire r Q) env
    (.head q a b)).value=decide (SemiprimeMaterializedScoreEnvironment.denote original a q=
      SemiprimeMaterializedScoreEnvironment.denote original b q) at ht
  have hp := SemiprimeSourceCountPowers.acquire_value r Q
  have hfourth : bitValue (SemiprimeSourceCountPowers.acquire r Q).fourth=(r^Q)^4 := by
    rw [hp.2.2.1,←pow_mul]
    congr 1
    omega
  rw [count_bits,SemiprimeSourceHeadCountFormula.head_padded_original r Q q a b remaining original hn]
  by_cases hab : a=b
  · simp only [hab,ite_true,hfourth]
  · by_cases hactive : a∈remaining ∨ b∈remaining
    · simp only [hab,ite_false,hactive,ite_true,hp.2.2.2]
    · simp only [hab,ite_false,hactive,ht]
      by_cases h : SemiprimeMaterializedScoreEnvironment.denote original a q=
          SemiprimeMaterializedScoreEnvironment.denote original b q
      · simp [h,hfourth]
      · simp [h,bitValue]

end RiemannGaussian.SemiprimeSourceHeadCountBits
