/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdEnvironment
import RiemannGaussian.SemiprimeSourceWordBankBounds
import RiemannGaussian.SemiprimeSourceWordBankSemantics

/-! # Actual original source predicates over physical candidate IDs
Runtime environments/descriptors/bank rows contain ONLY acquired Boolean data.
No Word function, CachedWord construction or truth callback occurs on this path.
Original decoding is used solely in the refinement theorems.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeSourceWordIdPredicate
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords SemiprimeRationalBits SemiprimeBitArithmetic
open SemiprimeSourceScorePredicateBits SemiprimeSourceWordIdEnvironment
open SemiprimeSourceWordBank (Bank)

/-- Acquired physical score descriptor, containing no natural source lookup keys. -/
inductive Program where
  /-- Four actual Boolean variable-key words. -/
  | incidence (a b c d : ID)
  /-- Actual Boolean coordinate address and two Boolean variable keys. -/
  | head (coordinate a b : ID)

/-- Acquire descriptor keys/coordinate once from the ORIGINAL finite source descriptor. -/
def acquireProgram {Q : ℕ} : SemiprimeMaterializedScoreEnvironment.ScoreProgram Q → Run Program
  | .incidence a b c d =>
    let ka := acquireKey a
    let kb := acquireKey b
    let kc := acquireKey c
    let kd := acquireKey d
    ⟨.incidence ka.value kb.value kc.value kd.value,ka.work+kb.work+kc.work+kd.work+5⟩
  | .head t a b =>
    let kt := acquireKey t.val
    let ka := acquireKey a
    let kb := acquireKey b
    ⟨.head kt.value ka.value kb.value,kt.work+ka.work+kb.work+4⟩

/-- Actual key scan and then actual Boolean-address bank lookup; no semantic decoder. -/
def resolve (bank : Bank) (env : Env) (key : ID) : Run Row :=
  let id := read env key
  let row := SemiprimeSourceWordBank.readRow bank id.value
  ⟨row.value,id.work+row.work+3⟩

/-- Execute the finite physical descriptor on the actual candidate-ID environment. -/
def terminalPrepared (bank : Bank) (env : Env) : Program → Run Bool
  | .incidence a b c d =>
    let wa := read env a
    let wb := read env b
    let wc := read env c
    let wd := read env d
    let heads := equalID wa.value wc.value
    let slots := equalID wb.value wd.value
    ⟨heads.value && slots.value,wa.work+wb.work+wc.work+wd.work+heads.work+slots.work+4⟩
  | .head t a b =>
    let wa := resolve bank env a
    let wb := resolve bank env b
    let ca := SemiprimeSourceMemoryBits.readWord wa.value t
    let cb := SemiprimeSourceMemoryBits.readWord wb.value t
    let same := equalWord ca.word cb.word
    ⟨same.value,wa.work+wb.work+ca.clock+cb.clock+same.work+5⟩

/-- Original descriptor endpoint; descriptor acquisition is actually retained. -/
def terminal (bank : Bank) (env : Env) {Q : ℕ}
    (p : SemiprimeMaterializedScoreEnvironment.ScoreProgram Q) : Run Bool :=
  let program := acquireProgram p
  let out := terminalPrepared bank env program.value
  ⟨out.value,program.work+out.work+2⟩

/-- Fully acquired ORIGINAL dimension endpoint, with no supplied bank or word oracle. -/
def terminal_acquired (r Q : ℕ) (env : Env)
    (p : SemiprimeMaterializedScoreEnvironment.ScoreProgram Q) : Run Bool :=
  let bank := SemiprimeSourceWordBank.acquire r Q
  let out := terminal bank env p
  ⟨out.value,bank.clock+out.work+2⟩

/-- Actual coordinate-map equality yields each physically scanned source coordinate. -/
theorem coordinate_values {r Q : ℕ} (row : Row) (w : Word r Q)
    (h : row.map RationalWord.value=SemiprimeSourceWordBankRows.coordinates w) (t : Fin Q) :
    (coordinate row t.val).word.value=((w t).val:ℚ) := by
  rw [coordinate_value,h]
  simp [SemiprimeSourceWordBankRows.coordinates]

/-- Actual valid acquired bank rows have exactly the ORIGINAL whole-word equality. -/
theorem bank_rows_equal (r Q : ℕ) [NeZero r] (a b : ID)
    (ha : a∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hb : b∈(SemiprimeSourceWordBank.acquire r Q).ids) :
    (equalRows (SemiprimeSourceWordBank.readRow (SemiprimeSourceWordBank.acquire r Q) a).value
      (SemiprimeSourceWordBank.readRow (SemiprimeSourceWordBank.acquire r Q) b).value Q).value=
      decide (SemiprimeSourceWordBankSemantics.decode r Q a=SemiprimeSourceWordBankSemantics.decode r Q b) := by
  have hva := fun x hx => (SemiprimeSourceWordBankBounds.readRow_good r Q a x hx).1
  have hvb := fun x hx => (SemiprimeSourceWordBankBounds.readRow_good r Q b x hx).1
  have hca := SemiprimeSourceWordBankSemantics.readRow_coordinates r Q a ha
  have hcb := SemiprimeSourceWordBankSemantics.readRow_coordinates r Q b hb
  apply Bool.eq_iff_iff.mpr
  rw [equalRows_correct _ _ Q hva hvb]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    funext t
    have hh := h t.val t.isLt
    rw [coordinate_values _ _ hca t,coordinate_values _ _ hcb t] at hh
    exact Fin.ext (by exact_mod_cast hh)
  · intro h i hi
    let t : Fin Q := ⟨i,hi⟩
    rw [coordinate_values _ _ hca t,coordinate_values _ _ hcb t]
    exact congrArg (fun c : Fin r => (c.val:ℚ)) (congrFun h t)

/-- Actual acquired head-coordinate addresses yield the ORIGINAL colour equality. -/
theorem bank_colours_equal (r Q : ℕ) [NeZero r] (a b : ID)
    (ha : a∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hb : b∈(SemiprimeSourceWordBank.acquire r Q).ids) (t : Fin Q) :
    (equalWord
      (SemiprimeSourceMemoryBits.readWord
        (SemiprimeSourceWordBank.readRow (SemiprimeSourceWordBank.acquire r Q) a).value (acquireKey t.val).value).word
      (SemiprimeSourceMemoryBits.readWord
        (SemiprimeSourceWordBank.readRow (SemiprimeSourceWordBank.acquire r Q) b).value (acquireKey t.val).value).word).value=
      decide (SemiprimeSourceWordBankSemantics.decode r Q a t=SemiprimeSourceWordBankSemantics.decode r Q b t) := by
  have hva := fun x hx => (SemiprimeSourceWordBankBounds.readRow_good r Q a x hx).1
  have hvb := fun x hx => (SemiprimeSourceWordBankBounds.readRow_good r Q b x hx).1
  have hca := SemiprimeSourceWordBankSemantics.readRow_coordinates r Q a ha
  have hcb := SemiprimeSourceWordBankSemantics.readRow_coordinates r Q b hb
  change (equalWord (coordinate _ t.val).word (coordinate _ t.val).word).value=_
  apply Bool.eq_iff_iff.mpr
  rw [equalWord_correct _ _ (coordinate_valid _ _ hva) (coordinate_valid _ _ hvb),
    coordinate_values _ _ hca t,coordinate_values _ _ hcb t]
  simp only [decide_eq_true_eq]
  constructor
  · intro h;exact Fin.ext (by exact_mod_cast h)
  · intro h;rw [h]

/-- CERTIFIED acquired-bank injectivity licenses direct incidence ID comparison.
Numeric equality implies equal decoding even with padding; the converse uses
actual valid-menu injectivity, never a runtime truth assumption. -/
theorem equalID_decoded (r Q : ℕ) [NeZero r] (a b : ID)
    (ha : a∈(SemiprimeSourceWordBank.acquire r Q).ids)
    (hb : b∈(SemiprimeSourceWordBank.acquire r Q).ids) :
    (equalID a b).value=decide (SemiprimeSourceWordBankSemantics.decode r Q a=
      SemiprimeSourceWordBankSemantics.decode r Q b) := by
  apply Bool.eq_iff_iff.mpr
  rw [equalID_correct]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    simp only [SemiprimeSourceWordBankSemantics.decode,h]
  · intro h
    exact congrArg bitValue (SemiprimeSourceWordBankSemantics.decode_injective r Q ha hb h)

/-- A resolved actual ID denotes the ORIGINAL selected cached source word. -/
theorem decoded_read (r Q : ℕ) [NeZero r] (env : Env) (n : ℕ) :
    SemiprimeSourceWordBankSemantics.decode r Q (read env (acquireKey n).value).value=
      SemiprimeMaterializedScoreEnvironment.wordAt
        (SemiprimeMaterializedScoreEnvironment.readEnv
          (decodeEnvironment (SemiprimeSourceWordBankSemantics.decode r Q) env) n).value := by
  symm
  have h := read_decode (SemiprimeSourceWordBankSemantics.decode r Q) env (acquireKey n).value
  simpa only [acquireKey_value] using h

/-- The ACTUAL acquired-bank terminal is the original source hit for every
valid-menu environment; no truth, encoded word bank or decoding callback is supplied. -/
theorem terminal_value (r Q : ℕ) [NeZero r] (env : Env)
    (p : SemiprimeMaterializedScoreEnvironment.ScoreProgram Q)
    (he : ValidIds (SemiprimeSourceWordBank.acquire r Q).ids env) :
    (terminal (SemiprimeSourceWordBank.acquire r Q) env p).value=
      (SemiprimeSourceScoreCounts.hit p
        (decodeEnvironment (SemiprimeSourceWordBankSemantics.decode r Q) env)).value := by
  have hm (n : ℕ) := read_valid (SemiprimeSourceWordBank.acquire r Q).ids env (acquireKey n).value he
  cases p with
  | incidence a b c d =>
    simp only [terminal,acquireProgram,terminalPrepared]
    rw [equalID_decoded r Q _ _ (hm a) (hm c),equalID_decoded r Q _ _ (hm b) (hm d)]
    simp only [decoded_read,SemiprimeSourceScoreCounts.hit,
      SemiprimeMaterializedScoreEnvironment.equalCoordinates_value]
  | head t a b =>
    simp only [terminal,acquireProgram,terminalPrepared,resolve]
    rw [bank_colours_equal r Q _ _ (hm a) (hm b) t]
    simp only [decoded_read,SemiprimeSourceScoreCounts.hit]

/-- Concrete valid-menu relations instantiate physical count refinement. -/
theorem terminal_rel (r Q : ℕ) [NeZero r] (env : Env)
    (original : SemiprimeMaterializedScoreEnvironment.Environment r Q)
    (p : SemiprimeMaterializedScoreEnvironment.ScoreProgram Q)
    (h : Rel (SemiprimeSourceWordBank.acquire r Q).ids (SemiprimeSourceWordBankSemantics.decode r Q) env original) :
    (terminal (SemiprimeSourceWordBank.acquire r Q) env p).value=(SemiprimeSourceScoreCounts.hit p original).value := by
  rw [h.2]
  exact terminal_value r Q env p h.1

/-- Fully acquired original-input predicate preserves source truth with no bank advice. -/
theorem terminal_acquired_value (r Q : ℕ) [NeZero r] (env : Env)
    (p : SemiprimeMaterializedScoreEnvironment.ScoreProgram Q)
    (he : ValidIds (SemiprimeSourceWordBank.acquire r Q).ids env) :
    (terminal_acquired r Q env p).value=
      (SemiprimeSourceScoreCounts.hit p
        (decodeEnvironment (SemiprimeSourceWordBankSemantics.decode r Q) env)).value :=
  terminal_value r Q env p he

end RiemannGaussian.SemiprimeSourceWordIdPredicate
