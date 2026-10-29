/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdPredicate
import RiemannGaussian.SemiprimeSourceWordIdEnvironmentBounds
import RiemannGaussian.SemiprimeSourceWordBankAcquisitionBudget
import RiemannGaussian.SemiprimeSourceWordBankIndexed

/-! # Original acquired-bank physical terminal work
Every bound is derived from original finite descriptors, actual acquired-menu
membership and actual environment lengths. No encoded row, truth or cost oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeSourceWordIdPredicateBounds
open SemiprimeRationalBits SemiprimeMaterializedWords SemiprimeSourceWordIdEnvironment
open SemiprimeSourceWordIdPredicate SemiprimeSourceWordIdEnvironmentBounds
open SemiprimeSourceWordBank (acquire)
open SemiprimeMaterializedScoreEnvironment (ScoreProgram support)
open SemiprimeReportPolynomialGrowth

/-- Descriptor acquisition pays four original finite key producers conservatively. -/
def programBudget (N Q : ℕ) : ℕ := 4*keyBudget (N+Q+1)+10
/-- Actual acquired-bank row copy/address budget, keeping materialized L independent. -/
def bankReadBudget (r Q L : ℕ) : ℕ :=
  (L+1)*(SemiprimeSourceScorePredicateBitsBounds.copyBudget (r+1) Q+15*(2*L+1)+30)
/-- An actual prepared head coordinate scan, without an address oracle. -/
def colourReadBudget (r Q : ℕ) : ℕ := (Q+1)*(8*(r+1)+15*(Q+1)+30)
/-- Every actual key scan, optional bank read, ID/colour comparator and control. -/
def terminalStepBudget (r Q L N s : ℕ) : ℕ :=
  4*readBudget (N+1) N (2*L) s+2*eqBudget (2*L+1)+2*bankReadBudget r Q L+
    2*colourReadBudget r Q+SemiprimeSourceScorePredicateBitsBounds.equalityBudget (r+1)+20
/-- Complete original finite-descriptor terminal work. -/
def terminalBudget (r Q L N s : ℕ) : ℕ := programBudget N Q+terminalStepBudget r Q L N s+2

/-- Every descriptor key is actually acquired and charged from original support IDs. -/
theorem acquireProgram_work {Q : ℕ} (p : ScoreProgram Q) (N : ℕ)
    (hp : ∀ i∈support p,i ≤ N) : (acquireProgram p).work ≤ programBudget N Q := by
  have hkey (i : ℕ) (hi : i ≤ N+Q+1) : (acquireKey i).work ≤ keyBudget (N+Q+1) := by
    exact (acquireKey_work i).trans (by unfold keyBudget;gcongr)
  cases p with
  | incidence a b c d =>
    have ha := hkey a (by have := hp a (by simp [support]);omega)
    have hb := hkey b (by have := hp b (by simp [support]);omega)
    have hc := hkey c (by have := hp c (by simp [support]);omega)
    have hd := hkey d (by have := hp d (by simp [support]);omega)
    unfold acquireProgram programBudget
    dsimp only
    omega
  | head t a b =>
    have ht := hkey t.val (by have := t.isLt;omega)
    have ha := hkey a (by have := hp a (by simp [support]);omega)
    have hb := hkey b (by have := hp b (by simp [support]);omega)
    unfold acquireProgram programBudget
    dsimp only
    omega

/-- Original acquired-bank membership supplies each returned row's physical shape. -/
theorem row_bounded (r Q : ℕ) [NeZero r] (id : ID) (hi : id∈(acquire r Q).ids) :
    SemiprimeSourceScorePredicateBitsBounds.RowBound (r+1) Q
      (SemiprimeSourceWordBank.readRow (acquire r Q) id).value := by
  refine ⟨(SemiprimeSourceWordBankIndexed.readRow_length r Q id hi).le,?_⟩
  intro x hx
  exact (SemiprimeSourceWordBankBounds.readRow_good r Q id x hx).2

/-- The prepared physical head address scans all actual visited payload cells. -/
theorem colourRead_work (r Q : ℕ) [NeZero r] (id : ID)
    (hi : id∈(acquire r Q).ids) (t : Fin Q) :
    (SemiprimeSourceMemoryBits.readWord
      (SemiprimeSourceWordBank.readRow (acquire r Q) id).value (acquireKey t.val).value).clock ≤
        colourReadBudget r Q := by
  have hw := row_bounded r Q id hi
  have ha : (acquireKey t.val).value.length ≤ Q+1 := (acquireKey_length t.val).trans (by have := t.isLt;omega)
  have h := (SemiprimeSourceMemoryBits.readWord_clock _ _ (r+1) (Q+1) (by omega) ha hw.2).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hw.1 1))
  exact h

/-- All original-data prepared predicates have a derived work cap, including
actual menu-only ID comparisons and actual physical head bank/coordinate reads. -/
theorem terminalPrepared_work (r Q : ℕ) [NeZero r] (env : Env) (p : ScoreProgram Q) (N s : ℕ)
    (he : ValidIds (acquire r Q).ids env) (hf : env.fixedIDs.length ≤ N)
    (ho : env.overrides.length ≤ s) (hk : KeysBound (N+1) env)
    (hp : ∀ i∈support p,i ≤ N) :
    (terminalPrepared (acquire r Q) env (acquireProgram p).value).work ≤
      terminalStepBudget r Q (r^Q) N s := by
  have hmenu := SemiprimeSourceWordBankAcquisitionBudget.acquire_ids_bounded r Q
  have hpay := valid_payload (acquire r Q).ids env (2*r^Q) he hmenu
  have hm (i : ℕ) := read_valid (acquire r Q).ids env (acquireKey i).value he
  have hlen (i : ℕ) : (read env (acquireKey i).value).value.length ≤ 2*r^Q := hmenu _ (hm i)
  have hread (i : ℕ) (hi : i ≤ N) :
      (read env (acquireKey i).value).work ≤ readBudget (N+1) N (2*r^Q) s :=
    read_work env _ (N+1) N (2*r^Q) s hpay hk hf ho
      ((acquireKey_length i).trans (by omega))
  have hbank (i : ℕ) :
      (SemiprimeSourceWordBank.readRow (acquire r Q) (read env (acquireKey i).value).value).work ≤
        bankReadBudget r Q (r^Q) :=
    SemiprimeSourceWordBankAcquisitionBudget.readRow_clock_original r Q _ (hm i)
  cases p with
  | incidence a b c d =>
    have ha := hread a (hp a (by simp [support]))
    have hb := hread b (hp b (by simp [support]))
    have hc := hread c (hp c (by simp [support]))
    have hd := hread d (hp d (by simp [support]))
    have hheads := equalID_work (read env (acquireKey a).value).value (read env (acquireKey c).value).value
      (2*r^Q+1) (by omega) ((hlen a).trans (by omega)) ((hlen c).trans (by omega))
    have hslots := equalID_work (read env (acquireKey b).value).value (read env (acquireKey d).value).value
      (2*r^Q+1) (by omega) ((hlen b).trans (by omega)) ((hlen d).trans (by omega))
    unfold acquireProgram terminalPrepared terminalStepBudget
    dsimp only
    omega
  | head t a b =>
    have ha := hread a (hp a (by simp [support]))
    have hb := hread b (hp b (by simp [support]))
    have hba := hbank a
    have hbb := hbank b
    have hca := colourRead_work r Q _ (hm a) t
    have hcb := colourRead_work r Q _ (hm b) t
    have hva := row_bounded r Q _ (hm a)
    have hvb := row_bounded r Q _ (hm b)
    have hwa := SemiprimeSourceMemoryBits.readWord_width _ (acquireKey t.val).value (r+1) (by omega) hva.2
    have hwb := SemiprimeSourceMemoryBits.readWord_width _ (acquireKey t.val).value (r+1) (by omega) hvb.2
    have hsame := SemiprimeSourceScorePredicateBitsBounds.equalWord_work
      (SemiprimeSourceMemoryBits.readWord
        (SemiprimeSourceWordBank.readRow (acquire r Q) (read env (acquireKey a).value).value).value (acquireKey t.val).value).word
      (SemiprimeSourceMemoryBits.readWord
        (SemiprimeSourceWordBank.readRow (acquire r Q) (read env (acquireKey b).value).value).value (acquireKey t.val).value).word
      (r+1) hwa hwb
    unfold acquireProgram terminalPrepared resolve terminalStepBudget
    dsimp only
    omega

/-- The acquired ORIGINAL bank and ORIGINAL finite metadata close terminal work:
no bank contents, output truth, row height or callback-cost premise remains. -/
theorem terminal_work (r Q : ℕ) [NeZero r] (env : Env) (p : ScoreProgram Q) (N s : ℕ)
    (he : ValidIds (acquire r Q).ids env) (hf : env.fixedIDs.length ≤ N)
    (ho : env.overrides.length ≤ s) (hk : KeysBound (N+1) env)
    (hp : ∀ i∈support p,i ≤ N) :
    (terminal (acquire r Q) env p).work ≤ terminalBudget r Q (r^Q) N s := by
  have hprogram := acquireProgram_work p N hp
  have hbody := terminalPrepared_work r Q env p N s he hf ho hk hp
  unfold terminal terminalBudget
  dsimp only
  omega

/-- Fully acquired source endpoint retains the original bank acquisition as well. -/
theorem terminal_acquired_work (r Q : ℕ) [NeZero r] (env : Env) (p : ScoreProgram Q) (N s : ℕ)
    (he : ValidIds (acquire r Q).ids env) (hf : env.fixedIDs.length ≤ N)
    (ho : env.overrides.length ≤ s) (hk : KeysBound (N+1) env)
    (hp : ∀ i∈support p,i ≤ N) :
    (terminal_acquired r Q env p).work ≤
      SemiprimeSourceWordBankAcquisitionBudget.budget r Q (r^Q)+terminalBudget r Q (r^Q) N s+2 := by
  have ha := SemiprimeSourceWordBankAcquisitionBudget.acquire_clock r Q (NeZero.pos r)
  have ht := terminal_work r Q env p N s he hf ho hk hp
  unfold terminal_acquired
  dsimp only
  omega

/-- Fixed polynomial witnesses in independent ORIGINAL materialized dimensions.
The actual caller substitutes L=r^Q instead of bounding exponentials by 2^S. -/
theorem terminalBudget_monomial : ∃ C k : ℕ,∀ r Q L N s S,
    r ≤ S → Q ≤ S → L ≤ S → N ≤ S → s ≤ S → terminalBudget r Q L N s ≤ C*(S+1)^k := by
  have hh : Bound (fun S => terminalBudget S S S S S) := by
    simp only [terminalBudget,programBudget,terminalStepBudget,bankReadBudget,colourReadBudget,
      readBudget,scanStep,keyBudget,idCopyBudget,eqBudget,
      SemiprimeSourceScorePredicateBitsBounds.copyBudget,
      SemiprimeSourceScorePredicateBitsBounds.equalityBudget]
    boundArithmetic
  obtain ⟨C,k,h⟩ := hh
  refine ⟨C,k,?_⟩
  intro r Q L N s S hr hQ hL hN hs
  apply le_trans _ (h S)
  simp only [terminalBudget,programBudget,terminalStepBudget,bankReadBudget,colourReadBudget,
    readBudget,scanStep,keyBudget,idCopyBudget,eqBudget,
    SemiprimeSourceScorePredicateBitsBounds.copyBudget,
    SemiprimeSourceScorePredicateBitsBounds.equalityBudget]
  gcongr

end RiemannGaussian.SemiprimeSourceWordIdPredicateBounds
