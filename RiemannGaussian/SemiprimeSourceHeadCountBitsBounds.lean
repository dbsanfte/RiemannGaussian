/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHeadCountBits

/-! # Original-metadata work of the closed-form physical head counter
There is no completion enumeration or unary count padding. The fixed/fixed
branch pays its concrete original-bank head predicate; cached powers are copied.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHeadCountBitsBounds
open SemiprimeSourceHeadCountBits SemiprimeSourceOffsetInputsCore SemiprimeMaterializedWords
open SemiprimeSourceCountPowers (Powers)
open SemiprimeSourceWordBank (Bank)
open SemiprimeSourceWordIdEnvironment (Env ValidIds)
open SemiprimeSourceWordIdEnvironmentBounds (KeysBound)
open SemiprimeReportPolynomialGrowth

/-- Every actual branch retains scans, payload copies and any physical truth report. -/
theorem count_clock (bank : Bank) (env : Env) (powers : Powers) {Q : ℕ} (q : Fin Q)
    (a b : ℕ) (remaining : List ℕ) :
    (count bank env powers q a b remaining).clock  ≤ 
      4*remaining.length+4*max powers.fourth.length powers.head.length+
        (SemiprimeSourceWordIdPredicate.terminal bank env (.head q a b)).work+20 := by
  have hm := memberRun_work a remaining
  have hn := memberRun_work b remaining
  have hf := SemiprimeSourceChoiceBits.copyID_work powers.fourth
  have hh := SemiprimeSourceChoiceBits.copyID_work powers.head
  have hfl := le_max_left powers.fourth.length powers.head.length
  have hhl := le_max_right powers.fourth.length powers.head.length
  unfold count
  split
  · dsimp only
    omega
  · dsimp only
    split
    · dsimp only
      omega
    · split <;> dsimp only <;> omega

/-- Closed head-callback work from original bank/cache/finite metadata dimensions. -/
def budget (r Q L N s : ℕ) : ℕ :=
  4*N+4*SemiprimeSourceCountPowers.width r Q+
    SemiprimeSourceWordIdPredicateBounds.terminalBudget r Q L N s+20

/-- Original acquired powers and bank discharge all physical value/width/callback
conditions. The remaining hypotheses are literal original finite metadata bounds. -/
theorem count_original_clock (r Q : ℕ) [NeZero r] (env : Env) (q : Fin Q)
    (a b : ℕ) (remaining : List ℕ) (N s : ℕ)
    (he : ValidIds (SemiprimeSourceWordBank.acquire r Q).ids env)
    (hf : env.fixedIDs.length ≤ N) (ho : env.overrides.length ≤ s) (hk : KeysBound (N+1) env)
    (hn : remaining.length ≤ N) (ha : a ≤ N) (hb : b ≤ N) :
    (count (SemiprimeSourceWordBank.acquire r Q) env (SemiprimeSourceCountPowers.acquire r Q)
      q a b remaining).clock ≤ budget r Q (r^Q) N s := by
  have hc := count_clock (SemiprimeSourceWordBank.acquire r Q) env
    (SemiprimeSourceCountPowers.acquire r Q) q a b remaining
  have hl := SemiprimeSourceCountPowers.acquire_length r Q
  have hm : max (SemiprimeSourceCountPowers.acquire r Q).fourth.length
      (SemiprimeSourceCountPowers.acquire r Q).head.length ≤ SemiprimeSourceCountPowers.width r Q :=
    max_le hl.2.2.1 hl.2.2.2
  have ht := SemiprimeSourceWordIdPredicateBounds.terminal_work r Q env (.head q a b) N s
    he hf ho hk (by
      intro i hi
      simp only [SemiprimeMaterializedScoreEnvironment.support,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl <;> assumption)
  unfold budget
  omega

/-- Componentwise resource monotonicity, isolated from all actual source expressions. -/
theorem budget_mono {r Q L N s r' Q' L' N' s' : ℕ}
    (hr : r ≤ r') (hQ : Q ≤ Q') (hL : L ≤ L') (hN : N ≤ N') (hs : s ≤ s') :
    budget r Q L N s ≤ budget r' Q' L' N' s' := by
  unfold budget SemiprimeSourceCountPowers.width
    SemiprimeSourceWordIdPredicateBounds.terminalBudget
    SemiprimeSourceWordIdPredicateBounds.programBudget
    SemiprimeSourceWordIdPredicateBounds.terminalStepBudget
    SemiprimeSourceWordIdPredicateBounds.bankReadBudget
    SemiprimeSourceWordIdPredicateBounds.colourReadBudget
    SemiprimeSourceWordIdEnvironmentBounds.readBudget
    SemiprimeSourceWordIdEnvironmentBounds.scanStep
    SemiprimeSourceWordIdEnvironmentBounds.keyBudget
    SemiprimeSourceWordIdEnvironmentBounds.idCopyBudget
    SemiprimeSourceWordIdEnvironmentBounds.eqBudget
    SemiprimeSourceScorePredicateBitsBounds.copyBudget
    SemiprimeSourceScorePredicateBitsBounds.equalityBudget
  gcongr

/-- Fixed monomial growth counts materialized L explicitly, never a unary L^4 loop. -/
theorem budget_monomial : ∃ C k : ℕ,∀ S,budget S S S S S ≤ C*(S+1)^k := by
  change Bound (fun S => budget S S S S S)
  simp only [budget,SemiprimeSourceCountPowers.width,
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

end RiemannGaussian.SemiprimeSourceHeadCountBitsBounds
