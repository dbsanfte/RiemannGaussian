/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceIncidenceCountBits

/-! # Original-input physical incidence classifier budgets
Only original finite metadata caps and acquired-bank membership are premises.
No candidate completions, supplied truth, Fits or callback clock is used.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceIncidenceCountBitsBounds
open SemiprimeMaterializedWords SemiprimeSourceWordIdEnvironment
open SemiprimeSourceWordIdEnvironmentBounds SemiprimeSourceIncidenceCountBits
open SemiprimeReportPolynomialGrowth

/-- Both literal membership scans, two actual key producers, two physical
environment reads and one physical candidate-ID comparison. -/
def edgeBudget (L N s : ℕ) : ℕ :=
  4*N+2+2*keyBudget N+2*readBudget (N+1) N (2*L) s+eqBudget (2*L+1)+9

/-- Two edge reports and the actually selected cached power-word copy.
The cache's once-only power acquisition is a separate caller report. -/
def countBudget (r Q L N s : ℕ) : ℕ :=
  2*edgeBudget L N s+4*SemiprimeSourceCountPowers.width r Q+11

/-- Original acquired IDs bound all cached environment payloads. -/
theorem acquired_payload (r Q : ℕ) (env : Env)
    (he : ValidIds (SemiprimeSourceWordBank.acquire r Q).ids env) :
    PayloadBound (2*r^Q) env :=
  valid_payload _ env _ he (SemiprimeSourceWordBankAcquisitionBudget.acquire_ids_bounded r Q)

/-- The classifier pays its actual fixed-anchor reads and physical comparison,
or its genuinely shorter loop/free branch. -/
theorem edge_work (r Q : ℕ) (env : Env) (a c : ℕ) (remaining : List ℕ) (N s : ℕ)
    (he : ValidIds (SemiprimeSourceWordBank.acquire r Q).ids env)
    (hf : env.fixedIDs.length ≤ N) (ho : env.overrides.length ≤ s)
    (hk : KeysBound (N+1) env) (hrem : remaining.length ≤ N) (ha : a ≤ N) (hc : c ≤ N) :
    (edge env a c remaining).clock ≤ edgeBudget (r^Q) N s := by
  have hma := (memberRun_work a remaining).trans
    (show 2*remaining.length+1 ≤ 2*N+1 by omega)
  have hmc := (memberRun_work c remaining).trans
    (show 2*remaining.length+1 ≤ 2*N+1 by omega)
  have hka := (acquireKey_work a).trans
    (show 20*(a+1)^2+2 ≤ keyBudget N by unfold keyBudget;gcongr)
  have hkc := (acquireKey_work c).trans
    (show 20*(c+1)^2+2 ≤ keyBudget N by unfold keyBudget;gcongr)
  have hp := acquired_payload r Q env he
  have hra := read_work env (acquireKey a).value (N+1) N (2*r^Q) s hp hk hf ho
    ((acquireKey_length a).trans (by omega))
  have hrc := read_work env (acquireKey c).value (N+1) N (2*r^Q) s hp hk hf ho
    ((acquireKey_length c).trans (by omega))
  have hva := SemiprimeSourceWordBankAcquisitionBudget.acquire_ids_bounded r Q
    (read env (acquireKey a).value).value (read_valid _ env _ he)
  have hvc := SemiprimeSourceWordBankAcquisitionBudget.acquire_ids_bounded r Q
    (read env (acquireKey c).value).value (read_valid _ env _ he)
  have hsame := equalID_work (read env (acquireKey a).value).value
    (read env (acquireKey c).value).value (2*r^Q+1) (by omega)
    (hva.trans (by omega)) (hvc.trans (by omega))
  unfold edge edgeBudget
  dsimp only
  split_ifs <;> dsimp only <;> omega

/-- Generic cached-powers form: only the literal input payload lengths are used,
not decoded count magnitude or advised intermediate fit. -/
theorem count_work_cached (r Q : ℕ) (env : Env) (powers : SemiprimeSourceCountPowers.Powers)
    (a b c d : ℕ) (remaining : List ℕ) (N s : ℕ)
    (he : ValidIds (SemiprimeSourceWordBank.acquire r Q).ids env)
    (hf : env.fixedIDs.length ≤ N) (ho : env.overrides.length ≤ s)
    (hk : KeysBound (N+1) env) (hrem : remaining.length ≤ N)
    (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) (hd : d ≤ N)
    (hsq : powers.square.length ≤ SemiprimeSourceCountPowers.width r Q)
    (hcu : powers.cube.length ≤ SemiprimeSourceCountPowers.width r Q)
    (hfo : powers.fourth.length ≤ SemiprimeSourceCountPowers.width r Q) :
    (count env powers a b c d remaining).clock ≤ countBudget r Q (r^Q) N s := by
  have hfirst := edge_work r Q env a c remaining N s he hf ho hk hrem ha hc
  have hsecond := edge_work r Q env b d remaining N s he hf ho hk hrem hb hd
  have hsquare := (SemiprimeSourceChoiceBits.copyID_work powers.square).trans
    (show 4*powers.square.length+2 ≤ 4*SemiprimeSourceCountPowers.width r Q+2 by omega)
  have hcube := (SemiprimeSourceChoiceBits.copyID_work powers.cube).trans
    (show 4*powers.cube.length+2 ≤ 4*SemiprimeSourceCountPowers.width r Q+2 by omega)
  have hfourth := (SemiprimeSourceChoiceBits.copyID_work powers.fourth).trans
    (show 4*powers.fourth.length+2 ≤ 4*SemiprimeSourceCountPowers.width r Q+2 by omega)
  unfold count countBudget
  dsimp only
  split_ifs <;> dsimp only <;> omega

/-- Acquiring the cache internally supplies every length premise of the actual
count call. The acquired cache's report must be retained once by its caller. -/
theorem count_work (r Q : ℕ) (env : Env) (a b c d : ℕ) (remaining : List ℕ) (N s : ℕ)
    (he : ValidIds (SemiprimeSourceWordBank.acquire r Q).ids env)
    (hf : env.fixedIDs.length ≤ N) (ho : env.overrides.length ≤ s)
    (hk : KeysBound (N+1) env) (hrem : remaining.length ≤ N)
    (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) (hd : d ≤ N) :
    (count env (SemiprimeSourceCountPowers.acquire r Q) a b c d remaining).clock ≤
      countBudget r Q (r^Q) N s := by
  have hp := SemiprimeSourceCountPowers.acquire_length r Q
  exact count_work_cached r Q env _ a b c d remaining N s he hf ho hk hrem ha hb hc hd
    hp.1 hp.2.1 hp.2.2.1

/-- Edge budgets are monotone in original finite resource caps. -/
theorem edgeBudget_mono {L N s L' N' s' : ℕ} (hL : L ≤ L') (hN : N ≤ N') (hs : s ≤ s') :
    edgeBudget L N s ≤ edgeBudget L' N' s' := by
  simp only [edgeBudget,keyBudget,readBudget,scanStep,idCopyBudget,eqBudget]
  gcongr

/-- Count budgets are monotone without completion enumeration factors. -/
theorem countBudget_mono {r Q L N s r' Q' L' N' s' : ℕ}
    (hr : r ≤ r') (hQ : Q ≤ Q') (hL : L ≤ L') (hN : N ≤ N') (hs : s ≤ s') :
    countBudget r Q L N s ≤ countBudget r' Q' L' N' s' := by
  unfold countBudget
  have he := edgeBudget_mono hL hN hs
  have hw : SemiprimeSourceCountPowers.width r Q ≤ SemiprimeSourceCountPowers.width r' Q' := by
    unfold SemiprimeSourceCountPowers.width
    gcongr
  omega

/-- One fixed polynomial controls the entire original-dimensional family.
L appears only through actual candidate-ID payload widths/read scans. -/
theorem countBudget_monomial : ∃ C k : ℕ,∀ r Q L N s S,
    r ≤ S → Q ≤ S → L ≤ S → N ≤ S → s ≤ S → countBudget r Q L N s ≤ C*(S+1)^k := by
  have hp : Bound (fun S => countBudget S S S S S) := by
    simp only [countBudget,edgeBudget,keyBudget,readBudget,scanStep,idCopyBudget,eqBudget,
      SemiprimeSourceCountPowers.width]
    boundArithmetic
  obtain ⟨C,k,h⟩ := hp
  exact ⟨C,k,fun r Q L N s S hr hQ hL hN hs =>
    (countBudget_mono hr hQ hL hN hs).trans (h S)⟩

end RiemannGaussian.SemiprimeSourceIncidenceCountBitsBounds
