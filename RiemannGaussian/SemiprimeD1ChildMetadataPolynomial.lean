/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildOriginalClock
import RiemannGaussian.SemiprimeD1PhysicalSourcePolynomial

/-! # Closed scalar metadata envelopes for actual child constructors
Original source work is never substituted by a fake-context source. Only the
literal numeric metadata polynomials and acquired replay budget are bounded.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1ChildMetadataPolynomial
open SemiprimeD1PhysicalSourcePolynomial
open SemiprimeSourceHistogramScalesBounds (clog_cap)
open SemiprimeReportPolynomialGrowth

/-- Original graph scans retain all replay-dependent payload widths. -/
def graphEnvelope (S : ℕ) : ℕ :=
  SemiprimeSourceHistogramPortKeys.encodeBudget S+
    S*(SemiprimeD1ChildMetadataPrimitives.oneBudget S S (3*(2*S+1)+1)
      (S*(2*(S+1)+1)) (S+1)+8)+2+
    S*((2*S)*(6*replayEnvelope S+9)+6)+2+2*S+12

/-- Original activation scans use actual acquired IDs and row widths. -/
def activationEnvelope (S : ℕ) : ℕ :=
  SemiprimeSourceHistogramPortKeys.encodeBudget S+(2*S)*(3*(S+1)+7)+2+
    (2*S)*(SemiprimeD1ChildActivationBudget.oneBudget S S (S+1)
      (S*(2*(S+1)+1)) (S+1)+4)+2+2*S+8

/-- Whole port pullback retains the acquired replay report at every use. -/
def pullbackEnvelope (S : ℕ) : ℕ :=
  graphEnvelope S+activationEnvelope S+S*(3*replayEnvelope S+7)+2+
    (2*S^2)*(S*(6*replayEnvelope S+10)+7)+2+50*S+30

/-- Packet header/mode-mask loop with 2^a capped independently by S. -/
def maskEnvelope (S : ℕ) : ℕ :=
  SemiprimeSourceHistogramPortKeys.encodeBudget S+
    (10*S+10+S*(10*(S*S)+10))+
    (S*S*S)*(SemiprimeD1PacketModeMaskBudget.itemBudget S (replayEnvelope S) S S+4)+9

/-- Actual original packet prepare overhead, excluding its explicit source.work. -/
def prepareEnvelope (S : ℕ) : ℕ := maskEnvelope S+graphEnvelope S+3*S+10

/-- Every literal original graph overhead obeys a fixed scalar polynomial. -/
theorem graph_bound (n F r a M S : ℕ) (hr0 : 0 < r)
    (hn : n ≤ S) (hF : F ≤ S) (hr : r ≤ S) (ha : a ≤ S)
    (hM : M ≤ S) (hL : r^a ≤ S) :
    SemiprimeD1OriginalChildGraphBudget.overhead n F r a M ≤ graphEnvelope S := by
  have hb:=replay_budget n F r a M S hr0 hn hF hr ha hM hL
  have hw:=feature_width n F (r^a) S hn hF hL
  have hc:=clog_cap r S hr
  simp only [SemiprimeD1OriginalChildGraphBudget.overhead,
    SemiprimeD1OriginalChildGraphBudget.keyCap,SemiprimeD1OriginalChildGraphBudget.rowCap,
    SemiprimeD1OriginalChildGraphBudget.replayCap,SemiprimeSourceHistogramPortKeys.keyWidth,
    SemiprimeD1ChildMetadataPrimitives.oneBudget,SemiprimeD1ChildMetadataPrimitives.colourBudget,
    SemiprimeSourceHistogramPortKeys.encodeBudget,graphEnvelope]
  gcongr

/-- Every original activation metadata scan has a closed dimension bound. -/
theorem activation_bound (n F r a S : ℕ)
    (hn : n ≤ S) (hF : F ≤ S) (hr : r ≤ S) (ha : a ≤ S) (hL : r^a ≤ S) :
    SemiprimeD1ChildActivationBudget.overhead n F r a ≤ activationEnvelope S := by
  have hc:=clog_cap r S hr
  have hl:=clog_cap (r^a) S hL
  have hnf : n+F ≤ 2*S := by omega
  simp only [SemiprimeD1ChildActivationBudget.overhead,SemiprimeD1ChildActivationBudget.oneBudget,
    SemiprimeD1OriginalChildGraphBudget.rowCap,SemiprimeSourceHistogramPortKeys.keyWidth,
    SemiprimeD1ChildMetadataPrimitives.colourBudget,
    SemiprimeSourceHistogramPortKeys.encodeBudget,activationEnvelope]
  gcongr

/-- Literal pullback overhead remains polynomial after original replay acquisition. -/
theorem pullback_bound (n F r a M S : ℕ) (hr0 : 0 < r)
    (hn : n ≤ S) (hF : F ≤ S) (hr : r ≤ S) (ha : a ≤ S)
    (hM : M ≤ S) (hL : r^a ≤ S) :
    SemiprimeD1ChildPullbackBudget.overhead n F r a M ≤ pullbackEnvelope S := by
  have hg:=graph_bound n F r a M S hr0 hn hF hr ha hM hL
  have ha':=activation_bound n F r a S hn hF hr ha hL
  have hb:=replay_budget n F r a M S hr0 hn hF hr ha hM hL
  simp only [SemiprimeD1ChildPullbackBudget.overhead,
    SemiprimeD1OriginalChildGraphBudget.replayCap,pullbackEnvelope]
  gcongr

/-- Original cached packet masks have no unknown byte/report advice. -/
theorem mask_bound (n F r a M P S : ℕ) (hr0 : 0 < r)
    (hn : n ≤ S) (hF : F ≤ S) (hr : r ≤ S) (ha : a ≤ S)
    (hM : M ≤ S) (hP : P ≤ S) (hL : r^a ≤ S) (hN : 2^a ≤ S) :
    SemiprimeD1PacketModeMaskBudget.overhead r a M P
      (SemiprimeD1OriginalChildGraphBudget.replayCap n F r a M) ≤ maskEnvelope S := by
  have hb:=replay_budget n F r a M S hr0 hn hF hr ha hM hL
  simp only [SemiprimeD1PacketModeMaskBudget.overhead,
    SemiprimeD1PacketModeMaskBudget.itemBudget,SemiprimeD1ModeRoutingBudget.budget,
    SemiprimeD1OriginalChildGraphBudget.replayCap,
    SemiprimeSourceHistogramPortKeys.encodeBudget,maskEnvelope]
  gcongr

/-- Original prepare overhead is closed in actual graph/alphabet dimensions. -/
theorem prepare_bound (n F r a M P S : ℕ) (hr0 : 0 < r)
    (hn : n ≤ S) (hF : F ≤ S) (hr : r ≤ S) (ha : a ≤ S)
    (hM : M ≤ S) (hP : P ≤ S) (hL : r^a ≤ S) (hN : 2^a ≤ S) :
    SemiprimeD1PacketModeMaskBudget.prepareOverhead n F r a M P ≤ prepareEnvelope S := by
  have hm:=mask_bound n F r a M P S hr0 hn hF hr ha hM hP hL hN
  have hg:=graph_bound n F r a M S hr0 hn hF hr ha hM hL
  simp only [SemiprimeD1PacketModeMaskBudget.prepareOverhead,prepareEnvelope]
  gcongr



/-- One polynomial cap for all acquired original metadata suppliers. -/
def envelope (S : ℕ) : ℕ := S+1+replayEnvelope S+graphEnvelope S+
  activationEnvelope S+pullbackEnvelope S+prepareEnvelope S+
  SemiprimeD1ChildOrderBudget.overhead S (2*S^2)

open Lean Elab Tactic
/-- Fixed arithmetic closure retaining the previously derived replay polynomial. -/
syntax "metadataBoundArithmetic" : tactic
elab_rules : tactic
  | `(tactic| metadataBoundArithmetic) => do
    let target ← Lean.instantiateMVars (← getMainTarget)
    let f ← Lean.instantiateMVars (target.getArg! 0)
    let body := (Lean.mkApp (f.liftLooseBVars 0 1) (Lean.mkBVar 0)).headBeta
    if !body.hasLooseBVars then
      evalTactic (← `(tactic| exact constant_bound _))
    else if body matches .bvar 0 then
      evalTactic (← `(tactic| exact identity_bound))
    else
      let name := body.getAppFn.constName?
      if name == some ``SemiprimeD1PhysicalSourcePolynomial.replayEnvelope then
        evalTactic (← `(tactic| exact replayEnvelope_monomial))
      else if name == some ``HAdd.hAdd || name == some ``Nat.add then
        evalTactic (← `(tactic| apply add_bound <;> metadataBoundArithmetic))
      else if name == some ``HMul.hMul || name == some ``Nat.mul then
        evalTactic (← `(tactic| apply mul_bound <;> metadataBoundArithmetic))
      else if name == some ``HPow.hPow || name == some ``Pow.pow || name == some ``Nat.pow then
        evalTactic (← `(tactic| apply pow_bound <;> metadataBoundArithmetic))
      else
        throwError "unsupported arithmetic node: {body}"

/-- Fixed coefficients and exponents bound all literal original metadata work. -/
theorem envelope_monomial : Bound envelope := by
  change Bound (fun S => envelope S)
  simp only [envelope,graphEnvelope,activationEnvelope,pullbackEnvelope,prepareEnvelope,maskEnvelope,
    SemiprimeD1ChildOrderBudget.overhead,SemiprimeD1ChildMetadataPrimitives.oneBudget,
    SemiprimeD1ChildActivationBudget.oneBudget,SemiprimeD1ChildMetadataPrimitives.colourBudget,
    SemiprimeD1PacketModeMaskBudget.itemBudget,SemiprimeD1ModeRoutingBudget.budget,
    SemiprimeSourceHistogramPortKeys.encodeBudget]
  metadataBoundArithmetic

/-- Every component cap is included literally in the full envelope. -/
theorem components (S : ℕ) :
    S ≤ envelope S ∧ replayEnvelope S ≤ envelope S ∧ graphEnvelope S ≤ envelope S ∧
    pullbackEnvelope S ≤ envelope S ∧ prepareEnvelope S ≤ envelope S ∧
    SemiprimeD1ChildOrderBudget.overhead S (2*S^2) ≤ envelope S := by
  unfold envelope
  omega

end RiemannGaussian.SemiprimeD1ChildMetadataPolynomial
