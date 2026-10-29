/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalSourceBudget
import RiemannGaussian.SemiprimeSourceHistogramResources

/-! # Fixed polynomial overhead of the actual original sparse source supplier
The actual output menu factor remains explicit; no once-per-parent sharing of
repeated child/header source reports is asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1PhysicalSourcePolynomial
open SemiprimeSourceHistogramResources
open SemiprimeSourceHistogramScalesBounds (clog_cap)
open SemiprimeReportPolynomialGrowth

/-- Pure polynomial overhead beyond the already proved original selector envelope. -/
def replayTail (S : ℕ) : ℕ :=
  prefixPolynomial S+featurePolynomial S+2*S+10+
  S*(3*(2*S+1)+2)*(88*(S+2)+7)+1+40*(S+(S+1)+3)+6+2+
  S*SemiprimeD1PacketReplayBudget.stepBudget S (3*(2*S+1)+1)
    (S*(2*(S+1)+1)) (S+2)

/-- Full sparse selector/padding/replay fixed polynomial envelope. -/
def replayEnvelope (S : ℕ) : ℕ := envelope S+replayTail S

/-- Actual source-key widths derive from original graph/alphabet dimensions. -/
theorem feature_width (n F L S : ℕ) (hn : n ≤ S) (hF : F ≤ S) (hL : L ≤ S) :
    SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) L ≤ 2*S+1 := by
  have hN:=clog_cap (n+F) (2*S) (by omega)
  have hLlog:=clog_cap L S hL
  exact max_le hN (hLlog.trans (by omega))

/-- All original sparse source replay/padding/index reports have a fixed
polynomial bound in actual input dimension caps, not a supplied report answer. -/
theorem replay_budget (n F r a M S : ℕ) (hr0 : 0 < r)
    (hn : n ≤ S) (hF : F ≤ S) (hr : r ≤ S) (ha : a ≤ S)
    (hM : M ≤ S) (hL : r^a ≤ S) :
    SemiprimeD1PacketReplayBudget.budget n F r a M ≤ replayEnvelope S := by
  have hs:=budget_polynomial n F r a 0 M S hr0 hn hF hr ha (by omega) hM hL
  have hp:=prefixBudget_polynomial (r^a) (n+F) S hL (by omega)
  have hf:=featureBudget_polynomial n F M (r^a) S hn hF hM hL
  have hw:=feature_width n F (r^a) S hn hF hL
  have hc:=clog_cap M S hM
  have hclock:=clog_cap (M+1) (S+1) (by omega)
  have hstep:=SemiprimeD1PacketReplayBudget.stepBudget_mono ha
    (show 3*SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) (r^a)+1 ≤ 3*(2*S+1)+1 by omega)
    (show a*(2*(r+1)+1) ≤ S*(2*(S+1)+1) by gcongr)
    (show SemiprimeSourceHistogramTrieBounds.clockWidth M ≤ S+2 from hclock)
  have hm:=Nat.mul_le_mul hM hstep
  have hpad : M*(3*SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) (r^a)+2)*
      (88*(Nat.clog 2 (M+1)+1)+7) ≤ S*(3*(2*S+1)+2)*(88*(S+2)+7) := by
    exact Nat.mul_le_mul (Nat.mul_le_mul hM (by omega)) (by omega)
  have htail : 40*(a+Nat.clog 2 (M+1)+3) ≤ 40*(S+(S+1)+3) := by gcongr
  unfold SemiprimeD1PacketReplayBudget.budget SemiprimeD1PacketPadding.budget
    SemiprimeD1IncidenceAcquisitionBounds.budget replayEnvelope replayTail
  omega

/-- Original replay polynomial has fixed monomial witnesses before all resources. -/
theorem replayEnvelope_monomial : Bound replayEnvelope := by
  apply add_bound (show Bound envelope from envelope_monomial)
  unfold replayTail prefixPolynomial featurePolynomial squaresPolynomial
    SemiprimeD1PacketReplayBudget.stepBudget SemiprimeD1PacketReplayBudget.packetLength
  dsimp only
  boundArithmetic

/-- Fixed source supplier factor; the actual mode count is kept outside. -/
def sourceFactor (S : ℕ) : ℕ :=
  replayEnvelope S+SemiprimeD1WeightedCardinality.modeFactor (S*S) S+
    SemiprimeD1WeightedCardinality.modeOverhead (S*S) S+8*S+20

/-- Nonnegative actual supplier dimensions give polynomial cost per ACTUAL mode,
including the original source producer each time a caller retains it. -/
theorem source_budget (n F r a M u i p packets P modes S : ℕ)
    (hr0 : 0 < r) (hn : n ≤ S) (hF : F ≤ S) (hr : r ≤ S) (ha : a ≤ S)
    (hM : M ≤ S) (hu : u ≤ S) (hi : i ≤ S) (hp : p ≤ S)
    (hL : r^a ≤ S) (hpackets : packets ≤ S) (hP : P ≤ S) (htiles : 2^(i+1) ≤ S) :
    SemiprimeD1PhysicalSourceBudget.budget n F r a M u i p packets P modes ≤
      sourceFactor S*(modes+1) := by
  have hb:=replay_budget n F r a M S hr0 hn hF hr ha hM hL
  have hslots:=Nat.mul_le_mul hpackets htiles
  have hfactor : SemiprimeD1WeightedCardinality.modeFactor (packets*2^(i+1)) P ≤
      SemiprimeD1WeightedCardinality.modeFactor (S*S) S := by
    unfold SemiprimeD1WeightedCardinality.modeFactor
    gcongr
  have hover : SemiprimeD1WeightedCardinality.modeOverhead (packets*2^(i+1)) P ≤
      SemiprimeD1WeightedCardinality.modeOverhead (S*S) S := by
    unfold SemiprimeD1WeightedCardinality.modeOverhead
    gcongr
  have hmode:=Nat.mul_le_mul_right modes hfactor
  unfold SemiprimeD1PhysicalSourceBudget.budget sourceFactor
  nlinarith only [hb,hmode,hover,hM,hpackets,ha,hi,hu,hp]

/-- Fixed monomial growth of the actual source factor, no cost-growth premise. -/
theorem sourceFactor_monomial : Bound sourceFactor := by
  unfold sourceFactor
  apply add_bound
  · apply add_bound
    · apply add_bound
      · apply add_bound replayEnvelope_monomial
        unfold SemiprimeD1WeightedCardinality.modeFactor
        boundArithmetic
      · unfold SemiprimeD1WeightedCardinality.modeOverhead
        boundArithmetic
    · boundArithmetic
  · boundArithmetic

end RiemannGaussian.SemiprimeD1PhysicalSourcePolynomial
