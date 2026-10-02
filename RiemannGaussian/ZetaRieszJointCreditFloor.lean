/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFinitePhasePayment
import RiemannGaussian.ZetaRieszComplexProjection

/-!
# Retain the whole-carrier phase credit in the paid signed-energy floor

Prove the missing COST comparison before adding the global credit to the
signed-energy floor. All geometric pair payments use the same original
adverse set. The credit is retained once, without a size assumption.
The independent remaining cost-minus-credit bound is still open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszJointCreditFloor
open ZetaRieszCofactorPhaseEnergy ZetaRieszDiagonalPayment
open ZetaRieszSharedFactorPayment ZetaRieszNearLabelPayment
open ZetaRieszPhaseOrbitPayment ZetaRieszJointPrimeEnergy
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszJointAllocation
open ZetaRieszWideOwnerAudit ZetaRieszCutoffPeriodFloor ZetaRieszPostHingeEnergy
open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint ZetaRieszParityPacket

private theorem adverse_energy_eq (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    (∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
      correlation S w k^2/(k : ℝ)) =
        (∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
          (∑ n ∈ S,(w n*sharp k n)^2)/(k : ℝ))+adverseCrossEnergy X S w f := by
  unfold adverseCrossEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← add_div]
  congr 1
  rw [correlation,pow_two,Finset.sum_mul_sum]
  simp only [← Finset.sum_add_distrib,pow_two]
  apply Finset.sum_congr rfl
  intro n hn
  exact (Finset.sum_erase_add S
    (fun m => (w n*sharp k n)*(w m*sharp k m)) hn).symm.trans (by ring_nf)

private theorem adverse_price_split (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    ZetaRieszRejoinedPhaseFloor.negativeCost X S w f ≤
      sqrt (max (adverseCrossEnergy X S w f) 0*adverseProfileEnergy X S w f)+
        sqrt (diagonalEnergy X S w f*profileEnergy X f) := by
  let K := ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f
  let D := ∑ k ∈ K,(∑ n ∈ S,(w n*sharp k n)^2)/(k : ℝ)
  let E := ∑ k ∈ K,correlation S w k^2/(k : ℝ)
  have hK : K ⊆ activeCutoffs X f := Finset.filter_subset _ _
  have he : E=D+adverseCrossEnergy X S w f := adverse_energy_eq X S w f
  have hDle : D ≤ diagonalEnergy X S w f :=
    Finset.sum_le_sum_of_subset_of_nonneg hK (fun _ _ _ =>
      div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _))
  have hP' : 0 ≤ adverseProfileEnergy X S w f :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hPle : adverseProfileEnergy X S w f ≤ profileEnergy X f :=
    Finset.sum_le_sum_of_subset_of_nonneg hK (fun _ _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hD : 0 ≤ diagonalEnergy X S w f :=
    Finset.sum_nonneg (fun _ _ => div_nonneg
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _))
  have hP : 0 ≤ profileEnergy X f :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hE : 0 ≤ E :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hEP := mul_nonneg hE hP'
  have hDP := mul_nonneg hD hP
  have hCP := mul_nonneg (le_max_right (adverseCrossEnergy X S w f) 0) hP'
  have hbound : E*adverseProfileEnergy X S w f ≤
      max (adverseCrossEnergy X S w f) 0*adverseProfileEnergy X S w f+
        diagonalEnergy X S w f*profileEnergy X f := by
    have h := mul_le_mul_of_nonneg_right
      (le_max_left (adverseCrossEnergy X S w f) 0) hP'
    have hd := mul_le_mul hDle hPle hP' hD
    rw [he]
    nlinarith only [h,hd]
  change sqrt (E*adverseProfileEnergy X S w f) ≤ _
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt hEP]
  nlinarith only [hbound,sq_sqrt hDP,sq_sqrt hCP,
    mul_nonneg (sqrt_nonneg (max (adverseCrossEnergy X S w f) 0*adverseProfileEnergy X S w f))
      (sqrt_nonneg (diagonalEnergy X S w f*profileEnergy X f))]

/-- All independent pair prices exactly once; there is no carrier transfer in this cost. -/
def paidPrice (y : ℝ) (N : ℕ) : ℝ :=
  ZetaRieszDirectPhaseFloor.paidPrice y N+
    ZetaRieszSmallGcdPayment.sharedPrice 1 N+
      ZetaRieszWidePhasePayment.widePrice 1 y N+
        ZetaRieszFinitePhasePayment.price 1 y N

/-- No credit or unpaid signed energy enters the vanishing pair price. -/
theorem tendsto_paidPrice (y : ℝ) : Tendsto (paidPrice y) atTop (𝓝 0) := by
  change Tendsto (fun N => ZetaRieszDirectPhaseFloor.paidPrice y N+
    ZetaRieszSmallGcdPayment.sharedPrice 1 N+
      ZetaRieszWidePhasePayment.widePrice 1 y N+
        ZetaRieszFinitePhasePayment.price 1 y N) atTop (𝓝 0)
  simpa only [add_zero] using
    (((ZetaRieszDirectPhaseFloor.tendsto_paidPrice y).add
      (ZetaRieszSmallGcdPayment.tendsto_sharedPrice 1)).add
        (ZetaRieszWidePhasePayment.tendsto_widePrice 1 y)).add
          (ZetaRieszFinitePhasePayment.tendsto_price 1 y)

/-- The actual original Cauchy COST, rather than just its carrier floor,
is bounded by the current signed remainder and the paid differences.
This is the necessary comparison for retaining the global phase credit. -/
theorem core_negativeCost_bound {u y : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (hy : 3 ≤ |y|) {N : ℕ} (hN : 65536 ≤ N) (K : ℕ) :
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let S := coreBand u N K
    let X := max 1 (S.sup id)
    let f := correctedProfile X L 1 0
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    ZetaRieszRejoinedPhaseFloor.negativeCost X (S.filter Squarefree) w f ≤
      sqrt (max (ZetaRieszFinitePhasePayment.remainingEnergy X N (S.filter Squarefree) w f y) 0*
        ((129/200 : ℝ)*N))+paidPrice y N := by
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N K
  let X := max 1 (S.sup id)
  let f := correctedProfile X L 1 0
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  have hX : 0 < X := by dsimp [X]; omega
  have hwin : S ⊆ literalWindow N := ZetaRieszDirectPhaseFloor.core_subset_window u N K
  have hswin := (Finset.filter_subset Squarefree S).trans hwin
  have hSX : S.filter Squarefree ⊆ Finset.Icc 1 X := by
    intro n hn
    obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hs.ne_zero,
      (Finset.le_sup (f := id) hn).trans (le_max_right _ _)⟩
  have hlog : log X ≤ 3*((N : ℝ)+1) := window_sup_log S hwin
  have hL : 1 ≤ L := by
    have hh := length_ge_rational hN hu hU
    have hn : (65536 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [L]
    linarith
  have hq : ∀ n ∈ S.filter Squarefree, |(1 : ℝ)| ≤ 1 := by norm_num
  have hsf : ∀ n ∈ S.filter Squarefree,Squarefree n := fun _ hn => (Finset.mem_filter.mp hn).2
  have hp0 : 0 ≤ adverseProfileEnergy X (S.filter Squarefree) w f :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hcap := core_profile_bound hN hu hU K S w (Finset.Subset.refl _)
  have hpbig : adverseProfileEnergy X (S.filter Squarefree) w f ≤
      4*((N : ℝ)+1)^2 := by
    apply hcap.trans
    nlinarith only [Nat.cast_nonneg (α := ℝ) N]
  have hpsmall : adverseProfileEnergy X (S.filter Squarefree) w f ≤
      4*((N : ℝ)+1) := by
    apply hcap.trans
    nlinarith only [Nat.cast_nonneg (α := ℝ) N]
  have hcost := adverse_price_split X (S.filter Squarefree) w f
  have hs₁ := shared_crossCost_split X N (S.filter Squarefree) w f
  have hs₂ := near_crossCost_split X N (S.filter Squarefree) w f
  have hs₃ := orbit_crossCost_split X N (S.filter Squarefree) w f y hp0
  have hs₄ := ZetaRieszSmallGcdPayment.cost_split X N (S.filter Squarefree) w f y hp0
  have hs₅ := ZetaRieszWidePhasePayment.cost_split X N (S.filter Squarefree) w f y hp0
  have hs₆ := ZetaRieszFinitePhasePayment.cost_split X N (S.filter Squarefree) w f y hp0
  have hd := weighted_diagonal_price X N A (S.filter Squarefree) (fun _ => 1) y
    (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hswin hlog hq
  have he₁ := weighted_shared_price X N A (S.filter Squarefree) (fun _ => 1) y
    (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hX hSX hsf hlog hq
  have he₂ := weighted_near_price X N A (S.filter Squarefree) (fun _ => 1) y
    (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hX hSX hlog hq
  have he₃ := weighted_orbit_price X N A (S.filter Squarefree) f (fun _ => 1) y
    hy hswin (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hX hSX hlog hq hp0 hpbig
  have he₄ := ZetaRieszSmallGcdPayment.weighted_maskedShared_price
    X N A (S.filter Squarefree) f (fun _ => 1) (ZetaRieszAntiphaseCredit.retainedPair N y) y
    (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hX hSX hsf hlog hq hp0 hpsmall
  have he₅ := ZetaRieszWidePhasePayment.weighted_maskedOrbit_price
    X N A (S.filter Squarefree) f (fun _ => 1) (ZetaRieszWidePhasePayment.remainingPair N y) y
    hy hswin (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hX hSX hlog hq hp0 hpsmall
  have he₆ := ZetaRieszFinitePhasePayment.weighted_maskedEnergy_price
    X N A (S.filter Squarefree) f (fun _ => 1) (ZetaRieszFinitePhasePayment.remainingPair N y) y
    hy hswin (by norm_num : (0 : ℝ) ≤ 1) hL hu.le hU hX hSX hlog hq hp0 hpsmall
  have hc : sqrt (max (ZetaRieszFinitePhasePayment.remainingEnergy X N
      (S.filter Squarefree) w f y) 0*adverseProfileEnergy X (S.filter Squarefree) w f) ≤
      sqrt (max (ZetaRieszFinitePhasePayment.remainingEnergy X N
        (S.filter Squarefree) w f y) 0*((129/200 : ℝ)*N)) :=
    sqrt_le_sqrt (mul_le_mul_of_nonneg_left hcap (le_max_right _ _))
  simp only [mul_one] at hd he₁ he₂ he₃ he₄ he₅ he₆
  dsimp only at hcost hs₁ hs₂ hs₃ hs₄ hs₅ hs₆ hd he₁ he₂ he₃ he₄ he₅ he₆ hc ⊢
  unfold paidPrice ZetaRieszDirectPhaseFloor.paidPrice
  linarith only [hcost,hs₁,hs₂,hs₃,hs₄,hs₅,hs₆,hd,he₁,he₂,he₃,he₄,he₅,he₆,hc]

/-- Literal imaginary/core-transfer error plus independent pair prices.
No native credit, source resonance or remaining energy is norm-paid. -/
def joinedError (u y : ℝ) (j : ℕ) : ℝ :=
  ZetaRieszComplexProjection.nativeError u y j+paidPrice y (dyadicMomentOrder j)

/-- The same source-normalized ORIGINAL carrier now keeps the whole
phase credit in the current signed-energy floor. Its numerical credit
size and cost-minus-credit budget are not assumed or proved here. -/
theorem eventually_joined_floor_with_credit {u y : ℝ} (hu : 0 < u)
    (hU : u ≤ radiusCeiling) (hy : 54 ≤ y) :
    ∀ᶠ j : ℕ in atTop,
      let N := dyadicMomentOrder j
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
      let X := max 1 (S.sup id)
      let f := correctedProfile X L 1 0
      let w := fun n => u^(N+1)*primeWeight A L y N n 1;
      ZetaRieszComplexProjection.nativeCredit u y j-
        sqrt (max (ZetaRieszFinitePhasePayment.remainingEnergy X N (S.filter Squarefree) w f y) 0*
          ((129/200 : ℝ)*N))-joinedError u y j ≤
        ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  filter_upwards [tendsto_dyadicMomentOrder.eventually
    (eventually_ge_atTop (65536 : ℕ))] with j hN
  have hf := ZetaRieszComplexProjection.native_floor u y j
  have hcredit := ZetaRieszComplexProjection.nativeCost_add_credit_le_original u y j
  have hcost := core_negativeCost_bound hu hU
    (by linarith only [hy,le_abs_self y] : 3 ≤ |y|) hN
    (ZetaRieszNearCriticalCountPayment.countCeiling j)
  dsimp only at hcredit hcost ⊢
  unfold joinedError
  linarith only [hf,hcredit,hcost]

/-- Under the existing exposed source, the WHOLE imaginary error
vanishes at every multiplicity. No adverse-subset null is inferred. -/
theorem tendsto_joinedError (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ radiusCeiling) :
    Tendsto (joinedError (3/2-rho.1.re) rho.1.im) atTop (𝓝 0) := by
  have he := ZetaRieszComplexProjection.tendsto_nativeError rho hrho hexposed hU
  have hp := (tendsto_paidPrice rho.1.im).comp tendsto_dyadicMomentOrder
  change Tendsto (fun j => ZetaRieszComplexProjection.nativeError
    (3/2-rho.1.re) rho.1.im j+paidPrice rho.1.im (dyadicMomentOrder j)) atTop (𝓝 0)
  simpa only [Function.comp_def,add_zero] using he.add hp

/-- The explicit remaining independent target joins the signed energy
cost and the ACTUAL global credit. Its cofinal bound would close the
simple exposed source. Neither term is assumed small separately. -/
theorem false_of_cofinal_cost_sub_credit (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ radiusCeiling) (hy : 54 ≤ rho.1.im)
    (hsimple : analyticZetaZeroMultiplicity rho=1)
    (hcost : ∃ᶠ j : ℕ in atTop,
      let u := 3/2-rho.1.re
      let N := dyadicMomentOrder j
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
      let X := max 1 (S.sup id)
      let f := correctedProfile X L 1 0
      let w := fun n => u^(N+1)*primeWeight A L rho.1.im N n 1;
      sqrt (max (ZetaRieszFinitePhasePayment.remainingEnergy X N (S.filter Squarefree) w f rho.1.im) 0*
        ((129/200 : ℝ)*N))-ZetaRieszComplexProjection.nativeCredit u rho.1.im j ≤ 399/5000) : False := by
  have hu : 0 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (joinedError (3/2-rho.1.re) rho.1.im) (tendsto_joinedError rho hrho hexposed hU)
  have hf := eventually_joined_floor_with_credit hu hU hy
  exact (hcost.and_eventually hf).mono fun j hj => by
    obtain ⟨hc,hf⟩ := hj
    dsimp only at hc hf ⊢
    linarith only [hc,hf]

end RiemannGaussian.ZetaRieszJointCreditFloor
