/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeHeadTransport
import RiemannGaussian.ZetaRieszCosineCarrier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Signed cubic transport of the balanced main and the same prime head

Join every literal count and the entire head before pairing opposite real
arithmetic amplitudes. Keep the signed centered first phase moment; pay
only its cubic defect. Every unmatched amplitude stays explicit and signed.
The new whole price is an alternative to the old funded price, never an
additional credit. No cofinal smallness or zero hypothesis is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszJointPhaseTransport
open ZetaRieszPrimeCountFrequency ZetaRieszBalancedRadialPayment
open ZetaRieszPrimeHeadTransport (pairAmount pairInterval)

/-- Centering the phases leaves a cubic defect. The first moment stays
signed, even when it reinforces rather than cancels the unmatched sum. -/
theorem centered_cosine_defect (a b : ℝ) :
    |cos a-cos b+sin ((a+b)/2)*(a-b)|≤|a-b|^3/24 := by
  rw [cos_sub_cos]
  have he : -2*sin ((a+b)/2)*sin ((a-b)/2)+sin ((a+b)/2)*(a-b)=
      2*sin ((a+b)/2)*((a-b)/2-sin ((a-b)/2)) := by ring
  rw [he,abs_mul,abs_mul]
  have h := mul_le_mul_of_nonneg_left (abs_sub_sin_le ((a-b)/2))
    (show 0≤|(2 : ℝ)| * |sin ((a+b)/2)| by positivity)
  have hs := abs_sin_le_one ((a+b)/2)
  have hp : 0≤|(a-b)/2|^3/6 := by positivity
  have hh := mul_le_mul_of_nonneg_right hs hp
  have ha : |(a-b)/2|=|a-b|/2 := by rw [abs_div]; norm_num
  rw [ha] at h hh
  norm_num at h
  nlinarith only [h,hh]

/-- Both one-sided estimates use the same retained signed moment. -/
theorem centered_cosine_bounds (a b : ℝ) :
    -sin ((a+b)/2)*(a-b)-|a-b|^3/24≤cos a-cos b ∧
    cos a-cos b≤-sin ((a+b)/2)*(a-b)+|a-b|^3/24 := by
  have h := abs_le.mp (centered_cosine_defect a b)
  constructor <;> linarith only [h.1,h.2]

/-- The literal balanced labels and every original prime-head pair. -/
def atoms (u : ℝ) (j : ℕ) : Finset (ℕ ⊕ ℕ×ℕ) :=
  (centralLabels u j).disjSum
    ((ZetaRieszSmallTagNativeFloor.owners u (dyadicMomentOrder j)).biUnion
      (fun p => (pairInterval (dyadicMomentOrder j) p).image (fun q => (p,q))))

/-- Signed amplitude at height zero, keeping the original Riesz response
and the entire head allocation and rough-prime sieve. -/
def amplitude (u : ℝ) (j : ℕ) : ℕ ⊕ ℕ×ℕ → ℝ
  | .inl n =>
      u^(dyadicMomentOrder j+1)*
        (SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n).re*
        (exp (-(3/2 : ℝ)*log n)*log n^(dyadicMomentOrder j)/
          (dyadicMomentOrder j).factorial)
  | .inr (p,q) => -pairAmount u 0 (dyadicMomentOrder j) p q

/-- Original product phase on both the balanced labels and the head. -/
def phase (y : ℝ) : ℕ ⊕ ℕ×ℕ → ℝ
  | .inl n => y*log n
  | .inr (p,q) => y*(log p+log q)

private theorem kernel_re (N : ℕ) (y : ℝ) (n : ℕ) :
    (zetaPrimeLogKernel N (3/2+Complex.I*y) n).re=
      exp (-(3/2 : ℝ)*log n)*log n^N/N.factorial*cos (y*log n) := by
  have h := ZetaRieszCosineCarrier.re_filterKernel_one N y (n : ℝ)
  simpa only [zetaPrimeFilterKernel, ZetaRieszCosineCarrier.factorialPolynomial_one,
    zetaPrimeLogKernel, zetaPrimeFeature,neg_mul] using h

private theorem pairAmount_phase (u y : ℝ) (N p q : ℕ) :
    pairAmount u y N p q=pairAmount u 0 N p q*cos (y*(log p+log q)) := by
  unfold pairAmount
  split_ifs <;>
    simp only [ZetaRieszOwnerLatticePhase.ownerTest_nat,zero_mul,cos_zero,mul_one]
  all_goals ring

private theorem sum_head_atoms (u y : ℝ) (j : ℕ) :
    (∑ pq∈(ZetaRieszSmallTagNativeFloor.owners u (dyadicMomentOrder j)).biUnion
      (fun p => (pairInterval (dyadicMomentOrder j) p).image (fun q => (p,q))),
        pairAmount u y (dyadicMomentOrder j) pq.1 pq.2)=
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j) := by
  rw [Finset.sum_biUnion (by
    intro p hp p' hp' hpp
    apply Finset.disjoint_left.mpr
    intro pq hq hq'
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨q',_,he⟩ := Finset.mem_image.mp hq'
    exact hpp (congrArg Prod.fst he).symm)]
  rw [ZetaRieszPrimeHeadTransport.nativeHead_eq_sum_pairAmount]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_image (by
    intro q _ q' _ h
    exact (congrArg Prod.snd h : q=q'))]

/-- Exact whole all-count phase identity before any pricing. -/
theorem joint_real_eq (u y : ℝ) (j : ℕ) :
    (∑ a∈atoms u j,amplitude u j a*cos (phase y a))=
      (centralRest u y j).re-
        ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j) := by
  rw [atoms,Finset.sum_disjSum]
  have hm : (∑ n∈centralLabels u j,amplitude u j (.inl n)*cos (phase y (.inl n)))=
      (centralRest u y j).re := by
    unfold centralRest
    rw [Finset.mul_sum,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,Complex.mul_re,
      ZetaRieszCosineCarrier.coefficient_im_eq_zero,zero_mul,sub_zero,kernel_re]
    dsimp [amplitude,phase]
    ring
  rw [hm]
  simp only [amplitude,phase,neg_mul,← pairAmount_phase,Finset.sum_neg_distrib,
    sum_head_atoms,sub_eq_add_neg]

/-- Row and column mass removed by the SAME joint pairing. All residual
arithmetic amplitudes, of either sign, stay in the literal population. -/
def unmatched (u y : ℝ) (j : ℕ)
    (w : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℝ) : ℝ :=
  ∑ x∈atoms u j,
    (amplitude u j x-(∑ z∈atoms u j,w x z)+(∑ z∈atoms u j,w z x))*cos (phase y x)

/-- A pairwise phase lift may wind by any integer. Its cosine is exactly
the original phase, not a frozen or replaced prime phase. -/
def leftAngle (y : ℝ) (k : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℤ)
    (x z : ℕ ⊕ ℕ×ℕ) : ℝ := phase y x-(k x z : ℝ)*(2*Real.pi)

/-- This scalar stays SIGNED across all counts/head pairs and periods. -/
def signedMoment (u y : ℝ) (j : ℕ)
    (w : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℝ)
    (k : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℤ) : ℝ :=
  ∑ x∈atoms u j,∑ z∈atoms u j,
    w x z*sin ((leftAngle y k x z+phase y z)/2)*(leftAngle y k x z-phase y z)

/-- Only the cubic defect is norm-paid; unmatched mass is not norm-paid. -/
def cubicCost (u y : ℝ) (j : ℕ)
    (w : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℝ)
    (k : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℤ) : ℝ :=
  ∑ x∈atoms u j,∑ z∈atoms u j,w x z*|leftAngle y k x z-phase y z|^3/24

/-- Exact mass ledger, including every unmatched row and column. No
existence of prime partners or full transport cover is presumed. -/
theorem joint_transport_eq (u y : ℝ) (j : ℕ)
    (w : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℝ) :
    (centralRest u y j).re-
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)=
    unmatched u y j w+
      ∑ x∈atoms u j,∑ z∈atoms u j,w x z*(cos (phase y x)-cos (phase y z)) := by
  rw [← joint_real_eq]
  simp only [unmatched,add_mul,sub_mul,mul_sub,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,Finset.sum_mul]
  rw [Finset.sum_comm (s:=atoms u j) (t:=atoms u j) (f:=fun x z => w z x*cos (phase y x))]
  ring

/-- A literal paired phase estimate: no arithmetic floor or smallness
premise. The entire unmatched contribution keeps its original sign. -/
theorem central_joint_floor (u y : ℝ) (j : ℕ)
    (w : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℝ)
    (k : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℤ)
    (hw : ∀ x∈atoms u j,∀ z∈atoms u j,0≤w x z) :
    unmatched u y j w-signedMoment u y j w k-cubicCost u y j w k≤
      (centralRest u y j).re-
        ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j) := by
  have hh x (hx : x∈atoms u j) z (hz : z∈atoms u j) :
      -(w x z*sin ((leftAngle y k x z+phase y z)/2)*(leftAngle y k x z-phase y z))-
        w x z*|leftAngle y k x z-phase y z|^3/24≤
      w x z*(cos (phase y x)-cos (phase y z)) := by
    have h := mul_le_mul_of_nonneg_left
      (centered_cosine_bounds (leftAngle y k x z) (phase y z)).1 (hw x hx z hz)
    simp only [leftAngle,cos_sub_int_mul_two_pi] at h ⊢
    convert h using 1 <;> first | rfl | ring
  have h := Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun z hz => hh x hx z hz))
  simp_rw [Finset.sum_sub_distrib,Finset.sum_neg_distrib] at h
  rw [joint_transport_eq u y j w]
  unfold signedMoment cubicCost
  linarith only [h]

/-- The upper estimate uses exactly the SAME signed transport and
unmatched sum. A positive unmatched response is not silently dropped. -/
theorem central_joint_ceiling (u y : ℝ) (j : ℕ)
    (w : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℝ)
    (k : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℤ)
    (hw : ∀ x∈atoms u j,∀ z∈atoms u j,0≤w x z) :
    (centralRest u y j).re-
        ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)≤
      unmatched u y j w-signedMoment u y j w k+cubicCost u y j w k := by
  have hh x (hx : x∈atoms u j) z (hz : z∈atoms u j) :
      w x z*(cos (phase y x)-cos (phase y z))≤
      -(w x z*sin ((leftAngle y k x z+phase y z)/2)*(leftAngle y k x z-phase y z))+
        w x z*|leftAngle y k x z-phase y z|^3/24 := by
    have h := mul_le_mul_of_nonneg_left
      (centered_cosine_bounds (leftAngle y k x z) (phase y z)).2 (hw x hx z hz)
    simp only [leftAngle,cos_sub_int_mul_two_pi] at h ⊢
    convert h using 1 <;> first | rfl | ring
  have h := Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun z hz => hh x hx z hz))
  simp_rw [Finset.sum_add_distrib,Finset.sum_neg_distrib] at h
  rw [joint_transport_eq u y j w]
  unfold signedMoment cubicCost
  linarith only [h]

/-- The full arithmetic signed main-minus-head is approximated, with
an explicit error; the signed first moment is never declared small. -/
theorem central_joint_error (u y : ℝ) (j : ℕ)
    (w : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℝ)
    (k : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℤ)
    (hw : ∀ x∈atoms u j,∀ z∈atoms u j,0≤w x z) :
    |(centralRest u y j).re-
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)-
        (unmatched u y j w-signedMoment u y j w k)|≤cubicCost u y j w k := by
  have hl := central_joint_floor u y j w k hw
  have hu := central_joint_ceiling u y j w k hw
  exact abs_le.mpr ⟨by linarith only [hl],by linarith only [hu]⟩

/-- A quantitative whole-population phase saving. For every gap at most
epsilon, only epsilon^2/24 of the absolute angular transport is paid;
the first moment and all unmatched phases remain signed. -/
theorem cubicCost_le_small_gap (u y : ℝ) (j : ℕ)
    (w : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℝ)
    (k : (ℕ ⊕ ℕ×ℕ)→(ℕ ⊕ ℕ×ℕ)→ℤ) {ε : ℝ}
    (hw : ∀ x∈atoms u j,∀ z∈atoms u j,0≤w x z)
    (hgap : ∀ x∈atoms u j,∀ z∈atoms u j,w x z≠0→|leftAngle y k x z-phase y z|≤ε) :
    cubicCost u y j w k≤ε^2/24*
      (∑ x∈atoms u j,∑ z∈atoms u j,w x z*|leftAngle y k x z-phase y z|) := by
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  unfold cubicCost
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro z hz
  by_cases hzero : w x z=0
  · simp only [hzero,zero_mul,mul_zero,zero_div,le_refl]
  have hδ := hgap x hx z hz hzero
  have hδ0 := abs_nonneg (leftAngle y k x z-phase y z)
  have hp : |leftAngle y k x z-phase y z|^2≤ε^2 := by nlinarith only [hδ,hδ0]
  have hh := mul_le_mul_of_nonneg_right hp hδ0
  have hh' := mul_le_mul_of_nonneg_left hh (hw x hx z hz)
  nlinarith only [hh']

/-- An exact pairwise circular lift; no phase is approximated. -/
def nearestTurns (y : ℝ) (x z : ℕ ⊕ ℕ×ℕ) : ℤ :=
  ⌊(phase y x-phase y z+Real.pi)/(2*Real.pi)⌋

/-- A cut chooses an ordering on the circle, not a new prime phase. -/
def circlePhase (y cut : ℝ) (x : ℕ ⊕ ℕ×ℕ) : ℝ :=
  phase y x-(⌊(phase y x-cut)/(2*Real.pi)⌋ : ℝ)*(2*Real.pi)

/-- Positive and negative ORIGINAL arithmetic amplitudes. -/
def sideMass (u : ℝ) (j : ℕ) (positive : Bool) (x : ℕ ⊕ ℕ×ℕ) : ℝ :=
  max (if positive then amplitude u j x else -amplitude u j x) 0

/-- Normalize only the common mass. The remaining imbalance is retained
in unmatched, with its original phase and its original sign. -/
def normalizedMass (u : ℝ) (j : ℕ) (positive : Bool) (x : ℕ ⊕ ℕ×ℕ) : ℝ :=
  (min (∑ a∈atoms u j,sideMass u j true a) (∑ a∈atoms u j,sideMass u j false a)/
    (∑ a∈atoms u j,sideMass u j positive a))*sideMass u j positive x

/-- Exact cumulative mass in phase order. The original finite-list
index breaks phase ties deterministically without deleting a label. -/
def prefixMass (u y cut : ℝ) (j : ℕ) (positive : Bool) (x : ℕ ⊕ ℕ×ℕ) : ℝ :=
  ∑ a∈(atoms u j).filter (fun a => circlePhase y cut a<circlePhase y cut x ∨
    (circlePhase y cut a=circlePhase y cut x ∧
      (atoms u j).toList.idxOf a<(atoms u j).toList.idxOf x)),
        normalizedMass u j positive a

/-- A concrete nonnegative joint coupling. Its rows and columns are
not assumed to cover the carrier: the exact residual ledger pays them. -/
def cdfCoupling (u y cut : ℝ) (j : ℕ) (x z : ℕ ⊕ ℕ×ℕ) : ℝ :=
  max 0 (min
    (prefixMass u y cut j true x+normalizedMass u j true x)
    (prefixMass u y cut j false z+normalizedMass u j false z)-
      max (prefixMass u y cut j true x) (prefixMass u y cut j false z))

theorem cdfCoupling_nonneg (u y cut : ℝ) (j : ℕ) (x z : ℕ ⊕ ℕ×ℕ) :
    0≤cdfCoupling u y cut j x z := le_max_left _ _

/-- The retained signed moment minus the unmatched signed response,
plus only the cubic phase cost. This is NOT proved cofinally small. -/
def transportPrice (u y cut : ℝ) (j : ℕ) : ℝ :=
  signedMoment u y j (cdfCoupling u y cut j) (nearestTurns y)+
    cubicCost u y j (cdfCoupling u y cut j) (nearestTurns y)-
      unmatched u y j (cdfCoupling u y cut j)

/-- Direct arithmetic inequality for the concrete whole native coupling,
with all counts, masks, original phases and SAME full head assembled. -/
theorem central_floor (u y cut : ℝ) (j : ℕ) :
    -transportPrice u y cut j≤(centralRest u y j).re-
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j) := by
  have h := central_joint_floor u y j (cdfCoupling u y cut j) (nearestTurns y)
    (fun x _ z _ => cdfCoupling_nonneg u y cut j x z)
  unfold transportPrice
  linarith only [h]

/-- Source-scale transfer spends ONLY the existing paid differences.
The signed transport price is explicit, not hidden in any o(1) term. -/
theorem eventually_joined_floor_transport {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (cut : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -transportPrice u y (cut j) j-ZetaRieszBalancedOwnerFloor.budget u y j-
        ZetaRieszBalancedAllocationPayment.allocationBudget j-radialBudget j-
          ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [ZetaRieszBalancedOwnerFloor.eventually_high_packet_joint_bound hu hU hy]
    with j hb
  have hf := central_floor u y (cut j) j
  have ha := ZetaRieszBalancedAllocationPayment.unallocated_sub_rest_bound
    (by linarith : 0≤u) hU j y
  have hrad := central_sub_unallocated_real_bound (by linarith : 0≤u) hU j y
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have he := ZetaRieszBalancedOwnerFloor.native_real_eq_rest_high u y j
  change Q.re=ZetaRieszBalancedOwnerFloor.restPacket u y j+
    ZetaRieszBalancedOwnerFloor.highPacket u y j at he
  change -transportPrice u y (cut j) j-ZetaRieszBalancedOwnerFloor.budget u y j-
    ZetaRieszBalancedAllocationPayment.allocationBudget j-radialBudget j-
      (4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,he,hr,(abs_le.mp hb).1,(abs_le.mp ha).2,(abs_le.mp hrad).2,
    abs_nonneg P.im,norm_nonneg (Q-P)]

/-- Preserve the previous funded whole price as an alternative. -/
def price (u y cut : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  min (ZetaRieszPrimeHeadTransport.price u y j p q a)
    (transportPrice u y cut j+ZetaRieszBalancedOwnerFloor.budget u y j+
      ZetaRieszBalancedAllocationPayment.allocationBudget j+radialBudget j)

theorem price_le_previous (u y cut : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    price u y cut j p q a≤ZetaRieszPrimeHeadTransport.price u y j p q a := min_le_left _ _

/-- The current whole floor uses the best funded alternative, never
adds two credits against the same former cost. No cofinal cap is assumed. -/
theorem eventually_joined_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (cut : ℕ→ℝ) (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -price u y (cut j) j (p j) (q j) (a j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_transport hu hU hy cut,
    ZetaRieszPrimeHeadTransport.eventually_joined_floor hu hU hy p q a] with j ht hp
  unfold price
  rcases le_total (ZetaRieszPrimeHeadTransport.price u y j (p j) (q j) (a j))
    (transportPrice u y (cut j) j+ZetaRieszBalancedOwnerFloor.budget u y j+
      ZetaRieszBalancedAllocationPayment.allocationBudget j+radialBudget j) with h | h
  · rw [min_eq_left h]
    exact hp
  · rw [min_eq_right h]
    linarith only [ht]

end RiemannGaussian.ZetaRieszJointPhaseTransport
