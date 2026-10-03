/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszZeroResponseFloor

/-!
# Label-dependent complex zero responses in the same whole floor

Each certified zero label annihilates the original base profile, not merely
one aggregate real projection. Its complex coefficient may therefore depend
on the literal label and on the moving order. Join this correction with every
previous direction and the independently paid owner rows BEFORE pricing whole
cutoff periods. No coefficient bound, source-envelope payment or zero
hypothesis is needed for the arithmetic inequality. The numerical cofinal
bound remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszWeightedZeroFloor
open ZetaRieszZeroResponseFloor ZetaRieszPaidIncidenceFloor
open ZetaRieszCutoffPeriodFloor ZetaRieszComplexProjection
open ZetaRieszCofactorPhaseEnergy ZetaRieszJointPrimeEnergy
open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket

/-- Every selected label has zero base response even with an arbitrary
complex observation. This is a finite arithmetic equality, not a limiting
phase replacement or a change to the original carrier weights. -/
theorem complexPrefix_zero_weighted (u : ℝ) (j : ℕ) (V : ℕ→ℂ) :
    complexPrefix (nativeEndpoint u j) (zeroLabels u j) V
      (correctedProfile (nativeEndpoint u j)
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0)=0 := by
  unfold complexPrefix
  apply Finset.sum_eq_zero
  intro n hn
  have hd := zeroLabels_data hn
  have hX : n≤nativeEndpoint u j :=
    (Finset.le_sup (f:=id) hd.1).trans (le_max_right _ _)
  rw [corrected_prefix_eq hd.2.1 (core_count hd.1) hX,hd.2.2,
      Complex.ofReal_zero,mul_zero]

/-- An exact correction with a label-dependent COMPLEX coefficient.
The original all-prime allocation, source factorial and phase remain in W;
only a certified zero response is multiplied by v. The owner allocation in
the independent paid increment is still distinct. -/
def weightedIncrement (u y : ℝ) (j : ℕ) (v : ℕ→ℂ) (k : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let X := nativeEndpoint u j
  let W := sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N) L u y N
  correlation (zeroLabels u j) (fun n=>(W n*v n).re) k*
    (correctedProfile X L 1 0 k-correctedProfile X L 1 0 (k+1))

/-- All moving complex coefficients are free AFTER complete signed
response cancellation. No norm or positive allowance is assigned to v. -/
theorem sum_weightedIncrement_zero (u y : ℝ) (j : ℕ) (v : ℕ→ℂ) :
    (∑ k∈Finset.Icc 1 (nativeEndpoint u j),weightedIncrement u y j v k)=0 := by
  have he := ZetaRieszTangentCubicCredit.sum_profile_direction
    (nativeEndpoint u j) (zeroLabels u j)
    (fun n=>sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) u y (dyadicMomentOrder j) n*v n)
    (correctedProfile (nativeEndpoint u j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0)
    (by simp [correctedProfile,ZetaRieszCenteredPrimeEnergy.centeredProfile]) 1 0
  rw [complexPrefix_zero_weighted] at he
  simpa only [weightedIncrement,one_mul,zero_mul,sub_zero,Complex.zero_re,
    Complex.zero_im] using he

/-- The same flat original base profile prevents any new early-cutoff
debit, for arbitrary label-dependent coefficients. -/
theorem weightedIncrement_zero_early {u y : ℝ} {j k : ℕ} (v : ℕ→ℂ)
    (hk : k∈Finset.Icc 1 (nativeEndpoint u j))
    (hL : log (k+1 : ℕ)≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    weightedIncrement u y j v k=0 := by
  have hf : correctedProfile (nativeEndpoint u j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0 k=
    correctedProfile (nativeEndpoint u j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0 (k+1) := by
    by_contra h
    exact low_cutoff_inactive (nativeEndpoint u j) k hL
      (Finset.mem_filter.mpr ⟨hk,h⟩)
  simp only [weightedIncrement,hf,sub_self,mul_zero]

/-- The old real/tilted correction is an EXACT special case. The new
imaginary freedom is independent of the fixed tilt on the nonzero carrier. -/
theorem weightedIncrement_previous (u y r : ℝ) (j k : ℕ) :
    weightedIncrement u y j (fun _=>(r : ℂ)+Complex.I*(r*nativeTilt u y j : ℝ)) k=
      r*zeroIncrement u y j k := by
  unfold weightedIncrement zeroIncrement
  dsimp only
  have he (W : ℕ→ℂ) :
      correlation (zeroLabels u j)
        (fun n=>(W n*((r : ℂ)+Complex.I*(r*nativeTilt u y j : ℝ))).re) k=
      r*(correlation (zeroLabels u j) (fun n=>(W n).re) k-
        nativeTilt u y j*correlation (zeroLabels u j) (fun n=>(W n).im) k) := by
    unfold correlation
    rw [mul_sub]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp [Complex.mul_re,Complex.mul_im]
    ring
  rw [he]
  ring

/-- The actual whole cost with the new complex correction assembled
with all previous corrections and independently paid rows before clipping. -/
def weightedCost (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) (v : ℕ→ℂ) : ℝ :=
  blockCost (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
    (fun k=>nativeStep u y j q a k-nativePaidIncrement u y j k-weightedIncrement u y j v k)

/-- Price an exact native null on the same baseline. This API is used
only after proving its full signed total is zero on the ORIGINAL axis. -/
def nullCost (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) (z : ℕ→ℝ) : ℝ :=
  blockCost (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
    (fun k=>nativeStep u y j q a k-nativePaidIncrement u y j k-z k)

theorem weightedCost_zero (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) :
    weightedCost u y j q a 0=nativePrunedCost u y j q a := by
  simp [weightedCost,nativePrunedCost,weightedIncrement,correlation]

theorem weightedCost_previous (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) :
    weightedCost u y j q a (fun _=>(r : ℂ)+Complex.I*(r*nativeTilt u y j : ℝ))=
      zeroClearedCost u y j q a r := by
  unfold weightedCost zeroClearedCost
  simp only [weightedIncrement_previous]

/-- The combined variation gain is exact; individual label/count prices
are never summed. A particular coefficient may worsen the joined price. -/
theorem weightedCost_saving_eq (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ)
    (a : ℝ) (v : ℕ→ℂ) :
    nativePrunedCost u y j q a-weightedCost u y j q a v=
      ((∑ c∈(Finset.Icc 1 (nativeEndpoint u j)).image (cutoffPeriod y),
        |blockTotal (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
          (fun k=>nativeStep u y j q a k-nativePaidIncrement u y j k) c|)-
      (∑ c∈(Finset.Icc 1 (nativeEndpoint u j)).image (cutoffPeriod y),
        |blockTotal (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
          (fun k=>nativeStep u y j q a k-nativePaidIncrement u y j k-weightedIncrement u y j v k) c|))/2 := by
  exact blockCost_sub_zero_saving _ _ _ _ (sum_weightedIncrement_zero u y j v)

theorem eventually_joined_floor_after_null {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) (z : ℕ→ℕ→ℝ)
    (hz : ∀ j,(∑ k∈Finset.Icc 1 (nativeEndpoint u j),z j k)=0) :
    ∀ᶠ j in atTop,
      -nullCost u y j (q j) (a j) (z j)-nativePaidBudget y j-
        ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_nativePaidPacket_bound hu hU hy] with j hp
  have hf := pruned_block_floor (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
    (fun k=>nativeStep u y j (q j) (a j) k-z j k)
    (nativePaidIncrement u y j) (E:=nativePaidBudget y j)
      (by rw [sum_nativePaidIncrement]; exact hp)
  rw [Finset.sum_sub_distrib,hz j,sub_zero,sum_nativeStep] at hf
  have hc : blockCost (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
      (fun k=>nativeStep u y j (q j) (a j) k-z j k-nativePaidIncrement u y j k)=
        nullCost u y j (q j) (a j) (z j) := by
    congr 1
    funext k
    ring
  rw [hc] at hf
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have ht := nativeTilt_bound u y j
  have him := abs_mul (nativeTilt u y j) Q.im
  have hscale := mul_le_mul_of_nonneg_right ht (abs_nonneg Q.im)
  have hneg := neg_abs_le (nativeTilt u y j*Q.im)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have hi : |Q.im|≤|P.im|+‖Q-P‖ := by
    have htri := abs_sub_le Q.im P.im 0
    have hd : |Q.im-P.im|≤‖Q-P‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (Q-P)
    simp only [sub_zero] at htri
    linarith only [htri,hd]
  change -nullCost u y j (q j) (a j) (z j)-nativePaidBudget y j≤
    Q.re-nativeTilt u y j*Q.im at hf
  change -nullCost u y j (q j) (a j) (z j)-nativePaidBudget y j-
    (4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,hscale,him,hneg,hr,hi]

theorem eventually_joined_floor_weighted {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) (v : ℕ→ℕ→ℂ) :
    ∀ᶠ j in atTop,
      -weightedCost u y j (q j) (a j) (v j)-nativePaidBudget y j-
        ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  exact eventually_joined_floor_after_null hu hU hy q a
    (fun j=>weightedIncrement u y j (v j)) (fun j=>sum_weightedIncrement_zero u y j (v j))

/-- Retain the entire previous credited price as an alternative. The
new correction is spent jointly, never added as an unfunded second credit. -/
def weightedPrice (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) (v : ℕ→ℂ) : ℝ :=
  min (zeroClearedPrice u y j q a r) (weightedCost u y j q a v+nativePaidBudget y j)

theorem weightedPrice_le_previous (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ)
    (a r : ℝ) (v : ℕ→ℂ) : weightedPrice u y j q a r v≤zeroClearedPrice u y j q a r :=
  min_le_left _ _

theorem weightedPrice_zero (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) :
    weightedPrice u y j q a r 0=zeroClearedPrice u y j q a r := by
  unfold weightedPrice
  rw [weightedCost_zero]
  exact min_eq_left ((zeroClearedPrice_le_previous u y j q a r).trans
    (nativePrunedPrice_le_pruned u y j q a))

theorem weightedPrice_previous (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) :
    weightedPrice u y j q a r
      (fun _=>(r : ℂ)+Complex.I*(r*nativeTilt u y j : ℝ))=zeroClearedPrice u y j q a r := by
  unfold weightedPrice
  rw [weightedCost_previous]
  exact min_eq_left (min_le_right _ _)

/-- The additional whole-price saving, capped by the same previous
credited price. The separate coefficient experiments do not add credits. -/
def weightedGain (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) (v : ℕ→ℂ) : ℝ :=
  zeroClearedPrice u y j q a r-weightedPrice u y j q a r v

theorem weightedGain_nonneg (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ)
    (a r : ℝ) (v : ℕ→ℂ) : 0≤weightedGain u y j q a r v :=
  sub_nonneg.mpr (weightedPrice_le_previous u y j q a r v)

theorem eventually_joined_floor_with_weighted_zero_credit {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a r : ℕ→ℝ) (v : ℕ→ℕ→ℂ) :
    ∀ᶠ j in atTop,
      -weightedPrice u y j (q j) (a j) (r j) (v j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_weighted hu hU hy q a v,
    eventually_joined_floor_with_zero_response_credit hu hU hy q a r] with j hnew hold
  unfold weightedPrice
  rcases le_total (zeroClearedPrice u y j (q j) (a j) (r j))
      (weightedCost u y j (q j) (a j) (v j)+nativePaidBudget y j) with h | h
  · rw [min_eq_left h]
    exact hold
  · rw [min_eq_right h]
    linarith only [hnew]

/-- The independent numerical native premise is unchanged and OPEN.
This endpoint does not assert it for the new coefficient family. -/
theorem false_of_cofinal_weighted_price (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) (hsimple : analyticZetaZeroMultiplicity rho=1)
    (q : ℕ→Fin 6→ℝ) (a r : ℕ→ℝ) (v : ℕ→ℕ→ℂ)
    (hcost : ∃ᶠ j in atTop,
      weightedPrice (3/2-rho.1.re) rho.1.im j (q j) (a j) (r j) (v j)≤399/5000) : False := by
  have hu : 1/2<3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
      (ZetaRieszComplexProjection.tendsto_nativeError rho hrho hexposed hU)
  have hf := eventually_joined_floor_with_weighted_zero_credit hu hU hy q a r v
  exact (hcost.and_eventually hf).mono (fun j hj=>by
    obtain ⟨hc,hf⟩ := hj
    linarith only [hc,hf])

end RiemannGaussian.ZetaRieszWeightedZeroFloor
