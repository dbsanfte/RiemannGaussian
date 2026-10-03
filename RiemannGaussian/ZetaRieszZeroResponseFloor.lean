/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPaidIncidenceFloor
import RiemannGaussian.ZetaRieszSmallCofactorCancellation

/-!
# Clear certified zero responses before pricing the whole native floor

The least-prime pair need not meet any polynomial size bound. If its
divisor blocks miss the moving hinge, the COMPLETE label response is zero.
Its signed cutoff direction can be combined with the previous corrections
at exactly zero funding cost. Every factorial order, phase and mask remains.
Keep the previous price as an alternative: forced deletion can destroy
useful cancellation. No numerical cofinal price is claimed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszZeroResponseFloor
open ZetaRieszCutoffPeriodFloor ZetaRieszPaidIncidenceFloor
open ZetaRieszComplexProjection ZetaRieszCofactorPhaseEnergy
open ZetaRieszPrimeCountFrequency ZetaRieszJointAllocation
open ZetaRieszParityPacket ZetaRieszJointPrimeEnergy

/-- An exact integer test: every divisor block is on one affine side
of the cutoff. No floating logarithm or density hypothesis is used. -/
def IntegerGap (X n R : ℕ) : Prop :=
  R∣n ∧ 2≤R.primeFactors.card ∧
    ∀ d∈(n/R).divisors, X≤d ∨ d*R≤X

/-- The integer gap invokes the existing all-rank signed block zero.
It applies to an arbitrary squarefree factor, at unrestricted counts. -/
theorem riesz_zero_of_integerGap {X n R : ℕ} (hX : 0<X)
    (hs : Squarefree n) (hg : IntegerGap X n R) :
    VaughanLogAverage.riesz (log X) n=0 := by
  obtain ⟨hRn,hc,hgap⟩ := hg
  have he : n/R*R=n := Nat.div_mul_cancel hRn
  have hsprod : Squarefree (n/R*R) := he.symm ▸ hs
  have hRpos : 0<R := Nat.pos_of_ne_zero hsprod.of_mul_right.ne_zero
  have hh := ZetaRieszSmallCofactorCancellation.spectrum_gap_cutoff_zero
    hsprod.of_mul_right hc (Nat.coprime_of_squarefree_mul hsprod)
      (D:=log X) (fun d hd=>by
        have hdpos := Nat.pos_of_mem_divisors hd
        rcases hgap d hd with h | h
        · exact Or.inl (log_le_log (by exact_mod_cast hX)
            (by exact_mod_cast h))
        · right
          have hl := log_le_log (by exact_mod_cast Nat.mul_pos hdpos hRpos)
            (show (d*R : ℕ)≤(X : ℝ) by exact_mod_cast h)
          rwa [Nat.cast_mul,log_mul (by exact_mod_cast hdpos.ne')
            (by exact_mod_cast hRpos.ne')] at hl)
  rwa [he] at hh

/-- The original physical cutoff as an integer, with no rounded log
substitution. -/
def physicalCutoff (u : ℝ) (j : ℕ) : ℕ :=
  (ZetaVaughanCutoffBudget.linearDampedCutoff u (dyadicMomentOrder j)+2)^2

theorem physicalCutoff_pos (u : ℝ) (j : ℕ) : 0<physicalCutoff u j := by
  unfold physicalCutoff
  positivity

theorem length_eq_log_physicalCutoff (u : ℝ) (j : ℕ) :
    SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)=
      log (physicalCutoff u j) := by
  simp only [SquarefreeVaughanLogSource.length,physicalCutoff,Nat.cast_pow,
    Nat.cast_add,Nat.cast_ofNat]

/-- Certified zero-response labels in the CURRENT native crop. Their
canonical least pair and every original product mask are retained. -/
def zeroLabels (u : ℝ) (j : ℕ) : Finset ℕ :=
  (nativeLabels u j).filter (fun n=>Squarefree n ∧ IntegerGap (physicalCutoff u j) n
    (ZetaRieszShortDivisorCancellation.leastPairBlock n))

theorem zeroLabels_data {u : ℝ} {j n : ℕ} (hn : n∈zeroLabels u j) :
    n∈nativeLabels u j ∧ Squarefree n ∧
      VaughanLogAverage.riesz
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n=0 := by
  obtain ⟨hn,hs,hg⟩ := Finset.mem_filter.mp hn
  refine ⟨hn,hs,?_⟩
  rw [length_eq_log_physicalCutoff]
  exact riesz_zero_of_integerGap (physicalCutoff_pos u j) hs hg

/-- The same whole-label complex phase and all-prime allocation as the
native floor, summed only after the complete signed zero response. -/
theorem zeroLabels_complexPrefix (u y : ℝ) (j : ℕ) :
    complexPrefix (nativeEndpoint u j) (zeroLabels u j)
      (sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) u y (dyadicMomentOrder j))
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

/-- A full native zero-label cutoff increment, with the SAME imaginary
tilt. The earlier null/tangent directions are not changed or spent twice. -/
def zeroIncrement (u y : ℝ) (j k : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let X := nativeEndpoint u j
  let W := sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N) L u y N
  (correlation (zeroLabels u j) (fun n=>(W n).re) k-
    nativeTilt u y j*correlation (zeroLabels u j) (fun n=>(W n).im) k)*
      (correctedProfile X L 1 0 k-correctedProfile X L 1 0 (k+1))

/-- Exact signed cancellation across every cutoff of every selected
count. No geometric error budget or zero hypothesis is needed. -/
theorem sum_zeroIncrement (u y : ℝ) (j : ℕ) :
    (∑ k∈Finset.Icc 1 (nativeEndpoint u j),zeroIncrement u y j k)=0 := by
  have he := ZetaRieszTangentCubicCredit.sum_profile_direction
    (nativeEndpoint u j) (zeroLabels u j)
      (sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) u y (dyadicMomentOrder j))
      (correctedProfile (nativeEndpoint u j)
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0)
      (by simp [correctedProfile,ZetaRieszCenteredPrimeEnergy.centeredProfile])
      1 (nativeTilt u y j)
  rw [zeroLabels_complexPrefix] at he
  simpa only [zeroIncrement,one_mul,Complex.zero_re,Complex.zero_im,mul_zero,sub_zero]
    using he

/-- The zero-response direction adds no early-cutoff debit. -/
theorem zeroIncrement_zero_early {u y : ℝ} {j k : ℕ}
    (hk : k∈Finset.Icc 1 (nativeEndpoint u j))
    (hL : log (k+1 : ℕ)≤SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    zeroIncrement u y j k=0 := by
  have hf : correctedProfile (nativeEndpoint u j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0 k=
    correctedProfile (nativeEndpoint u j)
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0 (k+1) := by
    by_contra h
    exact low_cutoff_inactive (nativeEndpoint u j) k hL
      (Finset.mem_filter.mpr ⟨hk,h⟩)
  simp only [zeroIncrement,hf,sub_self,mul_zero]

/-- Removing an EXACT signed zero changes the price only by its joined
period variation. Counts and boundaries are never clipped separately. -/
theorem blockCost_sub_zero_saving (K : Finset ℕ) (g : ℕ→ℕ) (t z : ℕ→ℝ)
    (hz : (∑ k∈K,z k)=0) :
    blockCost K g t-blockCost K g (fun k=>t k-z k)=
      ((∑ c∈K.image g,|blockTotal K g t c|)-
        (∑ c∈K.image g,|blockTotal K g (fun k=>t k-z k) c|))/2 := by
  rw [blockCost_eq,blockCost_eq,Finset.sum_sub_distrib,hz,sub_zero]
  ring

/-- Price the whole signed remainder with the independent paid rows
and the signed zero-response direction joined. Forced deletion is only
the special coefficient one; neither direction is norm-priced. -/
def zeroClearedCost (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) : ℝ :=
  blockCost (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
    (fun k=>nativeStep u y j q a k-nativePaidIncrement u y j k-r*zeroIncrement u y j k)

theorem zeroCleared_saving_eq (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) :
    nativePrunedCost u y j q a-zeroClearedCost u y j q a r=
      ((∑ c∈(Finset.Icc 1 (nativeEndpoint u j)).image (cutoffPeriod y),
        |blockTotal (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
          (fun k=>nativeStep u y j q a k-nativePaidIncrement u y j k) c|)-
      (∑ c∈(Finset.Icc 1 (nativeEndpoint u j)).image (cutoffPeriod y),
        |blockTotal (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
          (fun k=>nativeStep u y j q a k-nativePaidIncrement u y j k-r*zeroIncrement u y j k) c|))/2 := by
  exact blockCost_sub_zero_saving _ _ _ _ (by
    rw [← Finset.mul_sum,sum_zeroIncrement,mul_zero])

/-- Coefficient zero recovers the previous paid-row price exactly. The
coefficient need not be positive or bounded, since the total is EXACT zero. -/
theorem zeroClearedCost_zero (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) :
    zeroClearedCost u y j q a 0=nativePrunedCost u y j q a := by
  simp only [zeroClearedCost,nativePrunedCost,zero_mul,sub_zero]

theorem eventually_joined_floor_zeroCleared {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a r : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -zeroClearedCost u y j (q j) (a j) (r j)-nativePaidBudget y j-
        ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_nativePaidPacket_bound hu hU hy] with j hp
  have hf := pruned_block_floor (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
    (fun k=>nativeStep u y j (q j) (a j) k-r j*zeroIncrement u y j k)
    (nativePaidIncrement u y j) (E:=nativePaidBudget y j)
      (by rw [sum_nativePaidIncrement]; exact hp)
  have hz : (∑ k∈Finset.Icc 1 (nativeEndpoint u j),r j*zeroIncrement u y j k)=0 := by
    rw [← Finset.mul_sum,sum_zeroIncrement,mul_zero]
  rw [Finset.sum_sub_distrib,hz,sub_zero,sum_nativeStep] at hf
  have hc : blockCost (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
      (fun k=>nativeStep u y j (q j) (a j) k-r j*zeroIncrement u y j k-nativePaidIncrement u y j k)=
        zeroClearedCost u y j (q j) (a j) (r j) := by
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
  change -zeroClearedCost u y j (q j) (a j) (r j)-nativePaidBudget y j≤
    Q.re-nativeTilt u y j*Q.im at hf
  change -zeroClearedCost u y j (q j) (a j) (r j)-nativePaidBudget y j-
    (4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,hscale,him,hneg,hr,hi]

/-- Keep the old price as an alternative. A zero signed contribution
need not lower intermediate variation when simply deleted. -/
def zeroClearedPrice (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) : ℝ :=
  min (nativePrunedPrice u y j q a) (zeroClearedCost u y j q a r+nativePaidBudget y j)

theorem zeroClearedPrice_le_previous (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) :
    zeroClearedPrice u y j q a r≤nativePrunedPrice u y j q a := min_le_left _ _

theorem zeroClearedPrice_zero (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ) :
    zeroClearedPrice u y j q a 0=nativePrunedPrice u y j q a := by
  unfold zeroClearedPrice
  rw [zeroClearedCost_zero,min_eq_left (nativePrunedPrice_le_pruned u y j q a)]

/-- The exact additional WHOLE-price gain, with every old credit and
the existing signed-row payment charged on the same baseline once. -/
def zeroClearedGain (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) : ℝ :=
  nativePrunedPrice u y j q a-zeroClearedPrice u y j q a r

theorem zeroClearedGain_nonneg (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r : ℝ) :
    0≤zeroClearedGain u y j q a r := sub_nonneg.mpr (zeroClearedPrice_le_previous u y j q a r)

theorem eventually_joined_floor_with_zero_response_credit {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a r : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -zeroClearedPrice u y j (q j) (a j) (r j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_zeroCleared hu hU hy q a r,
    eventually_joined_floor_with_pruned_price hu hU hy q a] with j hnew hold
  unfold zeroClearedPrice
  rcases le_total (nativePrunedPrice u y j (q j) (a j))
      (zeroClearedCost u y j (q j) (a j) (r j)+nativePaidBudget y j) with h | h
  · rw [min_eq_left h]
    exact hold
  · rw [min_eq_right h]
    linarith only [hnew]

/-- The cofinal numerical threshold remains an explicit open arithmetic
premise. No zero exclusion is inferred from the free cancellation alone. -/
theorem false_of_cofinal_zeroCleared_price (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) (hsimple : analyticZetaZeroMultiplicity rho=1)
    (q : ℕ→Fin 6→ℝ) (a r : ℕ→ℝ)
    (hcost : ∃ᶠ j in atTop,
      zeroClearedPrice (3/2-rho.1.re) rho.1.im j (q j) (a j) (r j)≤399/5000) : False := by
  have hu : 1/2<3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
      (ZetaRieszComplexProjection.tendsto_nativeError rho hrho hexposed hU)
  have hf := eventually_joined_floor_with_zero_response_credit hu hU hy q a r
  exact (hcost.and_eventually hf).mono (fun j hj=>by
    obtain ⟨hc,hf⟩ := hj
    linarith only [hc,hf])

end RiemannGaussian.ZetaRieszZeroResponseFloor
