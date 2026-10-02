/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEndgameSlack

/-!
# Retain the imaginary channel in the whole one-sided floor

Join every count, owner and cutoff period before choosing ONE bounded real
phase tilt. The whole source has zero imaginary part; an adverse subset's
imaginary contribution is not claimed to vanish. The compact minimum of
the complete grouped one-sided cost never exceeds the old zero-tilt cost.

This gives an explicit nonnegative global cost credit and a direct floor
for the ORIGINAL carrier with its literal masks. The numerical bound on
the least directional cost remains OPEN. There is no energy monotonicity,
source decay or zero exclusion theorem without that arithmetic premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszComplexProjection
open ZetaRieszCofactorPhaseEnergy ZetaRieszCutoffPeriodFloor
open ZetaRieszJointAllocation ZetaRieszJointPrimeEnergy ZetaRieszGammaJoint
open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint ZetaRieszParityPacket

/-- Both phases stay in the SAME literal divisor-prefix pairing. -/
def complexPrefix (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (f : ℕ → ℝ) : ℂ :=
  ∑ n ∈ S,W n*(∑ d ∈ Finset.Icc 1 X,
    f d*(if d ∣ n then (μ d : ℝ) else 0) : ℝ)

/-- One global tilt; it is not chosen independently by count or cutoff. -/
def tilt (W : ℕ → ℂ) (v : ℝ) (n : ℕ) : ℝ := (W n).re-v*(W n).im

/-- Only complete signed cutoff GROUPS enter the one-sided price. -/
def directionalCost (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (v : ℝ) : ℝ :=
  groupedCost X S (tilt W v) f g

/-- The bounded optimization has a genuine mathematical minimizer. -/
theorem continuous_directionalCost (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) : Continuous (directionalCost X S W f g) := by
  unfold directionalCost groupedCost blockCost blockTotal correlation tilt
  fun_prop

/-- Compactness gives one optimum for the entire joined population. -/
theorem exists_best_tilt (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) :
    ∃ v ∈ Set.Icc (-|B|) |B|,
      ∀ t ∈ Set.Icc (-|B|) |B|,
        directionalCost X S W f g v ≤ directionalCost X S W f g t := by
  exact isCompact_Icc.exists_isMinOn
    ⟨0,by constructor <;> linarith only [abs_nonneg B]⟩
    (continuous_directionalCost X S W f g).continuousOn

/-- A globally chosen bounded optimum, retaining every finite mask. -/
def bestTilt (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) : ℝ :=
  Classical.choose (exists_best_tilt X S W f g B)

/-- The corresponding least one-sided cost, with all counts joined. -/
def bestCost (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) : ℝ :=
  directionalCost X S W f g (bestTilt X S W f g B)

/-- Exact savings relative to the original complete period cost. It
is not a numerical lower bound on the credit in the native population. -/
def credit (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) : ℝ :=
  directionalCost X S W f g 0-bestCost X S W f g B

/-- Moving optimal tilts remain uniformly bounded by the SAME fixed B. -/
theorem bestTilt_bound (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) :
    |bestTilt X S W f g B| ≤ |B| := by
  exact abs_le.mpr (Classical.choose_spec (exists_best_tilt X S W f g B)).1

/-- Including zero tilt makes the new whole cost never larger. -/
theorem bestCost_le_zero (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) :
    bestCost X S W f g B ≤ directionalCost X S W f g 0 := by
  exact (Classical.choose_spec (exists_best_tilt X S W f g B)).2 0
    (by constructor <;> linarith only [abs_nonneg B])

/-- A whole-population signed saving, without an orthogonality premise. -/
theorem credit_nonneg (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) : 0 ≤ credit X S W f g B :=
  sub_nonneg.mpr (bestCost_le_zero X S W f g B)

/-- The optimum is a genuine nonnegative arithmetic cost. -/
theorem bestCost_nonneg (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) : 0 ≤ bestCost X S W f g B := by
  unfold bestCost directionalCost groupedCost blockCost
  exact Finset.sum_nonneg (fun _ _ => le_max_right _ _)

/-- The complete complex prefix, not its adverse subpopulation, occurs
in the exact imaginary correction. -/
theorem tilted_pairing_eq (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (v : ℝ) :
    (∑ n ∈ S,tilt W v n*(∑ d ∈ Finset.Icc 1 X,
      f d*(if d ∣ n then (μ d : ℝ) else 0))) =
      (complexPrefix X S W f).re-v*(complexPrefix X S W f).im := by
  simp only [complexPrefix,Complex.re_sum,Complex.im_sum,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,
    sub_zero,zero_add,Finset.mul_sum,← Finset.sum_sub_distrib,tilt]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- A DIRECT finite joint floor. Every group is summed with both phases
before its one-sided cost; the imaginary channel is not discarded. -/
theorem prefix_floor (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) (hend : f (X+1)=0) :
    -bestCost X S W f g B-|B| * |(complexPrefix X S W f).im| ≤
      (complexPrefix X S W f).re := by
  have hf := grouped_prefix_floor X S (tilt W (bestTilt X S W f g B)) f g hend
  rw [tilted_pairing_eq] at hf
  have hm : -( |B| * |(complexPrefix X S W f).im|) ≤
      bestTilt X S W f g B*(complexPrefix X S W f).im := by
    have hh := mul_le_mul_of_nonneg_right (bestTilt_bound X S W f g B)
      (abs_nonneg (complexPrefix X S W f).im)
    rw [← abs_mul] at hh
    linarith only [hh,neg_abs_le (bestTilt X S W f g B*(complexPrefix X S W f).im)]
  change -bestCost X S W f g B ≤ _ at hf
  linarith only [hf,hm]

/-- The nonnegative global credit is retained in the original whole
floor. No individual count, radial cell or favorable pair is spent. -/
theorem prefix_floor_with_credit (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) (hend : f (X+1)=0) :
    -directionalCost X S W f g 0+credit X S W f g B-
      |B| * |(complexPrefix X S W f).im| ≤ (complexPrefix X S W f).re := by
  dsimp only [credit]
  linarith only [prefix_floor X S W f g B hend]

/-- The zero imaginary source is not a licence to pay the selected real
source to zero: even the optimal directional cost must pay its negative
real contribution. No bound on that contribution is assumed here. -/
theorem negative_real_le_bestCost_of_im_eq_zero (X : ℕ) (S : Finset ℕ)
    (W : ℕ → ℂ) (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ)
    (hend : f (X+1)=0) (him : (complexPrefix X S W f).im=0) :
    max (-(complexPrefix X S W f).re) 0 ≤ bestCost X S W f g B := by
  have hf := prefix_floor X S W f g B hend
  rw [him,abs_zero,mul_zero,sub_zero] at hf
  exact max_le (by linarith only [hf]) (bestCost_nonneg X S W f g B)

/-- The new cost is also no larger than the former one-sided Cauchy
price, without needing a bound on ANY separate count or imaginary sector. -/
theorem bestCost_le_negativeCost (X : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) :
    bestCost X S W f g B ≤
      ZetaRieszRejoinedPhaseFloor.negativeCost X S (fun n => (W n).re) f := by
  apply (bestCost_le_zero X S W f g B).trans
  have ht : tilt W 0=(fun n => (W n).re) := by
    funext n
    simp only [tilt,zero_mul,sub_zero]
  rw [directionalCost,ht]
  exact groupedCost_le_negativeCost X S (fun n => (W n).re) f g

/-- The old signed Cauchy price pays BOTH the new least cost and its
exact retained credit. This prevents adding a credit to a carrier floor
without proving the corresponding cost comparison. -/
theorem bestCost_add_credit_le_negativeCost (X : ℕ) (S : Finset ℕ)
    (W : ℕ → ℂ) (f : ℕ → ℝ) (g : ℕ → ℕ) (B : ℝ) :
    bestCost X S W f g B+credit X S W f g B ≤
      ZetaRieszRejoinedPhaseFloor.negativeCost X S (fun n => (W n).re) f := by
  have ht : tilt W 0=(fun n => (W n).re) := by
    funext n
    simp only [tilt,zero_mul,sub_zero]
  dsimp only [credit]
  have hh := groupedCost_le_negativeCost X S (fun n => (W n).re) f g
  change _ ≤ _
  rw [← ht] at hh
  change directionalCost X S W f g 0 ≤ _ at hh
  rw [ht] at hh
  linarith only [hh]

/-- A regression: zero imaginary part of the whole sum DOES NOT imply
zero imaginary part of its adverse contribution. These are illustrative
complex increments, not a native prime population. -/
theorem adverse_imaginary_regression :
    ((-1+Complex.I)+(2-Complex.I)).im=0 ∧ (-1+Complex.I).re<0 ∧
      (-1+Complex.I).im=1 := by norm_num

/-- A finite sign regression: one common bounded tilt can remove an
adverse debit by using a favorable increment with the opposite imaginary
part. This is an illustrative identity, not a native population bound. -/
theorem joint_tilt_credit_regression :
    max (-(-1+Complex.I).re) 0+max (-(2-Complex.I).re) 0=1 ∧
      max (-((-1+Complex.I).re+(-1+Complex.I).im)) 0+
        max (-((2-Complex.I).re+(2-Complex.I).im)) 0=0 := by
  norm_num

/-- The complex factorial weight of the ORIGINAL physical Riesz atom.
No cofactor is completed and no support or count is changed. -/
def sourceWeight (A : Finset ℕ) (L u y : ℝ) (N n : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*(-(1-boundedShare A N n : ℝ)/L : ℝ)*
    (log n : ℂ)*zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- Zero tilt recovers the exact source-scaled weight of the existing
whole-floor energy. The prime coordinate is one because n is the TOTAL
label, not a completed cofactor. -/
theorem sourceWeight_re (A : Finset ℕ) (L u y : ℝ) (N n : ℕ) :
    (sourceWeight A L u y N n).re=u^(N+1)*primeWeight A L y N n 1 := by
  by_cases hn : n=0
  · subst n
    simp [sourceWeight,primeWeight,pow_succ]
  have hnR : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have he : exp (-(3/2 : ℝ)*log n)=exp (-log n/2)/(n : ℝ) := by
    calc
      _ = exp (-log n/2-log n) := by congr 1; ring
      _ = exp (-log n/2)/exp (log n) := exp_sub _ _
      _ = _ := by rw [exp_log hnR]
  simp only [sourceWeight,← Complex.ofReal_pow,← Complex.ofReal_mul,
    Complex.re_ofReal_mul,← ZetaRieszJointAllocation.filter_one_eq,
    ZetaRieszCosineCarrier.re_filterKernel_one]
  simp only [primeWeight,one_mul,Nat.cast_one,log_one,zero_add,mul_one,he,pow_succ]
  ring

private theorem atom_eq_weight_riesz (A : Finset ℕ) (L u y : ℝ) (N n : ℕ)
    (hsf : Squarefree n) (hnp : ¬n.Prime) :
    (u : ℂ)^(N+1)*(residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
        sourceWeight A L u y N n*(VaughanLogAverage.riesz L n : ℂ) := by
  simp only [sourceWeight,residualCoefficient,SquarefreeVaughanLogSource.coefficient,
    if_pos (And.intro hsf hnp)]
  push_cast
  ring

/-- Exact embedding of BOTH phases, with the original full allocation,
squarefree/count/physical/radial masks and all low factorial orders. -/
theorem native_prefix_eq (A S : Finset ℕ) (L u y : ℝ) (N : ℕ)
    (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card) :
    let X := max 1 (S.sup id)
    let f := correctedProfile X L 1 0;
    complexPrefix X (S.filter Squarefree) (sourceWeight A L u y N) f =
      (u : ℂ)^(N+1)*(∑ n ∈ S,residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
  dsimp only
  rw [complexPrefix,Finset.mul_sum]
  have hrestrict : (∑ n ∈ S.filter Squarefree,(u : ℂ)^(N+1)*
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)) =
        ∑ n ∈ S,(u : ℂ)^(N+1)*
          (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hout
    have hnsf : ¬Squarefree n := fun hs => hout (Finset.mem_filter.mpr ⟨hn,hs⟩)
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hnsf]
  rw [← hrestrict]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hnS,hsf⟩ := Finset.mem_filter.mp hn
  have hnp : ¬n.Prime := by
    intro hp
    have hh := hc n hnS
    simp [hp.primeFactors] at hh
  rw [corrected_prefix_eq hsf (hc n hnS)
    ((Finset.le_sup (f := id) hnS).trans (le_max_right _ _))]
  exact (atom_eq_weight_riesz A L u y N n hsf hnp).symm

/-- The least whole-period cost on the CURRENT literal count-cropped
core. It is not a cost for a completed or sector-selected carrier. -/
def nativeCost (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  bestCost X (S.filter Squarefree) (sourceWeight A L u y N)
    (correctedProfile X L 1 0) (cutoffPeriod y) 4

/-- The retained credit is for the SAME whole literal native cost. -/
def nativeCredit (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  credit X (S.filter Squarefree) (sourceWeight A L u y N)
    (correctedProfile X L 1 0) (cutoffPeriod y) 4

/-- No count-by-count or pair-by-pair credit is added to this global saving. -/
theorem nativeCredit_nonneg (u y : ℝ) (j : ℕ) : 0 ≤ nativeCredit u y j := by
  unfold nativeCredit
  exact credit_nonneg _ _ _ _ _ _

/-- A direct comparison to the SAME original adverse Cauchy cost.
All existing geometric payments may be applied to its right-hand side;
this theorem does not assume their remaining signed energy is small. -/
theorem nativeCost_add_credit_le_original (u y : ℝ) (j : ℕ) :
    let N := dyadicMomentOrder j
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
    let X := max 1 (S.sup id)
    let f := correctedProfile X L 1 0;
    nativeCost u y j+nativeCredit u y j ≤
      ZetaRieszRejoinedPhaseFloor.negativeCost X (S.filter Squarefree)
        (fun n => u^(N+1)*primeWeight A L y N n 1) f := by
  dsimp only
  have he := bestCost_add_credit_le_negativeCost
    (max 1 ((coreBand u (dyadicMomentOrder j)
      (ZetaRieszNearCriticalCountPayment.countCeiling j)).sup id))
    ((coreBand u (dyadicMomentOrder j)
      (ZetaRieszNearCriticalCountPayment.countCeiling j)).filter Squarefree)
    (sourceWeight (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) u y (dyadicMomentOrder j))
    (correctedProfile (max 1 ((coreBand u (dyadicMomentOrder j)
      (ZetaRieszNearCriticalCountPayment.countCeiling j)).sup id))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) 1 0) (cutoffPeriod y) 4
  simpa only [nativeCost,nativeCredit,sourceWeight_re] using he

/-- All imaginary and mask-transfer corrections are stated literally.
They vanish under the exposed-zero source, not for arbitrary subsets. -/
def nativeError (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let P := (u : ℂ)^(N+1)*joinedPhysical u y N (dyadicPrimeCount j)
  let Q := (u : ℂ)^(N+1)*coreResponse u y N
    (ZetaRieszNearCriticalCountPayment.countCeiling j)
  4*|P.im|+5*‖Q-P‖

/-- DIRECT whole-carrier floor, valid before any zero assumption. The
explicit imaginary correction prevents using a false adverse-only null. -/
theorem native_floor (u y : ℝ) (j : ℕ) :
    -nativeCost u y j-nativeError u y j ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let f := correctedProfile X L 1 0
  let P := (u : ℂ)^(N+1)*joinedPhysical u y N (dyadicPrimeCount j)
  let Q := (u : ℂ)^(N+1)*coreResponse u y N
    (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have h := prefix_floor X (S.filter Squarefree) (sourceWeight A L u y N) f
    (cutoffPeriod y) 4 (by simp [f,correctedProfile,ZetaRieszCenteredPrimeEnergy.centeredProfile])
  have he := native_prefix_eq A S L u y N (fun n hn => core_count hn)
  dsimp only at he
  change complexPrefix X (S.filter Squarefree) (sourceWeight A L u y N) f=Q at he
  rw [he] at h
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at h
  have hr : Q.re-P.re ≤ ‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have hi : |Q.im| ≤ |P.im|+‖Q-P‖ := by
    have hh := abs_sub_le Q.im P.im 0
    simp only [sub_zero] at hh
    have hd : |Q.im-P.im| ≤ ‖Q-P‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (Q-P)
    linarith only [hh,hd]
  change -nativeCost u y j-nativeError u y j ≤ P.re
  change -nativeCost u y j-4*|Q.im| ≤ Q.re at h
  unfold nativeError
  change -nativeCost u y j-(4*|P.im|+5*‖Q-P‖) ≤ P.re
  linarith only [h,hr,hi]

/-- The SAME native whole-floor comparison now retains the exact signed
phase credit. This is an inequality for the original carrier, not a new
support sector or an assumption that the global credit is numerically large. -/
theorem native_floor_with_credit (u y : ℝ) (j : ℕ) :
    let N := dyadicMomentOrder j
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
    let X := max 1 (S.sup id)
    let f := correctedProfile X L 1 0;
    -ZetaRieszRejoinedPhaseFloor.negativeCost X (S.filter Squarefree)
      (fun n => u^(N+1)*primeWeight A L y N n 1) f+
        nativeCredit u y j-nativeError u y j ≤
          ((u : ℂ)^(N+1)*joinedPhysical u y N (dyadicPrimeCount j)).re := by
  have hf := native_floor u y j
  have hc := nativeCost_add_credit_le_original u y j
  dsimp only at hc ⊢
  linarith only [hf,hc]

/-- The complete count-cropped/core-to-joined error is already paid.
No phase approximation or additional prime-count estimate is needed. -/
theorem tendsto_crop_sub_joined {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(dyadicMomentOrder j+1)*
      (coreResponse u y (dyadicMomentOrder j)
        (ZetaRieszNearCriticalCountPayment.countCeiling j)-
          joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)))
      atTop (𝓝 0) := by
  have hh := tendsto_core_sub_joined hu hU (fun _ => y)
    dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder
  have hc := ZetaRieszNearCriticalCountPayment.tendsto_core_count_change
    (fun _ => u) (fun _ => y) (fun _ => hu.le) (fun _ => hU)
  have he := hh.sub hc
  simp only [sub_zero] at he
  exact he.congr' (Eventually.of_forall fun _ => by ring)

/-- The WHOLE imaginary source vanishes at every analytic multiplicity.
This does not assert a null for any adverse cutoff or count subset. -/
theorem tendsto_nativeError (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (nativeError (3/2-rho.1.re) rho.1.im) atTop (𝓝 0) := by
  have hu : 0 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hs := ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source
    rho hrho hexposed hU
  have hreal : (-(analyticZetaZeroMultiplicity rho : ℂ)+
      (analyticZetaZeroMultiplicity rho : ℂ)^2*
        (ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) : ℂ)) =
      ((-(analyticZetaZeroMultiplicity rho : ℝ)+
        (analyticZetaZeroMultiplicity rho : ℝ)^2*
          ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hreal] at hs
  have hi := Complex.continuous_im.tendsto _ |>.comp hs
  simp only [Complex.ofReal_im] at hi
  have hd := (tendsto_crop_sub_joined hu hU rho.1.im).norm
  have he := (hi.abs.const_mul 4).add (hd.const_mul 5)
  unfold nativeError
  simpa only [Function.comp_def,norm_zero,abs_zero,mul_zero,
    add_zero,mul_sub] using he

/-- An independent cofinal bound for the ACTUAL least directional cost
would close the relaxed simple-zero floor. This arithmetic premise remains
OPEN; the phase projection and imaginary null do not supply it. -/
theorem false_of_cofinal_nativeCost (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1)
    (hcost : ∃ᶠ j in atTop,nativeCost (3/2-rho.1.re) rho.1.im j ≤ 399/5000) : False := by
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (nativeError (3/2-rho.1.re) rho.1.im) (tendsto_nativeError rho hrho hexposed hU)
  exact hcost.mono fun j hj => by
    have hf := native_floor (3/2-rho.1.re) rho.1.im j
    linarith only [hj,hf]

end RiemannGaussian.ZetaRieszComplexProjection
