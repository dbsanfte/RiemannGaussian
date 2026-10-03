/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszClosedTailFloor

/-!
# Signed feedback from closed divisor tails in the whole floor

Choose each null coefficient from its correlation with the SAME adverse
complete-period aggregate. The resulting whole-direction correlation is
exactly a sum of squares. Its boundary debit is priced AFTER joining the
direction, and the quantitative step pays every changed sign. Repeating
the step adds only the successive, actually funded savings. All original
labels, phases, masks and previously paid owner rows remain unchanged.

This supplies a mathematically defined, count-independent rule and a
quantified improvement of the native whole-floor inequality. It does not
bound the cofinal size of the remaining native price.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszTailFeedbackFloor
open ZetaRieszCutoffPeriodFloor ZetaRieszSignedNullGain
open ZetaRieszQuantitativeNullStep ZetaRieszWeightedZeroFloor
open ZetaRieszClosedTailFloor ZetaRieszPaidIncidenceFloor
open ZetaRieszZeroResponseFloor ZetaRieszCofactorPhaseEnergy
open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket

/-- One full signed feedback direction, after every count and cutoff
period has been joined. The nonnegative weights may normalize columns;
they do not change any original carrier observation. -/
def feedback (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) (k : ℕ) : ℝ :=
  ∑ i∈I,w i*adverseCorrelation K g t (Z i)*Z i k

theorem blockTotal_feedback (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) (c : ℕ) :
    blockTotal K g (feedback K g I t Z w) c=
      ∑ i∈I,w i*adverseCorrelation K g t (Z i)*blockTotal K g (Z i) c := by
  unfold blockTotal feedback
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _=>by rw [Finset.mul_sum])

/-- The coefficients are chosen by the actual adverse periods. This
identity is signed, not an absolute prime or Fourier allowance. -/
theorem adverseCorrelation_feedback_eq (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) :
    adverseCorrelation K g t (feedback K g I t Z w)=
      ∑ i∈I,w i*adverseCorrelation K g t (Z i)^2 := by
  unfold adverseCorrelation at ⊢
  simp_rw [blockTotal_feedback]
  have h c : (if blockTotal K g t c<0 then
      ∑ i∈I,w i*adverseCorrelation K g t (Z i)*blockTotal K g (Z i) c else 0)=
      ∑ i∈I,w i*adverseCorrelation K g t (Z i)*
        (if blockTotal K g t c<0 then blockTotal K g (Z i) c else 0) := by
    split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  change w i*adverseCorrelation K g t (Z i)*adverseCorrelation K g t (Z i)=
    w i*adverseCorrelation K g t (Z i)^2
  ring

theorem adverseCorrelation_feedback_nonneg (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) (hw : ∀ i∈I,0≤w i) :
    0≤adverseCorrelation K g t (feedback K g I t Z w) := by
  rw [adverseCorrelation_feedback_eq]
  exact Finset.sum_nonneg (fun i hi=>mul_nonneg (hw i hi) (sq_nonneg _))

theorem sum_feedback_zero (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ)
    (hZ : ∀ i∈I,(∑ k∈K,Z i k)=0) :
    (∑ k∈K,feedback K g I t Z w k)=0 := by
  unfold feedback
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum,hZ i hi,mul_zero]

/-- Keep zero and near-zero periods in the actual joint boundary charge.
The step is zero when their debit exhausts the squared correlation. -/
def feedbackCredit (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) (τ : ℝ) : ℝ :=
  thresholdGain K g t (feedback K g I t Z w) τ

/-- One safely priced step on the original aggregate; every sign crossing
is covered by the threshold estimate before the cost saving is spent. -/
def adjusted (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) (τ : ℝ) (k : ℕ) : ℝ :=
  t k+thresholdStep K g t (feedback K g I t Z w) τ*feedback K g I t Z w k

theorem feedbackCredit_eq (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) (τ : ℝ) :
    feedbackCredit K g I t Z w τ=
      max ((∑ i∈I,w i*adverseCorrelation K g t (Z i)^2)-
        nearDebit K g t (feedback K g I t Z w) τ) 0 ^2/
          (4*farPrice K g t (feedback K g I t Z w) τ) := by
  simp only [feedbackCredit,thresholdGain,thresholdAvailable,adverseCorrelation_feedback_eq]

theorem feedbackCredit_nonneg (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) (τ : ℝ) :
    0≤feedbackCredit K g I t Z w τ := thresholdGain_nonneg _ _ _ _ _

/-- Near-period cancellation is imposed on the JOINED columns, not on
individual prime/count sectors. Exact cancellation removes the entire
near debit; approximate cancellation must retain it in feedbackCredit. -/
theorem nearDebit_feedback_zero (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) (τ : ℝ)
    (hnear : ∀ c∈K.image g,|blockTotal K g t c|≤τ→
      ∀ i∈I,blockTotal K g (Z i) c=0) :
    nearDebit K g t (feedback K g I t Z w) τ=0 := by
  unfold nearDebit
  apply Finset.sum_eq_zero
  intro c hc
  by_cases hn : |blockTotal K g t c|≤τ
  · have hz : blockTotal K g (feedback K g I t Z w) c=0 := by
      rw [blockTotal_feedback]
      exact Finset.sum_eq_zero (fun i hi=>by rw [hnear c hc hn i hi,mul_zero])
    simp [hz]
  · simp [if_neg hn]

/-- Once the near rows are annihilated jointly, ALL of the correlation
square enters the safe credit. This is a direct quantitative inequality,
not a claimed construction of a cofinal native projection. -/
theorem feedbackCredit_eq_of_near_zero (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) (τ : ℝ)
    (hw : ∀ i∈I,0≤w i)
    (hnear : ∀ c∈K.image g,|blockTotal K g t c|≤τ→
      ∀ i∈I,blockTotal K g (Z i) c=0) :
    feedbackCredit K g I t Z w τ=
      (∑ i∈I,w i*adverseCorrelation K g t (Z i)^2)^2/
        (4*farPrice K g t (feedback K g I t Z w) τ) := by
  rw [feedbackCredit_eq,nearDebit_feedback_zero K g I t Z w τ hnear,sub_zero,
    max_eq_left (Finset.sum_nonneg (fun i hi=>mul_nonneg (hw i hi) (sq_nonneg _)))]

/-- A positive, QUANTIFIED whole-cost saving, with no smallness or
vanishing premise on an individual label. This still needs the actual
joined debit to be smaller than the computed signed correlation. -/
theorem feedbackCredit_pos (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) (τ : ℝ)
    (hD : nearDebit K g t (feedback K g I t Z w) τ<
      ∑ i∈I,w i*adverseCorrelation K g t (Z i)^2)
    (hH : 0<farPrice K g t (feedback K g I t Z w) τ) :
    0<feedbackCredit K g I t Z w τ := by
  rw [feedbackCredit_eq]
  exact div_pos (sq_pos_of_pos ((sub_pos.mpr hD).trans_le (le_max_left _ _)))
    (mul_pos (by norm_num) hH)

theorem cost_adjusted_add_credit_le (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) {τ : ℝ} (hτ : 0≤τ) :
    blockCost K g (adjusted K g I t Z w τ)+feedbackCredit K g I t Z w τ≤
      blockCost K g t := by
  have h := thresholdGain_le_saving K g t (feedback K g I t Z w) hτ
  change feedbackCredit K g I t Z w τ≤blockCost K g t-
    blockCost K g (adjusted K g I t Z w τ) at h
  linarith only [h]

theorem sum_adjusted_eq (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (t : ℕ→ℝ) (Z : ℕ→ℕ→ℝ) (w : ℕ→ℝ) (τ : ℝ)
    (hZ : ∀ i∈I,(∑ k∈K,Z i k)=0) :
    (∑ k∈K,adjusted K g I t Z w τ k)=∑ k∈K,t k := by
  simp only [adjusted,Finset.sum_add_distrib,← Finset.mul_sum,
    sum_feedback_zero K g I t Z w hZ,mul_zero,add_zero]

/-- Recompute the WHOLE signed correlation and boundary after each step.
These are successive prices, not credits fitted to the old baseline. -/
def iterate (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℕ→ℝ) (w : ℕ→ℕ→ℝ) (τ : ℕ→ℝ) (t : ℕ→ℝ) : ℕ→ℕ→ℝ
  | 0=>t
  | r+1=>adjusted K g I (iterate K g I Z w τ t r) (Z r) (w r) (τ r)

/-- Sum successive guaranteed savings, each calculated on its own current
aggregate and boundary. None is reused from the original baseline. -/
def accumulatedCredit (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℕ→ℝ) (w : ℕ→ℕ→ℝ) (τ : ℕ→ℝ) (t : ℕ→ℝ) (r : ℕ) : ℝ :=
  ∑ s∈Finset.range r,feedbackCredit K g I (iterate K g I Z w τ t s) (Z s) (w s) (τ s)

theorem accumulatedCredit_nonneg (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℕ→ℝ) (w : ℕ→ℕ→ℝ) (τ : ℕ→ℝ) (t : ℕ→ℝ) (r : ℕ) :
    0≤accumulatedCredit K g I Z w τ t r :=
  Finset.sum_nonneg (fun _ _=>feedbackCredit_nonneg _ _ _ _ _ _ _)

theorem cost_iterate_add_credit_le (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℕ→ℝ) (w : ℕ→ℕ→ℝ) (τ : ℕ→ℝ) (t : ℕ→ℝ) (r : ℕ)
    (hτ : ∀ s,0≤τ s) :
    blockCost K g (iterate K g I Z w τ t r)+accumulatedCredit K g I Z w τ t r≤
      blockCost K g t := by
  induction r with
  | zero=>simp [iterate,accumulatedCredit]
  | succ r ih=>
    have h := cost_adjusted_add_credit_le K g I (iterate K g I Z w τ t r) (Z r) (w r) (hτ r)
    simp only [iterate,accumulatedCredit,Finset.sum_range_succ] at ⊢
    unfold accumulatedCredit at ih
    linarith only [h,ih]

theorem sum_iterate_eq (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℕ→ℝ) (w : ℕ→ℕ→ℝ) (τ : ℕ→ℝ) (t : ℕ→ℝ) (r : ℕ)
    (hZ : ∀ s i,i∈I→(∑ k∈K,Z s i k)=0) :
    (∑ k∈K,iterate K g I Z w τ t r k)=∑ k∈K,t k := by
  induction r with
  | zero=>rfl
  | succ r ih=>exact (sum_adjusted_eq K g I _ (Z r) (w r) (τ r) (hZ r)).trans ih

/-- Exact rational regression: the original zero period is charged, not
deleted. Joined feedback earns 16/41 after that charge. -/
theorem feedback_zero_face_regression :
    feedbackCredit (Finset.range 3) id (Finset.range 2)
      (fun k=>if k=0 then -1 else if k=1 then 0 else 1)
      (fun i k=>if i=0 then (if k=0 then 2 else if k=1 then -1 else -1)
        else (if k=0 then 1 else if k=1 then 1 else -2))
      (fun _=>1) 0=16/41 := by
  norm_num [feedbackCredit,thresholdGain,thresholdAvailable,feedback,
    adverseCorrelation,nearDebit,farPrice,blockTotal,Finset.sum_range_succ]

/-- Joining the two columns from the previous regression first makes
their originally zero-period responses cancel. The safe credit increases
to 1/2. No zero period or individual column has been dropped. -/
theorem feedback_joined_near_zero_regression :
    feedbackCredit (Finset.range 3) id (Finset.range 1)
      (fun k=>if k=0 then -1 else if k=1 then 0 else 1)
      (fun _ k=>if k=0 then 3 else if k=1 then 0 else -3)
      (fun _=>1) 0=1/2 := by
  norm_num [feedbackCredit,thresholdGain,thresholdAvailable,feedback,
    adverseCorrelation,nearDebit,farPrice,blockTotal,Finset.sum_range_succ]

/-- The current native increment, including every earlier null and the
independently paid original owner rows ONCE. -/
def nativeSeed (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ)
    (v w : ℕ→ℂ) (k : ℕ) : ℝ :=
  nativeStep u y j q a k-nativePaidIncrement u y j k-
    (weightedIncrement u y j v k+tailIncrement u y j w k)

/-- Exact closed-tail columns on the original native integer cutoff axis,
with arbitrary complex observations only on the null correction. -/
def nativeColumns (u y : ℝ) (j : ℕ) (V : ℕ→ℕ→ℂ) (i k : ℕ) : ℝ :=
  tailIncrement u y j (V i) k

theorem sum_nativeColumns_zero (u y : ℝ) (j i : ℕ) (V : ℕ→ℕ→ℂ) :
    (∑ k∈Finset.Icc 1 (nativeEndpoint u j),nativeColumns u y j V i k)=0 :=
  sum_tailIncrement_zero u y j (V i)

/-- Exact conditioning from the complete signed period column. A zero
column has weight zero by the real inverse convention. This is not an
energy bound for the carrier; it only selects an exact null coefficient. -/
def columnWeight (K : Finset ℕ) (g : ℕ→ℕ) (Z : ℕ→ℝ) : ℝ :=
  (∑ c∈K.image g,blockTotal K g Z c^2)⁻¹

theorem columnWeight_nonneg (K : Finset ℕ) (g : ℕ→ℕ) (Z : ℕ→ℝ) :
    0≤columnWeight K g Z := by
  exact inv_nonneg.mpr (Finset.sum_nonneg (fun _ _=>sq_nonneg _))

/-- The phase alignment acts only on a CERTIFIED zero correction of one
original label. The nonzero base carrier's observation remains unchanged. -/
def canonicalObservation (y : ℝ) (i n : ℕ) : ℂ :=
  if n=i then Complex.exp (Complex.I*(y*log n : ℝ)) else 0

/-- Condition each canonical label column by its actual complete-period
square norm, without assigning a norm cost to the original carrier. -/
def canonicalWeights (u y : ℝ) (j i : ℕ) : ℝ :=
  columnWeight (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y)
    (nativeColumns u y j (canonicalObservation y) i)

theorem canonicalWeights_nonneg (u y : ℝ) (j i : ℕ) :
    0≤canonicalWeights u y j i := columnWeight_nonneg _ _ _

/-- Mixing columns before the near-period projection remains an exact
literal closed-tail correction. Its original phase is inside W throughout;
there is no new independently paid count/owner or completion population. -/
theorem nativeColumns_mix (u y : ℝ) (j k : ℕ) (I : Finset ℕ)
    (V : ℕ→ℕ→ℂ) (b : ℕ→ℝ) :
    tailIncrement u y j (fun n=>∑ i∈I,(b i : ℂ)*V i n) k=
      ∑ i∈I,b i*nativeColumns u y j V i k := by
  have he (W : ℂ) (n : ℕ) :
      (W*(∑ i∈I,(b i : ℂ)*V i n)).re=∑ i∈I,b i*(W*V i n).re := by
    rw [Finset.mul_sum,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero]
    ring
  unfold nativeColumns tailIncrement
  dsimp only
  simp_rw [he,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Successive safe feedback credit in the same native cost branch, with
all previous nulls and the independently paid owner rows in its seed. -/
def nativeCredit (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ)
    (v w : ℕ→ℂ) (I : Finset ℕ) (V : ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℝ) (τ : ℕ→ℝ) (r : ℕ) : ℝ :=
  accumulatedCredit (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y) I
    (fun s=>nativeColumns u y j (V s)) weights τ (nativeSeed u y j q a v w) r

/-- A guaranteed signed saving in the SAME native whole floor. There
is no coefficient fitting, count truncation or new source error here;
the magnitude of the computed cofinal credit remains arithmetic. -/
theorem eventually_joined_floor_with_feedback {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) (v w : ℕ→ℕ→ℂ)
    (I : ℕ→Finset ℕ) (V : ℕ→ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℕ→ℝ) (τ : ℕ→ℕ→ℝ) (r : ℕ→ℕ)
    (hτ : ∀ j s,0≤τ j s) :
    ∀ᶠ j in atTop,
      -tailCost u y j (q j) (a j) (v j) (w j)+
        nativeCredit u y j (q j) (a j) (v j) (w j) (I j) (V j) (weights j) (τ j) (r j)-
        nativePaidBudget y j-ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  let seed j := nativeSeed u y j (q j) (a j) (v j) (w j)
  let final j := iterate (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y) (I j)
    (fun s=>nativeColumns u y j (V j s)) (weights j) (τ j) (seed j) (r j)
  let z j k := weightedIncrement u y j (v j) k+tailIncrement u y j (w j) k+
    (seed j k-final j k)
  have hz j : (∑ k∈Finset.Icc 1 (nativeEndpoint u j),z j k)=0 := by
    simp only [z,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      sum_weightedIncrement_zero,sum_tailIncrement_zero]
    rw [sum_iterate_eq _ _ _ _ _ _ _ _ (fun s i _=>sum_nativeColumns_zero u y j i (V j s))]
    ring
  filter_upwards [eventually_joined_floor_after_null hu hU hy q a z hz] with j hf
  have hc := cost_iterate_add_credit_le (Finset.Icc 1 (nativeEndpoint u j))
    (cutoffPeriod y) (I j) (fun s=>nativeColumns u y j (V j s))
      (weights j) (τ j) (seed j) (r j) (hτ j)
  have he : nullCost u y j (q j) (a j) (z j)=
      blockCost (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y) (final j) := by
    unfold nullCost
    congr 1
    funext k
    dsimp only [z,seed,nativeSeed]
    ring
  rw [he] at hf
  change blockCost _ _ (final j)+nativeCredit u y j (q j) (a j) (v j) (w j)
    (I j) (V j) (weights j) (τ j) (r j)≤tailCost u y j (q j) (a j) (v j) (w j) at hc
  linarith only [hf,hc]

/-- Retain the entire old price, and spend only SUCCESSIVE guaranteed
credits on the same tail-cost branch. No independent credit is added. -/
def feedbackPrice (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r₀ : ℝ)
    (v w : ℕ→ℂ) (I : Finset ℕ) (V : ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℝ) (τ : ℕ→ℝ) (r : ℕ) : ℝ :=
  min (tailPrice u y j q a r₀ v w)
    (tailCost u y j q a v w+nativePaidBudget y j-
      nativeCredit u y j q a v w I V weights τ r)

theorem feedbackPrice_le_previous (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r₀ : ℝ)
    (v w : ℕ→ℂ) (I : Finset ℕ) (V : ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℝ) (τ : ℕ→ℝ) (r : ℕ) :
    feedbackPrice u y j q a r₀ v w I V weights τ r≤tailPrice u y j q a r₀ v w :=
  min_le_left _ _

theorem feedbackPrice_zero_steps (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r₀ : ℝ)
    (v w : ℕ→ℂ) (I : Finset ℕ) (V : ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℝ) (τ : ℕ→ℝ) :
    feedbackPrice u y j q a r₀ v w I V weights τ 0=tailPrice u y j q a r₀ v w := by
  simp only [feedbackPrice,nativeCredit,accumulatedCredit,Finset.range_zero,
    Finset.sum_empty,sub_zero]
  exact min_eq_left (min_le_right _ _)

theorem eventually_joined_floor_with_feedback_price {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a r₀ : ℕ→ℝ) (v w : ℕ→ℕ→ℂ)
    (I : ℕ→Finset ℕ) (V : ℕ→ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℕ→ℝ) (τ : ℕ→ℕ→ℝ) (r : ℕ→ℕ)
    (hτ : ∀ j s,0≤τ j s) :
    ∀ᶠ j in atTop,
      -feedbackPrice u y j (q j) (a j) (r₀ j) (v j) (w j) (I j) (V j)
        (weights j) (τ j) (r j)-ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_with_feedback hu hU hy q a v w I V weights τ r hτ,
    eventually_joined_floor_with_closed_tail_credit hu hU hy q a r₀ v w] with j hnew hold
  unfold feedbackPrice
  simp only [min_def]
  split_ifs <;> linarith only [hnew,hold]

/-- One canonical rule across ALL original native squarefree labels.
There are no independently fitted label coefficients: adverse signed
correlations and complete-period column norms define every new coefficient.
The prior nulls/paid rows remain in the seed and are not charged again. -/
def canonicalPrice (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r₀ : ℝ)
    (v w : ℕ→ℂ) (τ : ℕ→ℝ) (r : ℕ) : ℝ :=
  feedbackPrice u y j q a r₀ v w ((nativeLabels u j).filter Squarefree)
    (fun _=>canonicalObservation y) (fun _=>canonicalWeights u y j) τ r

theorem canonicalPrice_le_previous (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r₀ : ℝ)
    (v w : ℕ→ℂ) (τ : ℕ→ℝ) (r : ℕ) :
    canonicalPrice u y j q a r₀ v w τ r≤tailPrice u y j q a r₀ v w :=
  feedbackPrice_le_previous u y j q a r₀ v w ((nativeLabels u j).filter Squarefree)
    (fun _=>canonicalObservation y) (fun _=>canonicalWeights u y j) τ r

theorem eventually_joined_floor_with_canonical_feedback {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a r₀ : ℕ→ℝ) (v w : ℕ→ℕ→ℂ)
    (τ : ℕ→ℕ→ℝ) (r : ℕ→ℕ) (hτ : ∀ j s,0≤τ j s) :
    ∀ᶠ j in atTop,
      -canonicalPrice u y j (q j) (a j) (r₀ j) (v j) (w j) (τ j) (r j)-
        ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  exact eventually_joined_floor_with_feedback_price hu hU hy q a r₀ v w
    (fun j=>(nativeLabels u j).filter Squarefree) (fun _ _=>canonicalObservation y)
      (fun j _=>canonicalWeights u y j) τ r hτ

/-- The actual cofinal arithmetic price premise is still explicit and
OPEN. The feedback rule itself supplies no zero-exclusion certificate. -/
theorem false_of_cofinal_feedback_price (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) (hsimple : analyticZetaZeroMultiplicity rho=1)
    (q : ℕ→Fin 6→ℝ) (a r₀ : ℕ→ℝ) (v w : ℕ→ℕ→ℂ)
    (I : ℕ→Finset ℕ) (V : ℕ→ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℕ→ℝ) (τ : ℕ→ℕ→ℝ) (r : ℕ→ℕ)
    (hτ : ∀ j s,0≤τ j s)
    (hcost : ∃ᶠ j in atTop,
      feedbackPrice (3/2-rho.1.re) rho.1.im j (q j) (a j) (r₀ j) (v j) (w j)
        (I j) (V j) (weights j) (τ j) (r j)≤399/5000) : False := by
  have hu : 1/2<3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
      (ZetaRieszComplexProjection.tendsto_nativeError rho hrho hexposed hU)
  have hf := eventually_joined_floor_with_feedback_price hu hU hy q a r₀ v w I V weights τ r hτ
  exact (hcost.and_eventually hf).mono (fun j hj=>by
    obtain ⟨hc,hf⟩ := hj
    linarith only [hc,hf])

end RiemannGaussian.ZetaRieszTailFeedbackFloor
