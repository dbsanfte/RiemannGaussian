/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTailFeedbackFloor

/-!
# Resolve the whole signed crossing cost by a weighted median

The complete-period feedback direction is unchanged. Its step is a weighted
median of the actual sign-crossing parameters, including the zero faces.
This minimizes the SAME whole-period price on the entire real line. In
particular it pays all crossings exactly rather than by a quadratic upper
bound. It neither changes the arithmetic carrier nor supplies an independent
cofinal numerical bound on its remaining signed price.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszTailMedianFloor
open ZetaRieszCutoffPeriodFloor ZetaRieszSignedNullGain
open ZetaRieszQuantitativeNullStep ZetaRieszTailFeedbackFloor
open ZetaRieszClosedTailFloor ZetaRieszWeightedZeroFloor ZetaRieszPaidIncidenceFloor
open ZetaRieszCofactorPhaseEnergy ZetaRieszPrimeCountFrequency

/-- Both sides of the weighted median retain their literal weights.
Coincident roots and zero weights require no tie-breaking assumption. -/
def IsWeightedMedian (C : Finset ℕ) (x w : ℕ→ℝ) (a : ℝ) : Prop :=
  2*(∑ i∈C.filter (fun i=>x i<a),w i)≤∑ i∈C,w i ∧
    2*(∑ i∈C.filter (fun i=>a<x i),w i)≤∑ i∈C,w i

/-- A finite nonnegative weighted population has a median at an actual
node, even when its total weight is zero. -/
theorem exists_weightedMedian (C : Finset ℕ) (x w : ℕ→ℝ)
    (hC : C.Nonempty) (hw : ∀ i∈C,0≤w i) :
    ∃ i∈C,IsWeightedMedian C x w (x i) := by
  let W := ∑ i∈C,w i
  have hW : 0≤W := Finset.sum_nonneg hw
  let E := C.filter (fun i=>W≤2*(∑ c∈C.filter (fun c=>x c≤x i),w c))
  have hE : E.Nonempty := by
    obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image C x hC
    refine ⟨i,Finset.mem_filter.mpr ⟨hi,?_⟩⟩
    have he : C.filter (fun c=>x c≤x i)=C :=
      Finset.filter_eq_self.mpr hmax
    rw [he]
    linarith only [hW]
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image E x hE
  obtain ⟨hiC,hiW⟩ := Finset.mem_filter.mp hi
  refine ⟨i,hiC,?_,?_⟩
  · by_contra hbad
    have hbig : W<2*(∑ c∈C.filter (fun c=>x c<x i),w c) := lt_of_not_ge hbad
    let B := C.filter (fun c=>x c<x i)
    have hB : B.Nonempty := by
      by_contra h
      have he : B=∅ := Finset.not_nonempty_iff_eq_empty.mp h
      change W<2*(∑ c∈B,w c) at hbig
      rw [he,Finset.sum_empty,mul_zero] at hbig
      linarith only [hbig,hW]
    obtain ⟨b,hb,hbmax⟩ := Finset.exists_max_image B x hB
    obtain ⟨hbC,hbi⟩ := Finset.mem_filter.mp hb
    have he : C.filter (fun c=>x c≤x b)=B := by
      ext c
      simp only [Finset.mem_filter,B]
      constructor
      · rintro ⟨hc,hcb⟩
        exact ⟨hc,hcb.trans_lt hbi⟩
      · rintro ⟨hc,hci⟩
        exact ⟨hc,hbmax c (Finset.mem_filter.mpr ⟨hc,hci⟩)⟩
    have hbE : b∈E := by
      apply Finset.mem_filter.mpr
      refine ⟨hbC,?_⟩
      rw [he]
      exact le_of_lt hbig
    linarith only [hmin b hbE,hbi]
  · have he := Finset.sum_filter_add_sum_filter_not C (fun c=>x c≤x i) w
    simp only [not_le] at he
    change (∑ c∈C.filter (fun c=>x c≤x i),w c)+
      (∑ c∈C.filter (fun c=>x i<x c),w c)=W at he
    linarith only [hiW,he]

private theorem abs_right_lower (a b x : ℝ) (hab : a≤b) :
    |a-x|+(b-a)*(if x≤a then 1 else -1)≤|b-x| := by
  by_cases hxa : x≤a
  · rw [if_pos hxa,abs_of_nonneg (sub_nonneg.mpr hxa),
      abs_of_nonneg (sub_nonneg.mpr (hxa.trans hab))]
    ring_nf
    exact le_rfl
  · rw [if_neg hxa]
    have h := abs_add_le (a-b) (b-x)
    rw [show a-b+(b-x)=a-x by ring,abs_of_nonpos (sub_nonpos.mpr hab)] at h
    linarith only [h]

private theorem abs_left_lower (a b x : ℝ) (hba : b≤a) :
    |a-x|+(a-b)*(if a≤x then 1 else -1)≤|b-x| := by
  by_cases hax : a≤x
  · rw [if_pos hax,abs_of_nonpos (sub_nonpos.mpr hax),
      abs_of_nonpos (sub_nonpos.mpr (hba.trans hax))]
    ring_nf
    exact le_rfl
  · rw [if_neg hax]
    have h := abs_add_le (a-b) (b-x)
    rw [show a-b+(b-x)=a-x by ring,abs_of_nonneg (sub_nonneg.mpr hba)] at h
    linarith only [h]

/-- A median globally minimizes the joined weighted absolute displacement.
This is a finite signed optimization theorem, not an arithmetic estimate
for the size of that minimum. -/
theorem weightedMedian_minimizes (C : Finset ℕ) (x w : ℕ→ℝ)
    (hw : ∀ i∈C,0≤w i) {a : ℝ} (ha : IsWeightedMedian C x w a) (b : ℝ) :
    (∑ i∈C,w i*|a-x i|)≤∑ i∈C,w i*|b-x i| := by
  by_cases hab : a≤b
  · have h := Finset.sum_le_sum (fun i hi=>
      mul_le_mul_of_nonneg_left (abs_right_lower a b (x i) hab) (hw i hi))
    have he : (∑ i∈C,w i*(if x i≤a then 1 else -1))=
        (∑ i∈C,w i)-2*(∑ i∈C.filter (fun i=>a<x i),w i) := by
      simp only [mul_ite,mul_one,mul_neg_one,Finset.sum_ite,
        Finset.sum_neg_distrib,not_le]
      have hh := Finset.sum_filter_add_sum_filter_not C (fun i=>x i≤a) w
      simp only [not_le] at hh
      linarith only [hh]
    have hp := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ha.2)
    simp only [mul_add,Finset.sum_add_distrib] at h
    have hfactor : (∑ i∈C,w i*((b-a)*(if x i≤a then 1 else -1)))=
        (b-a)*((∑ i∈C,w i)-2*(∑ i∈C.filter (fun i=>a<x i),w i)) := by
      rw [← he,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _=>by ring)
    rw [hfactor] at h
    linarith only [h,hp]
  · have hba := le_of_not_ge hab
    have h := Finset.sum_le_sum (fun i hi=>
      mul_le_mul_of_nonneg_left (abs_left_lower a b (x i) hba) (hw i hi))
    have he : (∑ i∈C,w i*(if a≤x i then 1 else -1))=
        (∑ i∈C,w i)-2*(∑ i∈C.filter (fun i=>x i<a),w i) := by
      simp only [mul_ite,mul_one,mul_neg_one,Finset.sum_ite,
        Finset.sum_neg_distrib,not_le]
      have hh := Finset.sum_filter_add_sum_filter_not C (fun i=>a≤x i) w
      simp only [not_le] at hh
      linarith only [hh]
    have hp := mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr ha.1)
    simp only [mul_add,Finset.sum_add_distrib] at h
    have hfactor : (∑ i∈C,w i*((a-b)*(if a≤x i then 1 else -1)))=
        (a-b)*((∑ i∈C,w i)-2*(∑ i∈C.filter (fun i=>x i<a),w i)) := by
      rw [← he,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _=>by ring)
    rw [hfactor] at h
    linarith only [h,hp]

/-- Choose a weighted median at an actual node. An empty population
has step zero. This is a mathematical rule with no fitted coefficient. -/
def weightedMedian (C : Finset ℕ) (x w : ℕ→ℝ) : ℝ :=
  if h : C.Nonempty ∧ ∀ i∈C,0≤w i then
    x (Classical.choose (exists_weightedMedian C x w h.1 h.2)) else 0

theorem weightedMedian_spec (C : Finset ℕ) (x w : ℕ→ℝ)
    (hw : ∀ i∈C,0≤w i) : IsWeightedMedian C x w (weightedMedian C x w) := by
  by_cases hC : C.Nonempty
  · rw [weightedMedian,dif_pos ⟨hC,hw⟩]
    exact (Classical.choose_spec (exists_weightedMedian C x w hC hw)).2
  · have he := Finset.not_nonempty_iff_eq_empty.mp hC
    simp [IsWeightedMedian,he]

/-- The actual zero of one complete-period affine increment. A zero
direction is totalized to root zero and receives zero weight below. -/
def crossingRoot (K : Finset ℕ) (g : ℕ→ℕ) (t v : ℕ→ℝ) (c : ℕ) : ℝ :=
  -blockTotal K g t c/blockTotal K g v c

/-- Complete-period change mass, including every originally zero face. -/
def crossingWeight (K : Finset ℕ) (g : ℕ→ℕ) (v : ℕ→ℝ) (c : ℕ) : ℝ :=
  |blockTotal K g v c|

/-- One mathematically defined weighted-median step on the whole direction. -/
def medianStep (K : Finset ℕ) (g : ℕ→ℕ) (t v : ℕ→ℝ) : ℝ :=
  weightedMedian (K.image g) (crossingRoot K g t v) (crossingWeight K g v)

/-- The same literal signed increment after its crossing-minimizing step. -/
def medianAdjusted (K : Finset ℕ) (g : ℕ→ℕ) (t v : ℕ→ℝ) (k : ℕ) : ℝ :=
  t k+medianStep K g t v*v k

private theorem abs_affine_eq (T V a : ℝ) :
    |T+a*V|=|V| * |a-(-T/V)|+(if V=0 then |T| else 0) := by
  by_cases hV : V=0
  · simp [hV]
  · rw [if_neg hV,add_zero]
    have he : T+a*V=V*(a-(-T/V)) := by field_simp; ring
    rw [he,abs_mul]

/-- This exact step minimizes the whole signed period price for EVERY
real step on the same null direction. Every zero face is included as a
crossing root with its full weight. -/
theorem medianAdjusted_minimizes (K : Finset ℕ) (g : ℕ→ℕ) (t v : ℕ→ℝ)
    (hv : (∑ k∈K,v k)=0) (a : ℝ) :
    blockCost K g (medianAdjusted K g t v)≤
      blockCost K g (fun k=>t k+a*v k) := by
  have hw c (_ : c∈K.image g) : 0≤crossingWeight K g v c := abs_nonneg _
  have hmed := weightedMedian_spec (K.image g) (crossingRoot K g t v)
    (crossingWeight K g v) hw
  have hm := weightedMedian_minimizes (K.image g) (crossingRoot K g t v)
    (crossingWeight K g v) hw hmed a
  have hb c b : blockTotal K g (fun k=>t k+b*v k) c=
      blockTotal K g t c+b*blockTotal K g v c := by
    simp only [blockTotal,Finset.sum_add_distrib,Finset.mul_sum]
  have hn b : (∑ c∈K.image g,|blockTotal K g (fun k=>t k+b*v k) c|)=
      (∑ c∈K.image g,crossingWeight K g v c*|b-crossingRoot K g t v c|)+
        (∑ c∈K.image g,if blockTotal K g v c=0 then |blockTotal K g t c| else 0) := by
    simp only [hb,abs_affine_eq,Finset.sum_add_distrib,crossingWeight,crossingRoot]
  have hs (b : ℝ) : (∑ k ∈ K, (t k + b * v k))=(∑ k ∈ K, t k) := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,hv,mul_zero,add_zero]
  unfold medianAdjusted
  rw [blockCost_eq,blockCost_eq,hn,hn,hs,hs]
  change (∑ _∈_,_*|medianStep K g t v-_|)≤∑ _∈_,_*|a-_| at hm
  linarith only [hm]

theorem sum_medianAdjusted_eq (K : Finset ℕ) (g : ℕ→ℕ) (t v : ℕ→ℝ)
    (hv : (∑ k∈K,v k)=0) :
    (∑ k∈K,medianAdjusted K g t v k)=∑ k∈K,t k := by
  simp only [medianAdjusted,Finset.sum_add_distrib,← Finset.mul_sum,hv,mul_zero,add_zero]

/-- The exact actual saving. This is funded by one joined baseline cost;
it is not the sum of independent per-period or per-column allowances. -/
def medianCredit (K : Finset ℕ) (g : ℕ→ℕ) (t v : ℕ→ℝ) : ℝ :=
  blockCost K g t-blockCost K g (medianAdjusted K g t v)

theorem medianCredit_nonneg (K : Finset ℕ) (g : ℕ→ℕ) (t v : ℕ→ℝ)
    (hv : (∑ k∈K,v k)=0) : 0 ≤ medianCredit K g t v := by
  have h := medianAdjusted_minimizes K g t v hv 0
  simp only [zero_mul,add_zero] at h
  exact sub_nonneg.mpr h

/-- Exact joined signed correlation minus ALL actual crossings. No
near/far envelope or zero-face exemption enters the final credit. -/
theorem medianCredit_eq_crossing (K : Finset ℕ) (g : ℕ→ℕ) (t v : ℕ→ℝ) :
    medianCredit K g t v=medianStep K g t v*adverseCorrelation K g t v-
      crossingCost K g t v (medianStep K g t v) := by
  unfold medianCredit medianAdjusted
  rw [blockCost_shift_eq]
  ring

theorem median_floor (K : Finset ℕ) (g : ℕ→ℕ) (t v : ℕ→ℝ)
    (hv : (∑ k∈K,v k)=0) :
    -blockCost K g t+medianCredit K g t v≤∑ k∈K,t k := by
  have h := block_floor K g (medianAdjusted K g t v)
  rw [sum_medianAdjusted_eq K g t v hv] at h
  unfold medianCredit
  linarith only [h]

/-- An actual line saving is always retained, regardless of which
threshold would have been used to price it. -/
theorem medianCredit_ge_stepGain (K : Finset ℕ) (g : ℕ→ℕ) (t v : ℕ→ℝ)
    (hv : (∑ k∈K,v k)=0) (a : ℝ) :
    blockCost K g t-blockCost K g (fun k=>t k+a*v k) ≤ medianCredit K g t v := by
  unfold medianCredit
  linarith only [medianAdjusted_minimizes K g t v hv a]

/-- The zero-face regression has true gain4/5, compared with the
previous quadratic guarantee16/41. Its middle zero face is retained. -/
theorem median_zero_face_regression :
    medianCredit (Finset.range 3) id
      (fun k=>if k=0 then -1 else if k=1 then 0 else 1)
      (fun k=>if k=0 then 5 else if k=1 then -1 else -4)=4/5 := by
  let t : ℕ→ℝ := fun k=>if k=0 then -1 else if k=1 then 0 else 1
  let v : ℕ→ℝ := fun k=>if k=0 then 5 else if k=1 then -1 else -4
  have hv : (∑ k∈Finset.range 3,v k)=0 := by
    norm_num [v,Finset.sum_range_succ]
  have hcost (a : ℝ) : blockCost (Finset.range 3) id (fun k=>t k+a*v k)=
      max (1-5*a) 0+max a 0+max (4*a-1) 0 := by
    norm_num [blockCost,blockTotal,t,v,Finset.sum_range_succ,Finset.filter_insert]
    ring_nf
  have hbase : blockCost (Finset.range 3) id t=1 := by
    have hb := hcost 0
    norm_num at hb
    exact hb
  have hchoice := medianAdjusted_minimizes (Finset.range 3) id t v hv (1/5)
  rw [hcost] at hchoice
  norm_num at hchoice
  have hlower (a : ℝ) : 1/5≤blockCost (Finset.range 3) id (fun k=>t k+a*v k) := by
    rw [hcost]
    have h1 := le_max_left (1-5*a) 0
    have ha := le_max_left a 0
    have h0 := le_max_right (1-5*a) 0
    have h4 := le_max_right (4*a-1) 0
    by_cases hh : a≤1/5 <;> linarith only [h1,ha,h0,h4,hh]
  have he : blockCost (Finset.range 3) id (medianAdjusted (Finset.range 3) id t v)=1/5 :=
    le_antisymm hchoice (hlower (medianStep (Finset.range 3) id t v))
  change medianCredit (Finset.range 3) id t v=4/5
  rw [medianCredit,hbase,he]
  norm_num

/-- Once the columns are joined to annihilate the zero face, the exact
crossing step earns the entire unit cost, instead of the old guarantee1/2. -/
theorem median_joined_zero_regression :
    medianCredit (Finset.range 3) id
      (fun k=>if k=0 then -1 else if k=1 then 0 else 1)
      (fun k=>if k=0 then 3 else if k=1 then 0 else -3)=1 := by
  let t : ℕ→ℝ := fun k=>if k=0 then -1 else if k=1 then 0 else 1
  let v : ℕ→ℝ := fun k=>if k=0 then 3 else if k=1 then 0 else -3
  have hv : (∑ k∈Finset.range 3,v k)=0 := by
    norm_num [v,Finset.sum_range_succ]
  have hbase : blockCost (Finset.range 3) id t=1 := by
    norm_num [blockCost,blockTotal,t,Finset.sum_range_succ,Finset.filter_insert]
  have hzero : (fun k=>t k+(1/3)*v k)=(0 : ℕ→ℝ) := by
    funext k
    dsimp [t,v]
    split_ifs <;> norm_num
  have hmin := medianAdjusted_minimizes (Finset.range 3) id t v hv (1/3)
  rw [hzero] at hmin
  have he : blockCost (Finset.range 3) id (medianAdjusted (Finset.range 3) id t v)=0 := by
    apply le_antisymm
    · simpa [blockCost,blockTotal] using hmin
    · exact Finset.sum_nonneg (fun _ _=>le_max_right _ _)
  change medianCredit (Finset.range 3) id t v=1
  rw [medianCredit,hbase,he,sub_zero]

/-- Along the same whole signed feedback direction, the exact median
earns at least EVERY previously paid quadratic threshold saving. This is
an arithmetic cost comparison, with no native credit-size premise. -/
theorem medianCredit_ge_feedbackCredit (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℝ) (weights : ℕ→ℝ) (t : ℕ→ℝ) {τ : ℝ} (hτ : 0≤τ)
    (hZ : ∀ i∈I,(∑ k∈K,Z i k)=0) :
    feedbackCredit K g I t Z weights τ≤
      medianCredit K g t (feedback K g I t Z weights) := by
  have hv := sum_feedback_zero K g I t Z weights hZ
  have hmin := medianAdjusted_minimizes K g t (feedback K g I t Z weights) hv
    (thresholdStep K g t (feedback K g I t Z weights) τ)
  have hpaid := cost_adjusted_add_credit_le K g I t Z weights hτ
  change blockCost K g (fun k=>t k+
    thresholdStep K g t (feedback K g I t Z weights) τ*
      feedback K g I t Z weights k)+feedbackCredit K g I t Z weights τ≤
        blockCost K g t at hpaid
  unfold medianCredit
  linarith only [hmin,hpaid]

/-- Sum all columns before choosing the optimal crossing step. -/
def medianFeedback (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℝ) (weights : ℕ→ℝ) (t : ℕ→ℝ) : ℕ→ℝ :=
  medianAdjusted K g t (feedback K g I t Z weights)

/-- Recompute the whole signed feedback and its median at every stage.
Column mixtures may change; no count or period is priced separately. -/
def medianIterate (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℕ→ℝ) (weights : ℕ→ℕ→ℝ) (t : ℕ→ℝ) : ℕ→ℕ→ℝ
  | 0=>t
  | r+1=>medianFeedback K g I (Z r) (weights r) (medianIterate K g I Z weights t r)

/-- Sum successive actual rebates, each funded by its own current cost. -/
def medianAccumulated (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℕ→ℝ) (weights : ℕ→ℕ→ℝ) (t : ℕ→ℝ) (r : ℕ) : ℝ :=
  ∑ s∈Finset.range r,medianCredit K g (medianIterate K g I Z weights t s)
    (feedback K g I (medianIterate K g I Z weights t s) (Z s) (weights s))

/-- Successive actual savings telescope exactly. No stage reuses the
old baseline or spends an independently fitted positive credit. -/
theorem cost_medianIterate_add_credit_eq (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℕ→ℝ) (weights : ℕ→ℕ→ℝ) (t : ℕ→ℝ) (r : ℕ) :
    blockCost K g (medianIterate K g I Z weights t r)+
      medianAccumulated K g I Z weights t r=blockCost K g t := by
  induction r with
  | zero=>simp [medianIterate,medianAccumulated]
  | succ r hr=>
    rw [medianAccumulated,Finset.sum_range_succ]
    change blockCost K g (medianFeedback K g I (Z r) (weights r)
      (medianIterate K g I Z weights t r))+(medianAccumulated K g I Z weights t r+
        medianCredit K g (medianIterate K g I Z weights t r)
          (feedback K g I (medianIterate K g I Z weights t r) (Z r) (weights r)))=
            blockCost K g t
    unfold medianFeedback medianCredit
    linarith only [hr]

theorem medianAccumulated_nonneg (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℕ→ℝ) (weights : ℕ→ℕ→ℝ) (t : ℕ→ℝ) (r : ℕ)
    (hZ : ∀ s i,i∈I→(∑ k∈K,Z s i k)=0) :
    0 ≤ medianAccumulated K g I Z weights t r := by
  apply Finset.sum_nonneg
  intro s _
  exact medianCredit_nonneg K g _ _
    (sum_feedback_zero K g I _ (Z s) (weights s) (hZ s))

theorem sum_medianIterate_eq (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℕ→ℝ) (weights : ℕ→ℕ→ℝ) (t : ℕ→ℝ) (r : ℕ)
    (hZ : ∀ s i,i∈I→(∑ k∈K,Z s i k)=0) :
    (∑ k∈K,medianIterate K g I Z weights t r k)=∑ k∈K,t k := by
  induction r with
  | zero=>rfl
  | succ r hr=>
    change (∑ k∈K,medianAdjusted K g (medianIterate K g I Z weights t r)
      (feedback K g I (medianIterate K g I Z weights t r) (Z r) (weights r)) k)=_
    rw [sum_medianAdjusted_eq K g _ _
      (sum_feedback_zero K g I _ (Z r) (weights r) (hZ r)),hr]

/-- Even optimal successive null steps cannot remove the adverse part
of the unchanged total. This identifies the actual remaining arithmetic
obligation rather than promising that more steps necessarily close it. -/
theorem medianAccumulated_le_excess (K : Finset ℕ) (g : ℕ→ℕ) (I : Finset ℕ)
    (Z : ℕ→ℕ→ℕ→ℝ) (weights : ℕ→ℕ→ℝ) (t : ℕ→ℝ) (r : ℕ)
    (hZ : ∀ s i,i∈I→(∑ k∈K,Z s i k)=0) :
    medianAccumulated K g I Z weights t r≤
      blockCost K g t-max (-(∑ k∈K,t k)) 0 := by
  let final := medianIterate K g I Z weights t r
  have hfloor := block_floor K g final
  rw [sum_medianIterate_eq K g I Z weights t r hZ] at hfloor
  have hnonneg : 0≤blockCost K g final :=
    Finset.sum_nonneg (fun _ _=>le_max_right _ _)
  have hmax : max (-(∑ k∈K,t k)) 0≤blockCost K g final :=
    max_le (by linarith only [hfloor]) hnonneg
  have hpaid := cost_medianIterate_add_credit_eq K g I Z weights t r
  linarith only [hpaid,hmax]

/-- Successive exact crossing savings on the current native seed. -/
def nativeMedianCredit (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a : ℝ)
    (v w : ℕ→ℂ) (I : Finset ℕ) (V : ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℝ) (r : ℕ) : ℝ :=
  medianAccumulated (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y) I
    (fun s=>nativeColumns u y j (V s)) weights (nativeSeed u y j q a v w) r

/-- A direct signed inequality for the WHOLE unchanged physical carrier.
The exact crossing rebate replaces the conservative step price. All
counts, masks, phases, original nulls and distinct paid rows remain.
The numerical cofinal size of the resulting price remains open. -/
theorem eventually_joined_floor_with_median {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) (v w : ℕ→ℕ→ℂ)
    (I : ℕ→Finset ℕ) (V : ℕ→ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℕ→ℝ) (r : ℕ→ℕ) :
    ∀ᶠ j in atTop,
      -tailCost u y j (q j) (a j) (v j) (w j)+
        nativeMedianCredit u y j (q j) (a j) (v j) (w j) (I j) (V j) (weights j) (r j)-
        nativePaidBudget y j-ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  let seed j := nativeSeed u y j (q j) (a j) (v j) (w j)
  let final j := medianIterate (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y) (I j)
    (fun s=>nativeColumns u y j (V j s)) (weights j) (seed j) (r j)
  let z j k := weightedIncrement u y j (v j) k+tailIncrement u y j (w j) k+
    (seed j k-final j k)
  have hz j : (∑ k∈Finset.Icc 1 (nativeEndpoint u j),z j k)=0 := by
    simp only [z,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      sum_weightedIncrement_zero,sum_tailIncrement_zero]
    rw [sum_medianIterate_eq _ _ _ _ _ _ _
      (fun s i _=>sum_nativeColumns_zero u y j i (V j s))]
    ring
  filter_upwards [eventually_joined_floor_after_null hu hU hy q a z hz] with j hf
  have hc := cost_medianIterate_add_credit_eq (Finset.Icc 1 (nativeEndpoint u j))
    (cutoffPeriod y) (I j) (fun s=>nativeColumns u y j (V j s))
      (weights j) (seed j) (r j)
  have he : nullCost u y j (q j) (a j) (z j)=
      blockCost (Finset.Icc 1 (nativeEndpoint u j)) (cutoffPeriod y) (final j) := by
    unfold nullCost
    congr 1
    funext k
    dsimp only [z,seed,nativeSeed]
    ring
  rw [he] at hf
  change blockCost _ _ (final j)+nativeMedianCredit u y j (q j) (a j) (v j) (w j)
    (I j) (V j) (weights j) (r j)=tailCost u y j (q j) (a j) (v j) (w j) at hc
  linarith only [hf,hc]

/-- Retain the ENTIRE previous feedback inequality as an alternative.
Different successive trajectories are not asserted to dominate one another.
Credits are spent solely on their own exact native cost branch. -/
def medianPrice (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r₀ : ℝ)
    (v w : ℕ→ℂ) (I : Finset ℕ) (V : ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℝ) (τ : ℕ→ℝ) (r : ℕ) : ℝ :=
  min (feedbackPrice u y j q a r₀ v w I V weights τ r)
    (tailCost u y j q a v w+nativePaidBudget y j-
      nativeMedianCredit u y j q a v w I V weights r)

theorem medianPrice_le_previous (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r₀ : ℝ)
    (v w : ℕ→ℂ) (I : Finset ℕ) (V : ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℝ) (τ : ℕ→ℝ) (r : ℕ) :
    medianPrice u y j q a r₀ v w I V weights τ r≤
      feedbackPrice u y j q a r₀ v w I V weights τ r := min_le_left _ _

theorem eventually_joined_floor_with_median_price {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a r₀ : ℕ→ℝ) (v w : ℕ→ℕ→ℂ)
    (I : ℕ→Finset ℕ) (V : ℕ→ℕ→ℕ→ℕ→ℂ)
    (weights : ℕ→ℕ→ℕ→ℝ) (τ : ℕ→ℕ→ℝ) (r : ℕ→ℕ)
    (hτ : ∀ j s,0≤τ j s) :
    ∀ᶠ j in atTop,
      -medianPrice u y j (q j) (a j) (r₀ j) (v j) (w j) (I j) (V j)
        (weights j) (τ j) (r j)-ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_with_median hu hU hy q a v w I V weights r,
    eventually_joined_floor_with_feedback_price hu hU hy q a r₀ v w I V weights τ r hτ]
    with j hnew hold
  unfold medianPrice
  simp only [min_def]
  split_ifs <;> linarith only [hnew,hold]

/-- The canonical column rule applies to EVERY native squarefree label.
There is no new per-label fit or count-sector pricing. -/
def canonicalMedianPrice (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r₀ : ℝ)
    (v w : ℕ→ℂ) (τ : ℕ→ℝ) (r : ℕ) : ℝ :=
  medianPrice u y j q a r₀ v w ((nativeLabels u j).filter Squarefree)
    (fun _=>canonicalObservation y) (fun _=>canonicalWeights u y j) τ r

theorem canonicalMedianPrice_le_previous (u y : ℝ) (j : ℕ) (q : Fin 6→ℝ) (a r₀ : ℝ)
    (v w : ℕ→ℂ) (τ : ℕ→ℝ) (r : ℕ) :
    canonicalMedianPrice u y j q a r₀ v w τ r≤canonicalPrice u y j q a r₀ v w τ r :=
  medianPrice_le_previous u y j q a r₀ v w ((nativeLabels u j).filter Squarefree)
    (fun _=>canonicalObservation y) (fun _=>canonicalWeights u y j) τ r

theorem eventually_joined_floor_with_canonical_median {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (q : ℕ→Fin 6→ℝ) (a r₀ : ℕ→ℝ) (v w : ℕ→ℕ→ℂ)
    (τ : ℕ→ℕ→ℝ) (r : ℕ→ℕ) (hτ : ∀ j s,0≤τ j s) :
    ∀ᶠ j in atTop,
      -canonicalMedianPrice u y j (q j) (a j) (r₀ j) (v j) (w j) (τ j) (r j)-
        ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  exact eventually_joined_floor_with_median_price hu hU hy q a r₀ v w
    (fun j=>(nativeLabels u j).filter Squarefree) (fun _ _=>canonicalObservation y)
      (fun j _=>canonicalWeights u y j) τ r hτ

end RiemannGaussian.ZetaRieszTailMedianFloor
