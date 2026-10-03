/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszQuantitativeNullStep

/-!
# Joined log, log-square and cubic corrections in the actual whole floor

The four existing log/log-square null directions and both cubic directions
are joined BEFORE any cutoff crossing is charged. The original imaginary
tilt is fixed; every new coefficient multiplies an exact finite null.
The quantitative threshold gain transfers to the same `joinedPhysical`
carrier with the same `nativeError`. This does not prove its cofinal size.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszJointNullCredit
open ZetaRieszCutoffPeriodFloor ZetaRieszSignedNullGain
open ZetaRieszQuantitativeNullStep ZetaRieszComplexProjection
open ZetaRieszCofactorPhaseEnergy ZetaRieszPrimeCountFrequency
open ZetaRieszJointAllocation ZetaRieszAnnulusJoint ZetaRieszParityPacket
open ZetaRieszJointPrimeEnergy

/-- The four non-cubic coefficients, with ZERO imaginary tilt. -/
def nullParameters (q : Fin 6 → ℝ) : Fin 5 → ℝ := ![0,q 0,q 1,q 2,q 3]

/-- The full signed joint direction. Count three participates in log and
log-square only; all higher counts receive the SAME two cubic coefficients.
No population mask or finite endpoint changes. -/
def jointIncrement (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (q : Fin 6 → ℝ) (k : ℕ) : ℝ :=
  ZetaRieszComplexNullFloor.increment X N S W L (nullParameters q) k-
    ZetaRieszComplexNullFloor.increment X N S W L 0 k+
      cubicIncrement X N S W (q 4) (q 5) k

/-- Every moving joint vector is an exact null on the literal support.
In particular, its low-cutoff/zero-face debits must be joined, not added. -/
theorem sum_jointIncrement_zero (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (q : Fin 6 → ℝ) (hs : ∀ n ∈ S,Squarefree n)
    (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card) (hX : ∀ n ∈ S,n ≤ X) :
    (∑ k ∈ Finset.Icc 1 X,jointIncrement X N S W L q k)=0 := by
  simp only [jointIncrement,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [ZetaRieszComplexNullFloor.sum_increment_eq X N S W L hs hc hX,
    ZetaRieszComplexNullFloor.sum_increment_eq X N S W L hs hc hX,
    sum_cubicIncrement_eq_zero X N S W hs hX]
  simp [nullParameters]

/-- Scaling uses one WHOLE joint direction, never separately priced
logarithmic and cubic credits. The original tilt remains untouched. -/
theorem jointIncrement_scaled (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (q : Fin 6 → ℝ) (a : ℝ) (k : ℕ) :
    jointIncrement X N S W L (fun i => a*q i) k=
      a*jointIncrement X N S W L q k := by
  dsimp [jointIncrement,nullParameters,ZetaRieszComplexNullFloor.increment,cubicIncrement]
  ring

/-- All six corrections join linearly before their crossing debit is
computed. In particular a cubic/logarithmic boundary can cancel exactly. -/
theorem jointIncrement_add (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (q r : Fin 6 → ℝ) (k : ℕ) :
    jointIncrement X N S W L (fun i => q i+r i) k=
      jointIncrement X N S W L q k+jointIncrement X N S W L r k := by
  dsimp [jointIncrement,nullParameters,ZetaRieszComplexNullFloor.increment,cubicIncrement]
  ring

private theorem positivePart_eq (x : ℝ) : max x 0=(|x|+x)/2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx,abs_of_nonneg hx]
    ring
  · rw [max_eq_right (le_of_not_ge hx),abs_of_neg (lt_of_not_ge hx)]
    ring

/-- Exact cancellation of the ENTIRE near-block charge. The absolute
values measure already-joined null increments, not individual prime terms.
No extra credit is spent: this is part of the same threshold price. -/
theorem nearDebit_overlap_eq (K : Finset ℕ) (g : ℕ → ℕ)
    (t v w : ℕ → ℝ) (τ : ℝ) :
    nearDebit K g t v τ+nearDebit K g t w τ-
      nearDebit K g t (fun k => v k+w k) τ=
    ∑ c ∈ K.image g,if |blockTotal K g t c| ≤ τ then
      (|blockTotal K g v c|+|blockTotal K g w c|-
        |blockTotal K g v c+blockTotal K g w c|)/2 else 0 := by
  have hb c : blockTotal K g (fun k => v k+w k) c=
      blockTotal K g v c+blockTotal K g w c := by
    simp only [blockTotal,Finset.sum_add_distrib]
  unfold nearDebit
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [hb]
  by_cases hn : |blockTotal K g t c| ≤ τ
  · simp only [if_pos hn]
    by_cases ht : blockTotal K g t c < 0
    · simp only [if_pos ht,positivePart_eq]
      ring
    · simp only [if_neg ht,positivePart_eq,abs_neg]
      ring
  · simp only [if_neg hn,zero_add,sub_zero]

/-- Combining corrections never increases their near-face charge beyond
the separately charged sum. Opposite increments can strictly reduce it. -/
theorem nearDebit_add_le (K : Finset ℕ) (g : ℕ → ℕ)
    (t v w : ℕ → ℝ) (τ : ℝ) :
    nearDebit K g t (fun k => v k+w k) τ ≤
      nearDebit K g t v τ+nearDebit K g t w τ := by
  have hp : 0 ≤ ∑ c ∈ K.image g,if |blockTotal K g t c| ≤ τ then
      (|blockTotal K g v c|+|blockTotal K g w c|-
        |blockTotal K g v c+blockTotal K g w c|)/2 else 0 := by
    apply Finset.sum_nonneg
    intro c _
    split_ifs
    · exact div_nonneg (sub_nonneg.mpr (abs_add_le _ _)) (by norm_num)
    · exact le_rfl
  rw [← nearDebit_overlap_eq] at hp
  linarith only [hp]

/-- The adverse correlation is signed and exactly additive. Any new
joint benefit comes from cancelling the joined crossing debit, not from
counting the same signed correlation twice. -/
theorem adverseCorrelation_add (K : Finset ℕ) (g : ℕ → ℕ)
    (t v w : ℕ → ℝ) :
    adverseCorrelation K g t (fun k => v k+w k)=
      adverseCorrelation K g t v+adverseCorrelation K g t w := by
  unfold adverseCorrelation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · simp only [blockTotal,Finset.sum_add_distrib]
  · exact (zero_add _).symm

/-- A lower signed marginal for the joint correction, before any positive
part. This can be positive even when both individual marginals are not. -/
theorem joint_available_lower (K : Finset ℕ) (g : ℕ → ℕ)
    (t v w : ℕ → ℝ) (τ : ℝ) :
    (adverseCorrelation K g t v-nearDebit K g t v τ)+
      (adverseCorrelation K g t w-nearDebit K g t w τ) ≤
        adverseCorrelation K g t (fun k => v k+w k)-
          nearDebit K g t (fun k => v k+w k) τ := by
  rw [adverseCorrelation_add]
  have h := nearDebit_add_le K g t v w τ
  linarith only [h]

/-- Restricting to the cubic plane recovers the existing literal direction.
The larger correction space therefore retains every previous cubic choice. -/
theorem jointIncrement_cubic (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L a b : ℝ)
    (k : ℕ) :
    jointIncrement X N S W L ![0,0,0,0,a,b] k=cubicIncrement X N S W a b k := by
  have hp : nullParameters ![0,0,0,0,a,b]=(0 : Fin 5 → ℝ) := by
    ext i
    fin_cases i <;> simp [nullParameters]
  rw [jointIncrement,hp,sub_self,zero_add]
  rfl

/-- The ACTUAL whole-period cost of a proposed six-direction step. This
retains every crossed block instead of replacing it by a quadratic price. -/
def jointCost (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) : ℝ :=
  blockCost (Finset.Icc 1 X) g (fun k =>
    ZetaRieszComplexNullFloor.increment X N S W L
      (ZetaRieszComplexNullFloor.bestParameters X N S W L g B) k+
        jointIncrement X N S W L q k)

/-- Use an exact improvement only when it is positive. The old step is
always available, so a proposal can never worsen the paid floor. -/
def jointCredit (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) : ℝ :=
  max (ZetaRieszComplexNullFloor.bestCost X N S W L g B-
    jointCost X N S W L g B q) 0

/-- Exact signed correlation minus the FULL crossing cost. No near/far
relaxation or coordinatewise credit enters this identity. -/
theorem jointCredit_eq (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) :
    jointCredit X N S W L g B q=
      max (adverseCorrelation (Finset.Icc 1 X) g
        (ZetaRieszComplexNullFloor.increment X N S W L
          (ZetaRieszComplexNullFloor.bestParameters X N S W L g B))
        (jointIncrement X N S W L q)-
        crossingCost (Finset.Icc 1 X) g
          (ZetaRieszComplexNullFloor.increment X N S W L
            (ZetaRieszComplexNullFloor.bestParameters X N S W L g B))
          (jointIncrement X N S W L q) 1) 0 := by
  have he := blockCost_shift_eq (Finset.Icc 1 X) g
    (ZetaRieszComplexNullFloor.increment X N S W L
      (ZetaRieszComplexNullFloor.bestParameters X N S W L g B))
    (jointIncrement X N S W L q) 1
  simp only [one_mul] at he
  unfold jointCredit jointCost ZetaRieszComplexNullFloor.bestCost
    ZetaRieszComplexNullFloor.cost
  rw [he]
  congr 1
  ring

theorem jointCredit_nonneg (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) :
    0 ≤ jointCredit X N S W L g B q := le_max_right _ _

/-- The exact credit is funded by the SAME baseline cost. -/
theorem jointCredit_le_cost (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) :
    jointCredit X N S W L g B q ≤
      ZetaRieszComplexNullFloor.bestCost X N S W L g B := by
  have hc : 0 ≤ jointCost X N S W L g B q := by
    unfold jointCost blockCost
    exact Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  unfold jointCredit
  exact max_le (by linarith only [hc])
    (ZetaRieszComplexNullFloor.bestCost_nonneg X N S W L g B)

/-- An exact dual orthogonal to EVERY correction column bounds ALL real
coefficient vectors, without a search box. This diagnoses an obstruction
in a finite joined matrix; it does not assert one for the native population. -/
theorem signed_cost_lower_of_exact_dual (C I : Finset ℕ) (t h a : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (hh : ∀ c ∈ C,0 ≤ h c ∧ h c ≤ 1)
    (hnull : ∀ i ∈ I,(∑ c ∈ C,h c*v i c)=0) :
    -(∑ c ∈ C,h c*t c) ≤
      ∑ c ∈ C,max (-(t c+∑ i ∈ I,a i*v i c)) 0 := by
  have ha : ∀ i ∈ I,|a i| ≤ ∑ k ∈ I,|a k| := fun i hi =>
    Finset.single_le_sum (f := fun k => |a k|) (fun k _ => abs_nonneg (a k)) hi
  have hf := boxCost_lower_bound C I t h a v (∑ k ∈ I,|a k|) hh ha
  have hz : (∑ i ∈ I,|∑ c ∈ C,h c*v i c|)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hnull i hi,abs_zero]
  simpa only [hz,mul_zero,sub_zero] using hf

/-- The actual step pays at least its earlier threshold guarantee. The
rescaling is important: compare credits at the SAME proposed step. -/
theorem thresholdGain_le_jointCredit (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (L : ℝ) (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    let t := ZetaRieszComplexNullFloor.increment X N S W L
      (ZetaRieszComplexNullFloor.bestParameters X N S W L g B)
    let v := jointIncrement X N S W L q
    thresholdGain (Finset.Icc 1 X) g t v τ ≤
      jointCredit X N S W L g B
        (fun i => thresholdStep (Finset.Icc 1 X) g t v τ*q i) := by
  dsimp only
  have hg := thresholdGain_le_saving (Finset.Icc 1 X) g
    (ZetaRieszComplexNullFloor.increment X N S W L
      (ZetaRieszComplexNullFloor.bestParameters X N S W L g B))
    (jointIncrement X N S W L q) hτ
  unfold jointCredit jointCost
  simp only [jointIncrement_scaled]
  exact hg.trans (le_max_left _ _)

/-- Full exact crossing payment yields a stronger finite floor than its
near/far relaxation. The old imaginary tilt and its price are unchanged. -/
theorem prefix_floor_with_joint_credit (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (L : ℝ) (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ)
    (hs : ∀ n ∈ S,Squarefree n) (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card)
    (hX : ∀ n ∈ S,n ≤ X) :
    -ZetaRieszComplexNullFloor.bestCost X N S W L g B+
      jointCredit X N S W L g B q-
        |B| * |(complexPrefix X S W (correctedProfile X L 1 0)).im| ≤
          (complexPrefix X S W (correctedProfile X L 1 0)).re := by
  let p := ZetaRieszComplexNullFloor.bestParameters X N S W L g B
  have hf := block_floor (Finset.Icc 1 X) g (fun k =>
    ZetaRieszComplexNullFloor.increment X N S W L p k+jointIncrement X N S W L q k)
  rw [Finset.sum_add_distrib,sum_jointIncrement_zero X N S W L q hs hc hX,add_zero,
    ZetaRieszComplexNullFloor.sum_increment_eq X N S W L hs hc hX] at hf
  have hm := mul_le_mul_of_nonneg_right
    (ZetaRieszComplexNullFloor.bestParameters_bound X N S W L g B 0)
    (abs_nonneg (complexPrefix X S W (correctedProfile X L 1 0)).im)
  rw [← abs_mul] at hm
  have hl := neg_abs_le (p 0*(complexPrefix X S W (correctedProfile X L 1 0)).im)
  change -jointCost X N S W L g B q ≤ _ at hf
  change |p 0*(complexPrefix X S W (correctedProfile X L 1 0)).im| ≤ _ at hm
  unfold jointCredit
  by_cases h : ZetaRieszComplexNullFloor.bestCost X N S W L g B-
      jointCost X N S W L g B q ≤ 0
  · rw [max_eq_right h]
    simpa only [add_zero] using
      ZetaRieszComplexNullFloor.best_floor X N S W L g B hs hc hX
  · rw [max_eq_left (le_of_lt (lt_of_not_ge h))]
    linarith only [hf,hm,hl]

/-- The joint gain lowers the ORIGINAL signed cost. The bounded
imaginary correction is the OLD one; none of the new null coefficients
requires an absolute common-moment price. -/
theorem prefix_floor_with_joint_gain (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (L : ℝ) (g : ℕ → ℕ) (B : ℝ) (q : Fin 6 → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hs : ∀ n ∈ S,Squarefree n) (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card)
    (hX : ∀ n ∈ S,n ≤ X) :
    let p := ZetaRieszComplexNullFloor.bestParameters X N S W L g B;
    let t := ZetaRieszComplexNullFloor.increment X N S W L p;
    let v := jointIncrement X N S W L q;
    -ZetaRieszComplexNullFloor.bestCost X N S W L g B+
      thresholdGain (Finset.Icc 1 X) g t v τ-
        |B| * |(complexPrefix X S W (correctedProfile X L 1 0)).im| ≤
          (complexPrefix X S W (correctedProfile X L 1 0)).re := by
  dsimp only
  let p := ZetaRieszComplexNullFloor.bestParameters X N S W L g B
  let t := ZetaRieszComplexNullFloor.increment X N S W L p
  let v := jointIncrement X N S W L q
  let a := thresholdStep (Finset.Icc 1 X) g t v τ
  have hg := thresholdGain_le_saving (Finset.Icc 1 X) g t v hτ
  have hf := block_floor (Finset.Icc 1 X) g (fun k => t k+a*v k)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,
    sum_jointIncrement_zero X N S W L q hs hc hX,mul_zero,add_zero] at hf
  rw [ZetaRieszComplexNullFloor.sum_increment_eq X N S W L hs hc hX] at hf
  have hm := mul_le_mul_of_nonneg_right
    (ZetaRieszComplexNullFloor.bestParameters_bound X N S W L g B 0)
    (abs_nonneg (complexPrefix X S W (correctedProfile X L 1 0)).im)
  rw [← abs_mul] at hm
  change |p 0*(complexPrefix X S W (correctedProfile X L 1 0)).im| ≤
    |B| * |(complexPrefix X S W (correctedProfile X L 1 0)).im| at hm
  have hl := neg_abs_le (p 0*(complexPrefix X S W (correctedProfile X L 1 0)).im)
  change thresholdGain (Finset.Icc 1 X) g t v τ ≤
    ZetaRieszComplexNullFloor.bestCost X N S W L g B-
      blockCost (Finset.Icc 1 X) g (fun k => t k+a*v k) at hg
  change -ZetaRieszComplexNullFloor.bestCost X N S W L g B+
    thresholdGain (Finset.Icc 1 X) g t v τ-
      |B| * |(complexPrefix X S W (correctedProfile X L 1 0)).im| ≤ _
  linarith only [hg,hf,hm,hl]

/-- Joint gain on the SAME native endpoint, after the current count crop.
All factorial orders, phases, ownership/allocation and masks are retained. -/
def nativeJointGain (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ) (τ : ℝ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let W := sourceWeight A L u y N
  thresholdGain (Finset.Icc 1 X) (cutoffPeriod y)
    (ZetaRieszComplexNullFloor.increment X N (S.filter Squarefree) W L
      (ZetaRieszComplexNullFloor.bestParameters X N (S.filter Squarefree) W L (cutoffPeriod y) 4))
    (jointIncrement X N (S.filter Squarefree) W L q) τ

theorem nativeJointGain_nonneg (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ) (τ : ℝ) :
    0 ≤ nativeJointGain u y j q τ := thresholdGain_nonneg _ _ _ _ _

/-- The joint gain is capped by the SAME baseline price. It is an
alternative to old cubic credits, never an extra credit spent twice. -/
theorem nativeJointGain_le_cost (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    nativeJointGain u y j q τ ≤ ZetaRieszComplexNullFloor.nativeCost u y j := by
  unfold nativeJointGain ZetaRieszComplexNullFloor.nativeCost
    ZetaRieszComplexNullFloor.bestCost ZetaRieszComplexNullFloor.cost
  dsimp only
  apply (thresholdGain_le_saving _ _ _ _ hτ).trans
  apply sub_le_self
  unfold blockCost
  exact Finset.sum_nonneg (fun _ _ => le_max_right _ _)

/-- The whole previous native cubic guarantee remains available EXACTLY. -/
theorem nativeJointGain_cubic (u y : ℝ) (j : ℕ) (a b τ : ℝ) :
    nativeJointGain u y j ![0,0,0,0,a,b] τ=nativeThresholdGain u y j a b τ := by
  unfold nativeJointGain nativeThresholdGain
  dsimp only
  congr 1
  ext k
  exact jointIncrement_cubic _ _ _ _ _ _ _ _

/-- A concrete stronger floor on the ORIGINAL whole physical carrier.
Every null coefficient can move with the order. There is no added analytic
error, zero assumption, numerical credit premise or mask relaxation. -/
theorem native_floor_with_joint_gain (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    -ZetaRieszComplexNullFloor.nativeCost u y j+nativeJointGain u y j q τ-
      ZetaRieszComplexProjection.nativeError u y j ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
        (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let P := (u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)
  let Q := (u : ℂ)^(N+1)*coreResponse u y N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hs : ∀ n ∈ S.filter Squarefree,Squarefree n := fun _ hn => (Finset.mem_filter.mp hn).2
  have hc : ∀ n ∈ S.filter Squarefree,3 ≤ n.primeFactors.card :=
    fun _ hn => core_count (Finset.mem_filter.mp hn).1
  have hX : ∀ n ∈ S.filter Squarefree,n ≤ X :=
    fun _ hn => (Finset.le_sup (f := id) (Finset.mem_filter.mp hn).1).trans (le_max_right _ _)
  have hf := prefix_floor_with_joint_gain X N (S.filter Squarefree) (sourceWeight A L u y N)
    L (cutoffPeriod y) 4 q hτ hs hc hX
  have he := native_prefix_eq A S L u y N (fun _ hn => core_count hn)
  dsimp only at he hf
  change complexPrefix X (S.filter Squarefree) (sourceWeight A L u y N)
    (correctedProfile X L 1 0)=Q at he
  rw [he] at hf
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hf
  have hr : Q.re-P.re ≤ ‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have hi : |Q.im| ≤ |P.im|+‖Q-P‖ := by
    have hh := abs_sub_le Q.im P.im 0
    simp only [sub_zero] at hh
    have hd : |Q.im-P.im| ≤ ‖Q-P‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (Q-P)
    linarith only [hh,hd]
  change -ZetaRieszComplexNullFloor.nativeCost u y j+nativeJointGain u y j q τ-
    4*|Q.im| ≤ Q.re at hf
  change -ZetaRieszComplexNullFloor.nativeCost u y j+nativeJointGain u y j q τ-
    (4*|P.im|+5*‖Q-P‖) ≤ P.re
  linarith only [hf,hr,hi]

/-- Exact six-direction credit on the SAME count-cropped native core.
There is no new imaginary tilt, population or analytic error. -/
def nativeJointCredit (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  jointCredit X N (S.filter Squarefree) (sourceWeight A L u y N) L (cutoffPeriod y) 4 q

theorem nativeJointCredit_nonneg (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ) :
    0 ≤ nativeJointCredit u y j q := jointCredit_nonneg _ _ _ _ _ _ _ _

theorem nativeJointCredit_le_cost (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ) :
    nativeJointCredit u y j q ≤ ZetaRieszComplexNullFloor.nativeCost u y j :=
  jointCredit_le_cost _ _ _ _ _ _ _ _

/-- The old exact cubic credit is recovered, not added a second time. -/
theorem nativeJointCredit_cubic (u y : ℝ) (j : ℕ) (a b : ℝ) :
    nativeJointCredit u y j ![0,0,0,0,a,b]=
      ZetaRieszSignedNullGain.nativeCredit u y j a b := by
  unfold nativeJointCredit ZetaRieszSignedNullGain.nativeCredit jointCredit
    ZetaRieszSignedNullGain.credit jointCost correctedCost
  dsimp only
  simp only [jointIncrement_cubic]

/-- A direct signed floor using the FULL joint step, with every crossing
paid exactly. This preserves the original nativeError and every mask. -/
theorem native_floor_with_joint_credit (u y : ℝ) (j : ℕ) (q : Fin 6 → ℝ) :
    -ZetaRieszComplexNullFloor.nativeCost u y j+nativeJointCredit u y j q-
      ZetaRieszComplexProjection.nativeError u y j ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
        (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let P := (u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)
  let Q := (u : ℂ)^(N+1)*coreResponse u y N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hs : ∀ n ∈ S.filter Squarefree,Squarefree n := fun _ hn => (Finset.mem_filter.mp hn).2
  have hc : ∀ n ∈ S.filter Squarefree,3 ≤ n.primeFactors.card :=
    fun _ hn => core_count (Finset.mem_filter.mp hn).1
  have hX : ∀ n ∈ S.filter Squarefree,n ≤ X :=
    fun _ hn => (Finset.le_sup (f := id) (Finset.mem_filter.mp hn).1).trans (le_max_right _ _)
  have hf := prefix_floor_with_joint_credit X N (S.filter Squarefree) (sourceWeight A L u y N)
    L (cutoffPeriod y) 4 q hs hc hX
  have he := native_prefix_eq A S L u y N (fun _ hn => core_count hn)
  dsimp only at he hf
  change complexPrefix X (S.filter Squarefree) (sourceWeight A L u y N)
    (correctedProfile X L 1 0)=Q at he
  rw [he] at hf
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hf
  have hr : Q.re-P.re ≤ ‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have hi : |Q.im| ≤ |P.im|+‖Q-P‖ := by
    have hh := abs_sub_le Q.im P.im 0
    simp only [sub_zero] at hh
    have hd : |Q.im-P.im| ≤ ‖Q-P‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (Q-P)
    linarith only [hh,hd]
  change -ZetaRieszComplexNullFloor.nativeCost u y j+nativeJointCredit u y j q-
    4*|Q.im| ≤ Q.re at hf
  change -ZetaRieszComplexNullFloor.nativeCost u y j+nativeJointCredit u y j q-
    (4*|P.im|+5*‖Q-P‖) ≤ P.re
  linarith only [hf,hr,hi]

/-- The stronger exact-payment endpoint. Its cofinal numerical premise
remains the unpaid arithmetic estimate, not a conclusion of this slice. -/
theorem false_of_cofinal_joint_credit (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho=1) (q : ℕ → Fin 6 → ℝ)
    (hcost : ∃ᶠ j in atTop,
      ZetaRieszComplexNullFloor.nativeCost (3/2-rho.1.re) rho.1.im j-
        nativeJointCredit (3/2-rho.1.re) rho.1.im j (q j) ≤ 399/5000) : False := by
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
    (tendsto_nativeError rho hrho hexposed hU)
  exact hcost.mono fun j hj => by
    have hf := native_floor_with_joint_credit (3/2-rho.1.re) rho.1.im j (q j)
    linarith only [hj,hf]

/-- The explicit cofinal arithmetic target for the combined correction.
Its numerical premise is OPEN; this conditional endpoint does not prove
the floor or a zero exclusion. No bilinear hypothesis is concealed. -/
theorem false_of_cofinal_joint_gain (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho=1)
    (q : ℕ → Fin 6 → ℝ) (τ : ℕ → ℝ) (hτ : ∀ j,0 ≤ τ j)
    (hcost : ∃ᶠ j in atTop,
      ZetaRieszComplexNullFloor.nativeCost (3/2-rho.1.re) rho.1.im j-
        nativeJointGain (3/2-rho.1.re) rho.1.im j (q j) (τ j) ≤ 399/5000) : False := by
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
    (tendsto_nativeError rho hrho hexposed hU)
  exact hcost.mono fun j hj => by
    have hf := native_floor_with_joint_gain (3/2-rho.1.re) rho.1.im j (q j) (hτ j)
    linarith only [hj,hf]

end RiemannGaussian.ZetaRieszJointNullCredit
