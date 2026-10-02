/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszComplexNullFloor
import RiemannGaussian.ZetaRieszCubicPrimeEnergy

/-!
# Quantitative signed null gains in the original whole floor

The exact cubic divisor null acts on all count-four-and-higher labels
simultaneously. Count three stays in the original aggregate. A proposed
correction is priced only after assembling whole cutoff groups. Its gain
is its SIGNED correlation with the adverse groups minus the exact cost
of groups that cross zero. No energy fit or capacity hypothesis is used.

The terminal inequality improves the actual `joinedPhysical` floor with
the same paid error. It does not bound the size of the native credit.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSignedNullGain
open ZetaRieszCutoffPeriodFloor ZetaRieszCofactorPhaseEnergy
open ZetaRieszCenteredPrimeEnergy ZetaRieszComplexProjection
open ZetaRieszJointPrimeEnergy ZetaRieszPrimeCountFrequency
open ZetaRieszJointAllocation ZetaRieszAnnulusJoint ZetaRieszParityPacket

/-- A cubic null with the exact finite endpoint and a conditioning scale.
There is no factorial-order, owner, phase or geometric restriction. -/
def cubicProfile (X N : ℕ) (d : ℕ) : ℝ :=
  centeredProfile X ZetaRieszCubicPrimeEnergy.logCube 0 d / (N+1 : ℝ)^2

/-- The genuine arithmetic cubic identity, not a fitted moment. -/
theorem cubic_pairing_zero {n X : ℕ} (hs : Squarefree n)
    (hc : 4 ≤ n.primeFactors.card) (hX : n ≤ X) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 X,cubicProfile X N d*
      (if d ∣ n then (μ d : ℝ) else 0))=0 := by
  have h1 : n ≠ 1 := by
    intro h
    simp only [h,Nat.primeFactors_one,Finset.card_empty] at hc
    omega
  have hp : ¬n.Prime := by
    intro h
    simp only [h.primeFactors,Finset.card_singleton] at hc
    omega
  simp only [cubicProfile,div_mul_eq_mul_div,← Finset.sum_div]
  rw [prefix_eq_divisors (Nat.pos_of_ne_zero hs.ne_zero) hX,
    divisor_centering hs hp h1 hX]
  change ZetaRieszCubicPrimeEnergy.thirdMoment n / (N+1 : ℝ)^2=0
  rw [ZetaRieszCubicPrimeEnergy.thirdMoment_eq_zero_of_count hs hc,zero_div]

/-- Count three is NEVER corrected. All remaining counts are joined
before the correction is priced, with their full original complex weight. -/
def higherCounts (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun n => 4 ≤ n.primeFactors.card)

/-- Both real and imaginary parts of the exact cubic null are available. -/
def cubicIncrement (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (a b : ℝ) (k : ℕ) : ℝ :=
  (a*correlation (higherCounts S) (fun n => (W n).re) k-
    b*correlation (higherCounts S) (fun n => (W n).im) k)*
      (cubicProfile X N k-cubicProfile X N (k+1))

/-- The full correction is zero, including all early cutoff increments. -/
theorem sum_cubicIncrement_eq_zero (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (hs : ∀ n ∈ S,Squarefree n) (hX : ∀ n ∈ S,n ≤ X) (a b : ℝ) :
    (∑ k ∈ Finset.Icc 1 X,cubicIncrement X N S W a b k)=0 := by
  have hend : cubicProfile X N (X+1)=0 := by
    simp [cubicProfile,centeredProfile]
  have he (w : ℕ → ℝ) :
      (∑ k ∈ Finset.Icc 1 X,correlation (higherCounts S) w k*
        (cubicProfile X N k-cubicProfile X N (k+1)))=0 := by
    have hz : (∑ n ∈ higherCounts S,w n*(∑ d ∈ Finset.Icc 1 X,
        cubicProfile X N d*(if d ∣ n then (μ d : ℝ) else 0)))=0 := by
      apply Finset.sum_eq_zero
      intro n hn
      obtain ⟨hn,hc⟩ := Finset.mem_filter.mp hn
      rw [cubic_pairing_zero (hs n hn) hc (hX n hn),mul_zero]
    simp_rw [ZetaRieszSignedCutoffEnergy.abel_profile X (cubicProfile X N) _ hend,
      Finset.mul_sum] at hz
    rw [Finset.sum_comm] at hz
    convert hz using 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [correlation,sharp,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum,Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp only [cubicIncrement,sub_mul,mul_assoc,Finset.sum_sub_distrib,
    ← Finset.mul_sum,he,mul_zero,sub_zero]

/-- The signed directional correlation AFTER joining each full group. -/
def adverseCorrelation (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) : ℝ :=
  ∑ c ∈ K.image g,if blockTotal K g t c < 0 then blockTotal K g v c else 0

/-- Every sign-changing group is retained. No 'small boundary' is assumed. -/
def crossingCost (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∑ c ∈ K.image g,
    if blockTotal K g t c < 0 then
      max (blockTotal K g t c+a*blockTotal K g v c) 0
    else max (-(blockTotal K g t c+a*blockTotal K g v c)) 0

private theorem clipped_shift_eq (x y : ℝ) :
    max (-(x+y)) 0 = max (-x) 0-(if x < 0 then y else 0)+
      (if x < 0 then max (x+y) 0 else max (-(x+y)) 0) := by
  by_cases hx : x < 0
  · simp only [hx,if_true,max_eq_left (by linarith : 0 ≤ -x)]
    by_cases hxy : 0 ≤ x+y
    · rw [max_eq_left hxy,max_eq_right (by linarith : -(x+y) ≤ 0)]
      ring
    · rw [max_eq_right (le_of_not_ge hxy),max_eq_left (by linarith : 0 ≤ -(x+y))]
      ring
  · simp only [hx,if_false,max_eq_right (by linarith : -x ≤ 0)]
    ring

/-- An EXACT savings identity for any signed aggregate and any direction.
This is not a derivative approximation and includes zero original blocks. -/
theorem blockCost_shift_eq (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (a : ℝ) :
    blockCost K g (fun k => t k+a*v k)=blockCost K g t-
      a*adverseCorrelation K g t v+crossingCost K g t v a := by
  have hb c : blockTotal K g (fun k => t k+a*v k) c=
      blockTotal K g t c+a*blockTotal K g v c := by
    simp only [blockTotal,Finset.sum_add_distrib,Finset.mul_sum]
  calc
    _ = ∑ c ∈ K.image g,
        (max (-blockTotal K g t c) 0-
          (if blockTotal K g t c < 0 then a*blockTotal K g v c else 0)+
          (if blockTotal K g t c < 0 then
            max (blockTotal K g t c+a*blockTotal K g v c) 0
          else max (-(blockTotal K g t c+a*blockTotal K g v c)) 0)) := by
      unfold blockCost
      apply Finset.sum_congr rfl
      intro c _
      conv_lhs => rw [hb,clipped_shift_eq]
    _ = _ := by
      simp only [blockCost,crossingCost,adverseCorrelation,
        Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,mul_ite,mul_zero]

theorem crossingCost_nonneg (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (a : ℝ) : 0 ≤ crossingCost K g t v a := by
  apply Finset.sum_nonneg
  intro c _
  split_ifs <;> exact le_max_right _ _

/-- A signed correlation is a real floor gain exactly when it exceeds
the actually crossed-group price. Countwise/termwise absolute costs do
not appear anywhere in this criterion. -/
theorem floor_with_null_gain (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (a : ℝ) (hv : (∑ k ∈ K,v k)=0) :
    -blockCost K g t+a*adverseCorrelation K g t v-crossingCost K g t v a ≤
      ∑ k ∈ K,t k := by
  have hf := block_floor K g (fun k => t k+a*v k)
  rw [blockCost_shift_eq,Finset.sum_add_distrib,← Finset.mul_sum,hv,mul_zero,add_zero] at hf
  linarith only [hf]

private theorem weighted_negative_le (x h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    -h*x ≤ max (-x) 0 := by
  by_cases hx : 0 ≤ x
  · have he : -h*x=-(h*x) := by ring
    rw [he]
    exact (neg_nonpos.mpr (mul_nonneg h0 hx)).trans (le_max_right _ _)
  · have hh := mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ -x)
    have he : -h*x=h*(-x) := by ring
    rw [he]
    exact hh.trans (by simpa only [one_mul] using le_max_left (-x) 0)

/-- A rigorously priced dual witness tests ALL correction vectors in a
box at once. Inexact dual orthogonality is paid explicitly by the last
term. This is the finite signed-cost lower bound used by the detector;
it neither assumes primal optimality nor loses cutoff/count correlations. -/
theorem boxCost_lower_bound (C I : Finset ℕ) (t h a : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (B : ℝ)
    (hh : ∀ c ∈ C,0 ≤ h c ∧ h c ≤ 1)
    (ha : ∀ i ∈ I,|a i| ≤ B) :
    -(∑ c ∈ C,h c*t c)-B*(∑ i ∈ I,|∑ c ∈ C,h c*v i c|) ≤
      ∑ c ∈ C,max (-(t c+∑ i ∈ I,a i*v i c)) 0 := by
  have hp : -(∑ c ∈ C,h c*(t c+∑ i ∈ I,a i*v i c)) ≤
      ∑ c ∈ C,max (-(t c+∑ i ∈ I,a i*v i c)) 0 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro c hc
    simpa only [neg_mul] using weighted_negative_le
      (t c+∑ i ∈ I,a i*v i c) (h c) (hh c hc).1 (hh c hc).2
  have hs : (∑ c ∈ C,h c*(∑ i ∈ I,a i*v i c))=
      ∑ i ∈ I,a i*(∑ c ∈ C,h c*v i c) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hd : (∑ i ∈ I,a i*(∑ c ∈ C,h c*v i c)) ≤
      B*(∑ i ∈ I,|∑ c ∈ C,h c*v i c|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ ≤ |a i*(∑ c ∈ C,h c*v i c)| := le_abs_self _
      _ = |a i| * |∑ c ∈ C,h c*v i c| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (ha i hi) (abs_nonneg _)
  simp only [mul_add,Finset.sum_add_distrib,hs] at hp
  linarith only [hp,hd]

/-- An explicitly verified step inside the current sign cells has no
crossing price. Zero baseline groups require zero change; they are not
silently omitted from the condition. -/
theorem crossingCost_eq_zero_of_margin (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (a : ℝ)
    (h : ∀ c ∈ K.image g,|a*blockTotal K g v c| ≤ |blockTotal K g t c|) :
    crossingCost K g t v a=0 := by
  unfold crossingCost
  apply Finset.sum_eq_zero
  intro c hc
  have hb := abs_le.mp (h c hc)
  by_cases ht : blockTotal K g t c < 0
  · rw [if_pos ht,max_eq_right]
    · rw [abs_of_neg ht] at hb
      linarith only [hb.2]
  · rw [if_neg ht,max_eq_right]
    · rw [abs_of_nonneg (le_of_not_gt ht)] at hb
      linarith only [hb.1]

/-- A concrete signed improvement whenever the exact stable direction
has positive adverse correlation. All counts/groups stay joined. -/
theorem floor_with_stable_null_gain (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (a : ℝ) (hv : (∑ k ∈ K,v k)=0)
    (h : ∀ c ∈ K.image g,|a*blockTotal K g v c| ≤ |blockTotal K g t c|) :
    -blockCost K g t+a*adverseCorrelation K g t v ≤ ∑ k ∈ K,t k := by
  have hf := floor_with_null_gain K g t v a hv
  rwa [crossingCost_eq_zero_of_margin K g t v a h,sub_zero] at hf

/-- The cubic correction is joined with the existing full signed vector.
It changes NO arithmetic label, phase, count, owner, mask or allocation. -/
def correctedCost (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (p : Fin 5 → ℝ) (a b : ℝ) : ℝ :=
  blockCost (Finset.Icc 1 X) g (fun k =>
    ZetaRieszComplexNullFloor.increment X N S W L p k+cubicIncrement X N S W a b k)

/-- Apply the exact correction to the whole carrier without a new
imaginary correction. The former single bounded tilt stays explicit. -/
theorem correctedCost_floor (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (hs : ∀ n ∈ S,Squarefree n)
    (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card) (hX : ∀ n ∈ S,n ≤ X)
    (p : Fin 5 → ℝ) (a b : ℝ) :
    -correctedCost X N S W L g p a b+
      p 0*(complexPrefix X S W (correctedProfile X L 1 0)).im ≤
        (complexPrefix X S W (correctedProfile X L 1 0)).re := by
  have hf := block_floor (Finset.Icc 1 X) g (fun k =>
    ZetaRieszComplexNullFloor.increment X N S W L p k+cubicIncrement X N S W a b k)
  rw [Finset.sum_add_distrib,ZetaRieszComplexNullFloor.sum_increment_eq X N S W L hs hc hX,
    sum_cubicIncrement_eq_zero X N S W hs hX,add_zero] at hf
  change -correctedCost X N S W L g p a b ≤ _ at hf
  linarith only [hf]

/-- Explicit savings, with every crossed cutoff period paid. A positive
right-hand side is an actual finite improvement, not an energy proxy. -/
theorem cost_sub_correctedCost_eq (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (p : Fin 5 → ℝ) (a b : ℝ) :
    ZetaRieszComplexNullFloor.cost X N S W L g p-
      correctedCost X N S W L g p a b =
    adverseCorrelation (Finset.Icc 1 X) g
      (ZetaRieszComplexNullFloor.increment X N S W L p)
      (cubicIncrement X N S W a b)-
    crossingCost (Finset.Icc 1 X) g
      (ZetaRieszComplexNullFloor.increment X N S W L p)
      (cubicIncrement X N S W a b) 1 := by
  have he := blockCost_shift_eq (Finset.Icc 1 X) g
    (ZetaRieszComplexNullFloor.increment X N S W L p)
    (cubicIncrement X N S W a b) 1
  simp only [one_mul] at he
  change correctedCost X N S W L g p a b =
    ZetaRieszComplexNullFloor.cost X N S W L g p-_+_ at he
  linarith only [he]

/-- Retain only an actual saving, measured against the SAME old price.
Zero is always available, so no candidate can worsen the whole floor. -/
def credit (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B a b : ℝ) : ℝ :=
  max (ZetaRieszComplexNullFloor.bestCost X N S W L g B-
    correctedCost X N S W L g
      (ZetaRieszComplexNullFloor.bestParameters X N S W L g B) a b) 0

theorem credit_nonneg (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B a b : ℝ) : 0 ≤ credit X N S W L g B a b := le_max_right _ _

/-- The actual savings cannot exceed the same original price. This is
the cost ledger needed before combining it with older paid credits. -/
theorem credit_le_bestCost (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B a b : ℝ) :
    credit X N S W L g B a b ≤ ZetaRieszComplexNullFloor.bestCost X N S W L g B := by
  have hc : 0 ≤ correctedCost X N S W L g
      (ZetaRieszComplexNullFloor.bestParameters X N S W L g B) a b := by
    unfold correctedCost blockCost
    exact Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  unfold credit
  exact max_le (by linarith only [hc])
    (ZetaRieszComplexNullFloor.bestCost_nonneg X N S W L g B)

/-- The quantitative cubic saving raises the whole signed floor.
Its only error is the SAME old bounded whole-carrier imaginary part. -/
theorem floor_with_credit (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (L : ℝ)
    (g : ℕ → ℕ) (B a b : ℝ) (hs : ∀ n ∈ S,Squarefree n)
    (hc : ∀ n ∈ S,3 ≤ n.primeFactors.card) (hX : ∀ n ∈ S,n ≤ X) :
    -ZetaRieszComplexNullFloor.bestCost X N S W L g B+credit X N S W L g B a b-
      |B| * |(complexPrefix X S W (correctedProfile X L 1 0)).im| ≤
        (complexPrefix X S W (correctedProfile X L 1 0)).re := by
  have hnew := correctedCost_floor X N S W L g hs hc hX
    (ZetaRieszComplexNullFloor.bestParameters X N S W L g B) a b
  have hm := mul_le_mul_of_nonneg_right
    (ZetaRieszComplexNullFloor.bestParameters_bound X N S W L g B 0)
    (abs_nonneg (complexPrefix X S W (correctedProfile X L 1 0)).im)
  rw [← abs_mul] at hm
  have hl := neg_abs_le (ZetaRieszComplexNullFloor.bestParameters X N S W L g B 0*
    (complexPrefix X S W (correctedProfile X L 1 0)).im)
  have hnew' : -correctedCost X N S W L g
      (ZetaRieszComplexNullFloor.bestParameters X N S W L g B) a b-
      |B| * |(complexPrefix X S W (correctedProfile X L 1 0)).im| ≤
        (complexPrefix X S W (correctedProfile X L 1 0)).re := by
    linarith only [hnew,hm,hl]
  unfold credit
  by_cases h : ZetaRieszComplexNullFloor.bestCost X N S W L g B-
      correctedCost X N S W L g
        (ZetaRieszComplexNullFloor.bestParameters X N S W L g B) a b ≤ 0
  · rw [max_eq_right h]
    simpa only [add_zero] using ZetaRieszComplexNullFloor.best_floor X N S W L g B hs hc hX
  · rw [max_eq_left (le_of_lt (lt_of_not_ge h))]
    linarith only [hnew']

/-- Native cubic credit on the actual count-cropped core, with all
original labels and masks. Count three remains in the baseline price. -/
def nativeCredit (u y : ℝ) (j : ℕ) (a b : ℝ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  credit X N (S.filter Squarefree) (sourceWeight A L u y N) L (cutoffPeriod y) 4 a b

/-- A DIRECT quantitative improvement on `joinedPhysical`, not on a
new carrier. Existing errors and credits are neither dropped nor reused. -/
theorem native_floor_with_credit (u y : ℝ) (j : ℕ) (a b : ℝ) :
    -ZetaRieszComplexNullFloor.nativeCost u y j+nativeCredit u y j a b-
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
  have hf := floor_with_credit X N (S.filter Squarefree) (sourceWeight A L u y N) L
    (cutoffPeriod y) 4 a b hs hc hX
  have he := native_prefix_eq A S L u y N (fun _ hn => core_count hn)
  dsimp only at he
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
  change -ZetaRieszComplexNullFloor.nativeCost u y j+nativeCredit u y j a b-4*|Q.im| ≤ Q.re at hf
  change -ZetaRieszComplexNullFloor.nativeCost u y j+nativeCredit u y j a b-
    (4*|P.im|+5*‖Q-P‖) ≤ P.re
  linarith only [hf,hr,hi]

/-- The improved numerical endgame is still an EXPLICIT open premise.
Moving cubic coefficients need no extra analytic error: the null identity
is finite and exact at each endpoint. No cofinal credit size is supplied. -/
theorem false_of_cofinal_credited_cost (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho=1) (a b : ℕ → ℝ)
    (hcost : ∃ᶠ j in atTop,
      ZetaRieszComplexNullFloor.nativeCost (3/2-rho.1.re) rho.1.im j-
        nativeCredit (3/2-rho.1.re) rho.1.im j (a j) (b j) ≤ 399/5000) : False := by
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
    (tendsto_nativeError rho hrho hexposed hU)
  exact hcost.mono fun j hj => by
    have hf := native_floor_with_credit (3/2-rho.1.re) rho.1.im j (a j) (b j)
    linarith only [hj,hf]

end RiemannGaussian.ZetaRieszSignedNullGain
