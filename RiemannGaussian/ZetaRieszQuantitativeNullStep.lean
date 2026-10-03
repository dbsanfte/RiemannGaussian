/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedNullGain

/-!
# An explicit guaranteed step for the joined signed null credit

Keep all cutoff groups and all original zero blocks. The signed adverse
correlation is reduced only by the exact one-sided zero-block debit. On
nonzero blocks, an elementary quadratic estimate pays every sign crossing.
This gives a mathematically defined step and a quantitative saving in the
same whole-carrier cost, without fitting an energy proxy or assuming that
the native correlation has any particular size.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszQuantitativeNullStep
open ZetaRieszCutoffPeriodFloor ZetaRieszSignedNullGain
open ZetaRieszComplexProjection ZetaRieszJointPrimeEnergy ZetaRieszJointAllocation
open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint ZetaRieszParityPacket
open ZetaRieszCofactorPhaseEnergy

/-- Exact loss on the originally zero groups, in the positive direction.
These groups cannot be paid by an inverse-margin quadratic estimate. -/
def zeroDebit (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) : ℝ :=
  ∑ c ∈ K.image g,if blockTotal K g t c=0 then max (-blockTotal K g v c) 0 else 0

/-- A quadratic upper price for crossings of NONZERO joined blocks.
At a zero block the quotient is zero; its exact linear debit stays above. -/
def crossingPrice (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) : ℝ :=
  ∑ c ∈ K.image g,blockTotal K g v c^2/(4*|blockTotal K g t c|)

theorem crossingPrice_nonneg (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) :
    0 ≤ crossingPrice K g t v := by
  unfold crossingPrice
  exact Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (by positivity))

private theorem hinge_le_square (x r : ℝ) (hr : 0 < r) :
    max (x-r) 0 ≤ x^2/(4*r) := by
  rw [le_div_iff₀ (by positivity : 0 < 4*r)]
  by_cases h : 0 ≤ x-r
  · rw [max_eq_left h]
    nlinarith only [sq_nonneg (x-2*r)]
  · rw [max_eq_right (le_of_not_ge h),zero_mul]
    exact sq_nonneg x

private theorem max_neg_mul (a v : ℝ) (ha : 0 ≤ a) :
    max (-(a*v)) 0=a*max (-v) 0 := by
  by_cases hv : v ≤ 0
  · rw [max_eq_left (by linarith : 0 ≤ -v),
      max_eq_left (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos ha hv))]
    ring
  · rw [max_eq_right (by linarith : -v ≤ 0),
      max_eq_right (neg_nonpos.mpr (mul_nonneg ha (le_of_not_ge hv))),mul_zero]

private theorem crossing_term_le (t v a : ℝ) (ha : 0 ≤ a) :
    (if t < 0 then max (t+a*v) 0 else max (-(t+a*v)) 0) ≤
      a*(if t=0 then max (-v) 0 else 0)+a^2*(v^2/(4*|t|)) := by
  by_cases ht0 : t=0
  · subst t
    simp only [lt_self_iff_false,if_false,if_true,zero_add,abs_zero,mul_zero,
      div_zero,add_zero]
    exact le_of_eq (max_neg_mul a v ha)
  · simp only [if_neg ht0,mul_zero,zero_add]
    by_cases ht : t < 0
    · rw [if_pos ht,abs_of_neg ht]
      have h := hinge_le_square (a*v) (-t) (by linarith)
      have he : a*v- -t=t+a*v := by ring
      rw [he] at h
      exact h.trans_eq (by ring)
    · have htpos : 0 < t := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm ht0)
      rw [if_neg ht,abs_of_pos htpos]
      have h := hinge_le_square (-a*v) t htpos
      have he : -a*v-t=-(t+a*v) := by ring
      rw [he] at h
      exact h.trans_eq (by ring)

/-- No margin hypothesis: every crossed nonzero block has a quadratic
price, and every original zero block retains its full linear charge. -/
theorem crossingCost_le (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    crossingCost K g t v a ≤ a*zeroDebit K g t v+a^2*crossingPrice K g t v := by
  unfold crossingCost zeroDebit crossingPrice
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun c _ => crossing_term_le
    (blockTotal K g t c) (blockTotal K g v c) a ha)

/-- The original zero-face debit is unavoidable along this direction.
It is a LOWER as well as an upper crossing charge, for every positive step. -/
theorem zeroDebit_le_crossingCost (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    a*zeroDebit K g t v ≤ crossingCost K g t v a := by
  unfold zeroDebit crossingCost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  by_cases ht : blockTotal K g t c=0
  · simp only [ht,if_true,lt_self_iff_false,if_false,zero_add]
    exact le_of_eq (max_neg_mul a _ ha).symm
  · simp only [if_neg ht,mul_zero]
    split_ifs <;> exact le_max_right _ _

/-- If the signed correlation cannot pay the actual zero-face debit,
NO positive step along the direction can lower the full cost. This is not
an impossibility claim for a different direction or the arithmetic floor. -/
theorem cost_not_decreased_of_boundary (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (hD : adverseCorrelation K g t v ≤ zeroDebit K g t v)
    {a : ℝ} (ha : 0 ≤ a) :
    blockCost K g t ≤ blockCost K g (fun k => t k+a*v k) := by
  rw [blockCost_shift_eq]
  have hc := zeroDebit_le_crossingCost K g t v ha
  have hd := mul_le_mul_of_nonneg_left hD ha
  linarith only [hc,hd]

/-- Both boundary tests certify that EVERY real step on this one line
is unprofitable. Joint directions can escape; their zero-face charge must
be recomputed after they have been summed. -/
theorem cost_not_decreased_both_orientations (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (hD : adverseCorrelation K g t v ≤ zeroDebit K g t v)
    (hD' : adverseCorrelation K g t (fun k => -v k) ≤
      zeroDebit K g t (fun k => -v k)) (a : ℝ) :
    blockCost K g t ≤ blockCost K g (fun k => t k+a*v k) := by
  by_cases ha : 0 ≤ a
  · exact cost_not_decreased_of_boundary K g t v hD ha
  · have h := cost_not_decreased_of_boundary K g t (fun k => -v k) hD'
        (by linarith only [ha] : 0 ≤ -a)
    simpa only [neg_mul_neg] using h

/-- A signed global cost gain, AFTER joining counts and cutoff periods.
The null assumption is unnecessary for the cost comparison itself. -/
theorem cost_gain_lower (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    a*(adverseCorrelation K g t v-zeroDebit K g t v)-a^2*crossingPrice K g t v ≤
      blockCost K g t-blockCost K g (fun k => t k+a*v k) := by
  rw [blockCost_shift_eq]
  have h := crossingCost_le K g t v ha
  linarith only [h]

/-- Signed correlation available after charging the original zero blocks.
The positive part is taken only after the WHOLE signed correlation is formed. -/
def availableCorrelation (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) : ℝ :=
  max (adverseCorrelation K g t v-zeroDebit K g t v) 0

/-- An exact coefficient choice, rather than a searched numerical trial.
It is zero when the finite quadratic price is zero. -/
def step (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) : ℝ :=
  availableCorrelation K g t v/(2*crossingPrice K g t v)

/-- A quantified guaranteed saving. This is NOT a numerical estimate of
the native prime population; its signed correlation remains arithmetic. -/
def guaranteedGain (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) : ℝ :=
  availableCorrelation K g t v^2/(4*crossingPrice K g t v)

theorem step_nonneg (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) :
    0 ≤ step K g t v := by
  exact div_nonneg (le_max_right _ _) (mul_nonneg (by norm_num) (crossingPrice_nonneg K g t v))

theorem guaranteedGain_nonneg (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) :
    0 ≤ guaranteedGain K g t v := by
  exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (crossingPrice_nonneg K g t v))

/-- A genuine strictly positive saving whenever the whole signed
correlation beats the exact zero-block debit and the price is positive. -/
theorem guaranteedGain_pos (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ)
    (hD : zeroDebit K g t v < adverseCorrelation K g t v)
    (hH : 0 < crossingPrice K g t v) : 0 < guaranteedGain K g t v := by
  have he : 0 < availableCorrelation K g t v :=
    (sub_pos.mpr hD).trans_le (le_max_left _ _)
  exact div_pos (sq_pos_of_pos he) (mul_pos (by norm_num) hH)

/-- The actual joined cost falls by at least the explicit signed
correlation-square price. No crossing or zero group is dropped. -/
theorem guaranteedGain_le_saving (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) :
    guaranteedGain K g t v ≤ blockCost K g t-
      blockCost K g (fun k => t k+step K g t v*v k) := by
  have h := cost_gain_lower K g t v (step_nonneg K g t v)
  by_cases hH : crossingPrice K g t v=0
  · simp only [guaranteedGain,step,hH,mul_zero,div_zero,zero_mul,add_zero,
      sub_self,le_refl]
  · by_cases hD : adverseCorrelation K g t v-zeroDebit K g t v ≤ 0
    · simp only [guaranteedGain,step,availableCorrelation,max_eq_right hD,
        zero_div,zero_pow (by norm_num : 2 ≠ 0),zero_mul,add_zero,sub_self,le_refl]
    · have he : availableCorrelation K g t v=
          adverseCorrelation K g t v-zeroDebit K g t v := by
        exact max_eq_left (le_of_lt (lt_of_not_ge hD))
      have hq : step K g t v*(adverseCorrelation K g t v-zeroDebit K g t v)-
          step K g t v^2*crossingPrice K g t v=guaranteedGain K g t v := by
        unfold step guaranteedGain
        rw [he]
        field_simp
        ring
      rwa [hq] at h

/-- Apply the new saving to the SAME signed sum when the direction is
an exact null. There is no separate credit from a reconstructed carrier. -/
theorem floor_with_guaranteed_gain (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (hv : (∑ k ∈ K,v k)=0) :
    -blockCost K g t+guaranteedGain K g t v ≤ ∑ k ∈ K,t k := by
  have hg := guaranteedGain_le_saving K g t v
  have hf := block_floor K g (fun k => t k+step K g t v*v k)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,hv,mul_zero,add_zero] at hf
  linarith only [hg,hf]

/-- Scaling a cubic direction does not alter any arithmetic label or
support mask. It is the same exact null direction with a moving step. -/
theorem cubicIncrement_scaled (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (r a b : ℝ) (k : ℕ) :
    cubicIncrement X N S W (r*a) (r*b) k=r*cubicIncrement X N S W a b k := by
  unfold cubicIncrement
  ring

/-- Choose a single cubic correction perpendicular to the common
complex higher-count moment. This preserves all of its signed phases. -/
theorem cubicIncrement_orthogonal_eq (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (M : ℂ) (a : ℝ) (k : ℕ) :
    cubicIncrement X N S W (a*M.im) (a*M.re) k=
      a*(M.im*correlation (higherCounts S) (fun n => (W n).re) k-
        M.re*correlation (higherCounts S) (fun n => (W n).im) k)*
        (cubicProfile X N k-cubicProfile X N (k+1)) := by
  unfold cubicIncrement
  ring

/-- Every coherent prefix is killed exactly, regardless of the size of
its complex moment. This covers all higher counts simultaneously. -/
theorem cubicIncrement_coherent_zero (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (M : ℂ) (a : ℝ) (k : ℕ)
    (hc : M.im*correlation (higherCounts S) (fun n => (W n).re) k=
      M.re*correlation (higherCounts S) (fun n => (W n).im) k) :
    cubicIncrement X N S W (a*M.im) (a*M.re) k=0 := by
  rw [cubicIncrement_orthogonal_eq,hc]
  simp only [sub_self,mul_zero,zero_mul]

/-- The exact ideal direction does not create a new cutoff-one debit.
Its common moment is the SAME higher-count population, not the count-three
moment or a completed cofactor. No phase or roughness premise is required. -/
theorem cubicIncrement_first_zero (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ) (a : ℝ) :
    let M := ∑ n ∈ higherCounts S,W n;
    cubicIncrement X N S W (a*M.im) (a*M.re) 1=0 := by
  dsimp only
  apply cubicIncrement_coherent_zero
  simp [correlation,sharp,Complex.re_sum,Complex.im_sum,mul_comm]

/-- At the actual positive-height working range, no integer cutoff
after one belongs to period zero. There is no continuous-period completion. -/
theorem cutoffPeriod_pos {y : ℝ} (hy : 54 ≤ y) {k : ℕ} (hk : 2 ≤ k) :
    0 < cutoffPeriod y k := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hl2 : (1/2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hl : (1/2 : ℝ) ≤ log (k : ℝ) :=
    hl2.trans (log_le_log (by norm_num : (0 : ℝ) < 2) hkr)
  have hm : (54 : ℝ)*(1/2) ≤ y*log (k : ℝ) :=
    mul_le_mul hy hl (by norm_num) (by linarith)
  unfold cutoffPeriod
  apply Nat.floor_pos.mpr
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*Real.pi)).2
  nlinarith only [hm,Real.pi_lt_four]

/-- A concrete COMPLETE-period payment: the phase-aligned correction
has exactly zero weight on period zero for every higher-count population.
Neither its complex common moment nor its prime inventory is norm-paid. -/
theorem cubic_zero_period (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    {y : ℝ} (hy : 54 ≤ y) (a : ℝ) :
    let M := ∑ n ∈ higherCounts S,W n;
    blockTotal (Finset.Icc 1 X) (cutoffPeriod y)
      (cubicIncrement X N S W (a*M.im) (a*M.re)) 0=0 := by
  dsimp only
  unfold blockTotal
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨hk,hg⟩ := Finset.mem_filter.mp hk
  have hk1 : k=1 := by
    by_contra hn
    have hkp : 2 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
    have hp := cutoffPeriod_pos hy hkp
    rw [hg] at hp
    omega
  rw [hk1]
  exact cubicIncrement_first_zero X N S W a

/-- A lower bound for the PREVIOUS exact cubic credit. This replaces no
ledger and introduces no new paid error or independent numerical premise. -/
theorem credit_ge_guaranteedGain (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (L : ℝ) (g : ℕ → ℕ) (B a b : ℝ) :
    let t := ZetaRieszComplexNullFloor.increment X N S W L
      (ZetaRieszComplexNullFloor.bestParameters X N S W L g B)
    let v := cubicIncrement X N S W a b;
    guaranteedGain (Finset.Icc 1 X) g t v ≤
      credit X N S W L g B
        (step (Finset.Icc 1 X) g t v*a) (step (Finset.Icc 1 X) g t v*b) := by
  dsimp only
  let p := ZetaRieszComplexNullFloor.bestParameters X N S W L g B
  let t := ZetaRieszComplexNullFloor.increment X N S W L p
  let v := cubicIncrement X N S W a b
  let r := step (Finset.Icc 1 X) g t v
  have hc : correctedCost X N S W L g p (r*a) (r*b)=
      blockCost (Finset.Icc 1 X) g (fun k => t k+r*v k) := by
    unfold correctedCost
    simp only [cubicIncrement_scaled]
    rfl
  have hg := guaranteedGain_le_saving (Finset.Icc 1 X) g t v
  change guaranteedGain (Finset.Icc 1 X) g t v ≤
    max (ZetaRieszComplexNullFloor.bestCost X N S W L g B-
      correctedCost X N S W L g p (r*a) (r*b)) 0
  rw [hc]
  exact hg.trans (le_max_left _ _)

/-- Mathematically specified step on the literal source-scaled core.
It uses the same count ceiling, squarefree labels, physical masks, phase
and factorial/owner allocation as the existing whole-floor credit. -/
def nativeStep (u y : ℝ) (j : ℕ) (a b : ℝ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let W := sourceWeight A L u y N
  step (Finset.Icc 1 X) (cutoffPeriod y)
    (ZetaRieszComplexNullFloor.increment X N (S.filter Squarefree) W L
      (ZetaRieszComplexNullFloor.bestParameters X N (S.filter Squarefree) W L (cutoffPeriod y) 4))
    (cubicIncrement X N (S.filter Squarefree) W a b)

/-- Explicit lower credit on the original native carrier. Its magnitude
still needs an arithmetic bound; finite model regressions do not supply it. -/
def nativeGuaranteedGain (u y : ℝ) (j : ℕ) (a b : ℝ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let W := sourceWeight A L u y N
  guaranteedGain (Finset.Icc 1 X) (cutoffPeriod y)
    (ZetaRieszComplexNullFloor.increment X N (S.filter Squarefree) W L
      (ZetaRieszComplexNullFloor.bestParameters X N (S.filter Squarefree) W L (cutoffPeriod y) 4))
    (cubicIncrement X N (S.filter Squarefree) W a b)

theorem nativeGuaranteedGain_nonneg (u y : ℝ) (j : ℕ) (a b : ℝ) :
    0 ≤ nativeGuaranteedGain u y j a b := by
  exact guaranteedGain_nonneg _ _ _ _

/-- Keep the exact ORIGINAL finite endpoint: the supremum is taken
before the squarefree filter, just as in `nativeCredit`. -/
theorem nativeGuaranteedGain_le_credit (u y : ℝ) (j : ℕ) (a b : ℝ) :
    nativeGuaranteedGain u y j a b ≤
      ZetaRieszSignedNullGain.nativeCredit u y j
        (nativeStep u y j a b*a) (nativeStep u y j a b*b) := by
  unfold nativeGuaranteedGain nativeStep ZetaRieszSignedNullGain.nativeCredit
  dsimp only
  exact credit_ge_guaranteedGain _ _ _ _ _ _ _ _ _

/-- The explicit saving is bounded by the SAME prior native price.
It cannot double spend any previous phase or funded sector credit. -/
theorem nativeGuaranteedGain_le_cost (u y : ℝ) (j : ℕ) (a b : ℝ) :
    nativeGuaranteedGain u y j a b ≤ ZetaRieszComplexNullFloor.nativeCost u y j := by
  apply (nativeGuaranteedGain_le_credit u y j a b).trans
  exact credit_le_bestCost _ _ _ _ _ _ _ _ _

/-- A quantitative improvement to the ORIGINAL whole-carrier floor.
All masks, phases, counts, allocation and previous funding are retained.
Only the SAME old analytic error appears. No fixed size for this gain,
cofinal 399/5000 bound, or zero exclusion is inferred. -/
theorem native_floor_with_guaranteed_gain (u y : ℝ) (j : ℕ) (a b : ℝ) :
    -ZetaRieszComplexNullFloor.nativeCost u y j+nativeGuaranteedGain u y j a b-
      ZetaRieszComplexProjection.nativeError u y j ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
        (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  have hf := native_floor_with_credit u y j
    (nativeStep u y j a b*a) (nativeStep u y j a b*b)
  have hg := nativeGuaranteedGain_le_credit u y j a b
  linarith only [hf,hg]

/-- Test both orientations of the same mathematical direction, choosing
the better guaranteed saving. It is a MAXIMUM, never the sum of two credits
spent against the same native price. -/
theorem native_floor_with_best_orientation (u y : ℝ) (j : ℕ) (a b : ℝ) :
    -ZetaRieszComplexNullFloor.nativeCost u y j+
      max (nativeGuaranteedGain u y j a b) (nativeGuaranteedGain u y j (-a) (-b))-
        ZetaRieszComplexProjection.nativeError u y j ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
        (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  have h1 := native_floor_with_guaranteed_gain u y j a b
  have h2 := native_floor_with_guaranteed_gain u y j (-a) (-b)
  rw [max_def]
  split_ifs <;> assumption

/-- Near-zero groups keep their exact signed linear crossing debit.
The threshold is imposed AFTER every count and cutoff group is joined. -/
def nearDebit (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) (τ : ℝ) : ℝ :=
  ∑ c ∈ K.image g,if |blockTotal K g t c| ≤ τ then
    if blockTotal K g t c < 0 then max (blockTotal K g v c) 0
      else max (-blockTotal K g v c) 0
    else 0

/-- Only the non-near groups receive an inverse-margin price. No group
is dropped: its complementary linear charge remains in `nearDebit`. -/
def farPrice (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) (τ : ℝ) : ℝ :=
  ∑ c ∈ K.image g,if τ < |blockTotal K g t c| then
    blockTotal K g v c^2/(4*|blockTotal K g t c|) else 0

theorem farPrice_nonneg (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (τ : ℝ) : 0 ≤ farPrice K g t v τ := by
  unfold farPrice
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact div_nonneg (sq_nonneg _) (by positivity)
  · exact le_rfl

private theorem crossing_term_linear_le (t v a : ℝ) (ha : 0 ≤ a) :
    (if t < 0 then max (t+a*v) 0 else max (-(t+a*v)) 0) ≤
      a*(if t < 0 then max v 0 else max (-v) 0) := by
  by_cases ht : t < 0
  · simp only [if_pos ht]
    calc
      _ ≤ max (a*v) 0 := max_le_max (by linarith only [ht]) le_rfl
      _ = _ := by simpa only [mul_neg,neg_neg] using max_neg_mul a (-v) ha
  · simp only [if_neg ht]
    calc
      _ ≤ max (-(a*v)) 0 := max_le_max (by linarith only [ht]) le_rfl
      _ = _ := max_neg_mul a v ha

/-- Uniform crossing payment even at arbitrarily small baseline margins.
This avoids a spurious inverse-margin blowup WITHOUT hiding zero groups. -/
theorem crossingCost_le_near_far (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) {τ a : ℝ} (hτ : 0 ≤ τ) (ha : 0 ≤ a) :
    crossingCost K g t v a ≤ a*nearDebit K g t v τ+a^2*farPrice K g t v τ := by
  unfold crossingCost nearDebit farPrice
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  by_cases hn : |blockTotal K g t c| ≤ τ
  · simp only [if_pos hn,if_neg (not_lt.mpr hn),mul_zero,add_zero]
    exact crossing_term_linear_le _ _ _ ha
  · have hf : τ < |blockTotal K g t c| := lt_of_not_ge hn
    have ht : blockTotal K g t c ≠ 0 := by
      intro h
      rw [h,abs_zero] at hf
      exact (not_lt_of_ge hτ) hf
    simp only [if_neg hn,if_pos hf,mul_zero,zero_add]
    have h := crossing_term_le (blockTotal K g t c) (blockTotal K g v c) a ha
    simpa only [if_neg ht,mul_zero,zero_add] using h

/-- Signed correlation AFTER paying every near-margin block. -/
def thresholdAvailable (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (τ : ℝ) : ℝ :=
  max (adverseCorrelation K g t v-nearDebit K g t v τ) 0

/-- A concrete step with no reciprocal of a near-zero block margin. -/
def thresholdStep (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (τ : ℝ) : ℝ :=
  thresholdAvailable K g t v τ/(2*farPrice K g t v τ)

/-- Explicit joined gain with the entire near-margin crossing debit paid. -/
def thresholdGain (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (τ : ℝ) : ℝ :=
  thresholdAvailable K g t v τ^2/(4*farPrice K g t v τ)

theorem thresholdStep_nonneg (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (τ : ℝ) : 0 ≤ thresholdStep K g t v τ := by
  exact div_nonneg (le_max_right _ _)
    (mul_nonneg (by norm_num) (farPrice_nonneg K g t v τ))

theorem thresholdGain_nonneg (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) (τ : ℝ) : 0 ≤ thresholdGain K g t v τ := by
  exact div_nonneg (sq_nonneg _)
    (mul_nonneg (by norm_num) (farPrice_nonneg K g t v τ))

/-- The new gain is a rigorous reduction of the SAME actual signed cost.
Any nonnegative threshold works; it is not an assumed arithmetic saving. -/
theorem thresholdGain_le_saving (K : Finset ℕ) (g : ℕ → ℕ)
    (t v : ℕ → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    thresholdGain K g t v τ ≤ blockCost K g t-
      blockCost K g (fun k => t k+thresholdStep K g t v τ*v k) := by
  have ha := thresholdStep_nonneg K g t v τ
  have h : thresholdStep K g t v τ*(adverseCorrelation K g t v-nearDebit K g t v τ)-
      thresholdStep K g t v τ^2*farPrice K g t v τ ≤ blockCost K g t-
        blockCost K g (fun k => t k+thresholdStep K g t v τ*v k) := by
    rw [blockCost_shift_eq]
    have hc := crossingCost_le_near_far K g t v hτ ha
    linarith only [hc]
  by_cases hH : farPrice K g t v τ=0
  · simp only [thresholdGain,thresholdStep,hH,mul_zero,div_zero,zero_mul,add_zero,
      sub_self,le_refl]
  · by_cases hD : adverseCorrelation K g t v-nearDebit K g t v τ ≤ 0
    · simp only [thresholdGain,thresholdStep,thresholdAvailable,max_eq_right hD,
        zero_div,zero_pow (by norm_num : 2 ≠ 0),zero_mul,add_zero,sub_self,le_refl]
    · have he : thresholdAvailable K g t v τ=
          adverseCorrelation K g t v-nearDebit K g t v τ :=
        max_eq_left (le_of_lt (lt_of_not_ge hD))
      have hq : thresholdStep K g t v τ*
          (adverseCorrelation K g t v-nearDebit K g t v τ)-
            thresholdStep K g t v τ^2*farPrice K g t v τ=thresholdGain K g t v τ := by
        unfold thresholdStep thresholdGain
        rw [he]
        field_simp
        ring
      rwa [hq] at h

/-- A threshold zero is exactly the original guaranteed gain. Thus the
new crossing estimate can retain the old result without a new debit. -/
theorem thresholdGain_zero (K : Finset ℕ) (g : ℕ → ℕ) (t v : ℕ → ℝ) :
    thresholdGain K g t v 0=guaranteedGain K g t v := by
  have hz : nearDebit K g t v 0=zeroDebit K g t v := by
    unfold nearDebit zeroDebit
    apply Finset.sum_congr rfl
    intro c _
    by_cases ht : blockTotal K g t c=0
    · simp [ht]
    · have hh : ¬|blockTotal K g t c| ≤ 0 := by
        simpa only [abs_nonpos_iff] using ht
      simp [ht,hh]
  have hh : farPrice K g t v 0=crossingPrice K g t v := by
    unfold farPrice crossingPrice
    apply Finset.sum_congr rfl
    intro c _
    by_cases ht : blockTotal K g t c=0
    · simp [ht]
    · simp [abs_pos.mpr ht]
  simp only [thresholdGain,thresholdAvailable,guaranteedGain,availableCorrelation,hz,hh]

/-- Lower bound for the existing literal cubic credit using the sharpened
crossing payment. Its value must still be bounded on the prime population. -/
theorem credit_ge_thresholdGain (X N : ℕ) (S : Finset ℕ) (W : ℕ → ℂ)
    (L : ℝ) (g : ℕ → ℕ) (B a b : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    let t := ZetaRieszComplexNullFloor.increment X N S W L
      (ZetaRieszComplexNullFloor.bestParameters X N S W L g B)
    let v := cubicIncrement X N S W a b;
    thresholdGain (Finset.Icc 1 X) g t v τ ≤ credit X N S W L g B
      (thresholdStep (Finset.Icc 1 X) g t v τ*a)
      (thresholdStep (Finset.Icc 1 X) g t v τ*b) := by
  dsimp only
  let p := ZetaRieszComplexNullFloor.bestParameters X N S W L g B
  let t := ZetaRieszComplexNullFloor.increment X N S W L p
  let v := cubicIncrement X N S W a b
  let r := thresholdStep (Finset.Icc 1 X) g t v τ
  have hc : correctedCost X N S W L g p (r*a) (r*b)=
      blockCost (Finset.Icc 1 X) g (fun k => t k+r*v k) := by
    unfold correctedCost
    simp only [cubicIncrement_scaled]
    rfl
  have hg := thresholdGain_le_saving (Finset.Icc 1 X) g t v hτ
  change thresholdGain (Finset.Icc 1 X) g t v τ ≤
    max (ZetaRieszComplexNullFloor.bestCost X N S W L g B-
      correctedCost X N S W L g p (r*a) (r*b)) 0
  rw [hc]
  exact hg.trans (le_max_left _ _)

/-- Threshold step on the original native endpoint and complete population. -/
def nativeThresholdStep (u y : ℝ) (j : ℕ) (a b τ : ℝ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let W := sourceWeight A L u y N
  thresholdStep (Finset.Icc 1 X) (cutoffPeriod y)
    (ZetaRieszComplexNullFloor.increment X N (S.filter Squarefree) W L
      (ZetaRieszComplexNullFloor.bestParameters X N (S.filter Squarefree) W L (cutoffPeriod y) 4))
    (cubicIncrement X N (S.filter Squarefree) W a b) τ

/-- A fully priced lower credit, retaining the original native masks. -/
def nativeThresholdGain (u y : ℝ) (j : ℕ) (a b τ : ℝ) : ℝ :=
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let W := sourceWeight A L u y N
  thresholdGain (Finset.Icc 1 X) (cutoffPeriod y)
    (ZetaRieszComplexNullFloor.increment X N (S.filter Squarefree) W L
      (ZetaRieszComplexNullFloor.bestParameters X N (S.filter Squarefree) W L (cutoffPeriod y) 4))
    (cubicIncrement X N (S.filter Squarefree) W a b) τ

theorem nativeThresholdGain_nonneg (u y : ℝ) (j : ℕ) (a b τ : ℝ) :
    0 ≤ nativeThresholdGain u y j a b τ := thresholdGain_nonneg _ _ _ _ _

theorem nativeThresholdGain_le_credit (u y : ℝ) (j : ℕ) (a b : ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    nativeThresholdGain u y j a b τ ≤ ZetaRieszSignedNullGain.nativeCredit u y j
      (nativeThresholdStep u y j a b τ*a) (nativeThresholdStep u y j a b τ*b) := by
  unfold nativeThresholdGain nativeThresholdStep ZetaRieszSignedNullGain.nativeCredit
  dsimp only
  exact credit_ge_thresholdGain _ _ _ _ _ _ _ _ _ hτ

/-- All threshold gains are funded by the SAME old native price. -/
theorem nativeThresholdGain_le_cost (u y : ℝ) (j : ℕ) (a b : ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    nativeThresholdGain u y j a b τ ≤ ZetaRieszComplexNullFloor.nativeCost u y j := by
  apply (nativeThresholdGain_le_credit u y j a b hτ).trans
  exact credit_le_bestCost _ _ _ _ _ _ _ _ _

/-- The original quantitative credit is retained at threshold zero. -/
theorem nativeThresholdGain_zero (u y : ℝ) (j : ℕ) (a b : ℝ) :
    nativeThresholdGain u y j a b 0=nativeGuaranteedGain u y j a b := by
  unfold nativeThresholdGain nativeGuaranteedGain
  dsimp only
  exact thresholdGain_zero _ _ _ _

/-- Sharpen the ACTUAL joint floor without near-zero reciprocal losses.
No numerical value or cofinal smallness of the signed native price is assumed. -/
theorem native_floor_with_threshold_gain (u y : ℝ) (j : ℕ) (a b : ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    -ZetaRieszComplexNullFloor.nativeCost u y j+nativeThresholdGain u y j a b τ-
      ZetaRieszComplexProjection.nativeError u y j ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
        (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  have hf := native_floor_with_credit u y j
    (nativeThresholdStep u y j a b τ*a) (nativeThresholdStep u y j a b τ*b)
  have hg := nativeThresholdGain_le_credit u y j a b hτ
  linarith only [hf,hg]

/-- Keep the better fully paid orientation, never add two savings
against the same old price. All original cutoff groups remain assembled. -/
theorem native_floor_with_best_threshold_gain (u y : ℝ) (j : ℕ) (a b : ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    -ZetaRieszComplexNullFloor.nativeCost u y j+
      max (nativeThresholdGain u y j a b τ) (nativeThresholdGain u y j (-a) (-b) τ)-
        ZetaRieszComplexProjection.nativeError u y j ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
        (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  have h1 := native_floor_with_threshold_gain u y j a b hτ
  have h2 := native_floor_with_threshold_gain u y j (-a) (-b) hτ
  rw [max_def]
  split_ifs <;> assumption

/-- An exact unit regression: the tiny-margin block is CHARGED, not
discarded, yet a substantial signed saving survives. This is not a native
prime population, and its constant must not be used for the RH floor. -/
theorem threshold_tiny_margin_regression :
    thresholdGain (Finset.range 3) id
      (fun k => if k=0 then -(1/1000000 : ℝ) else if k=1 then -1 else 1)
      (fun k => if k < 2 then 1 else -2) (1/1000000)=1/5 := by
  norm_num [thresholdGain,thresholdAvailable,adverseCorrelation,nearDebit,farPrice,
    blockTotal,Finset.sum_range_succ]

end RiemannGaussian.ZetaRieszQuantitativeNullStep
