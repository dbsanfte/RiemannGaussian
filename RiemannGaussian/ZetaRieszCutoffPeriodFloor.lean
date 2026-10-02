/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRejoinedPhaseFloor
import RiemannGaussian.ZetaRieszSharpOwnerPayment
import RiemannGaussian.ZetaRieszSignedConvolution

/-!
# Signed cutoff periods in the whole funded floor

Join the original labels/counts/funding first, then the divisor cutoffs in
each logarithmic phase period. Only an adverse COMPLETE period is charged.
The original phase and all masks remain. Quadratic logarithmic profiles
annihilate every squarefree label with at least three prime factors, so
their coefficients can be chosen before this signed price is measured.

This is an unconditional lower inequality for the existing finite sum,
with an explicit cost uniformly below the former one-sided energy cost
when the original profile is used. A source-scale numerical bound for the
new joint cost remains open. No bin orthogonality or power saving is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCutoffPeriodFloor
open ZetaRieszCofactorPhaseEnergy ZetaRieszCenteredPrimeEnergy
open ZetaRieszRejoinedPhaseFloor ZetaRieszJointAllocation ZetaRieszJointPrimeEnergy

/-- Group a COMPLETE signed cutoff increment, without clipping its labels
or its divisor summands. All finite boundary groups are retained. -/
def blockTotal (K : Finset ℕ) (g : ℕ → ℕ) (t : ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑ k ∈ K.filter (fun k => g k = b), t k

/-- Only the adverse net contribution of each full cutoff group is paid. -/
def blockCost (K : Finset ℕ) (g : ℕ → ℕ) (t : ℕ → ℝ) : ℝ :=
  ∑ b ∈ K.image g, max (-blockTotal K g t b) 0

/-- Every cutoff belongs to exactly one group; no edge or empty divisor
channel has been completed or omitted. -/
theorem sum_blockTotal (K : Finset ℕ) (g : ℕ → ℕ) (t : ℕ → ℝ) :
    (∑ b ∈ K.image g, blockTotal K g t b) = ∑ k ∈ K, t k := by
  exact Finset.sum_fiberwise_of_maps_to (fun k hk => Finset.mem_image.mpr ⟨k,hk,rfl⟩) t

private theorem max_neg_eq (x : ℝ) : max (-x) 0 = (|x|-x)/2 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx,max_eq_right (by linarith : -x ≤ 0)]
    ring
  · rw [abs_of_neg (lt_of_not_ge hx),max_eq_left (by linarith : 0 ≤ -x)]
    ring

/-- The price is half the total block variation minus the unchanged
signed sum. This retains cancellation between different cutoff signs. -/
theorem blockCost_eq (K : Finset ℕ) (g : ℕ → ℕ) (t : ℕ → ℝ) :
    blockCost K g t =
      ((∑ b ∈ K.image g, |blockTotal K g t b|)-(∑ k ∈ K,t k))/2 := by
  simp only [blockCost,max_neg_eq,← Finset.sum_div,Finset.sum_sub_distrib,sum_blockTotal]

/-- The full signed sum has this independent finite lower inequality. -/
theorem block_floor (K : Finset ℕ) (g : ℕ → ℕ) (t : ℕ → ℝ) :
    -blockCost K g t ≤ ∑ k ∈ K,t k := by
  rw [← sum_blockTotal K g t,blockCost,← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum (fun b _ => by
    have h := le_max_left (-blockTotal K g t b) 0
    linarith)

/-- Joining cutoff groups cannot cost more than clipping each cutoff
separately. It can improve the floor even after all labels are joined. -/
theorem blockCost_le_atomic (K : Finset ℕ) (g : ℕ → ℕ) (t : ℕ → ℝ) :
    blockCost K g t ≤ ∑ k ∈ K, max (-t k) 0 := by
  rw [blockCost_eq]
  have h : (∑ b ∈ K.image g,|blockTotal K g t b|) ≤ ∑ k ∈ K,|t k| := by
    calc
      _ ≤ ∑ b ∈ K.image g, ∑ k ∈ K.filter (fun k => g k=b),|t k| :=
        Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun k hk => Finset.mem_image.mpr ⟨k,hk,rfl⟩) (fun k => |t k|)
  simp only [max_neg_eq,← Finset.sum_div,Finset.sum_sub_distrib]
  linarith

/-- The saving is EXACTLY the cutoff variation cancelled within groups.
There is no prescribed sign or correlation on the right. -/
theorem block_saving_eq (K : Finset ℕ) (g : ℕ → ℕ) (t : ℕ → ℝ) :
    (∑ k ∈ K,max (-t k) 0)-blockCost K g t =
      ((∑ k ∈ K,|t k|)-(∑ b ∈ K.image g,|blockTotal K g t b|))/2 := by
  rw [blockCost_eq]
  simp only [max_neg_eq,← Finset.sum_div,Finset.sum_sub_distrib]
  ring

/-- The original complete cutoff increments, with the FULL signed
correlation inside each term. This is a cost, not another carrier. -/
def groupedCost (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (g : ℕ → ℕ) : ℝ :=
  blockCost (activeCutoffs X f) g (fun k => correlation S w k*(f k-f (k+1)))

private theorem prefix_pairing (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (hend : f (X+1)=0) :
    (∑ n ∈ S,w n*(∑ d ∈ Finset.Icc 1 X,
      f d*(if d ∣ n then (μ d : ℝ) else 0))) =
        ∑ k ∈ activeCutoffs X f,correlation S w k*(f k-f (k+1)) := by
  simp_rw [ZetaRieszSignedCutoffEnergy.abel_profile X f _ hend,Finset.mul_sum]
  rw [Finset.sum_comm]
  symm
  apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).trans
  · apply Finset.sum_congr rfl
    intro k _
    simp only [correlation,sharp,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum,Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  · intro k hk hn
    have he : f k=f (k+1) := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hk,h⟩)
    simp [he]

/-- Complete signed cutoff-period cancellation is retained before the
one-sided price. All original weights and the actual prefix are unchanged. -/
theorem grouped_prefix_floor (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (g : ℕ → ℕ) (hend : f (X+1)=0) :
    -groupedCost X S w f g ≤ ∑ n ∈ S,w n*(∑ d ∈ Finset.Icc 1 X,
      f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
  rw [prefix_pairing X S w f hend]
  exact block_floor _ _ _

/-- Clipping individual complete prefix increments already costs no
more than the earlier one-sided Cauchy price. -/
theorem atomicCost_le_negativeCost (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    (∑ k ∈ activeCutoffs X f,max (-(correlation S w k*(f k-f (k+1)))) 0) ≤
      negativeCost X S w f := by
  let K := negativeCutoffs X S w f
  have hK : K ⊆ activeCutoffs X f := Finset.filter_subset _ _
  have he : (∑ k ∈ activeCutoffs X f,max (-(correlation S w k*(f k-f (k+1)))) 0) =
      -∑ k ∈ K,correlation S w k*(f k-f (k+1)) := by
    rw [← Finset.sum_neg_distrib]
    symm
    have hterm (k : ℕ) (hk : k ∈ K) :
        -(correlation S w k*(f k-f (k+1))) =
          max (-(correlation S w k*(f k-f (k+1)))) 0 := by
      have hn := (Finset.mem_filter.mp hk).2
      rw [max_eq_left (by linarith)]
    have hnon (k : ℕ) (hk : k ∈ activeCutoffs X f) (hn : k ∉ K) :
        max (-(correlation S w k*(f k-f (k+1)))) 0 = 0 := by
      have hnon : 0 ≤ correlation S w k*(f k-f (k+1)) := by
        by_contra h
        exact hn (Finset.mem_filter.mpr ⟨hk,lt_of_not_ge h⟩)
      exact max_eq_right (by linarith)
    exact (Finset.sum_congr rfl hterm).trans (Finset.sum_subset hK hnon)
  have hb : |∑ k ∈ K,correlation S w k*(f k-f (k+1))| ≤ negativeCost X S w f := by
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs,sq_sqrt (by
      apply mul_nonneg
      · exact Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      · exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul K
      (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hK hk)).1).1
      exact_mod_cast (by omega : k ≠ 0)
    apply le_of_eq
    field_simp
  rw [he]
  exact (neg_le_abs _).trans hb

/-- A uniform finite improvement for the SAME weights and profile.
No cancellation sign, source estimate or different population is assumed. -/
theorem groupedCost_le_negativeCost (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (g : ℕ → ℕ) :
    groupedCost X S w f g ≤ negativeCost X S w f :=
  (blockCost_le_atomic _ _ _).trans (atomicCost_le_negativeCost X S w f)

/-- The complete squared-log moment vanishes on every original squarefree
label with count at least three. This includes signed funding labels. -/
theorem quadratic_divisor_zero {n : ℕ} (hn : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) :
    (∑ d ∈ n.divisors,(μ d : ℝ)*(log d)^2) = 0 := by
  have h := ZetaRieszSignedConvolution.higher_count_quadratic_cancellation hn hc 0 1 0 1
  simp only [ZetaRieszSignedConvolution.pairHinge,Nat.cast_one,log_one,
    zero_add,sub_zero,sub_self,mul_zero,Finset.sum_const_zero,one_mul,
    zero_sub,mul_neg,← pow_two,Finset.sum_neg_distrib] at h
  rw [Nat.sum_divisorsAntidiagonal' (fun _ b => (μ b : ℝ)*(log b)^2)] at h
  linarith

/-- Both exact null moments are subtracted inside the ORIGINAL profile;
no count, label, phase, allocation or physical mask is changed. -/
def correctedProfile (X : ℕ) (L linear quadratic : ℝ) : ℕ → ℝ :=
  centeredProfile X (fun d => max 0 (L-log d)+quadratic*(log d)^2) linear

/-- Unit logarithmic correction is exactly constant below the hinge.
No roughness, count, phase or funding assumption enters this identity. -/
theorem correctedProfile_flat {X k : ℕ} (hk : k ≤ X) {L : ℝ} (hL : log k ≤ L) :
    correctedProfile X L 1 0 k = L-(max 0 (L-log X)+log X) := by
  simp only [correctedProfile,zero_mul,add_zero,centeredProfile,if_pos hk,one_mul,
    max_eq_right (sub_nonneg.mpr hL)]
  ring

/-- Every early cutoff is EXACTLY inactive with unit logarithmic
correction. The coherent first/rough-prefix channel is not norm-priced. -/
theorem low_cutoff_inactive (X k : ℕ) {L : ℝ} (hL : log (k+1 : ℕ) ≤ L) :
    k ∉ activeCutoffs X (correctedProfile X L 1 0) := by
  intro h
  obtain ⟨hk,hneq⟩ := Finset.mem_filter.mp h
  obtain ⟨hk1,hkX⟩ := Finset.mem_Icc.mp hk
  by_cases he : k=X
  · subst k
    simp [correctedProfile,centeredProfile] at hneq
  · have hknext : k+1 ≤ X := by omega
    have hklog : log k ≤ log (k+1 : ℕ) := log_le_log
      (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast Nat.le_succ k)
    exact hneq ((correctedProfile_flat hkX (hklog.trans hL)).trans
      (correctedProfile_flat hknext hL).symm)

/-- Only the literal post-hinge tail can enter the resulting whole-floor
cost. This does not pay that surviving signed tail. -/
theorem active_cutoff_after_length {X k : ℕ} {L : ℝ}
    (hk : k ∈ activeCutoffs X (correctedProfile X L 1 0)) :
    L < log (k+1 : ℕ) := by
  by_contra h
  exact low_cutoff_inactive X k (le_of_not_gt h) hk

/-- Every original label retains exactly its original Riesz response,
for arbitrary coefficients of both logarithmic null moments. -/
theorem corrected_prefix_eq {n X : ℕ} (hn : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) (hX : n ≤ X) (L linear quadratic : ℝ) :
    (∑ d ∈ Finset.Icc 1 X,correctedProfile X L linear quadratic d*
      (if d ∣ n then (μ d : ℝ) else 0)) = VaughanLogAverage.riesz L n := by
  have hn1 : n ≠ 1 := by intro h; subst n; simp at hc
  have hnp : ¬n.Prime := by intro h; simp [h.primeFactors] at hc
  rw [prefix_eq_divisors (Nat.pos_of_ne_zero hn.ne_zero) hX,
    correctedProfile,divisor_centering hn hnp hn1 hX]
  simp only [mul_add,Finset.sum_add_distrib]
  have hq : (∑ d ∈ n.divisors,(μ d : ℝ)*(quadratic*(log d)^2)) =
      quadratic*(∑ d ∈ n.divisors,(μ d : ℝ)*(log d)^2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hq,quadratic_divisor_zero hn hc,mul_zero,add_zero]
  rfl

/-- Exact correction on the full masked literal sum, including arbitrary
signed population coefficients. Low divisor/factorial channels remain. -/
theorem weighted_corrected_eq_prefix (A B : Finset ℕ) (N : ℕ)
    (L y linear quadratic : ℝ) (q : ℕ → ℝ)
    (hB : ∀ n ∈ B,3 ≤ n.primeFactors.card) :
    let X := max 1 (B.sup id)
    let f := correctedProfile X L linear quadratic
    (∑ n ∈ B,q n*(residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) =
        ∑ n ∈ B.filter Squarefree,(q n*primeWeight A L y N n 1)*
          (∑ d ∈ Finset.Icc 1 X,f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
  have h := weighted_residual_eq_prefix A B N L y linear q hB
  dsimp only at h ⊢
  apply h.trans
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hnB,hs⟩ := Finset.mem_filter.mp hn
  have hX : n ≤ max 1 (B.sup id) := (Finset.le_sup (f := id) hnB).trans (le_max_right _ _)
  have hzero := corrected_prefix_eq hs (hB n hnB) hX L linear 0
  simp only [correctedProfile,zero_mul,add_zero] at hzero
  rw [hzero,corrected_prefix_eq hs (hB n hnB) hX]

/-- A direct unconditional lower bound for the literal signed sum using
complete cutoff groups and both exact null moments. -/
theorem weighted_grouped_floor (A B : Finset ℕ) (N : ℕ)
    (L y linear quadratic : ℝ) (q : ℕ → ℝ) (g : ℕ → ℕ)
    (hB : ∀ n ∈ B,3 ≤ n.primeFactors.card) :
    let X := max 1 (B.sup id)
    let f := correctedProfile X L linear quadratic;
    -groupedCost X (B.filter Squarefree) (fun n => q n*primeWeight A L y N n 1) f g ≤
      ∑ n ∈ B,q n*(residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  let X := max 1 (B.sup id)
  let f := correctedProfile X L linear quadratic
  have h := grouped_prefix_floor X (B.filter Squarefree)
    (fun n => q n*primeWeight A L y N n 1) f g (by simp [f,correctedProfile,centeredProfile])
  rw [← weighted_corrected_eq_prefix A B N L y linear quadratic q hB] at h
  exact h

/-- Canonical logarithmic phase-period grouping of the actual divisor
cutoffs. Partial first/last periods stay in the exact finite cost. -/
def cutoffPeriod (y : ℝ) (d : ℕ) : ℕ := ⌊y*log d/(2*Real.pi)⌋₊

/-- The complete retained ledger has one signed lower bound after joining
ALL populations/funding, then their cutoff periods. Original overlaps,
credits, debit and both null moments are retained exactly. -/
theorem rejoined_funding_grouped_floor (A H P T Y : Finset ℕ) (N : ℕ)
    (L y scale linear quadratic debit : ℝ) (g : ℕ → ℕ)
    (hB : ∀ n ∈ ((H ∪ P) ∪ T) ∪ Y,3 ≤ n.primeFactors.card) :
    let atom := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    let U := ((H ∪ P) ∪ T) ∪ Y
    let X := max 1 (U.sup id)
    let f := correctedProfile X L linear quadratic
    let a : ℝ := if 0 ≤ (∑ n ∈ P,atom n).re then 1 else 0
    let b : ℝ := if 0 ≤ (∑ n ∈ T,atom n).re then 1 else 0
    let w := fun n => (scale*rejoinedWeights H P T Y a b debit n)*primeWeight A L y N n 1;
    -groupedCost X (U.filter Squarefree) w f g ≤
      scale*((∑ n ∈ H,atom n).re+max (∑ n ∈ P,atom n).re 0+
        max (∑ n ∈ T,atom n).re 0-debit*(∑ n ∈ Y,atom n).re) := by
  let atom := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let a : ℝ := if 0 ≤ (∑ n ∈ P,atom n).re then 1 else 0
  let b : ℝ := if 0 ≤ (∑ n ∈ T,atom n).re then 1 else 0
  have ha : a*(∑ n ∈ P,atom n).re=max (∑ n ∈ P,atom n).re 0 := by
    dsimp [a]
    split_ifs with h
    · rw [one_mul,max_eq_left h]
    · rw [zero_mul,max_eq_right (le_of_lt (lt_of_not_ge h))]
  have hb : b*(∑ n ∈ T,atom n).re=max (∑ n ∈ T,atom n).re 0 := by
    dsimp [b]
    split_ifs with h
    · rw [one_mul,max_eq_left h]
    · rw [zero_mul,max_eq_right (le_of_lt (lt_of_not_ge h))]
  have hs : (∑ n ∈ ((H ∪ P) ∪ T) ∪ Y,
      (scale*rejoinedWeights H P T Y a b debit n)*(atom n).re) =
        scale*((∑ n ∈ H,atom n).re+max (∑ n ∈ P,atom n).re 0+
          max (∑ n ∈ T,atom n).re 0-debit*(∑ n ∈ Y,atom n).re) := by
    simp only [mul_assoc,← Finset.mul_sum]
    rw [rejoined_weight_sum H P T Y a b debit (fun n => (atom n).re)]
    simp only [← Complex.re_sum,ha,hb]
  have h := weighted_grouped_floor A (((H ∪ P) ∪ T) ∪ Y) N L y linear quadratic
    (fun n => scale*rejoinedWeights H P T Y a b debit n) g hB
  dsimp only at h ⊢
  change -_ ≤ (∑ n ∈ ((H ∪ P) ∪ T) ∪ Y,
    (scale*rejoinedWeights H P T Y a b debit n)*(atom n).re) at h
  rw [hs] at h
  exact h

open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszRejoinedPopulationFloor ZetaRieszJoinedPopulationFloor ZetaRieszFewBinCoverFloor
open ZetaRieszSevenCountTail
open ZetaRieszLowCountRefund (tailCost)

/-- A whole-floor inequality on the current native unpaid population,
with both EXACT null moments and signed cutoff-period cancellation.
The SAME funding witness, credit/debit and source-o(1) error remain.
An independent eventual bound for this combined price is still required. -/
theorem eventually_joined_period_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y)
    (linear quadratic : ℕ → ℝ) :
    ∃ h c κ : ℝ, 0 < h ∧ h ≤ 1/20 ∧ 0 < c ∧ 0 < κ ∧
      ∀ ε : ℝ, 0 < ε → ∃ err : ℕ → ℝ,
      (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let A := intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S₀ := coreBand u N K
        let atom := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Paid := (S₀.filter (fun n : ℕ =>
          3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪
            bin56Band u N K
        let H := (S₀ \ (Paid ∪ wholeTail S₀ N 0)) \ ZetaRieszSharpOwnerPayment.sector u N K
        let Ts := radialTail S₀ N 0
        let Ys := radialSupply N h v
        let U := ((H ∪ Paid) ∪ Ts) ∪ Ys
        let X := max 1 (U.sup id)
        let f := correctedProfile X L (linear N) (quadratic N)
        let a : ℝ := if 0 ≤ (∑ n ∈ Paid,atom n).re then 1 else 0
        let b : ℝ := if 0 ≤ (∑ n ∈ Ts,atom n).re then 1 else 0
        let debit := tailCost c N+ε+growingDebit κ N
        let w := fun n => (u^(N+1)*rejoinedWeights H Paid Ts Ys a b debit n)*primeWeight A L y N n 1
        0 < (∑ n ∈ Ys,atom n).re ∧
          -groupedCost X (U.filter Squarefree) w f (cutoffPeriod y)-err j ≤
            ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ :=
    ZetaRieszSharpOwnerPayment.eventually_rejoined_floor hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨err,he0,he,hfloor⟩ := hbase ε hε
  refine ⟨err,he0,he,?_⟩
  filter_upwards [hfloor,tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1000 : ℕ))]
    with j hj hN
  obtain ⟨v,hv,hpos,hbound⟩ := hj
  refine ⟨v,hv,hpos,?_⟩
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S₀ := coreBand u N K
  let Paid := (S₀.filter (fun n : ℕ =>
    3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪
      bin56Band u N K
  let H := (S₀ \ (Paid ∪ wholeTail S₀ N 0)) \ ZetaRieszSharpOwnerPayment.sector u N K
  let Ts := radialTail S₀ N 0
  let Ys := radialSupply N h v
  have hpaid : Paid ⊆ S₀ := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn|hn
    · rcases Finset.mem_union.mp hn with hn|hn
      · exact (Finset.mem_filter.mp hn).1
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
  have hcounts : ∀ n ∈ ((H ∪ Paid) ∪ Ts) ∪ Ys,3 ≤ n.primeFactors.card := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn|hn
    · rcases Finset.mem_union.mp hn with hn|hn
      · rcases Finset.mem_union.mp hn with hn|hn
        · exact ZetaRieszJointPrimeEnergy.core_count
            (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hn).1).1
        · exact ZetaRieszJointPrimeEnergy.core_count (hpaid hn)
      · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
        exact ZetaRieszJointPrimeEnergy.core_count (Finset.mem_filter.mp hn).1
    · have hc := ZetaRieszRoughFivePeriodFloor.radialSupply_count hN hh hhu v hv hn
      omega
  have hphase := rejoined_funding_grouped_floor A H Paid Ts Ys N L y
    (u^(N+1)) (linear N) (quadratic N) (tailCost c N+ε+growingDebit κ N) (cutoffPeriod y) hcounts
  dsimp only [N,K,A,L,S₀,H,Paid,Ts,Ys] at hphase
  dsimp only at hbound ⊢
  nlinarith only [hphase,hbound]

end RiemannGaussian.ZetaRieszCutoffPeriodFloor
