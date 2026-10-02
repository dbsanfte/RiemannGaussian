/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerHingeCancellation
import RiemannGaussian.ZetaRieszManyBinPhaseAudit

/-!
# One signed phase energy after rejoining every owner and count

The original residual atom has a common total-integer Riesz profile.
Its factorial/phase weight is independent of the choice of marked owner
after its product label is fixed. Apply the EXISTING signed prefix energy
on that label axis before splitting owners, counts, bins or radial periods.

This gives an unconditional finite signed inequality with no comparison
variation and no arithmetic hypothesis. The explicit weighted phase energy
still needs a source-scale bound. Joining disjoint populations in this
same profile never increases their combined energy cost; all cross terms
remain. The complete floor includes its original funding before the
square; favorable complete prefix increments are left uncharged by the
stronger one-sided cost. No numerical -79/1000 floor or zero exclusion is
asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszRejoinedPhaseFloor
open Real ZetaRieszJointPrimeEnergy ZetaRieszCenteredPrimeEnergy
open ZetaRieszCofactorPhaseEnergy ZetaRieszJointAllocation

/-- Once the product label is fixed, the original factorial/allocation
weight is exactly independent of its marked prime incidence. -/
theorem primeWeight_product (A : Finset ℕ) (L y : ℝ) (N : ℕ)
    {a p : ℕ} (ha : 0 < a) (hp : 0 < p) :
    primeWeight A L y N a p = primeWeight A L y N (p*a) 1 := by
  have hl : log (p*a : ℕ)=log p+log a := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast ha.ne')]
  simp only [primeWeight,one_mul,Nat.cast_one,log_one,zero_add,mul_one]
  rw [hl,Nat.cast_mul]
  ring

/-- Rejoining the two owner hinges gives the original Riesz profile of
the TOTAL integer. Its full phase and allocation are unchanged. -/
theorem residual_atom_total_riesz (A : Finset ℕ) (L y scale : ℝ) (N : ℕ)
    {n : ℕ} (hn : Squarefree n) (hnp : ¬n.Prime) :
    scale*(residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re =
      (scale*primeWeight A L y N n 1)*VaughanLogAverage.riesz L n := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn.ne_zero
  have he : exp (-(3/2 : ℝ)*log n)=exp (-log n/2)/(n : ℝ) := by
    calc
      _ = exp (-log n/2-log n) := by congr 1; ring
      _ = exp (-log n/2)/exp (log n) := exp_sub _ _
      _ = _ := by rw [exp_log hnR]
  rw [ZetaRieszManyBinPhaseAudit.re_residual_atom,
    SquarefreeVaughanLogSource.coefficient,if_pos ⟨hn,hnp⟩]
  simp only [Complex.ofReal_re]
  simp only [primeWeight,one_mul,Nat.cast_one,log_one,zero_add,pow_succ,he]
  ring

/-- The old constant-free signed prefix cost, on the original product
labels. This is NOT a new Gram carrier or a completed arithmetic sum. -/
def wholeCost (A B : Finset ℕ) (N : ℕ) (L y scale slope : ℝ) : ℝ :=
  let X := max 1 (B.sup id)
  let f := centeredProfile X (fun d => max 0 (L-log d)) slope
  sqrt (phaseEnergy X (B.filter Squarefree)
    (fun n => scale*primeWeight A L y N n 1) f*profileEnergy X f)

/-- Arbitrary signed population coefficients stay INSIDE the original
total-label prefix. This also permits joining the existing funding debit
with the unpaid population before any square or norm. -/
theorem weighted_residual_eq_prefix (A B : Finset ℕ) (N : ℕ)
    (L y slope : ℝ) (q : ℕ → ℝ)
    (hB : ∀ n ∈ B, 3 ≤ n.primeFactors.card) :
    let X := max 1 (B.sup id)
    let f := centeredProfile X (fun d => max 0 (L-log d)) slope
    (∑ n ∈ B,q n*(residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) =
        ∑ n ∈ B.filter Squarefree,(q n*primeWeight A L y N n 1)*
          (∑ d ∈ Finset.Icc 1 X,f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
  let X := max 1 (B.sup id)
  let f := centeredProfile X (fun d => max 0 (L-log d)) slope
  let S := B.filter Squarefree
  have he n (hn : n ∈ S) :
      (∑ d ∈ Finset.Icc 1 X,f d*(if d ∣ n then (μ d : ℝ) else 0)) =
        VaughanLogAverage.riesz L n := by
    obtain ⟨hnB,hSF⟩ := Finset.mem_filter.mp hn
    have hn1 : n ≠ 1 := by intro h; simpa [h] using hB n hnB
    have hnp : ¬n.Prime := by
      intro h
      have hc := hB n hnB
      simp [h.primeFactors] at hc
    have hnX : n ≤ X := (Finset.le_sup (f := id) hnB).trans (le_max_right _ _)
    rw [prefix_eq_divisors (Nat.pos_of_ne_zero hSF.ne_zero) hnX,
      divisor_centering hSF hnp hn1 hnX]
    rfl
  have hb : (∑ n ∈ B,q n*(residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) =
        ∑ n ∈ S,q n*(residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hout
    have hsf : ¬Squarefree n := fun h => hout (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hsf]
  rw [hb]
  apply Finset.sum_congr rfl
  intro n hn
  have h := Finset.mem_filter.mp hn
  have hnp : ¬n.Prime := by
    intro hp
    have hc := hB n h.1
    simp [hp.primeFactors] at hc
  rw [he n hn,residual_atom_total_riesz A L y (q n) N h.2 hnp]

/-- Both signed bounds for arbitrary REAL population weights, including
the original negative funding coefficient. No signed component is priced
separately, and no arithmetic cancellation premise is introduced. -/
theorem weighted_signed_bounds (A B : Finset ℕ) (N : ℕ)
    (L y slope : ℝ) (q : ℕ → ℝ)
    (hB : ∀ n ∈ B, 3 ≤ n.primeFactors.card) :
    let X := max 1 (B.sup id)
    let f := centeredProfile X (fun d => max 0 (L-log d)) slope
    let J := ∑ n ∈ B,q n*(residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    let C := sqrt (phaseEnergy X (B.filter Squarefree)
      (fun n => q n*primeWeight A L y N n 1) f*profileEnergy X f);
    -C ≤ J ∧ J ≤ C := by
  let X := max 1 (B.sup id)
  let f := centeredProfile X (fun d => max 0 (L-log d)) slope
  have hb := signed_prefix_bound X (B.filter Squarefree)
    (fun n => q n*primeWeight A L y N n 1) f (by simp [f,centeredProfile])
  rw [← weighted_residual_eq_prefix A B N L y slope q hB] at hb
  exact abs_le.mp hb

/-- Both signed bounds for EVERY original population with at least
three factors. Counts/owners/bins/periods are joined before the square.
There is no adjacent-variation cost, density approximation or unpaid
arithmetic premise in this inequality. Its explicit energy cost is open. -/
theorem whole_signed_bounds (A B : Finset ℕ) (N : ℕ) (L y scale slope : ℝ)
    (hB : ∀ n ∈ B, 3 ≤ n.primeFactors.card) :
    let J := scale*(∑ n ∈ B,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re;
    let C := wholeCost A B N L y scale slope;
    -C ≤ J ∧ J ≤ C := by
  simpa only [Complex.re_sum,Finset.mul_sum,wholeCost] using
    weighted_signed_bounds A B N L y slope (fun _ => scale) hB

private theorem phaseEnergy_nonneg (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    0 ≤ phaseEnergy X S w f :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

/-- The literal cross-population correlation is kept with its sign.
No diagonal-only or prime-bin orthogonality assumption is introduced. -/
theorem phaseEnergy_union (X : ℕ) (S T : Finset ℕ) (w f : ℕ → ℝ)
    (hST : Disjoint S T) :
    phaseEnergy X (S ∪ T) w f = phaseEnergy X S w f+phaseEnergy X T w f+
      2*(∑ k ∈ activeCutoffs X f,
        correlation S w k*correlation T w k/(k : ℝ)) := by
  have h k : correlation (S ∪ T) w k=correlation S w k+correlation T w k :=
    Finset.sum_union hST
  simp only [phaseEnergy,h,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Cauchy--Schwarz is applied AFTER the whole signed cofactor sums.
This controls the retained cross term without replacing its sign. -/
theorem phaseEnergy_cross_bound (X : ℕ) (S T : Finset ℕ) (w f : ℕ → ℝ) :
    |∑ k ∈ activeCutoffs X f,
      correlation S w k*correlation T w k/(k : ℝ)| ≤
        sqrt (phaseEnergy X S w f*phaseEnergy X T w f) := by
  apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
  rw [sq_abs,sq_sqrt (mul_nonneg (phaseEnergy_nonneg X S w f)
    (phaseEnergy_nonneg X T w f))]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (activeCutoffs X f)
    (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  intro k hk
  have hk0 : (k : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    exact_mod_cast (by omega : k ≠ 0)
  apply le_of_eq
  field_simp

/-- Joining all signed populations under this COMMON profile can never
cost more than summing their separate square-root costs. Actual negative
cross correlations give strict savings; occupancy alone does not. -/
theorem joined_cost_le (X : ℕ) (S T : Finset ℕ) (w f : ℕ → ℝ)
    (hST : Disjoint S T) {P : ℝ} :
    sqrt (phaseEnergy X (S ∪ T) w f*P) ≤
      sqrt (phaseEnergy X S w f*P)+sqrt (phaseEnergy X T w f*P) := by
  have hS := phaseEnergy_nonneg X S w f
  have hT := phaseEnergy_nonneg X T w f
  have hU := phaseEnergy_nonneg X (S ∪ T) w f
  have hcross := le_trans (le_abs_self _) (phaseEnergy_cross_bound X S T w f)
  rw [sqrt_mul hS] at hcross
  have hroot : sqrt (phaseEnergy X (S ∪ T) w f) ≤
      sqrt (phaseEnergy X S w f)+sqrt (phaseEnergy X T w f) := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt hU,phaseEnergy_union X S T w f hST]
    nlinarith only [hcross,sq_sqrt hS,sq_sqrt hT]
  rw [sqrt_mul hU,sqrt_mul hS,sqrt_mul hT]
  exact (mul_le_mul_of_nonneg_right hroot (sqrt_nonneg P)).trans_eq (by ring)

/-- The saved squared price is EXACTLY the retained cross-correlation
defect. This is measurable for the actual masked weights, with no assumed
distribution of prime counts or logarithmic bin masses. -/
theorem joined_cost_squared_saving (X : ℕ) (S T : Finset ℕ) (w f : ℕ → ℝ)
    (hST : Disjoint S T) {P : ℝ} (hP : 0 ≤ P) :
    (sqrt (phaseEnergy X S w f*P)+sqrt (phaseEnergy X T w f*P))^2-
      (sqrt (phaseEnergy X (S ∪ T) w f*P))^2 =
        2*P*(sqrt (phaseEnergy X S w f*phaseEnergy X T w f)-
          (∑ k ∈ activeCutoffs X f,
            correlation S w k*correlation T w k/(k : ℝ))) := by
  have hS := phaseEnergy_nonneg X S w f
  have hT := phaseEnergy_nonneg X T w f
  have hU := phaseEnergy_nonneg X (S ∪ T) w f
  have hm : sqrt (phaseEnergy X S w f*P)*sqrt (phaseEnergy X T w f*P) =
      sqrt (phaseEnergy X S w f*phaseEnergy X T w f)*P := by
    calc
      _ = (sqrt (phaseEnergy X S w f)*sqrt (phaseEnergy X T w f))*(sqrt P)^2 := by
        rw [sqrt_mul hS,sqrt_mul hT]
        ring
      _ = _ := by rw [sq_sqrt hP,sqrt_mul hS]
  rw [add_sq,sq_sqrt (mul_nonneg hS hP),sq_sqrt (mul_nonneg hT hP),
    sq_sqrt (mul_nonneg hU hP),phaseEnergy_union X S T w f hST]
  nlinarith only [hm]

/-- All counts, occupied-bin patterns or radial periods may be joined
at once under the SAME original profile and weights. The total price is
no larger than the separate prices, with no cardinality multiplier. -/
theorem all_populations_cost_le {ι : Type*} (I : Finset ι) (B : ι → Finset ℕ)
    (X : ℕ) (w f : ℕ → ℝ) {P : ℝ} (hdis : (I : Set ι).PairwiseDisjoint B) :
    sqrt (phaseEnergy X (I.biUnion B) w f*P) ≤
      ∑ i ∈ I,sqrt (phaseEnergy X (B i) w f*P) := by
  revert hdis
  induction I using Finset.induction_on with
  | empty => simp [phaseEnergy,correlation]
  | @insert i I hi ih =>
    intro hdis
    have hI : (I : Set ι).PairwiseDisjoint B := by
      intro a ha b hb hab
      exact hdis (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb) hab
    have hB : Disjoint (B i) (I.biUnion B) := by
      apply Finset.disjoint_left.mpr
      intro n hn hnI
      obtain ⟨b,hb,hnB⟩ := Finset.mem_biUnion.mp hnI
      have hib : i ≠ b := fun h => hi (h.symm ▸ hb)
      exact Finset.disjoint_left.mp
        (hdis (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hb) hib) hn hnB
    rw [Finset.biUnion_insert,Finset.sum_insert hi]
    apply (joined_cost_le X (B i) (I.biUnion B) w f hB).trans
    linarith only [ih hI]

/-- Only adverse cutoff contributions AFTER every original signed
population and its funding have been joined. This does not clip labels,
counts, owners, periods or individual divisor summands. -/
def negativeCutoffs (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) : Finset ℕ :=
  (activeCutoffs X f).filter (fun k => correlation S w k*(f k-f (k+1))<0)

/-- The one-sided price retains only adverse COMPLETE prefix increments.
It is a scalar cost for the existing sum, not another arithmetic carrier. -/
def negativeCost (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  sqrt ((∑ k ∈ negativeCutoffs X S w f,correlation S w k^2/(k : ℝ))*
    (∑ k ∈ negativeCutoffs X S w f,(k : ℝ)*(f k-f (k+1))^2))

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

/-- The desired FLOOR needs only adverse joined prefix increments.
Favorable increments are left uncharged, so no upper-bound strength or
decay of the complete signed source is required by this inequality. -/
theorem negative_signed_prefix_bound (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (hend : f (X+1)=0) :
    -negativeCost X S w f ≤ ∑ n ∈ S,w n*(∑ d ∈ Finset.Icc 1 X,
      f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
  let K := negativeCutoffs X S w f
  have hK : K ⊆ activeCutoffs X f := Finset.filter_subset _ _
  have he : |∑ k ∈ K,correlation S w k*(f k-f (k+1))| ≤ negativeCost X S w f := by
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs,sq_sqrt (mul_nonneg
      (Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)))
      (Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))))]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul K
      (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hK hk)).1).1
      exact_mod_cast (by omega : k ≠ 0)
    apply le_of_eq
    field_simp
  rw [prefix_pairing X S w f hend]
  apply (abs_le.mp he).1.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg hK
  intro k hk hout
  apply le_of_not_gt
  intro hneg
  exact hout (Finset.mem_filter.mpr ⟨hk,hneg⟩)

/-- A genuine uniform price improvement for the SAME original weights
and profile: removing favorable full-prefix increments never increases
the floor cost. No bin independence or numerical saving is assumed. -/
theorem negative_cost_le_full (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    negativeCost X S w f ≤ sqrt (phaseEnergy X S w f*profileEnergy X f) := by
  have he : (∑ k ∈ negativeCutoffs X S w f,correlation S w k^2/(k : ℝ)) ≤
      phaseEnergy X S w f := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hp : (∑ k ∈ negativeCutoffs X S w f,(k : ℝ)*(f k-f (k+1))^2) ≤
      profileEnergy X f := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  apply sqrt_le_sqrt
  exact mul_le_mul he hp
    (Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
    (phaseEnergy_nonneg X S w f)

/-- The one-sided price applies directly to the literal residual sum
with arbitrary signed population coefficients, after ALL masks and
cross-label/count/funding correlations have been retained. -/
theorem weighted_negative_floor (A B : Finset ℕ) (N : ℕ)
    (L y slope : ℝ) (q : ℕ → ℝ)
    (hB : ∀ n ∈ B,3 ≤ n.primeFactors.card) :
    let X := max 1 (B.sup id)
    let f := centeredProfile X (fun d => max 0 (L-log d)) slope;
    -negativeCost X (B.filter Squarefree) (fun n => q n*primeWeight A L y N n 1) f ≤
      ∑ n ∈ B,q n*(residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  let X := max 1 (B.sup id)
  let f := centeredProfile X (fun d => max 0 (L-log d)) slope
  have hb := negative_signed_prefix_bound X (B.filter Squarefree)
    (fun n => q n*primeWeight A L y N n 1) f (by simp [f,centeredProfile])
  rw [← weighted_residual_eq_prefix A B N L y slope q hB] at hb
  exact hb

/-- The EXACT real coefficients of the published floor ledger. Overlaps
are retained algebraically, so a funding label inside a paid population
receives both its original credit and its original negative debit. -/
def rejoinedWeights (H P T Y : Finset ℕ) (a b debit : ℝ) (n : ℕ) : ℝ :=
  (if n ∈ H then 1 else 0)+a*(if n ∈ P then 1 else 0)+
    b*(if n ∈ T then 1 else 0)-debit*(if n ∈ Y then 1 else 0)

/-- Join the original unpaid population, both original credits and the
SAME funding debit inside one literal signed sum. No disjointness or
completion is required, and overlaps cannot create an extra credit. -/
theorem rejoined_weight_sum (H P T Y : Finset ℕ) (a b debit : ℝ) (g : ℕ → ℝ) :
    (∑ n ∈ ((H ∪ P) ∪ T) ∪ Y,rejoinedWeights H P T Y a b debit n*g n) =
      (∑ n ∈ H,g n)+a*(∑ n ∈ P,g n)+b*(∑ n ∈ T,g n)-debit*(∑ n ∈ Y,g n) := by
  let U := ((H ∪ P) ∪ T) ∪ Y
  have hi (V : Finset ℕ) (hV : V ⊆ U) :
      (∑ n ∈ U,(if n ∈ V then (1 : ℝ) else 0)*g n) = ∑ n ∈ V,g n := by
    simp only [ite_mul,one_mul,zero_mul,← Finset.sum_filter]
    rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hV]
  have hH := hi H (by intro n hn; simp [U,hn])
  have hP := hi P (by intro n hn; simp [U,hn])
  have hT := hi T (by intro n hn; simp [U,hn])
  have hY := hi Y (by intro n hn; simp [U,hn])
  change (∑ n ∈ U,_) = _
  simp only [rejoinedWeights,add_mul,sub_mul,mul_assoc,
    Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hH,hP,hT,hY]

/-- One unconditional signed bound for the COMPLETE retained floor
aggregate, with its funding still inside the weighted prefix. The two
positive parts are EXACTLY the existing ledger's global credits; no
individual count, owner, bin or period is clipped or normed. -/
theorem rejoined_funding_signed_bounds (A H P T Y : Finset ℕ) (N : ℕ)
    (L y scale slope debit : ℝ)
    (hB : ∀ n ∈ ((H ∪ P) ∪ T) ∪ Y,3 ≤ n.primeFactors.card) :
    let atom := fun n => residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n
    let U := ((H ∪ P) ∪ T) ∪ Y
    let X := max 1 (U.sup id)
    let f := centeredProfile X (fun d => max 0 (L-log d)) slope
    let a : ℝ := if 0 ≤ (∑ n ∈ P,atom n).re then 1 else 0
    let b : ℝ := if 0 ≤ (∑ n ∈ T,atom n).re then 1 else 0
    let w := fun n => (scale*rejoinedWeights H P T Y a b debit n)*primeWeight A L y N n 1
    let C := sqrt (phaseEnergy X (U.filter Squarefree) w f*profileEnergy X f)
    let J := scale*((∑ n ∈ H,atom n).re+max (∑ n ∈ P,atom n).re 0+
      max (∑ n ∈ T,atom n).re 0-debit*(∑ n ∈ Y,atom n).re);
    -C ≤ J ∧ J ≤ C := by
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
  have h := weighted_signed_bounds A (((H ∪ P) ∪ T) ∪ Y) N L y slope
    (fun n => scale*rejoinedWeights H P T Y a b debit n) hB
  dsimp only at h ⊢
  change -_ ≤ (∑ n ∈ ((H ∪ P) ∪ T) ∪ Y,
    (scale*rejoinedWeights H P T Y a b debit n)*(atom n).re) ∧ _ at h
  rw [hs] at h
  exact h

/-- Charge only the adverse COMPLETE cutoff increments of the retained
aggregate, including the exact signed funding debit. This is stronger
than its two-sided energy price and needs no independent upper bound. -/
theorem rejoined_funding_negative_floor (A H P T Y : Finset ℕ) (N : ℕ)
    (L y scale slope debit : ℝ)
    (hB : ∀ n ∈ ((H ∪ P) ∪ T) ∪ Y,3 ≤ n.primeFactors.card) :
    let atom := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    let U := ((H ∪ P) ∪ T) ∪ Y
    let X := max 1 (U.sup id)
    let f := centeredProfile X (fun d => max 0 (L-log d)) slope
    let a : ℝ := if 0 ≤ (∑ n ∈ P,atom n).re then 1 else 0
    let b : ℝ := if 0 ≤ (∑ n ∈ T,atom n).re then 1 else 0
    let w := fun n => (scale*rejoinedWeights H P T Y a b debit n)*primeWeight A L y N n 1;
    -negativeCost X (U.filter Squarefree) w f ≤
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
  have h := weighted_negative_floor A (((H ∪ P) ∪ T) ∪ Y) N L y slope
    (fun n => scale*rejoinedWeights H P T Y a b debit n) hB
  dsimp only at h ⊢
  change -_ ≤ (∑ n ∈ ((H ∪ P) ∪ T) ∪ Y,
    (scale*rejoinedWeights H P T Y a b debit n)*(atom n).re) at h
  rw [hs] at h
  exact h

open Filter Topology ZetaRieszOwnerHingeCancellation
open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszRejoinedPopulationFloor ZetaRieszJoinedPopulationFloor ZetaRieszFewBinCoverFloor
open ZetaRieszSevenCountTail
open ZetaRieszLowCountRefund (tailCost)

/-- Spend ONE total-label signed phase cost in the EXISTING whole-floor
ledger. The same funding and vanishing error remain. There is no owner
comparison/variation term and no separate count/bin cost. Bounding this
actual coupled cost plus funding at -79/1000 remains the open estimate. -/
theorem eventually_joined_total_phase_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y)
    (slopes : ℕ → ℝ) :
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
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Paid := (S₀.filter (fun n : ℕ =>
          3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪
            bin56Band u N K
        let Ts := radialTail S₀ N 0
        let Ys := radialSupply N h v
        0 < (∑ n ∈ Ys,f n).re ∧
          -wholeCost A (remainingOwnerBand u N K) N L y (u^(N+1)) (slopes N)+
            u^(N+1)*(max (∑ n ∈ Paid,f n).re 0+max (∑ n ∈ Ts,f n).re 0-
              (tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re)-err j ≤
                ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ :=
    ZetaRieszCoreOwnerPayment.eventually_rejoined_floor_without_large_owners hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨err,he0,he,hfloor⟩ := hbase ε hε
  refine ⟨err,he0,he,?_⟩
  filter_upwards [hfloor] with j hj
  obtain ⟨v,hv,hpos,hbound⟩ := hj
  refine ⟨v,hv,hpos,?_⟩
  have hphase := whole_signed_bounds (intermediatePrimes u (dyadicMomentOrder j))
    (remainingOwnerBand u (dyadicMomentOrder j) (dyadicPrimeCount j)) (dyadicMomentOrder j)
    (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y
    (u^(dyadicMomentOrder j+1)) (slopes (dyadicMomentOrder j)) (by
      intro n hn
      have hcore : n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) :=
        (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hn).1).1
      exact ZetaRieszJointPrimeEnergy.core_count hcore)
  dsimp only at hphase hbound ⊢
  simp only [remainingOwnerBand] at hphase ⊢
  nlinarith only [hphase.1,hbound]

/-- A SINGLE one-sided energy for the whole retained floor, INCLUDING its
funding. Every unpaid count/bin/period and every old credit/debit is
assembled before the square; favorable COMPLETE increments are uncharged.
The original vanishing error is unchanged. This is an unconditional lower
bound with an explicit unpaid cost, not an assumed large-sieve saving or
a numerical -79/1000 floor. -/
theorem eventually_joined_funded_phase_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y)
    (slopes : ℕ → ℝ) :
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
        let H := remainingOwnerBand u N K
        let Ts := radialTail S₀ N 0
        let Ys := radialSupply N h v
        let U := ((H ∪ Paid) ∪ Ts) ∪ Ys
        let X := max 1 (U.sup id)
        let f := centeredProfile X (fun d => max 0 (L-log d)) (slopes N)
        let a : ℝ := if 0 ≤ (∑ n ∈ Paid,atom n).re then 1 else 0
        let b : ℝ := if 0 ≤ (∑ n ∈ Ts,atom n).re then 1 else 0
        let debit := tailCost c N+ε+growingDebit κ N
        let w := fun n => (u^(N+1)*rejoinedWeights H Paid Ts Ys a b debit n)*primeWeight A L y N n 1
        0 < (∑ n ∈ Ys,atom n).re ∧
          -negativeCost X (U.filter Squarefree) w f-err j ≤
            ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ :=
    ZetaRieszCoreOwnerPayment.eventually_rejoined_floor_without_large_owners hu hU hy
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
  let H := remainingOwnerBand u N K
  let Paid := (S₀.filter (fun n : ℕ =>
    3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪
      bin56Band u N K
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
  have hphase := rejoined_funding_negative_floor A H Paid Ts Ys N L y
    (u^(N+1)) (slopes N) (tailCost c N+ε+growingDebit κ N) hcounts
  dsimp only [N,K,A,L,S₀,H,Paid,Ts,Ys] at hphase
  dsimp only at hbound ⊢
  simp only [remainingOwnerBand] at hphase ⊢
  nlinarith only [hphase,hbound]

end RiemannGaussian.ZetaRieszRejoinedPhaseFloor
