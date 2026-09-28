/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointCapacityCeiling

/-!
# An explicit balanced-triple debit for the literal signed comparison

Every prime log-share lies within 1/1000 of one third. Two macroscopic
prime windows and the exact cofactor-dependent last-prime window bound
the original population. This is an unsigned counting budget inside a
signed inequality, not a source-scale approximation by prime density.
-/

namespace RiemannGaussian.ZetaRieszBalancedTripleBudget
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic

/-- The complete rational balanced band in one original total-log cell.
The ambient finite support retains all original physical/count masks. -/
def population (S : Finset ℕ) (t h : ℝ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 3 ∧
    t < Real.log n ∧ Real.log n ≤ t+h ∧
    ∀ p ∈ n.primeFactors, (997/3000 : ℝ)*Real.log n ≤ Real.log p ∧
      Real.log p ≤ (1003/3000 : ℝ)*Real.log n)

/-- A balanced-triple label retains the original half-open log interval. -/
theorem population_log_bounds {S : Finset ℕ} {t h : ℝ} {n : ℕ}
    (hn : n ∈ population S t h) : t < Real.log n ∧ Real.log n ≤ t+h := by
  exact ⟨(Finset.mem_filter.mp hn).2.2.2.1,(Finset.mem_filter.mp hn).2.2.2.2.1⟩

/-- The full period spends every balanced-triple label in its half-open
log window, including cosine boundaries; it is not a peak-only selection. -/
theorem mem_full_period_iff (S : Finset ℕ) {m : ℕ} (hm : 0 < m)
    {v y : ℝ} (hy : 0 < |y|) (n : ℕ) :
    (n ∈ (Finset.range (8*m)).biUnion (fun i => population S
      (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|)
      (Real.pi/(4*m*|y|)))) ↔
      n ∈ S ∧ Squarefree n ∧ n.primeFactors.card = 3 ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| ∧
      ∀ p ∈ n.primeFactors, (997/3000 : ℝ)*Real.log n ≤ Real.log p ∧
        Real.log p ≤ (1003/3000 : ℝ)*Real.log n := by
  constructor
  · intro hn
    obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hn,hs,hcount,hlo,hhi,hshare⟩ := Finset.mem_filter.mp hn
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy
    exact ⟨hn,hs,hcount,ht.1.trans_lt hlo,hhi.trans ht.2,hshare⟩
  · rintro ⟨hn,hs,hcount,hlo,hhi,hshare⟩
    obtain ⟨i,hi,hil,hih⟩ := ZetaRieszCapacityPhaseBudget.period_cells_cover hm hy hlo hhi
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hn,hs,hcount,hil,hih,hshare⟩⟩

/-- The three/four/five-prime union lies in one original log interval,
even when five-prime credit is spent only on selected phase cells. -/
theorem joint_population_log_bounds (S : Finset ℕ)
    {M : ℕ} {L lo hi t h b y a : ℝ} {spend : Prop} [Decidable spend] {n : ℕ}
    (hn : n ∈ population S t h ∪
      (ZetaRieszFourBoundaryCover.adversePopulation (ZetaRieszFourOrderingBudget.clippedSupport S)
        L t h y a ∪
        (if spend then
          ((ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/t) b).biUnion
            (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
              (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b)))
         else ∅))) : t < Real.log n ∧ Real.log n ≤ t+h := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact population_log_bounds hn
  · by_cases hp : spend
    · simp only [if_pos hp] at hn
      exact ZetaRieszJointCapacityFloor.joint_population_log_bounds _ hn
    · simp only [if_neg hp,Finset.union_empty] at hn
      exact ⟨(Finset.mem_filter.mp hn).2.2.2.2.1,
        (Finset.mem_filter.mp hn).2.2.2.2.2.1⟩

/-- Ordered log windows disjoin the actual three/four/five populations,
with arbitrary calibration heights and phase-dependent five-prime spending. -/
theorem joint_populations_disjoint (I : Finset ℕ) (S : Finset ℕ)
    (T Y : ℕ → ℝ) (spend : ℕ → Prop) [DecidablePred spend]
    {M : ℕ} {L lo hi h b a : ℝ}
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i < j → T i+h ≤ T j) :
    Set.PairwiseDisjoint (↑I) (fun i => population S (T i) h ∪
      (ZetaRieszFourBoundaryCover.adversePopulation (ZetaRieszFourOrderingBudget.clippedSupport S)
        L (T i) h (Y i) a ∪
        (if spend i then
          ((ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/T i) b).biUnion
            (fun v => ZetaRieszJointPrimeCells.supplyCell (T i) h (Y i)
              (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b v k) (fun _ => T i*b)))
         else ∅))) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hb := joint_population_log_bounds S hn
  have hb' := joint_population_log_bounds S hn'
  rcases lt_or_gt_of_ne hij with hij | hji
  · linarith [hsep i hi j hj hij]
  · linarith [hsep j hj i hi hji]

private def outerPrimes (t h : ℝ) : Finset ℕ :=
  logPrimes ((997/3000 : ℝ)*t) ((1/500 : ℝ)*t+(1003/3000 : ℝ)*h)

private theorem outer_log_upper {t h : ℝ} {p : ℕ} (hp : p ∈ outerPrimes t h) :
    Real.log p ≤ (1003/3000 : ℝ)*(t+h) := by
  have hb := (logPrimes_bounds hp).2.2
  change Real.log p ≤ (997/3000 : ℝ)*t+((1/500 : ℝ)*t+(1003/3000 : ℝ)*h) at hb
  linarith only [hb]

private theorem cofactor_log_gap {t h : ℝ} (ht : 1 ≤ t) (hhu : h ≤ 1/100000)
    {p q : ℕ} (hp : p ∈ outerPrimes t h) (hq : q ∈ outerPrimes t h) :
    (33/100 : ℝ)*t ≤ t-Real.log (p*q : ℕ) := by
  rw [Nat.cast_mul,Real.log_mul
    (by exact_mod_cast (logPrimes_bounds hp).1.ne_zero)
    (by exact_mod_cast (logPrimes_bounds hq).1.ne_zero)]
  linarith [outer_log_upper hp,outer_log_upper hq]

private theorem population_cover (S : Finset ℕ) (t h : ℝ) :
    population S t h ⊆
      ((outerPrimes t h).sigma (fun p => (outerPrimes t h).sigma
        (fun q => logPrimes (t-Real.log (p*q : ℕ)) h))).image
          (fun x : Σ _p : ℕ, Σ _q : ℕ, ℕ => (x.1*x.2.1)*x.2.2) := by
  intro n hn
  obtain ⟨_,hs,hcount,ht,hth,hshare⟩ := Finset.mem_filter.mp hn
  obtain ⟨p,q,r,hp,hq,hr,_,_,_,he⟩ := ZetaRieszTriplePrime.exists_three_primes hs hcount
  have hpl : p ∈ n.primeFactors := hp.mem_primeFactors
    (by rw [he]; exact dvd_mul_right _ _) hs.ne_zero
  have hql : q ∈ n.primeFactors := hq.mem_primeFactors
    (by rw [he]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _) hs.ne_zero
  have hmem (p : ℕ) (hp : p.Prime) (hpf : p ∈ n.primeFactors) : p ∈ outerPrimes t h := by
    apply (mem_logPrimes_iff _ _ _).mpr
    refine ⟨hp,?_,?_⟩
    · exact (mul_lt_mul_of_pos_left ht (by norm_num : (0 : ℝ) < 997/3000)).trans_le
        (hshare p hpf).1
    · have hu := (hshare p hpf).2.trans
        (mul_le_mul_of_nonneg_left hth (by norm_num : (0 : ℝ) ≤ 1003/3000))
      linarith only [hu]
  have hlog : Real.log n = Real.log (p*q : ℕ)+Real.log r := by
    rw [he,← mul_assoc,Nat.cast_mul,Real.log_mul
      (by exact_mod_cast Nat.mul_ne_zero hp.ne_zero hq.ne_zero)
      (by exact_mod_cast hr.ne_zero)]
  have hrmem : r ∈ logPrimes (t-Real.log (p*q : ℕ)) h := by
    apply (mem_logPrimes_iff _ _ _).mpr
    exact ⟨hr,by linarith,by linarith⟩
  exact Finset.mem_image.mpr ⟨⟨p,q,r⟩,Finset.mem_sigma.mpr
    ⟨hmem p hp hpl,Finset.mem_sigma.mpr ⟨hmem q hq hql,hrmem⟩⟩,by simpa [mul_assoc] using he.symm⟩

/-- A literal reciprocal-mass bound for the entire balanced triple band.
The cover may overcount triples, but only in this nonnegative upper bound;
no incidence factor is used to inflate a favorable supply. -/
theorem eventually_reciprocal_mass {h : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ) (t : ℝ), (N : ℝ) ≤ t →
      (∑ n ∈ population S t h, (n : ℝ)⁻¹) ≤ (1/8000 : ℝ)*h/t := by
  filter_upwards [eventually_macro_reciprocal_bounds
      (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (0 : ℝ) < 1/1000),
    ZetaRieszPhaseBudget.eventually_phase_window_mass hh hhu
      (by norm_num : (0 : ℝ) < 1/4),eventually_ge_atTop (1 : ℕ)]
    with N hmacro hlast hN S t hNt
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ t := hn.trans hNt
  have ht0 : 0 < t := by linarith
  let P := outerPrimes t h
  let D := P.sigma (fun p => P.sigma (fun q => logPrimes (t-Real.log (p*q : ℕ)) h))
  let product := fun x : Σ _p : ℕ, Σ _q : ℕ, ℕ => (x.1*x.2.1)*x.2.2
  have hm := (hmacro ((997/3000 : ℝ)*t) ((1/500 : ℝ)*t+(1003/3000 : ℝ)*h)
    (by linarith) (by linarith)).2
  have hm' : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 1/160 := by
    apply hm.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (997/3000 : ℝ)*t)).mpr
    linarith only [ht,hhu]
  have hlast' (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
      (∑ r ∈ logPrimes (t-Real.log (p*q : ℕ)) h, (r : ℝ)⁻¹) ≤ (31/10 : ℝ)*h/t := by
    have hgap := cofactor_log_gap ht hhu hp hq
    have hg0 : 0 < t-Real.log (p*q : ℕ) := by linarith
    apply (hlast (t-Real.log (p*q : ℕ)) (by linarith)).2.trans
    apply (div_le_div_iff₀ hg0 ht0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hgap hh.le]
  have hc : (∑ n ∈ population S t h, (n : ℝ)⁻¹) ≤
      ∑ x ∈ D, ((product x : ℕ) : ℝ)⁻¹ := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (population_cover S t h)
      (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg n))).trans
        (Finset.sum_image_le_of_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)))
  have he : (∑ x ∈ D, ((product x : ℕ) : ℝ)⁻¹) =
      ∑ p ∈ P, ∑ q ∈ P, ((p : ℝ)⁻¹*(q : ℝ)⁻¹)*
        (∑ r ∈ logPrimes (t-Real.log (p*q : ℕ)) h, (r : ℝ)⁻¹) := by
    simp only [D,product,Finset.sum_sigma,Nat.cast_mul,mul_inv_rev,Finset.mul_sum]
    simp only [mul_assoc,mul_comm]
  rw [he] at hc
  have hs := Finset.sum_le_sum (s := P) (fun p hp =>
    Finset.sum_le_sum (s := P) (fun q hq =>
      mul_le_mul_of_nonneg_left (hlast' p hp q hq)
        (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) (inv_nonneg.mpr (Nat.cast_nonneg q)))))
  have he' : (∑ p ∈ P, ∑ q ∈ P, ((p : ℝ)⁻¹*(q : ℝ)⁻¹)*((31/10 : ℝ)*h/t)) =
      (∑ p ∈ P, (p : ℝ)⁻¹)^2*((31/10 : ℝ)*h/t) := by
    simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
    ring
  rw [he'] at hs
  have hmass0 : 0 ≤ ∑ p ∈ P, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hsq : (∑ p ∈ P, (p : ℝ)⁻¹)^2 ≤ (1/160 : ℝ)^2 := by nlinarith
  have hpaid := mul_le_mul_of_nonneg_right hsq
    (show 0 ≤ (31/10 : ℝ)*h/t by positivity)
  have hcoef : (1/160 : ℝ)^2*((31/10 : ℝ)*h/t) ≤ (1/8000 : ℝ)*h/t := by
    have hb := mul_le_mul_of_nonneg_right
      (by norm_num : (1/160 : ℝ)^2*(31/10) ≤ 1/8000) (div_nonneg hh.le ht0.le)
    calc
      _ = ((1/160 : ℝ)^2*(31/10))*(h/t) := by ring
      _ ≤ (1/8000 : ℝ)*(h/t) := hb
      _ = _ := by ring
  exact hc.trans (hs.trans (hpaid.trans hcoef))

private theorem amplitude_le_window {n : ℕ} (hn : n ≠ 0) {t h : ℝ}
    (ht : t ≤ Real.log n) (hth : Real.log n ≤ t+h) (N : ℕ) :
    amplitude N n ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*(n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : Real.exp (-(3/2 : ℝ)*Real.log n) =
      Real.exp (-Real.log n/2)*(n : ℝ)⁻¹ := by
    rw [show (n : ℝ)⁻¹ = Real.exp (-Real.log n) by rw [Real.exp_neg,Real.exp_log hnR],
      ← Real.exp_add]
    congr 1
    ring
  have hr : Real.exp (-Real.log n/2)*(Real.log n)^N/N.factorial ≤
      Real.exp (-t/2)*(t+h)^N/N.factorial := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith))
      (pow_le_pow_left₀ (Real.log_natCast_nonneg n) hth N) (by positivity) (Real.exp_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hr (inv_nonneg.mpr hnR.le)
  unfold amplitude
  rw [he]
  convert hm using 1 <;> first | rfl | ring

/-- The original coefficient and factorial allocation are controlled on
the explicit balanced band by a fixed local mass budget. This is used
with the common signed phase, not multiplied by a whole-carrier envelope. -/
theorem eventually_coefficient_mass {h : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (t L : ℝ),
      (N : ℝ) ≤ t → 0 < L → t+h ≤ 2*L →
      (∑ n ∈ population S t h, weight A N n*(SquarefreeVaughanLogSource.coefficient L n).re) ≤
        (1/10000 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*h := by
  filter_upwards [eventually_reciprocal_mass hh hhu,eventually_ge_atTop (1 : ℕ)]
    with N hmass hN S A t L hNt hL hmid
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ t := hn.trans hNt
  have ht0 : 0 < t := by linarith
  let V := Real.exp (-t/2)*(t+h)^N/N.factorial
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hpoint (n : ℕ) (hn : n ∈ population S t h) :
      weight A N n*(SquarefreeVaughanLogSource.coefficient L n).re ≤
        ((4/5 : ℝ)*t*V)*(n : ℝ)⁻¹ := by
    obtain ⟨_,hs,hc,htn,hnt,_⟩ := Finset.mem_filter.mp hn
    have hb := ZetaRieszTriplePrime.actual_three_prime_coefficient_bounds hc hL (hnt.trans hmid)
    have hu : (SquarefreeVaughanLogSource.coefficient L n).re ≤ (4/5 : ℝ)*t :=
      ((Complex.re_le_norm _).trans hb.2).trans (by linarith only [hnt,ht,hhu])
    have haw := amplitude_le_window hs.ne_zero htn.le hnt N
    have hw := mul_le_mul_of_nonneg_right
      (show 1-boundedShare A N n ≤ 1 by linarith [(boundedShare_bounds A N n).1])
      (ZetaRieszCosineCarrier.factorial_envelope_nonneg N n)
    simp only [one_mul] at hw
    change weight A N n ≤ amplitude N n at hw
    have hbnd := mul_le_mul (hw.trans haw) hu hb.1
      (show 0 ≤ V*(n : ℝ)⁻¹ by positivity)
    convert hbnd using 1 <;> first | rfl | ring
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum] at hsum
  have hscaled := mul_le_mul_of_nonneg_left (hmass S t hNt)
    (show 0 ≤ (4/5 : ℝ)*t*V by positivity)
  have he : ((4/5 : ℝ)*t*V)*((1/8000 : ℝ)*h/t) = (1/10000 : ℝ)*V*h := by
    field_simp
    ring
  rw [he] at hscaled
  exact hsum.trans hscaled

/-- Explicit TWO-SIDED real bounds for the literal selected triple sum.
The common original phase is retained on each side; no absolute cosine,
zero hypothesis, prime-density transport or carrier completion is used. -/
theorem eventually_signed_bounds {h : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (t L y : ℝ),
      (N : ℝ) ≤ t → 0 < L → t+h ≤ 2*L →
      -(1/10000 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h ≤
        (∑ n ∈ population S t h, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (∑ n ∈ population S t h, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        (1/10000 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (Real.cos (y*t))+|y| * h)*h := by
  filter_upwards [eventually_coefficient_mass hh hhu] with N hmass S A t L y hNt hL hmid
  let M := ∑ n ∈ population S t h, weight A N n*(SquarefreeVaughanLogSource.coefficient L n).re
  let V := Real.exp (-t/2)*(t+h)^N/N.factorial
  let lo := max 0 (-Real.cos (y*t))+|y| * h
  let hi := max 0 (Real.cos (y*t))+|y| * h
  have hlo : 0 ≤ lo := by dsimp [lo]; positivity
  have hhi : 0 ≤ hi := by dsimp [hi]; positivity
  have hreal (n : ℕ) (hn : n ∈ population S t h) :
      0 ≤ weight A N n*(SquarefreeVaughanLogSource.coefficient L n).re := by
    obtain ⟨_,_,hc,_,hnt,_⟩ := Finset.mem_filter.mp hn
    exact mul_nonneg (weight_nonneg A N n)
      (ZetaRieszTriplePrime.actual_three_prime_coefficient_bounds hc hL (hnt.trans hmid)).1
  have hlow : -lo*M ≤ (∑ n ∈ population S t h, residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
    dsimp only [M]
    rw [Finset.mul_sum,Complex.re_sum]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨_,_,_,htn,hnt,_⟩ := Finset.mem_filter.mp hn
    have hc := ZetaRieszOppositePhase.cos_window_lower (y := y) htn.le hnt
    have hphase : -lo ≤ Real.cos (y*Real.log n) := by
      dsimp only [lo]
      linarith [le_max_right 0 (-Real.cos (y*t))]
    have hm := mul_le_mul_of_nonneg_left hphase (hreal n hn)
    rw [re_residual_atom]
    nlinarith only [hm]
  have hupp : (∑ n ∈ population S t h, residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤ hi*M := by
    dsimp only [M]
    rw [Finset.mul_sum,Complex.re_sum]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨_,_,_,htn,hnt,_⟩ := Finset.mem_filter.mp hn
    have hc := ZetaRieszOppositePhase.cos_window_upper (y := y) htn.le hnt
    have hphase : Real.cos (y*Real.log n) ≤ hi := by
      dsimp only [hi]
      linarith [le_max_right 0 (Real.cos (y*t))]
    have hm := mul_le_mul_of_nonneg_left hphase (hreal n hn)
    rw [re_residual_atom]
    nlinarith only [hm]
  have hM := hmass S A t L hNt hL hmid
  have hscaledL := mul_le_mul_of_nonpos_left hM (neg_nonpos.mpr hlo)
  have hscaledU := mul_le_mul_of_nonneg_left hM hhi
  dsimp only [M,lo,hi,V] at hlow hupp hscaledL hscaledU
  constructor <;> nlinarith only [hlow,hupp,hscaledL,hscaledU]

/-- The explicit triple budgets are spent in the ambient literal sum,
with its signed complement retained exactly. -/
theorem eventually_core_bounds {h : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (t L y : ℝ),
      (N : ℝ) ≤ t → 0 < L → t+h ≤ 2*L →
      (∑ n ∈ S\population S t h, residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (1/10000 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h ≤
        (∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        (∑ n ∈ S\population S t h, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
          (1/10000 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
            (max 0 (Real.cos (y*t))+|y| * h)*h := by
  filter_upwards [eventually_signed_bounds hh hhu] with N hJ S A t L y hNt hL hmid
  have hb := hJ S A t L y hNt hL hmid
  have he := congrArg Complex.re (Finset.sum_sdiff
    (f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
    (Finset.filter_subset _ _ : population S t h ⊆ S))
  simp only [Complex.add_re] at he
  dsimp only [population] at hb ⊢
  constructor <;> linarith only [he,hb.1,hb.2]

/-- Prime counts make the triple debit disjoint from BOTH populations
in the existing four/five-prime payment, even at different calibrations. -/
theorem disjoint_from_four_five (S : Finset ℕ)
    {M : ℕ} {L lo hi t h b y z a : ℝ} (ht : 0 < t) :
    Disjoint (population S t h)
      (ZetaRieszFourBoundaryCover.adversePopulation (ZetaRieszFourOrderingBudget.clippedSupport S)
        L t h y a ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/t) b).biUnion
          (fun v => ZetaRieszJointPrimeCells.supplyCell t h z
            (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b)))) := by
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hthree := (Finset.mem_filter.mp hn).2.2.1
  rcases Finset.mem_union.mp hn' with hfour | hfive
  · have hc := (Finset.mem_filter.mp hfour).2.2.1
    omega
  · obtain ⟨v,hv,hnv⟩ := Finset.mem_biUnion.mp hfive
    have hc := ZetaRieszJointCapacityFloor.interior_supply_count ht hv hnv
    omega

end
end RiemannGaussian.ZetaRieszBalancedTripleBudget
