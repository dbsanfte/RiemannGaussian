/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBalancedTripleBudget

/-!
# A broad balanced-triple debit with exact sixfold incidence

The original prime population has shares in 31/100..7/20. Each squarefree
triple supplies six DISTINCT ordered representations in the upper cover.
Dividing out that proven incidence makes its literal signed debit at most
1/200 of the original local radial/phase envelope. No favorable supply is
multiplied and no source-scale continuum approximation is used.
-/

namespace RiemannGaussian.ZetaRieszBroadTripleBudget
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic

/-- Every original squarefree triple in the broad rational share band. -/
def population (S : Finset ℕ) (t h : ℝ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 3 ∧
    t < Real.log n ∧ Real.log n ≤ t+h ∧
    ∀ p ∈ n.primeFactors, (31/100 : ℝ)*Real.log n ≤ Real.log p ∧
      Real.log p ≤ (7/20 : ℝ)*Real.log n)

/-- The broad band contains the previously paid narrow band. Its credit
must replace that old selection, never be spent a second time on top. -/
theorem narrow_subset (S : Finset ℕ) (t h : ℝ) :
    ZetaRieszBalancedTripleBudget.population S t h ⊆ population S t h := by
  intro n hn
  obtain ⟨hn,hs,hc,hlo,hhi,hshare⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hn,hs,hc,hlo,hhi,?_⟩
  intro p hp
  have hb := hshare p hp
  constructor <;> nlinarith [Real.log_natCast_nonneg n]

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
      ∀ p ∈ n.primeFactors, (31/100 : ℝ)*Real.log n ≤ Real.log p ∧
        Real.log p ≤ (7/20 : ℝ)*Real.log n := by
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
  logPrimes ((31/100 : ℝ)*t) ((1/25 : ℝ)*t+(7/20 : ℝ)*h)

private theorem outer_log_upper {t h : ℝ} {p : ℕ} (hp : p ∈ outerPrimes t h) :
    Real.log p ≤ (7/20 : ℝ)*(t+h) := by
  have hb := (logPrimes_bounds hp).2.2
  change Real.log p ≤ (31/100 : ℝ)*t+((1/25 : ℝ)*t+(7/20 : ℝ)*h) at hb
  linarith only [hb]

private theorem cofactor_log_gap {t h : ℝ} (ht : 1 ≤ t) (hhu : h ≤ 1/100000)
    {p q : ℕ} (hp : p ∈ outerPrimes t h) (hq : q ∈ outerPrimes t h) :
    (299/1000 : ℝ)*t ≤ t-Real.log (p*q : ℕ) := by
  rw [Nat.cast_mul,Real.log_mul
    (by exact_mod_cast (logPrimes_bounds hp).1.ne_zero)
    (by exact_mod_cast (logPrimes_bounds hq).1.ne_zero)]
  linarith [outer_log_upper hp,outer_log_upper hq]

/-- Six distinct ordered prime representations of EACH selected label
belong to the same literal moving last-prime window. -/
theorem six_le_representation_count (S : Finset ℕ) (t h : ℝ) {n : ℕ}
    (hn : n ∈ population S t h) :
    6 ≤ (((outerPrimes t h).sigma (fun p => (outerPrimes t h).sigma
      (fun q => logPrimes (t-Real.log (p*q : ℕ)) h))).filter
        (fun x : Σ _p : ℕ, Σ _q : ℕ, ℕ => (x.1*x.2.1)*x.2.2 = n)).card := by
  obtain ⟨_,hs,hcount,ht,hth,hshare⟩ := Finset.mem_filter.mp hn
  obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,he⟩ := ZetaRieszTriplePrime.exists_three_primes hs hcount
  have hmem (a : ℕ) (ha : a.Prime) (had : a ∣ n) : a ∈ outerPrimes t h := by
    have hpf := ha.mem_primeFactors had hs.ne_zero
    apply (mem_logPrimes_iff _ _ _).mpr
    refine ⟨ha,?_,?_⟩
    · exact (mul_lt_mul_of_pos_left ht (by norm_num : (0 : ℝ) < 31/100)).trans_le
        (hshare a hpf).1
    · have hu := (hshare a hpf).2.trans
        (mul_le_mul_of_nonneg_left hth (by norm_num : (0 : ℝ) ≤ 7/20))
      linarith only [hu]
  have hrep {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
      (habc : (a*b)*c = n) :
      (⟨a,b,c⟩ : Σ _p : ℕ, Σ _q : ℕ, ℕ) ∈
        (((outerPrimes t h).sigma (fun p => (outerPrimes t h).sigma
          (fun q => logPrimes (t-Real.log (p*q : ℕ)) h))).filter
            (fun x : Σ _p : ℕ, Σ _q : ℕ, ℕ => (x.1*x.2.1)*x.2.2 = n)) := by
    have had : a ∣ n := by rw [← habc]; exact dvd_mul_of_dvd_left (dvd_mul_right a b) c
    have hbd : b ∣ n := by rw [← habc]; exact dvd_mul_of_dvd_left (dvd_mul_left b a) c
    have hlog : Real.log n = Real.log (a*b : ℕ)+Real.log c := by
      rw [← habc,Nat.cast_mul,Real.log_mul
        (by exact_mod_cast Nat.mul_ne_zero ha.ne_zero hb.ne_zero)
        (by exact_mod_cast hc.ne_zero)]
    refine Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨hmem a ha had,
      Finset.mem_sigma.mpr ⟨hmem b hb hbd,?_⟩⟩,habc⟩
    exact (mem_logPrimes_iff _ _ _).mpr ⟨hc,by linarith,by linarith⟩
  let E : Finset (Σ _p : ℕ, Σ _q : ℕ, ℕ) :=
    {⟨p,q,r⟩,⟨p,r,q⟩,⟨q,p,r⟩,⟨q,r,p⟩,⟨r,p,q⟩,⟨r,q,p⟩}
  have hcard : E.card = 6 := by
    simp [E,hpq,hpr,hqr,Ne.symm hpq,Ne.symm hpr,Ne.symm hqr]
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  simp only [E,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hrep hp hq hr (by rw [he]; ring)
  · exact hrep hp hr hq (by rw [he]; ring)
  · exact hrep hq hp hr (by rw [he]; ring)
  · exact hrep hq hr hp (by rw [he]; ring)
  · exact hrep hr hp hq (by rw [he]; ring)
  · exact hrep hr hq hp (by rw [he]; ring)

/-- The exact sixfold incidence improves the ACTUAL reciprocal mass bound.
The outer cover may still overcount, but its six copies cannot be forgotten. -/
theorem six_mul_reciprocal_mass_le (S : Finset ℕ) (t h : ℝ) :
    (6 : ℝ)*(∑ n ∈ population S t h, (n : ℝ)⁻¹) ≤
      ∑ x ∈ (outerPrimes t h).sigma (fun p => (outerPrimes t h).sigma
        (fun q => logPrimes (t-Real.log (p*q : ℕ)) h)),
          (((x.1*x.2.1)*x.2.2 : ℕ) : ℝ)⁻¹ := by
  let D := (outerPrimes t h).sigma (fun p => (outerPrimes t h).sigma
    (fun q => logPrimes (t-Real.log (p*q : ℕ)) h))
  let f := fun x : Σ _p : ℕ, Σ _q : ℕ, ℕ => (x.1*x.2.1)*x.2.2
  have hfibre (n : ℕ) (hn : n ∈ population S t h) :
      (6 : ℝ)*(n : ℝ)⁻¹ ≤ ∑ x ∈ D.filter (fun x => f x = n), (f x : ℝ)⁻¹ := by
    have hcard : (6 : ℝ) ≤ (D.filter (fun x => f x = n)).card := by
      exact_mod_cast six_le_representation_count S t h hn
    have he : (∑ x ∈ D.filter (fun x => f x = n), (f x : ℝ)⁻¹) =
        (D.filter (fun x => f x = n)).card*(n : ℝ)⁻¹ := by
      calc
        _ = ∑ _x ∈ D.filter (fun x => f x = n), (n : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ = _ := by simp
    rw [he]
    exact mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hs := Finset.sum_le_sum hfibre
  rw [← Finset.mul_sum,Finset.sum_fiberwise_eq_sum_filter] at hs
  exact hs.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun x _ _ => inv_nonneg.mpr (Nat.cast_nonneg (f x))))

/-- Broad-band reciprocal mass, after retaining all six incidences. -/
theorem eventually_reciprocal_mass {h : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ) (t : ℝ), (N : ℝ) ≤ t →
      (∑ n ∈ population S t h, (n : ℝ)⁻¹) ≤ (19/2000 : ℝ)*h/t := by
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
  have hm := (hmacro ((31/100 : ℝ)*t) ((1/25 : ℝ)*t+(7/20 : ℝ)*h)
    (by linarith) (by linarith)).2
  have hm' : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 13/100 := by
    apply hm.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (31/100 : ℝ)*t)).mpr
    linarith only [ht,hhu]
  have hlast' (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
      (∑ r ∈ logPrimes (t-Real.log (p*q : ℕ)) h, (r : ℝ)⁻¹) ≤ (67/20 : ℝ)*h/t := by
    have hgap := cofactor_log_gap ht hhu hp hq
    have hg0 : 0 < t-Real.log (p*q : ℕ) := by linarith
    apply (hlast (t-Real.log (p*q : ℕ)) (by linarith)).2.trans
    apply (div_le_div_iff₀ hg0 ht0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hgap hh.le]
  have hc : (6 : ℝ)*(∑ n ∈ population S t h, (n : ℝ)⁻¹) ≤
      ∑ x ∈ D, ((product x : ℕ) : ℝ)⁻¹ := six_mul_reciprocal_mass_le S t h
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
  have he' : (∑ p ∈ P, ∑ q ∈ P, ((p : ℝ)⁻¹*(q : ℝ)⁻¹)*((67/20 : ℝ)*h/t)) =
      (∑ p ∈ P, (p : ℝ)⁻¹)^2*((67/20 : ℝ)*h/t) := by
    simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
    ring
  rw [he'] at hs
  have hmass0 : 0 ≤ ∑ p ∈ P, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hsq : (∑ p ∈ P, (p : ℝ)⁻¹)^2 ≤ (13/100 : ℝ)^2 := by nlinarith
  have hpaid := mul_le_mul_of_nonneg_right hsq
    (show 0 ≤ (67/20 : ℝ)*h/t by positivity)
  have hcoef : (13/100 : ℝ)^2*((67/20 : ℝ)*h/t) ≤ (6 : ℝ)*(19/2000)*h/t := by
    have hb := mul_le_mul_of_nonneg_right
      (by norm_num : (13/100 : ℝ)^2*(67/20) ≤ 6*(19/2000)) (div_nonneg hh.le ht0.le)
    calc
      _ = ((13/100 : ℝ)^2*(67/20))*(h/t) := by ring
      _ ≤ (6*(19/2000) : ℝ)*(h/t) := hb
      _ = _ := by ring
  have hfinal := hc.trans (hs.trans (hpaid.trans hcoef))
  rw [show (6 : ℝ)*(19/2000)*h/t = 6*((19/2000 : ℝ)*h/t) by ring] at hfinal
  linarith only [hfinal]

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
        (1/200 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*h := by
  filter_upwards [eventually_reciprocal_mass hh hhu,eventually_ge_atTop (1 : ℕ)]
    with N hmass hN S A t L hNt hL hmid
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ t := hn.trans hNt
  have ht0 : 0 < t := by linarith
  let V := Real.exp (-t/2)*(t+h)^N/N.factorial
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hpoint (n : ℕ) (hn : n ∈ population S t h) :
      weight A N n*(SquarefreeVaughanLogSource.coefficient L n).re ≤
        ((51/100 : ℝ)*t*V)*(n : ℝ)⁻¹ := by
    obtain ⟨_,hs,hc,htn,hnt,_⟩ := Finset.mem_filter.mp hn
    have hb := ZetaRieszTriplePrime.actual_three_prime_coefficient_bounds hc hL (hnt.trans hmid)
    have hu : (SquarefreeVaughanLogSource.coefficient L n).re ≤ (51/100 : ℝ)*t :=
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
    (show 0 ≤ (51/100 : ℝ)*t*V by positivity)
  have he : ((51/100 : ℝ)*t*V)*((19/2000 : ℝ)*h/t) = (969/200000 : ℝ)*V*h := by
    field_simp
    ring
  rw [he] at hscaled
  have hconstant : (969/200000 : ℝ)*V*h ≤ (1/200 : ℝ)*V*h := by
    nlinarith only [mul_nonneg hV hh.le]
  exact hsum.trans (hscaled.trans hconstant)

/-- Explicit TWO-SIDED real bounds for the literal selected triple sum.
The common original phase is retained on each side; no absolute cosine,
zero hypothesis, prime-density transport or carrier completion is used. -/
theorem eventually_signed_bounds {h : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (t L y : ℝ),
      (N : ℝ) ≤ t → 0 < L → t+h ≤ 2*L →
      -(1/200 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h ≤
        (∑ n ∈ population S t h, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (∑ n ∈ population S t h, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        (1/200 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
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
        (1/200 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h ≤
        (∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        (∑ n ∈ S\population S t h, residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
          (1/200 : ℝ)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
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
end RiemannGaussian.ZetaRieszBroadTripleBudget
