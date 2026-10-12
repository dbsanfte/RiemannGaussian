/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorCoprimeDiagonalAudit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Positive PSD repairs have a cofinally super-source trace cost

Retain every actual Mobius divisor fiber, the native diagonal credit and
the full fixed-height phase. Two disjoint genuine-prime windows generate
distinct squarefree semiprime rows with a uniformly negative diagonal.
ANY correction making the full Schur matrix PSD must pay each such row.
Off-diagonal corrections are arbitrary; no component is norm-paid here.

The actual PNT provides the count, rather than a signed prime estimate.
This rejects source-affordable nonnegative-trace PSD repairs, not every
changed carrier or a separately centered correction. No weighted source
asymptotic or RH endpoint is inferred from the unweighted source theorem.
-/

namespace RiemannGaussian.ArithmeticOperatorCoprimeRepairAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorCoprimeDiagonalAudit ArithmeticOperatorMoebiusCoprimeAudit
open SuzukiCarryCorrelation PrimeWindow
open scoped BigOperators Topology Classical ComplexConjugate

/-- Fixed positive phase width; the height is never rounded. -/
def width (y : ℝ) : ℝ := Real.exp (1/(8*|y|))

/-- First genuine-prime band, with its original floor endpoints. -/
def firstBand (y : ℝ) (J : ℕ) : Finset ℕ := primesInWindow (smallPhaseScale y J) (width y)

/-- Adjacent disjoint band in the same small positive phase rectangle. -/
def secondBand (y : ℝ) (J : ℕ) : Finset ℕ :=
  primesInWindow (width y*smallPhaseScale y J) (width y)

/-- Ordinary integer semiprime rows, not an incidence multiset. -/
def badRows (y : ℝ) (J : ℕ) : Finset ℕ :=
  ((firstBand y J) ×ˢ (secondBand y J)).image (fun pq => pq.1*pq.2)

/-- Literal physical cutoff encompassing both prime legs and all their products. -/
def physicalCutoff (y : ℝ) (J : ℕ) : ℕ :=
  ⌊(width y)^3*(smallPhaseScale y J)^2⌋₊

/-- Fixed height-dependent upper bound for prime logs divided by J+1. -/
def logConstant (y : ℝ) : ℝ := (2*Real.pi+1/2)/|y|

/-- A positive, nonoptimized lower prime-count constant from actual PNT. -/
def countConstant (y : ℝ) : ℝ := (width y-1)/(2*logConstant y)

private theorem width_gt_one {y : ℝ} (hy : y≠0) : 1<width y :=
  Real.one_lt_exp_iff.mpr (by positivity)

private theorem scale_tendsto {y : ℝ} (hy : y≠0) :
    Tendsto (smallPhaseScale y) atTop atTop := by
  have ht : Tendsto (fun J : ℕ => (J : ℝ)*(2*Real.pi)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (by positivity : 0<2*Real.pi)
  exact Real.tendsto_exp_atTop.comp
    ((tendsto_atTop_add_const_right atTop (1/4 : ℝ) ht).atTop_div_const (abs_pos.mpr hy))

private theorem bands_geometry {y : ℝ} (hy : y≠0) {J p q : ℕ}
    (hp : p∈firstBand y J) (hq : q∈secondBand y J) :
    p.Prime ∧ q.Prime ∧ p<q ∧ smallPhaseScale y J<p ∧
      p*q≤physicalCutoff y J := by
  have hA := width_gt_one hy
  have hx : 0<smallPhaseScale y J := Real.exp_pos _
  have hAx : 0<width y*smallPhaseScale y J := mul_pos (zero_lt_one.trans hA) hx
  obtain ⟨hpl,hpu,hpP⟩ := mem_primesInWindow_bounds hx.le (zero_lt_one.trans hA).le hp
  obtain ⟨hql,hqu,hqP⟩ := mem_primesInWindow_bounds hAx.le (zero_lt_one.trans hA).le hq
  have hpq : p<q := by exact_mod_cast hpu.trans_lt hql
  refine ⟨hpP,hqP,hpq,hpl,?_⟩
  apply (Nat.le_floor_iff (by positivity)).mpr
  have hmul := mul_le_mul hpu hqu (by exact_mod_cast hqP.pos.le) hAx.le
  simpa only [Nat.cast_mul] using hmul.trans_eq (by ring)

/-- Distinct prime pairs yield distinct physical rows because the two
bands are ordered. No diagonal or swapped incidence is counted twice. -/
theorem pair_mul_injective {y : ℝ} (hy : y≠0) (J : ℕ) :
    Set.InjOn (fun pq : ℕ×ℕ => pq.1*pq.2)
      ↑((firstBand y J) ×ˢ (secondBand y J)) := by
  intro a ha b hb he
  obtain ⟨ha1,ha2⟩ := Finset.mem_product.mp ha
  obtain ⟨hb1,hb2⟩ := Finset.mem_product.mp hb
  have hga := bands_geometry hy ha1 ha2
  have hgb := bands_geometry hy hb1 hb2
  change a.1*a.2=b.1*b.2 at he
  have hd : a.1∣b.1*b.2 := by rw [←he]; exact dvd_mul_right _ _
  rcases hga.1.dvd_mul.mp hd with hd | hd
  · have hp : a.1=b.1 := (Nat.dvd_prime hgb.1).mp hd |>.resolve_left hga.1.ne_one
    have hq : a.2=b.2 := by rw [hp] at he; exact Nat.eq_of_mul_eq_mul_left hgb.1.pos he
    exact Prod.ext hp hq
  · have hp : a.1=b.2 := (Nat.dvd_prime hgb.2.1).mp hd |>.resolve_left hga.1.ne_one
    have hlog := mem_primesInWindow_bounds (Real.exp_pos _).le
      (zero_lt_one.trans (width_gt_one hy)).le ha1
    have hlog' := mem_primesInWindow_bounds
      (mul_pos (zero_lt_one.trans (width_gt_one hy)) (Real.exp_pos _)).le
      (zero_lt_one.trans (width_gt_one hy)).le hb2
    have : (a.1 : ℝ)<b.2 := hlog.2.1.trans_lt hlog'.1
    exact False.elim (by rw [hp] at this; exact lt_irrefl _ this)

/-- Exact native row count, retaining distinct ordered prime incidences. -/
theorem card_badRows {y : ℝ} (hy : y≠0) (J : ℕ) :
    (badRows y J).card=(firstBand y J).card*(secondBand y J).card := by
  rw [badRows,Finset.card_image_of_injOn (pair_mul_injective hy J),Finset.card_product]

/-- Every row is a literal squarefree semiprime and lies inside the
physical cutoff. Both factors tend past any fixed head. -/
theorem mem_badRows_geometry {y : ℝ} (hy : y≠0) {J n : ℕ}
    (hn : n∈badRows y J) :
    Squarefree n ∧ smallPhaseScale y J<n ∧ n≤physicalCutoff y J := by
  obtain ⟨pq,hpq,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
  have hg := bands_geometry hy hp hq
  refine ⟨(Nat.squarefree_mul ((Nat.coprime_primes hg.1 hg.2.1).mpr hg.2.2.1.ne)).mpr
    ⟨hg.1.squarefree,hg.2.1.squarefree⟩,?_,hg.2.2.2.2⟩
  exact hg.2.2.2.1.trans_le (by exact_mod_cast Nat.le_mul_of_pos_right pq.1 hg.2.1.pos)

/-- The rational sign margin holds on ALL paired prime rows, not merely
on a selected counterexample or a floating sample. -/
theorem badRows_diagonal_negative {y : ℝ} (hy : y≠0) {J n : ℕ}
    (hn : n∈badRows y J) : (augmentedKernel y n n).re≤-(1/25 : ℝ) := by
  obtain ⟨pq,hpq,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
  have hg := bands_geometry hy hp hq
  have hA := width_gt_one hy
  have ha := abs_pos.mpr hy
  have hx : 0<smallPhaseScale y J := Real.exp_pos _
  obtain ⟨hpl,_,_⟩ := mem_primesInWindow_bounds hx.le (zero_lt_one.trans hA).le hp
  obtain ⟨_,hqu,_⟩ := mem_primesInWindow_bounds
    (mul_pos (zero_lt_one.trans hA) hx).le (zero_lt_one.trans hA).le hq
  let T := (J : ℝ)*(2*Real.pi)
  have hlo : (T+1/4)/|y|<Real.log pq.1 := by
    simpa [T,smallPhaseScale] using Real.log_lt_log hx hpl
  have hhi : Real.log pq.2≤1/(8*|y|)+(1/(8*|y|)+(T+1/4)/|y|) := by
    have h := Real.log_le_log (by exact_mod_cast hg.2.1.pos) hqu
    rw [Real.log_mul (by positivity : width y≠0)
      (mul_pos (zero_lt_one.trans hA) hx).ne',
      Real.log_mul (by positivity : width y≠0) hx.ne'] at h
    simpa [width,T,smallPhaseScale] using h
  let a := |y| *Real.log pq.1-T
  let b := |y| *Real.log pq.2-T
  have ha0 : 1/4≤a := by
    have h := (div_lt_iff₀ ha).mp hlo
    dsimp [a]
    nlinarith
  have hb1 : b≤1/2 := by
    have h := mul_le_mul_of_nonneg_left hhi ha.le
    field_simp at h
    dsimp [b]
    nlinarith
  have hab : a≤b := by
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by exact_mod_cast hg.1.pos) (by exact_mod_cast hg.2.2.1.le)) ha.le) T
  rw [semiprime_diagonal_real hg.1 hg.2.1 hg.2.2.1.ne]
  have he1 : |y| *Real.log pq.1=a+(J : ℝ)*(2*Real.pi) := by dsimp [a,T];ring
  have he2 : |y| *Real.log pq.2=b+(J : ℝ)*(2*Real.pi) := by dsimp [b,T];ring
  rw [he1,he2,Real.cos_add_nat_mul_two_pi,Real.cos_add_nat_mul_two_pi,
    Real.sin_add_nat_mul_two_pi,Real.sin_add_nat_mul_two_pi]
  exact small_angles_negative ha0 (hab.trans hb1) (ha0.trans hab) hb1

/-- Whole correction matrix; its off-diagonal entries are unrestricted. -/
def correctedQuadratic (K R : ℕ → ℕ → ℂ) (y : ℝ) (S : Finset ℕ)
    (alpha : ℕ → ℂ) : ℂ :=
  schurQuadratic K y S alpha+
    ∑ m∈S,∑ n∈S,alpha m*conj (alpha n)*R m n

/-- Positive correction trace on the literal physical cutoff. -/
def correctionTrace (R : ℕ → ℕ → ℂ) (X : ℕ) : ℝ :=
  ∑ n∈Finset.Icc 1 X,(R n n).re

/-- A corrected PSD singleton forces a repair of this actual diagonal;
no norm, Fourier projection or componentwise upper allowance is used. -/
theorem correction_diagonal_lower {K R : ℕ → ℕ → ℂ} {y : ℝ} (hy : y≠0)
    {J n : ℕ} (hn : n∈badRows y J) (hK : K n n=1)
    (hPSD : 0≤(correctedQuadratic K R y {n} (fun _ => 1)).re) :
    1/25≤(R n n).re := by
  have hneg := badRows_diagonal_negative hy hn
  simp only [correctedQuadratic,singleton_eq K y n hK,
    Finset.sum_singleton,one_mul,map_one,mul_one,add_re] at hPSD
  linarith

/-- Exact counting lower bound for ANY nonnegative-diagonal correction
making the matrix PSD after a head, even if its off-diagonal is coupled. -/
theorem trace_lower {K R : ℕ → ℕ → ℂ} {y : ℝ} (hy : y≠0) {J H : ℕ}
    (hHead : (H : ℝ)<smallPhaseScale y J)
    (hK : ∀ n∈Finset.Icc 1 (physicalCutoff y J),K n n=1)
    (hR : ∀ n∈Finset.Icc 1 (physicalCutoff y J),0≤(R n n).re)
    (hPSD : ∀ S : Finset ℕ,S⊆Finset.Icc 1 (physicalCutoff y J) →
      (∀ n∈S,H<n) → ∀ alpha,0≤(correctedQuadratic K R y S alpha).re) :
    ((firstBand y J).card : ℝ)*((secondBand y J).card : ℝ)/25≤
      correctionTrace R (physicalCutoff y J) := by
  have hsub : badRows y J⊆Finset.Icc 1 (physicalCutoff y J) := by
    intro n hn
    have hg := mem_badRows_geometry hy hn
    exact Finset.mem_Icc.mpr ⟨by
      have hpos := (Real.exp_pos _ : 0<smallPhaseScale y J).trans hg.2.1
      exact_mod_cast hpos, hg.2.2⟩
  have hlow (n : ℕ) (hn : n∈badRows y J) : 1/25≤(R n n).re := by
    have hg := mem_badRows_geometry hy hn
    have hnH : H<n := by exact_mod_cast hHead.trans hg.2.1
    apply correction_diagonal_lower hy hn (hK n (hsub hn))
    exact hPSD {n} (by simpa using hsub hn) (by simpa using hnH) (fun _ => 1)
  calc
    _ = ∑ _n∈badRows y J,(1/25 : ℝ) := by simp [card_badRows hy];ring
    _ ≤ ∑ n∈badRows y J,(R n n).re := Finset.sum_le_sum hlow
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn _ => hR n hn)

private theorem logConstant_pos {y : ℝ} (hy : y≠0) : 0<logConstant y := by
  unfold logConstant
  positivity

theorem countConstant_pos {y : ℝ} (hy : y≠0) : 0<countConstant y := by
  exact div_pos (sub_pos.mpr (width_gt_one hy)) (mul_pos (by norm_num) (logConstant_pos hy))

/-- Both genuine bands have logarithms bounded by the same linear log
scale. This does not estimate or discard their signed phase. -/
theorem band_log_le {y : ℝ} (hy : y≠0) {J p : ℕ}
    (hp : p∈firstBand y J ∨ p∈secondBand y J) :
    Real.log p≤logConstant y*((J : ℝ)+1) := by
  have hA := width_gt_one hy
  have hA0 := zero_lt_one.trans hA
  have hx : 0<smallPhaseScale y J := Real.exp_pos _
  have hpbound : 0<(p : ℝ) ∧ (p : ℝ)≤width y*(width y*smallPhaseScale y J) := by
    rcases hp with hp | hp
    · obtain ⟨_,hu,hP⟩ := mem_primesInWindow_bounds hx.le hA0.le hp
      refine ⟨by exact_mod_cast hP.pos, hu.trans ?_⟩
      nlinarith
    · obtain ⟨_,hu,hP⟩ := mem_primesInWindow_bounds (mul_pos hA0 hx).le hA0.le hp
      exact ⟨by exact_mod_cast hP.pos,hu⟩
  calc
    Real.log p≤Real.log (width y*(width y*smallPhaseScale y J)) :=
      Real.log_le_log hpbound.1 hpbound.2
    _ = ((J : ℝ)*(2*Real.pi)+1/2)/|y| := by
      rw [Real.log_mul hA0.ne' (mul_pos hA0 hx).ne',Real.log_mul hA0.ne' hx.ne']
      simp only [width,smallPhaseScale,Real.log_exp]
      ring
    _ ≤ logConstant y*((J : ℝ)+1) := by
      dsimp [logConstant]
      apply (div_le_iff₀ (abs_pos.mpr hy)).mpr
      field_simp
      nlinarith [Real.pi_pos]

/-- Qualitative actual PNT is used only for the cardinality of bad
rows. It supplies no signed source-scale prime cancellation. -/
theorem first_logMass_tendsto {y : ℝ} (hy : y≠0) :
    Tendsto (fun J : ℕ => (∑ p∈firstBand y J,Real.log p)/smallPhaseScale y J)
      atTop (𝓝 (width y-1)) := by
  have ht := (theta_interval_div_tendsto (zero_lt_one.trans (width_gt_one hy))).comp
    (scale_tendsto hy)
  convert ht using 1
  ext J
  rw [firstBand,sum_log_primesInWindow
    (show 0≤smallPhaseScale y J from (Real.exp_pos _).le) (width_gt_one hy).le]
  rfl

theorem second_logMass_tendsto {y : ℝ} (hy : y≠0) :
    Tendsto (fun J : ℕ => (∑ p∈secondBand y J,Real.log p)/smallPhaseScale y J)
      atTop (𝓝 ((width y-1)*width y)) := by
  have hA0 := zero_lt_one.trans (width_gt_one hy)
  have ht := ((theta_interval_div_tendsto hA0).comp
    ((scale_tendsto hy).const_mul_atTop hA0)).mul_const (width y)
  convert ht using 1
  ext J
  rw [secondBand,sum_log_primesInWindow
    (show 0≤width y*smallPhaseScale y J from (mul_pos hA0 (Real.exp_pos _)).le)
    (width_gt_one hy).le]
  dsimp
  field_simp

/-- Cofinal quantitative row count: each band has at least
c_y * X_J/(J+1) genuine primes. Native floor endpoints are retained. -/
theorem eventually_card_lower {y : ℝ} (hy : y≠0) :
    ∀ᶠ J : ℕ in atTop,
      countConstant y*smallPhaseScale y J/((J : ℝ)+1)≤(firstBand y J).card ∧
      countConstant y*smallPhaseScale y J/((J : ℝ)+1)≤(secondBand y J).card := by
  have hA := width_gt_one hy
  have hhalf : (width y-1)/2<width y-1 := by linarith
  have hhalf' : (width y-1)/2<(width y-1)*width y := by nlinarith
  have ht1 := (first_logMass_tendsto hy).eventually (eventually_gt_nhds hhalf)
  have ht2 := (second_logMass_tendsto hy).eventually (eventually_gt_nhds hhalf')
  filter_upwards [ht1,ht2] with J hJ1 hJ2
  have hx : 0<smallPhaseScale y J := Real.exp_pos _
  have hJ : 0<(J : ℝ)+1 := by positivity
  have hC := logConstant_pos hy
  have hbound (S : Finset ℕ) (hS : ∀ p∈S,p∈firstBand y J ∨ p∈secondBand y J)
      (hMass : (width y-1)/2<(∑ p∈S,Real.log p)/smallPhaseScale y J) :
      countConstant y*smallPhaseScale y J/((J : ℝ)+1)≤S.card := by
    have hsum : (∑ p∈S,Real.log p)≤(S.card : ℝ)*(logConstant y*((J : ℝ)+1)) := by
      simpa using Finset.sum_le_sum (fun p hp => band_log_le hy (hS p hp))
    have hm := (lt_div_iff₀ hx).mp hMass
    apply (div_le_iff₀ hJ).mpr
    dsimp [countConstant]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos (by norm_num) hC)).mpr
    nlinarith
  exact ⟨hbound _ (fun _ hp => Or.inl hp) hJ1,hbound _ (fun _ hp => Or.inr hp) hJ2⟩

/-- Every admissible PSD repair must pay a positive constant times
X_J squared / (J+1) squared in native diagonal trace. -/
theorem eventually_trace_lower {y : ℝ} (hy : y≠0) (H : ℕ)
    (K R : ℕ → ℕ → ℕ → ℂ)
    (hK : ∀ J n,n∈Finset.Icc 1 (physicalCutoff y J) → K J n n=1)
    (hR : ∀ J n,n∈Finset.Icc 1 (physicalCutoff y J) → 0≤(R J n n).re)
    (hPSD : ∀ J (S : Finset ℕ),S⊆Finset.Icc 1 (physicalCutoff y J) →
      (∀ n∈S,H<n) → ∀ alpha,0≤(correctedQuadratic (K J) (R J) y S alpha).re) :
    ∀ᶠ J : ℕ in atTop,
      (countConstant y)^2*(smallPhaseScale y J)^2/(25*((J : ℝ)+1)^2)≤
        correctionTrace (R J) (physicalCutoff y J) := by
  have hh := (scale_tendsto hy).eventually (eventually_gt_atTop (H : ℝ))
  filter_upwards [eventually_card_lower hy,hh] with J hJ hHead
  have hb : countConstant y*smallPhaseScale y J/((J : ℝ)+1)≥0 := by
    exact div_nonneg (mul_nonneg (countConstant_pos hy).le (Real.exp_pos _).le) (by positivity)
  have hprod := mul_le_mul hJ.1 hJ.2 hb (by positivity)
  calc
    _ = (countConstant y*smallPhaseScale y J/((J : ℝ)+1))^2/25 := by
      field_simp
    _ ≤ (firstBand y J).card*(secondBand y J).card/25 := by
      simpa only [pow_two] using div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℝ)≤25)
    _ ≤ _ := trace_lower hy hHead (hK J) (hR J) (hPSD J)

/-- Continuous upper endpoint for the literal NATURAL cutoff. It is
used only to lower-bound the normalized repair cost, not to replace a
carrier mask or assert a weighted source asymptotic. -/
def upperCutoff (y : ℝ) (J : ℕ) : ℝ := (width y)^3*(smallPhaseScale y J)^2

theorem upperCutoff_pos (y : ℝ) (J : ℕ) : 0<upperCutoff y J := by
  unfold upperCutoff width smallPhaseScale
  positivity

theorem cutoff_le_upper (y : ℝ) (J : ℕ) :
    (physicalCutoff y J : ℝ)≤upperCutoff y J :=
  Nat.floor_le (upperCutoff_pos y J).le

theorem cutoff_pos {y : ℝ} (hy : y≠0) (J : ℕ) : 0<physicalCutoff y J := by
  have hA := width_gt_one hy
  have hx : 1<smallPhaseScale y J := Real.one_lt_exp_iff.mpr (by positivity)
  have hA3 : 1≤(width y)^3 := one_le_pow₀ hA.le
  have hx2 : 1≤(smallPhaseScale y J)^2 := one_le_pow₀ hx.le
  apply Nat.succ_le_iff.mp
  exact (Nat.le_floor_iff (upperCutoff_pos y J).le).mpr
    (by simpa [upperCutoff] using mul_le_mul hA3 hx2 (by norm_num : (0 : ℝ)≤1) (by positivity))

/-- The physical cutoffs really tend to infinity; the cost obstruction
is cofinal in arithmetic scale, not merely in a fixed finite matrix. -/
theorem cutoff_tendsto {y : ℝ} (hy : y≠0) :
    Tendsto (physicalCutoff y) atTop atTop := by
  apply tendsto_atTop_mono ?_ ((tendsto_nat_floor_atTop (α := ℝ)).comp (scale_tendsto hy))
  intro J
  apply Nat.floor_mono
  have hx : 1<smallPhaseScale y J := Real.one_lt_exp_iff.mpr (by positivity)
  change smallPhaseScale y J≤(width y)^3*(smallPhaseScale y J)^2
  calc
    _ ≤ (smallPhaseScale y J)^2 := by nlinarith
    _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (width_gt_one hy).le)

/-- The positive lower count cost beats EVERY positive sublinear power
of the native cutoff along the cofinal phase-aligned scales. -/
theorem tendsto_lower_div_upper {y beta : ℝ} (hy : y≠0) (hbeta : beta<1) :
    Tendsto (fun J : ℕ =>
      ((countConstant y)^2*(smallPhaseScale y J)^2/(25*((J : ℝ)+1)^2)) /
        (upperCutoff y J)^beta) atTop atTop := by
  let b := (2-2*beta)*(2*Real.pi)/|y|
  let e := (2-2*beta)/(4*|y|)-3*beta/(8*|y|)-b
  have hb : 0<b := by
    exact div_pos (mul_pos (by linarith) (by positivity)) (abs_pos.mpr hy)
  have hJt : Tendsto (fun J : ℕ => (J : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := (tendsto_exp_mul_div_rpow_atTop (2 : ℝ) b hb).comp hJt
  have hc : 0<(countConstant y)^2/25*Real.exp e := by
    exact mul_pos (div_pos (sq_pos_of_pos (countConstant_pos hy)) (by norm_num)) (Real.exp_pos _)
  apply (ht.const_mul_atTop hc).congr
  intro J
  dsimp
  simp only [Real.rpow_two]
  have hpow : (upperCutoff y J)^beta =
      Real.exp ((3/(8*|y|)+2*((J : ℝ)*(2*Real.pi)+1/4)/|y|)*beta) := by
    rw [Real.rpow_def_of_pos (upperCutoff_pos y J)]
    congr 1
    have hA0 : 0<width y := Real.exp_pos _
    have hx0 : 0<smallPhaseScale y J := Real.exp_pos _
    rw [upperCutoff,Real.log_mul (pow_pos hA0 _).ne' (pow_pos hx0 _).ne',
      Real.log_pow,Real.log_pow]
    simp only [width,smallPhaseScale,Real.log_exp]
    ring
  rw [hpow]
  have hxpow : (smallPhaseScale y J)^2 =
      Real.exp (2*((J : ℝ)*(2*Real.pi)+1/4)/|y|) := by
    rw [smallPhaseScale,←Real.exp_nat_mul]
    congr 1
    ring
  rw [hxpow]
  have he : e+b*((J : ℝ)+1)=2*((J : ℝ)*(2*Real.pi)+1/4)/|y|-
      (3/(8*|y|)+2*((J : ℝ)*(2*Real.pi)+1/4)/|y|)*beta := by dsimp [b,e];ring
  calc
    _ = (countConstant y)^2*(Real.exp e*Real.exp (b*((J : ℝ)+1)))/
        (25*((J : ℝ)+1)^2) := by field_simp
    _ = (countConstant y)^2*Real.exp
        (2*((J : ℝ)*(2*Real.pi)+1/4)/|y|-
          (3/(8*|y|)+2*((J : ℝ)*(2*Real.pi)+1/4)/|y|)*beta)/
        (25*((J : ℝ)+1)^2) := by rw [←Real.exp_add,he]
    _ = _ := by rw [Real.exp_sub];field_simp

/-- Strong no-go for repairing the full phased matrix by a positive
correction: its native trace divided by X^beta tends to INFINITY, not
zero. This includes arbitrary coupled off-diagonal repairs. -/
theorem tendsto_trace_div_source {y beta : ℝ} (hy : y≠0)
    (hbeta0 : 0<beta) (hbeta1 : beta<1) (H : ℕ)
    (K R : ℕ → ℕ → ℕ → ℂ)
    (hK : ∀ J n,n∈Finset.Icc 1 (physicalCutoff y J) → K J n n=1)
    (hR : ∀ J n,n∈Finset.Icc 1 (physicalCutoff y J) → 0≤(R J n n).re)
    (hPSD : ∀ J (S : Finset ℕ),S⊆Finset.Icc 1 (physicalCutoff y J) →
      (∀ n∈S,H<n) → ∀ alpha,0≤(correctedQuadratic (K J) (R J) y S alpha).re) :
    Tendsto (fun J : ℕ => correctionTrace (R J) (physicalCutoff y J) /
      (physicalCutoff y J : ℝ)^beta) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ (tendsto_lower_div_upper hy hbeta1)
  filter_upwards [eventually_trace_lower hy H K R hK hR hPSD] with J hJ
  have hx : 0<(physicalCutoff y J : ℝ) := by exact_mod_cast cutoff_pos hy J
  have hnonneg : 0≤(countConstant y)^2*(smallPhaseScale y J)^2/(25*((J : ℝ)+1)^2) := by positivity
  calc
    _ ≤ ((countConstant y)^2*(smallPhaseScale y J)^2/(25*((J : ℝ)+1)^2)) /
        (physicalCutoff y J : ℝ)^beta :=
      div_le_div_of_nonneg_left hnonneg (Real.rpow_pos_of_pos hx _)
        (Real.rpow_le_rpow hx.le (cutoff_le_upper y J) hbeta0.le)
    _ ≤ _ := div_le_div_of_nonneg_right hJ (Real.rpow_pos_of_pos hx _).le

/-- No source-bounded positive repair exists, not even with a moving
matrix, arbitrary off-diagonal correction and an arbitrary finite head. -/
theorem not_eventually_source_bounded_repair {y beta : ℝ} (hy : y≠0)
    (hbeta0 : 0<beta) (hbeta1 : beta<1) (H : ℕ)
    (K R : ℕ → ℕ → ℕ → ℂ)
    (hK : ∀ J n,n∈Finset.Icc 1 (physicalCutoff y J) → K J n n=1)
    (hR : ∀ J n,n∈Finset.Icc 1 (physicalCutoff y J) → 0≤(R J n n).re)
    (hPSD : ∀ J (S : Finset ℕ),S⊆Finset.Icc 1 (physicalCutoff y J) →
      (∀ n∈S,H<n) → ∀ alpha,0≤(correctedQuadratic (K J) (R J) y S alpha).re)
    (C : ℝ) :
    ¬∀ᶠ J : ℕ in atTop,correctionTrace (R J) (physicalCutoff y J) /
      (physicalCutoff y J : ℝ)^beta≤C := by
  intro hbound
  have ht := tendsto_trace_div_source hy hbeta0 hbeta1 H K R hK hR hPSD
  obtain ⟨J,hJ⟩ := (hbound.and (ht.eventually (eventually_gt_atTop C))).exists
  exact not_lt_of_ge hJ.1 hJ.2

/-- In particular every actual-zero source scale is unaffordable for
this repair class. Exposure, simplicity and a weighted cutoff source
asymptotic are NOT assumed or inferred. -/
theorem not_source_bounded_repair_at_zero (rho : NontrivialZetaZero) (H : ℕ)
    (K R : ℕ → ℕ → ℕ → ℂ)
    (hK : ∀ J n,n∈Finset.Icc 1 (physicalCutoff rho.1.im J) → K J n n=1)
    (hR : ∀ J n,n∈Finset.Icc 1 (physicalCutoff rho.1.im J) → 0≤(R J n n).re)
    (hPSD : ∀ J (S : Finset ℕ),S⊆Finset.Icc 1 (physicalCutoff rho.1.im J) →
      (∀ n∈S,H<n) → ∀ alpha,0≤(correctedQuadratic (K J) (R J) rho.1.im S alpha).re)
    (C : ℝ) :
    ¬∀ᶠ J : ℕ in atTop,correctionTrace (R J) (physicalCutoff rho.1.im J) /
      (physicalCutoff rho.1.im J : ℝ)^rho.1.re≤C :=
  not_eventually_source_bounded_repair (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
    (NontrivialZetaZero.zero_lt_re rho) rho.re_lt_one H K R hK hR hPSD C

end
end RiemannGaussian.ArithmeticOperatorCoprimeRepairAudit
