/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGlobalPrimePeriod
import Mathlib.Data.Finset.NatDivisors
/-!
# One-sided cutoff-crossing costs in the literal prime sum

The affine error of each individual hinge is nonnegative. Consequently a
cutoff crossing with favorable Möbius-weighted prime phase is free on the
corresponding side of the joint estimate. The inequalities below retain the
constant and first prime moments, both cutoffs, and all literal weights.
They apply to every cofactor count and arbitrary clipped prime selections.
No source-scale estimate for the remaining adverse costs is assumed.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSignedCrossing
open ZetaRieszGlobalCurvature ZetaRieszGlobalPrimePeriod
open ZetaRieszFixedCountPeriod (response)

/-- Convexity of a hinge fixes the sign of its exact affine remainder,
including a base point exactly on the cutoff. -/
theorem hinge_error_nonneg (z x : ℝ) :
    0 ≤ max 0 (z+x)-max 0 z-x*(if 0 < z then 1 else 0) := by
  by_cases hz : 0 < z
  · rw [if_pos hz,max_eq_right hz.le]
    linarith [le_max_right 0 (z+x)]
  · rw [if_neg hz,max_eq_left (le_of_not_gt hz)]
    simp

/-- Only an adverse signed multiplier pays a cost on each side. -/
theorem weighted_hinge_bounds {h x : ℝ} (hh : 0 ≤ h) (hx : |x| ≤ h)
    (c z : ℝ) :
    min c 0 * max 0 (h-|z|) ≤
      c*(max 0 (z+x)-max 0 z-x*(if 0 < z then 1 else 0)) ∧
    c*(max 0 (z+x)-max 0 z-x*(if 0 < z then 1 else 0)) ≤
      max c 0 * max 0 (h-|z|) := by
  have h0 := hinge_error_nonneg z x
  have h1 := hinge_affine_error hh hx z
  rw [abs_of_nonneg h0] at h1
  by_cases hc : 0 ≤ c
  · rw [min_eq_right hc,max_eq_left hc]
    exact ⟨by simpa using mul_nonneg hc h0,mul_le_mul_of_nonneg_left h1 hc⟩
  · have hc' := le_of_not_ge hc
    rw [min_eq_left hc',max_eq_right hc']
    exact ⟨mul_le_mul_of_nonpos_left h1 hc',by nlinarith⟩

/-- These are bounds for the original signed divisor response. The sign is
tested after multiplying the actual prime weight by the divisor Möbius sign. -/
theorem riesz_signed_affine_bounds {h x : ℝ} (hh : 0 ≤ h) (hx : |x| ≤ h)
    (g D : ℝ) (a : ℕ) :
    (∑ d ∈ a.divisors, min (g*(μ d : ℝ)) 0 * max 0 (h-|D-Real.log d|)) ≤
      g*(VaughanLogAverage.riesz (D+x) a-VaughanLogAverage.riesz D a-
        x*cutoffSlope D a) ∧
    g*(VaughanLogAverage.riesz (D+x) a-VaughanLogAverage.riesz D a-
        x*cutoffSlope D a) ≤
      ∑ d ∈ a.divisors, max (g*(μ d : ℝ)) 0 * max 0 (h-|D-Real.log d|) := by
  have he : g*(VaughanLogAverage.riesz (D+x) a-VaughanLogAverage.riesz D a-
      x*cutoffSlope D a) = ∑ d ∈ a.divisors, (g*(μ d : ℝ))*
      (max 0 (D-Real.log d+x)-max 0 (D-Real.log d)-
        x*(if 0 < D-Real.log d then 1 else 0)) := by
    simp only [VaughanLogAverage.riesz,cutoffSlope,Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [show D+x-Real.log d = D-Real.log d+x by ring]
    ring
  rw [he]
  exact ⟨Finset.sum_le_sum (fun d _ => (weighted_hinge_bounds hh hx _ _).1),
    Finset.sum_le_sum (fun d _ => (weighted_hinge_bounds hh hx _ _).2)⟩

/-- Both original Riesz cutoffs stay in the affine baseline; the fixed
cofactor cutoff cancels exactly from its remainder. -/
theorem response_signed_affine_bounds {h T v : ℝ} (hh : 0 ≤ h)
    (hx : |T-v| ≤ h) (g L : ℝ) (a : ℕ) :
    (∑ d ∈ a.divisors, min (g*(μ d : ℝ)) 0 * max 0 (h-|v-L-Real.log d|)) ≤
      g*response L T a-(g*response L v a+cutoffSlope (v-L) a*(g*(T-v))) ∧
    g*response L T a-(g*response L v a+cutoffSlope (v-L) a*(g*(T-v))) ≤
      ∑ d ∈ a.divisors, max (g*(μ d : ℝ)) 0 * max 0 (h-|v-L-Real.log d|) := by
  have h := riesz_signed_affine_bounds hh hx g (v-L) a
  rw [show v-L+(T-v) = T-L by ring] at h
  have he : g*response L T a-(g*response L v a+cutoffSlope (v-L) a*(g*(T-v))) =
      g*(VaughanLogAverage.riesz (T-L) a-VaughanLogAverage.riesz (v-L) a-
        (T-v)*cutoffSlope (v-L) a) := by unfold response; ring
  rwa [he]

/-- Count-free simultaneous floor and ceiling for the literal masked prime
sum. Favorable crossings are never charged against the corresponding side. -/
theorem literal_signed_affine_bounds (A S : Finset ℕ) (N : ℕ)
    (P : ℕ → Finset ℕ) (L v y : ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hSF : ∀ a ∈ S, Squarefree a ∧ 2 ≤ a.primeFactors.card)
    (hP : ∀ a ∈ S, ∀ p ∈ P a, p.Prime ∧ ¬p ∣ a)
    (hx : ∀ a ∈ S, ∀ p ∈ P a, |Real.log p+Real.log a-v| ≤ h) :
    let g := signedPrimeWeight A L N y
    let M := ∑ a ∈ S,
      (response L v a*(∑ p ∈ P a, g a p)+cutoffSlope (v-L) a*
        (∑ p ∈ P a, g a p*(Real.log p+Real.log a-v)))/a
    let Eneg := ∑ a ∈ S, (∑ p ∈ P a, ∑ d ∈ a.divisors,
      min (g a p*(μ d : ℝ)) 0 * max 0 (h-|v-L-Real.log d|))/a
    let Epos := ∑ a ∈ S, (∑ p ∈ P a, ∑ d ∈ a.divisors,
      max (g a p*(μ d : ℝ)) 0 * max 0 (h-|v-L-Real.log d|))/a
    M+Eneg ≤ (∑ a ∈ S, ∑ p ∈ P a,
      ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re ∧
    (∑ a ∈ S, ∑ p ∈ P a,
      ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re ≤ M+Epos := by
  dsimp only
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  have hpoint a (ha : a ∈ S) p (hp : p ∈ P a) :=
    response_signed_affine_bounds hh (hx a ha p hp)
      (signedPrimeWeight A L N y a p) L a
  have he a (ha : a ∈ S) :
      (∑ p ∈ P a, (ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re) =
      (∑ p ∈ P a, signedPrimeWeight A L N y a p*
        response L (Real.log p+Real.log a) a)/a := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    exact re_residual_atom (hSF a ha).1 (hSF a ha).2 (hP a ha p hp).1
      (hP a ha p hp).2 A L y N
  constructor
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    rw [he a ha,← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg a)
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    linarith only [(hpoint a ha p hp).1]
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    rw [he a ha,← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg a)
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    linarith only [(hpoint a ha p hp).2]

/-- The sign improvement survives summing arbitrary radial periods. All
clipped endpoints retain their actual moments and actual signed costs. -/
theorem radial_signed_affine_bounds {ι : Type*} (B : Finset ι) (A : Finset ℕ)
    (S : ι → Finset ℕ) (N : ℕ) (P : ι → ℕ → Finset ℕ)
    (L y : ℝ) (v : ι → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hSF : ∀ j ∈ B, ∀ a ∈ S j, Squarefree a ∧ 2 ≤ a.primeFactors.card)
    (hP : ∀ j ∈ B, ∀ a ∈ S j, ∀ p ∈ P j a, p.Prime ∧ ¬p ∣ a)
    (hx : ∀ j ∈ B, ∀ a ∈ S j, ∀ p ∈ P j a, |Real.log p+Real.log a-v j| ≤ h) :
    let g := signedPrimeWeight A L N y
    let M : ι → ℝ := fun j => ∑ a ∈ S j,
      (response L (v j) a*(∑ p ∈ P j a, g a p)+cutoffSlope (v j-L) a*
        (∑ p ∈ P j a, g a p*(Real.log p+Real.log a-v j)))/a
    let Eneg : ι → ℝ := fun j => ∑ a ∈ S j, (∑ p ∈ P j a, ∑ d ∈ a.divisors,
      min (g a p*(μ d : ℝ)) 0 * max 0 (h-|v j-L-Real.log d|))/a
    let Epos : ι → ℝ := fun j => ∑ a ∈ S j, (∑ p ∈ P j a, ∑ d ∈ a.divisors,
      max (g a p*(μ d : ℝ)) 0 * max 0 (h-|v j-L-Real.log d|))/a
    B.sum (fun j : ι => M j+Eneg j) ≤ (∑ j ∈ B, ∑ a ∈ S j, ∑ p ∈ P j a,
      ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re ∧
    (∑ j ∈ B, ∑ a ∈ S j, ∑ p ∈ P j a,
      ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re ≤ B.sum (fun j : ι => M j+Epos j) := by
  dsimp only
  rw [Complex.re_sum]
  exact ⟨Finset.sum_le_sum (fun j hj =>
    (literal_signed_affine_bounds A (S j) N (P j) L (v j) y hh
      (hSF j hj) (hP j hj) (hx j hj)).1),
    Finset.sum_le_sum (fun j hj =>
    (literal_signed_affine_bounds A (S j) N (P j) L (v j) y hh
      (hSF j hj) (hP j hj) (hx j hj)).2)⟩

/-- A favorable cutoff crossing costs zero in the floor, without requiring
the response, its slope, or the complete prime moment to have a sign. -/
theorem response_affine_floor_of_crossing_sign {h T v : ℝ} (hh : 0 ≤ h)
    (hx : |T-v| ≤ h) (g L : ℝ) (a : ℕ)
    (hs : ∀ d ∈ a.divisors, |v-L-Real.log d| < h → 0 ≤ g*(μ d : ℝ)) :
    g*response L v a+cutoffSlope (v-L) a*(g*(T-v)) ≤ g*response L T a := by
  have he : (∑ d ∈ a.divisors, min (g*(μ d : ℝ)) 0 * max 0 (h-|v-L-Real.log d|)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    by_cases hc : |v-L-Real.log d| < h
    · rw [min_eq_right (hs d hd hc),zero_mul]
    · rw [max_eq_left (by linarith : h-|v-L-Real.log d| ≤ 0),mul_zero]
  have hb := (response_signed_affine_bounds hh hx g L a).1
  rw [he] at hb
  linarith only [hb]

/-- Dually, favorable crossings are free in the ceiling. -/
theorem response_affine_ceiling_of_crossing_sign {h T v : ℝ} (hh : 0 ≤ h)
    (hx : |T-v| ≤ h) (g L : ℝ) (a : ℕ)
    (hs : ∀ d ∈ a.divisors, |v-L-Real.log d| < h → g*(μ d : ℝ) ≤ 0) :
    g*response L T a ≤ g*response L v a+cutoffSlope (v-L) a*(g*(T-v)) := by
  have he : (∑ d ∈ a.divisors, max (g*(μ d : ℝ)) 0 * max 0 (h-|v-L-Real.log d|)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    by_cases hc : |v-L-Real.log d| < h
    · rw [max_eq_right (hs d hd hc),zero_mul]
    · rw [max_eq_left (by linarith : h-|v-L-Real.log d| ≤ 0),mul_zero]
  have hb := (response_signed_affine_bounds hh hx g L a).2
  rw [he] at hb
  linarith only [hb]

/-- An ordinary semiprime cofactor has its exact clipped linear response
below the larger prime logarithm. This identifies a real crossing sector. -/
theorem semiprime_response {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    {D : ℝ} (hD : 0 ≤ D) (hDq : D ≤ Real.log q) :
    VaughanLogAverage.riesz D (q*r) = min D (Real.log r) := by
  have he := ZetaSquarefreeRieszWindows.riesz_two_primes_eq_tent D hq hr hqr
    hq.not_dvd_one hr.not_dvd_one
  simp only [mul_one,Nat.divisors_one,Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_one,Int.cast_one,one_mul,Nat.cast_one,Real.log_one,sub_zero] at he
  rw [he]
  unfold ZetaSquarefreeRieszWindows.primePairTent
  have hr0 := Real.log_natCast_nonneg r
  rw [max_eq_right hD,max_eq_left (by linarith : D-Real.log q ≤ 0),
    max_eq_left (by linarith : D-Real.log q-Real.log r ≤ 0)]
  by_cases hDr : D ≤ Real.log r
  · rw [max_eq_left (by linarith : D-Real.log r ≤ 0),min_eq_left hDr]; ring
  · rw [max_eq_right (by linarith : 0 ≤ D-Real.log r),min_eq_right (by linarith : Real.log r ≤ D)]
    ring

/-- Below both semiprime factors the exact cutoff slope is one. -/
theorem semiprime_slope {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    {D : ℝ} (hD : 0 < D) (hDq : D < Real.log q) (hDr : D < Real.log r) :
    cutoffSlope D (q*r) = 1 := by
  have hd : (q*r).divisors = {1,r,q,q*r} := by
    rw [Nat.divisors_mul,hq.divisors,hr.divisors]
    ext d
    simp only [Finset.mul_def,Finset.mem_image,Finset.mem_product,Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨a,b⟩,⟨(rfl | rfl),(rfl | rfl)⟩,rfl⟩ <;> simp
    · rintro (hd | hd | hd | hd)
      · exact ⟨(1,1),⟨Or.inl rfl,Or.inl rfl⟩,by simp [hd]⟩
      · exact ⟨(1,r),⟨Or.inl rfl,Or.inr rfl⟩,by simp [hd]⟩
      · exact ⟨(q,1),⟨Or.inr rfl,Or.inl rfl⟩,by simp [hd]⟩
      · exact ⟨(q,r),⟨Or.inr rfl,Or.inr rfl⟩,hd.symm⟩
  have hq0 := Real.log_natCast_nonneg q
  have hr0 := Real.log_natCast_nonneg r
  have hlog : Real.log (q*r : ℕ) = Real.log q+Real.log r := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
  have hf (d : ℕ) (hd' : d ∈ ({r,q,q*r} : Finset ℕ)) :
      (μ d : ℝ)*(if 0 < D-Real.log d then 1 else 0) = 0 := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hd'
    rcases hd' with rfl | rfl | rfl <;> rw [if_neg (by linarith),mul_zero]
  unfold cutoffSlope
  have hqr1 : q*r ≠ 1 := by nlinarith [hq.two_le,hr.two_le]
  rw [hd,Finset.sum_insert (by simp [hq.ne_one,hr.ne_one,hqr1,eq_comm])]
  rw [Finset.sum_eq_zero hf]
  simp [hD]

/-- The exact crossing in the proposed two-large-prime box has the
opposite sign to its negative-phase affine baseline. -/
theorem triple_crossing_eq {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    {P L v : ℝ} (hD : 0 < v-L) (hDq : v-L < Real.log q)
    (hDr : v-L < Real.log r) (hcross : L ≤ P+Real.log q)
    (hupper : P+Real.log r ≤ L) :
    response L (P+Real.log (q*r : ℕ)) (q*r)-response L v (q*r)-
      cutoffSlope (v-L) (q*r)*(P+Real.log (q*r : ℕ)-v) = L-P-Real.log q := by
  have hlog : Real.log (q*r : ℕ) = Real.log q+Real.log r := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
  have hr0 := Real.log_natCast_nonneg r
  rw [semiprime_slope hq hr hD hDq hDr]
  unfold response
  rw [hlog,semiprime_response hq hr hqr hD.le hDq.le,min_eq_left hDr.le,
    semiprime_response hq hr hqr (by linarith : 0 ≤ P+(Real.log q+Real.log r)-L)
      (by linarith : P+(Real.log q+Real.log r)-L ≤ Real.log q),
    min_eq_right (by linarith : Real.log r ≤ P+(Real.log q+Real.log r)-L)]
  ring

/-- The actual difference already charged in the prime-period affine
estimate. This retains the original residual atom, rather than a completed
or continuum surrogate. -/
def crossingAtom (A : Finset ℕ) (L : ℝ) (N : ℕ) (y v : ℝ) (a p : ℕ) : ℝ :=
  (ZetaRieszJointAllocation.residualCoefficient A L N (p*a)*
    zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re-
  (signedPrimeWeight A L N y a p*response L v a+
    cutoffSlope (v-L) a*(signedPrimeWeight A L N y a p*(Real.log p+Real.log a-v)))/a

/-- The literal crossing error equals its signed Riesz affine remainder. -/
theorem crossingAtom_eq (A : Finset ℕ) (L : ℝ) (N : ℕ) (y v : ℝ)
    {a p : ℕ} (hs : Squarefree a) (hc : 2 ≤ a.primeFactors.card)
    (hp : p.Prime) (hpd : ¬p ∣ a) :
    crossingAtom A L N y v a p = signedPrimeWeight A L N y a p/a*
      (response L (Real.log p+Real.log a) a-response L v a-
        cutoffSlope (v-L) a*(Real.log p+Real.log a-v)) := by
  rw [crossingAtom,re_residual_atom hs hc hp hpd]
  ring

/-- Exact triple crossing with the original factorial allocation and phase.
In a negative cosine sector this correction is positive. -/
theorem triple_crossingAtom_eq (A : Finset ℕ) (N : ℕ) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {L v : ℝ} (hD : 0 < v-L) (hDq : v-L < Real.log q)
    (hDr : v-L < Real.log r) (hcross : L ≤ Real.log p+Real.log q)
    (hupper : Real.log p+Real.log r ≤ L) (y : ℝ) :
    crossingAtom A L N y v (q*r) p =
      ZetaRieszOneSidedArithmetic.weight A N (p*(q*r))*
        (Real.log (p*(q*r) : ℕ)/L*(L-Real.log p-Real.log q))*
          Real.cos (y*Real.log (p*(q*r) : ℕ)) := by
  have hcop : q.Coprime r := hq.coprime_iff_not_dvd.mpr
    (fun hd => hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp hd))
  have hs := Nat.squarefree_mul_iff.mpr ⟨hcop,hq.squarefree,hr.squarefree⟩
  have hc : (q*r).primeFactors.card = 2 := by
    simp [Nat.primeFactors_mul hq.ne_zero hr.ne_zero,hq.primeFactors,hr.primeFactors,hqr]
  have hpd : ¬p ∣ q*r := by
    intro hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp hd)
  rw [crossingAtom_eq A L N y v hs (by omega) hp hpd,
    triple_crossing_eq hq hr hqr hD hDq hDr hcross hupper]
  have hlog : Real.log (p*(q*r) : ℕ) = Real.log p+Real.log (q*r : ℕ) := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hs.ne_zero)]
  have hex : Real.exp (-(3/2 : ℝ)*Real.log (p*(q*r) : ℕ)) =
      Real.exp (-Real.log (p*(q*r) : ℕ)/2)*(p : ℝ)⁻¹*((q*r : ℕ) : ℝ)⁻¹ := by
    rw [show -(3/2 : ℝ)*Real.log (p*(q*r) : ℕ) =
      -Real.log (p*(q*r) : ℕ)/2-Real.log (p*(q*r) : ℕ) by ring,
      Real.exp_sub,Real.exp_log (by exact_mod_cast Nat.mul_pos hp.pos (Nat.mul_pos hq.pos hr.pos)),
      Nat.cast_mul]
    ring
  unfold signedPrimeWeight ZetaRieszOneSidedArithmetic.weight ZetaRieszOneSidedArithmetic.amplitude
  rw [hc,hex,hlog,pow_succ]
  norm_num only
  ring

/-- A genuine signed gain, not an absolute error charge. It applies to
every selected triple satisfying the explicit crossing geometry. -/
theorem triple_crossingAtom_lower (A : Finset ℕ) (N : ℕ) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {L v w y : ℝ} (hL : 0 < L) (hw : 0 ≤ w)
    (hD : 0 < v-L) (hDq : v-L < Real.log q) (hDr : v-L < Real.log r)
    (hcross : 2*w ≤ Real.log p+Real.log q-L)
    (hupper : Real.log p+Real.log r ≤ L)
    (hshare : (1/2 : ℝ) ≤ 1-ZetaRieszJointAllocation.boundedShare A N (p*(q*r)))
    (hcos : Real.cos (y*Real.log (p*(q*r) : ℕ)) ≤ -(1/2 : ℝ)) :
    (w/2)*ZetaRieszOneSidedArithmetic.amplitude N (p*(q*r)) ≤
      crossingAtom A L N y v (q*r) p := by
  have hcross' : L ≤ Real.log p+Real.log q := by linarith
  rw [triple_crossingAtom_eq A N hp hq hr hpq hpr hqr hD hDq hDr hcross' hupper y]
  have hlog : Real.log (p*(q*r) : ℕ) = Real.log p+Real.log q+Real.log r := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hq.ne_zero hr.ne_zero),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
    ring
  have hx : 1 ≤ Real.log (p*(q*r) : ℕ)/L := (le_div_iff₀ hL).mpr (by
    rw [one_mul,hlog]
    linarith [Real.log_natCast_nonneg r])
  have hprod : w ≤ (Real.log p+Real.log q-L)*(-Real.cos (y*Real.log (p*(q*r) : ℕ))) := by
    have hh := mul_le_mul hcross (show (1/2 : ℝ) ≤ -Real.cos (y*Real.log (p*(q*r) : ℕ)) by linarith)
      (by norm_num : (0 : ℝ) ≤ 1/2) (by linarith : 0 ≤ Real.log p+Real.log q-L)
    linarith
  have hx' := mul_le_mul hx hprod hw (by linarith : 0 ≤ Real.log (p*(q*r) : ℕ)/L)
  have hamp := ZetaRieszCosineCarrier.factorial_envelope_nonneg N (p*(q*r))
  change 0 ≤ ZetaRieszOneSidedArithmetic.amplitude N (p*(q*r)) at hamp
  have hwgt : ZetaRieszOneSidedArithmetic.amplitude N (p*(q*r))/2 ≤
      ZetaRieszOneSidedArithmetic.weight A N (p*(q*r)) := by
    unfold ZetaRieszOneSidedArithmetic.weight
    nlinarith [mul_le_mul_of_nonneg_right hshare hamp]
  have hfinal := mul_le_mul hwgt hx' (by simpa using hw)
    (ZetaRieszOneSidedArithmetic.weight_nonneg A N (p*(q*r)))
  nlinarith only [hfinal]

end RiemannGaussian.ZetaRieszSignedCrossing
