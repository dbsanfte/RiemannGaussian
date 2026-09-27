/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFivePrimePairSupply
import RiemannGaussian.ZetaRieszJointQuintupleFloor

/-!
# Ordered four-prime debits and three-tent five-prime credit

These inequalities retain the original atom and its phase. Ordering the
two smallest primes makes each coefficient a capped least-prime logarithm.
The cap is independent of that least logarithm when the other variables
and the sum of the two small logarithms are fixed. This is used for the
quantitative population comparison, without completing any prime sum.
-/

namespace RiemannGaussian.ZetaRieszOrderedCapacity
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaRieszPrimeEndpoint ZetaRieszReflectedLinear
open ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic

/-- The ordered three-prime clipped balance is one capped least log.
This evaluates its whole positive part, including inactive cutoffs. -/
theorem clipped_three_eq_cap {q a r D : ℝ} (hr0 : 0 ≤ r)
    (hra : r ≤ a) (haq : a ≤ q) :
    max 0 (min D q+min D a+min D r-2*D) =
      min r (max 0 (min D (min (a+r-D) (q+a+r-2*D)))) := by
  by_cases hDr : D ≤ r
  · rw [min_eq_left (hDr.trans (hra.trans haq)),min_eq_left (hDr.trans hra),
      min_eq_left hDr]
    have he : min D (min (a+r-D) (q+a+r-2*D)) = D :=
      min_eq_left (le_min (by linarith) (by linarith))
    rw [he,min_eq_right (max_le hr0 hDr)]
    congr 1
    ring
  have hrD : r ≤ D := le_of_not_ge hDr
  by_cases hDa : D ≤ a
  · rw [min_eq_left (hDa.trans haq),min_eq_left hDa,min_eq_right hrD]
    have hmin : r ≤ min D (min (a+r-D) (q+a+r-2*D)) :=
      le_min hrD (le_min (by linarith) (by linarith))
    rw [min_eq_left (hmin.trans (le_max_right _ _))]
    simpa only [show D+D+r-2*D = r by ring] using max_eq_right hr0
  have haD : a ≤ D := le_of_not_ge hDa
  by_cases hDq : D ≤ q
  · rw [min_eq_left hDq,min_eq_right haD,min_eq_right hrD]
    have he : min D (min (a+r-D) (q+a+r-2*D)) = a+r-D := by
      rw [min_eq_left (by linarith : a+r-D ≤ q+a+r-2*D),
        min_eq_right (by linarith : a+r-D ≤ D)]
    rw [he,min_eq_right (max_le hr0 (by linarith))]
    congr 1
    ring
  have hqD : q ≤ D := le_of_not_ge hDq
  rw [min_eq_right hqD,min_eq_right haD,min_eq_right hrD]
  have he : min D (min (a+r-D) (q+a+r-2*D)) = q+a+r-2*D := by
    rw [min_eq_right (by linarith : q+a+r-2*D ≤ a+r-D),
      min_eq_right (by linarith : q+a+r-2*D ≤ D)]
  rw [he,min_eq_right (max_le hr0 (by linarith))]

/-- On an ordered pair, the exact tent has a cap independent of its
smaller member once the sum of the two members is fixed. -/
theorem pair_tent_eq_cap {b r t : ℝ} (hr0 : 0 ≤ r) (hrb : r ≤ b) :
    primePairTent b r t = min r (max 0 (min t (b+r-t))) := by
  rw [primePairTent_eq_overlap (hr0.trans hrb) hr0]
  simp only [min_def,max_def]
  split_ifs <;> linarith

private theorem log_product_four {p q a r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hr : r.Prime) :
    Real.log (p*(q*(a*r)) : ℕ) = Real.log p+Real.log q+Real.log a+Real.log r := by
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
    (by exact_mod_cast mul_ne_zero hq.ne_zero (mul_ne_zero ha.ne_zero hr.ne_zero)),
    Nat.cast_mul,Real.log_mul (by exact_mod_cast hq.ne_zero)
      (by exact_mod_cast mul_ne_zero ha.ne_zero hr.ne_zero),
    Nat.cast_mul,Real.log_mul (by exact_mod_cast ha.ne_zero) (by exact_mod_cast hr.ne_zero)]
  ring

/-- Exact positive coefficient of an ordered squarefree four-prime
label. All three cap obstructions remain before the negative phase. -/
theorem positive_four_eq_cap {p q a r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hr : r.Prime)
    (hrA : r < a) (haQ : a < q) (hqP : q < p)
    (hs : Squarefree (p*(q*(a*r)))) {L : ℝ} (hL : 0 < L)
    (hLhi : L ≤ Real.log (p*(q*(a*r)) : ℕ))
    (hLlo : 2*Real.log (p*(q*(a*r)) : ℕ) ≤ 3*L) :
    max 0 (SquarefreeVaughanLogSource.coefficient L (p*(q*(a*r)))).re =
      (Real.log (p*(q*(a*r)) : ℕ)/L)*min (Real.log r)
        (max 0 (min (L-Real.log p)
          (min (Real.log (p*(q*(a*r)) : ℕ)-L-Real.log q)
            (Real.log p+Real.log (p*(q*(a*r)) : ℕ)-2*L)))) := by
  have hpf : (p*(q*(a*r))).primeFactors = {p,q,a,r} := by
    simp [Nat.primeFactors_mul,hp.ne_zero,hq.ne_zero,ha.ne_zero,hr.ne_zero,
      hp.primeFactors,hq.primeFactors,ha.primeFactors,hr.primeFactors,
      Finset.insert_comm]
  have hpq : p ≠ q := hqP.ne'
  have hpa : p ≠ a := (haQ.trans hqP).ne'
  have hpr : p ≠ r := ((hrA.trans haQ).trans hqP).ne'
  have hqa : q ≠ a := haQ.ne'
  have hqr : q ≠ r := (hrA.trans haQ).ne'
  have har : a ≠ r := hrA.ne'
  have hc : (p*(q*(a*r))).primeFactors.card = 4 := by
    simp [hpf,hpq,hpa,hpr,hqa,hqr,har]
  have hmax : largestPrime (p*(q*(a*r))) = p := by
    apply ZetaRieszPrimeIntervals.largestPrime_eq_of_max
    · simp [hpf]
    · intro v hv
      simp only [hpf,Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> omega
  have he : (p*(q*(a*r))).primeFactors.erase p = {q,a,r} := by
    simp [hpf,hpq,hpa,hpr]
  rw [← ZetaRieszFourPrimeExact.positiveAllowance_eq hc hL hLhi hLlo,
    ZetaRieszFourPrimeExact.positiveAllowance,if_pos hs,hmax,he]
  simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,hqa,hqr,har,
    or_self,not_false_eq_true,Finset.sum_singleton]
  have hlog := log_product_four hp hq ha hr
  have hmin (x D : ℝ) : min D x = x-max 0 (x-D) := by
    simp only [min_def,max_def]
    split_ifs <;> linarith
  have hbal : Real.log p+Real.log (p*(q*(a*r)) : ℕ)-2*L-
      (max 0 (Real.log q-(L-Real.log p))+
        (max 0 (Real.log a-(L-Real.log p))+max 0 (Real.log r-(L-Real.log p)))) =
      min (L-Real.log p) (Real.log q)+min (L-Real.log p) (Real.log a)+
        min (L-Real.log p) (Real.log r)-2*(L-Real.log p) := by
    simp only [hmin]
    linarith
  rw [hbal,clipped_three_eq_cap (Real.log_natCast_nonneg r)
    (Real.log_le_log (by exact_mod_cast hr.pos) (by exact_mod_cast hrA.le))
    (Real.log_le_log (by exact_mod_cast ha.pos) (by exact_mod_cast haQ.le))]
  congr 5 <;> linarith

/-- The ordered cap directly bounds the negative-cosine debit of the
literal four-prime atom. The original unassigned fraction is retained. -/
theorem re_four_atom_ge_cap (A : Finset ℕ) (N : ℕ) {p q a r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hr : r.Prime)
    (hrA : r < a) (haQ : a < q) (hqP : q < p)
    (hs : Squarefree (p*(q*(a*r)))) {L y : ℝ} (hL : 0 < L)
    (hLhi : L ≤ Real.log (p*(q*(a*r)) : ℕ))
    (hLlo : 2*Real.log (p*(q*(a*r)) : ℕ) ≤ 3*L)
    (hcos : Real.cos (y*Real.log (p*(q*(a*r)) : ℕ)) ≤ 0) :
    -(weight A N (p*(q*(a*r)))*(Real.log (p*(q*(a*r)) : ℕ)/L)*
      min (Real.log r) (max 0 (min (L-Real.log p)
        (min (Real.log (p*(q*(a*r)) : ℕ)-L-Real.log q)
          (Real.log p+Real.log (p*(q*(a*r)) : ℕ)-2*L))))*
        (-Real.cos (y*Real.log (p*(q*(a*r)) : ℕ)))) ≤
      (residualCoefficient A L N (p*(q*(a*r)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(a*r)))).re := by
  rw [re_residual_atom]
  have he := positive_four_eq_cap hp hq ha hr hrA haQ hqP hs hL hLhi hLlo
  have hc := mul_le_mul_of_nonpos_right
    (le_max_right 0 (SquarefreeVaughanLogSource.coefficient L (p*(q*(a*r)))).re) hcos
  rw [he] at hc
  have hw := mul_le_mul_of_nonneg_left hc (weight_nonneg A N (p*(q*(a*r))))
  nlinarith only [hw]

/-- A genuinely adverse ordered four-prime coefficient is confined to
these strict share inequalities. In particular its second-smallest prime
stays away from zero even when the least prime approaches zero. -/
theorem positive_four_geometry {p q a r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hr : r.Prime)
    (hrA : r < a) (haQ : a < q) (hqP : q < p)
    (hs : Squarefree (p*(q*(a*r)))) {L : ℝ} (hL : 0 < L)
    (hLhi : L ≤ Real.log (p*(q*(a*r)) : ℕ))
    (hLlo : 2*Real.log (p*(q*(a*r)) : ℕ) ≤ 3*L)
    (hpos : 0 < (SquarefreeVaughanLogSource.coefficient L (p*(q*(a*r)))).re) :
    2*L-Real.log (p*(q*(a*r)) : ℕ) < Real.log p ∧
      Real.log q < Real.log (p*(q*(a*r)) : ℕ)-L ∧
      (L-Real.log p)/2 < Real.log a ∧ Real.log p < L := by
  have he := positive_four_eq_cap hp hq ha hr hrA haQ hqP hs hL hLhi hLlo
  rw [max_eq_right hpos.le] at he
  have hscl : 0 ≤ Real.log (p*(q*(a*r)) : ℕ)/L :=
    div_nonneg (Real.log_natCast_nonneg _) hL.le
  have hcap : 0 < min (Real.log r) (max 0 (min (L-Real.log p)
      (min (Real.log (p*(q*(a*r)) : ℕ)-L-Real.log q)
        (Real.log p+Real.log (p*(q*(a*r)) : ℕ)-2*L)))) := by
    by_contra hh
    have hh' := mul_nonpos_of_nonneg_of_nonpos hscl (le_of_not_gt hh)
    linarith
  have hm := (lt_min_iff.mp hcap).2
  have hi := (lt_max_iff.mp hm).resolve_left (lt_irrefl (0 : ℝ))
  obtain ⟨hd,hq',hp'⟩ := (lt_min_iff.mp hi).imp_right lt_min_iff.mp
  have hlog := log_product_four hp hq ha hr
  have horder : Real.log r ≤ Real.log a :=
    Real.log_le_log (by exact_mod_cast hr.pos) (by exact_mod_cast hrA.le)
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- A common lower cap for a whole moving cutoff interval. Both tent
edges are kept; a cutoff crossing does not cost a triangle bound. -/
theorem pair_tent_ge_interval_cap {b r t lo hi : ℝ}
    (hr0 : 0 ≤ r) (hrb : r ≤ b) (hlo : lo ≤ t) (hhi : t ≤ hi) :
    min r (max 0 (min lo (b+r-hi))) ≤ primePairTent b r t := by
  rw [pair_tent_eq_cap hr0 hrb]
  exact min_le_min le_rfl (max_le_max le_rfl
    (min_le_min hlo (sub_le_sub_left hhi _)))

/-- The original five-prime atom is exactly a sum of three nonnegative
tents on the saturated three-large/two-small region. No prime completion,
count averaging or hypothetical-zero phase is used. -/
theorem re_five_atom_eq_three_tents (A : Finset ℕ) (N : ℕ) {p q a b r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hb : b.Prime) (hr : r.Prime)
    (hs : Squarefree (p*(q*(a*(b*r))))) {L y : ℝ}
    (hpb : Real.log p+Real.log (b*r : ℕ) ≤ L)
    (hqb : Real.log q+Real.log (b*r : ℕ) ≤ L)
    (hab : Real.log a+Real.log (b*r : ℕ) ≤ L)
    (hpqa : L ≤ Real.log p+Real.log q+Real.log a) :
    (residualCoefficient A L N (p*(q*(a*(b*r))))*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(a*(b*r))))).re =
      weight A N (p*(q*(a*(b*r))))*(Real.log (p*(q*(a*(b*r))) : ℕ)/L)*
        (primePairTent (Real.log b) (Real.log r) (L-Real.log p-Real.log q)+
          primePairTent (Real.log b) (Real.log r) (L-Real.log p-Real.log a)+
          primePairTent (Real.log b) (Real.log r) (L-Real.log q-Real.log a))*
        (-Real.cos (y*Real.log (p*(q*(a*(b*r))) : ℕ))) := by
  have hbr : b ≠ r := by
    intro he
    have hd := hb.coprime_iff_not_dvd.mp
      (Nat.coprime_of_squarefree_mul hs.of_mul_right.of_mul_right.of_mul_right)
    exact hd (he ▸ dvd_refl b)
  have hR := ZetaRieszJointQuintupleFloor.riesz_three_primes_small_composite
    hp hq ha hs (fun he => hb.ne_one (mul_eq_one.mp he).1)
    (Nat.not_prime_mul hb.ne_one hr.ne_one) hpb hqb hab hpqa
  rw [ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ hb hr hbr,
    ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ hb hr hbr,
    ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ hb hr hbr] at hR
  have hnp : ¬(p*(q*(a*(b*r)))).Prime := Nat.not_prime_mul hp.ne_one
    (fun he => hq.ne_one (mul_eq_one.mp he).1)
  rw [re_residual_atom,SquarefreeVaughanLogSource.coefficient,
    if_pos ⟨hs,hnp⟩,Complex.ofReal_re,hR]
  ring

/-- An explicit favorable credit uniform across a cutoff interval,
for the literal weighted, phased five-prime atom. Its three caps can
be integrated in the least-prime variable before any numerical cover. -/
theorem re_five_atom_ge_three_caps (A : Finset ℕ) (N : ℕ) {p q a b r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hb : b.Prime) (hr : r.Prime)
    (hrb : r ≤ b) (hs : Squarefree (p*(q*(a*(b*r)))))
    {L lo hi y : ℝ} (hL : 0 < L) (hlo : lo ≤ L) (hhi : L ≤ hi)
    (hpb : Real.log p+Real.log (b*r : ℕ) ≤ lo)
    (hqb : Real.log q+Real.log (b*r : ℕ) ≤ lo)
    (hab : Real.log a+Real.log (b*r : ℕ) ≤ lo)
    (hpqa : hi ≤ Real.log p+Real.log q+Real.log a)
    (hcos : Real.cos (y*Real.log (p*(q*(a*(b*r))) : ℕ)) ≤ 0) :
    weight A N (p*(q*(a*(b*r))))*(Real.log (p*(q*(a*(b*r))) : ℕ)/L)*
      (min (Real.log r) (max 0 (min (lo-Real.log p-Real.log q)
          (Real.log (p*(q*(a*(b*r))) : ℕ)-hi-Real.log a)))+
        min (Real.log r) (max 0 (min (lo-Real.log p-Real.log a)
          (Real.log (p*(q*(a*(b*r))) : ℕ)-hi-Real.log q)))+
        min (Real.log r) (max 0 (min (lo-Real.log q-Real.log a)
          (Real.log (p*(q*(a*(b*r))) : ℕ)-hi-Real.log p))))*
      (-Real.cos (y*Real.log (p*(q*(a*(b*r))) : ℕ))) ≤
      (residualCoefficient A L N (p*(q*(a*(b*r))))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(a*(b*r))))).re := by
  have hlog : Real.log (p*(q*(a*(b*r))) : ℕ) =
      Real.log p+Real.log q+Real.log a+Real.log b+Real.log r := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hs.of_mul_right.ne_zero),log_product_four hq ha hb hr]
    ring
  have horder : Real.log r ≤ Real.log b :=
    Real.log_le_log (by exact_mod_cast hr.pos) (by exact_mod_cast hrb)
  have hcap (v w : ℝ) := pair_tent_ge_interval_cap
    (Real.log_natCast_nonneg r) horder
    (show lo-v-w ≤ L-v-w by linarith) (show L-v-w ≤ hi-v-w by linarith)
  have h1 := hcap (Real.log p) (Real.log q)
  have h2 := hcap (Real.log p) (Real.log a)
  have h3 := hcap (Real.log q) (Real.log a)
  have he1 : Real.log b+Real.log r-(hi-Real.log p-Real.log q) =
      Real.log (p*(q*(a*(b*r))) : ℕ)-hi-Real.log a := by linarith
  have he2 : Real.log b+Real.log r-(hi-Real.log p-Real.log a) =
      Real.log (p*(q*(a*(b*r))) : ℕ)-hi-Real.log q := by linarith
  have he3 : Real.log b+Real.log r-(hi-Real.log q-Real.log a) =
      Real.log (p*(q*(a*(b*r))) : ℕ)-hi-Real.log p := by linarith
  rw [he1] at h1
  rw [he2] at h2
  rw [he3] at h3
  rw [re_five_atom_eq_three_tents A N hp hq ha hb hr hs
    (hpb.trans hlo) (hqb.trans hlo) (hab.trans hlo) (hhi.trans hpqa)]
  apply mul_le_mul_of_nonneg_right _ (neg_nonneg.mpr hcos)
  exact mul_le_mul_of_nonneg_left (by linarith only [h1,h2,h3])
    (mul_nonneg (weight_nonneg _ _ _)
      (div_nonneg (Real.log_natCast_nonneg _) hL.le))

private theorem cap_integrable {a b S : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbS : b < S) (m : ℝ) :
    IntervalIntegrable (fun x : ℝ => min x m/(x*(S-x))) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  apply ContinuousOn.div
  · exact (continuous_id.min continuous_const).continuousOn
  · fun_prop
  · intro x hx
    exact mul_ne_zero (ne_of_gt (ha.trans_le hx.1)) (ne_of_gt (by linarith [hx.2]))

private theorem integral_inverse_sub {a b S : ℝ} (hab : a ≤ b) (hbS : b < S) :
    (∫ x : ℝ in a..b, 1/(S-x)) = Real.log ((S-a)/(S-b)) := by
  have haS : a < S := hab.trans_lt hbS
  have hderiv (x : ℝ) (hx : x ∈ Set.uIcc a b) :
      HasDerivAt (fun x : ℝ => -Real.log (S-x)) (1/(S-x)) x := by
    rw [Set.uIcc_of_le hab] at hx
    have hne : S-x ≠ 0 := ne_of_gt (by linarith [hx.2])
    convert! (((hasDerivAt_id x).const_sub S).log hne).neg using 1
    simp only [id_eq]
    ring
  have hint : IntervalIntegrable (fun x : ℝ => 1/(S-x)) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ContinuousOn.div continuous_const.continuousOn (by fun_prop)
    intro x hx
    exact ne_of_gt (by linarith [hx.2])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    Real.log_div (sub_pos.mpr haS).ne' (sub_pos.mpr hbS).ne']
  ring

private theorem integral_inverse_product {a b S : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbS : b < S) (m : ℝ) :
    (∫ x : ℝ in a..b, m/(x*(S-x))) =
      (m/S)*Real.log (b*(S-a)/(a*(S-b))) := by
  have hb : 0 < b := ha.trans_le hab
  have hS : 0 < S := hb.trans hbS
  have haS : a < S := hab.trans_lt hbS
  have hderiv (x : ℝ) (hx : x ∈ Set.uIcc a b) :
      HasDerivAt (fun x : ℝ => (m/S)*(Real.log x-Real.log (S-x)))
        (m/(x*(S-x))) x := by
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    have hSx : S-x ≠ 0 := ne_of_gt (by linarith [hx.2])
    apply (((Real.hasDerivAt_log hx0).sub
      (((hasDerivAt_id x).const_sub S).log hSx)).const_mul (m/S)).congr_deriv
    simp only [id_eq]
    field_simp
    ring
  have hint : IntervalIntegrable (fun x : ℝ => m/(x*(S-x))) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ContinuousOn.div continuous_const.continuousOn (by fun_prop)
    intro x hx
    exact mul_ne_zero (ne_of_gt (ha.trans_le hx.1)) (ne_of_gt (by linarith [hx.2]))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    Real.log_div (mul_ne_zero hb.ne' (sub_pos.mpr haS).ne')
      (mul_ne_zero ha.ne' (sub_pos.mpr hbS).ne'),
    Real.log_mul hb.ne' (sub_pos.mpr haS).ne',
    Real.log_mul ha.ne' (sub_pos.mpr hbS).ne']
  ring

/-- Exact integral of the least-prime cap against the two-small-prime
harmonic density. It removes one integration dimension without dropping
the cancellation responsible for finiteness near the small-prime edge. -/
theorem cap_integral_eq {a b S m : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbS : b < S) :
    let c := max a (min m b)
    (∫ x : ℝ in a..b, min x m/(x*(S-x))) =
      Real.log ((S-a)/(S-c))+(m/S)*Real.log (b*(S-c)/(c*(S-b))) := by
  dsimp only
  have hb : 0 < b := ha.trans_le hab
  have haS : a < S := hab.trans_lt hbS
  by_cases hma : m ≤ a
  · rw [max_eq_left ((min_le_left m b).trans hma)]
    have he : (∫ x : ℝ in a..b, min x m/(x*(S-x))) =
        ∫ x : ℝ in a..b, m/(x*(S-x)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      dsimp only
      rw [min_eq_right (hma.trans hx.1)]
    rw [he,integral_inverse_product ha hab hbS,
      div_self (sub_pos.mpr haS).ne',Real.log_one,zero_add]
  by_cases hbm : b ≤ m
  · rw [min_eq_right hbm,max_eq_right hab]
    have he : (∫ x : ℝ in a..b, min x m/(x*(S-x))) =
        ∫ x : ℝ in a..b, 1/(S-x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      dsimp only
      rw [min_eq_left (hx.2.trans hbm)]
      field_simp [ne_of_gt (ha.trans_le hx.1)]
    rw [he,integral_inverse_sub hab hbS,
      div_self (mul_ne_zero hb.ne' (sub_pos.mpr hbS).ne'),Real.log_one,mul_zero,add_zero]
  have ham : a ≤ m := le_of_not_ge hma
  have hmb : m ≤ b := le_of_not_ge hbm
  have hm : 0 < m := ha.trans_le ham
  have hmS : m < S := hmb.trans_lt hbS
  rw [min_eq_left hmb,max_eq_right ham,
    ← intervalIntegral.integral_add_adjacent_intervals
      (cap_integrable ha ham hmS m) (cap_integrable hm hmb hbS m)]
  have he1 : (∫ x : ℝ in a..m, min x m/(x*(S-x))) =
      ∫ x : ℝ in a..m, 1/(S-x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le ham] at hx
    dsimp only
    rw [min_eq_left hx.2]
    field_simp [ne_of_gt (ha.trans_le hx.1)]
  have he2 : (∫ x : ℝ in m..b, min x m/(x*(S-x))) =
      ∫ x : ℝ in m..b, m/(x*(S-x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hmb] at hx
    dsimp only
    rw [min_eq_right hx.1]
  rw [he1,he2,integral_inverse_sub ham hmS,integral_inverse_product hm hmb hbS]

/-- The least-prime endpoint is integrable because the cap cancels its
harmonic singularity. The value at the single point zero is irrelevant. -/
theorem cap_integrable_zero {b S m : ℝ} (hb : 0 < b) (hbS : b < S)
    (hm : 0 < m) :
    IntervalIntegrable (fun x : ℝ => min x m/(x*(S-x))) MeasureTheory.volume 0 b := by
  let c := min m b
  have hc : 0 < c := lt_min hm hb
  have hcb : c ≤ b := min_le_right _ _
  have hcS : c < S := hcb.trans_lt hbS
  have hi : IntervalIntegrable (fun x : ℝ => 1/(S-x)) MeasureTheory.volume 0 c := by
    apply ContinuousOn.intervalIntegrable_of_Icc hc.le
    apply ContinuousOn.div continuous_const.continuousOn (by fun_prop)
    intro x hx
    exact ne_of_gt (by linarith [hx.2])
  have he : Set.EqOn (fun x : ℝ => min x m/(x*(S-x)))
      (fun x : ℝ => 1/(S-x)) (Set.uIoo 0 c) := by
    rw [Set.uIoo_of_lt hc]
    intro x hx
    dsimp only
    rw [min_eq_left (hx.2.le.trans (min_le_left _ _))]
    field_simp [hx.1.ne']
  exact ((intervalIntegrable_congr_uIoo he).mpr hi).trans
    (cap_integrable hc hcb hbS m)

/-- Exact zero-endpoint cap integral. This closes the endpoint used by
the four-prime population upper bound without an improper-limit assumption. -/
theorem cap_integral_zero_eq {b S m : ℝ} (hb : 0 < b) (hbS : b < S)
    (hm : 0 < m) :
    let c := min m b
    (∫ x : ℝ in 0..b, min x m/(x*(S-x))) =
      Real.log (S/(S-c))+(m/S)*Real.log (b*(S-c)/(c*(S-b))) := by
  dsimp only
  let c := min m b
  have hc : 0 < c := lt_min hm hb
  have hcb : c ≤ b := min_le_right _ _
  have hcS : c < S := hcb.trans_lt hbS
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (cap_integrable_zero hc hcS hm) (cap_integrable hc hcb hbS m)]
  have he : (∫ x : ℝ in 0..c, min x m/(x*(S-x))) =
      ∫ x : ℝ in 0..c, 1/(S-x) := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le hc.le] at hx
    rw [min_eq_left (hx.2.trans (min_le_left _ _))]
    field_simp [hx.1.ne']
  rw [he,integral_inverse_sub hc.le hcS,sub_zero,
    cap_integral_eq hc hcb hbS]
  change Real.log (S/(S-c)) +
    (Real.log ((S-c)/(S-max c c))+
      m/S*Real.log (b*(S-max c c)/(max c c*(S-b)))) = _
  rw [max_self,div_self (sub_pos.mpr hcS).ne',Real.log_one,zero_add]

/-- Every positive arithmetic lower cutoff is bounded by the same
zero-completed envelope. No small-prime mass is omitted. -/
theorem cap_integral_le_zero_envelope {a b S m : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hbS : b < S) (hm : 0 < m) :
    let c := min m b
    (∫ x : ℝ in a..b, min x m/(x*(S-x))) ≤
      Real.log (S/(S-c))+(m/S)*Real.log (b*(S-c)/(c*(S-b))) := by
  dsimp only
  rw [← cap_integral_zero_eq (ha.trans_le hab) hbS hm]
  apply intervalIntegral.integral_mono_interval ha.le hab le_rfl
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact div_nonneg (le_min hx.1.le hm.le)
      (mul_nonneg hx.1.le (by linarith [hx.2]))
  · exact cap_integrable_zero (ha.trans_le hab) hbS hm

/-- Integrability on every nonnegative subinterval, including a zero cap
or zero lower endpoint. This is used by closed numerical cells. -/
theorem cap_integrable_nonneg {a b S m : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbS : b < S) (hm : 0 ≤ m) :
    IntervalIntegrable (fun x : ℝ => min x m/(x*(S-x))) MeasureTheory.volume a b := by
  rcases hm.eq_or_lt with hm | hm
  · subst m
    apply (intervalIntegrable_congr_uIoo (g := fun _ : ℝ => 0) ?_).mpr
      intervalIntegrable_const
    rw [Set.uIoo_of_le hab]
    intro x hx
    simp [min_eq_right (ha.trans hx.1.le)]
  by_cases hb : b = 0
  · have ha0 : a = 0 := by linarith
    simp [ha0,hb]
  have hb0 : 0 < b := lt_of_le_of_ne (ha.trans hab) (Ne.symm hb)
  apply (cap_integrable_zero hb0 hbS hm).mono_set
  rw [Set.uIcc_of_le hab,Set.uIcc_of_le hb0.le]
  exact Set.Icc_subset_Icc ha le_rfl

/-- Increasing the cap or decreasing the total gives a larger nonnegative
density. The cancellation at zero is retained in the comparison. -/
theorem cap_density_mono {x S S₀ m M : ℝ} (hx : 0 ≤ x) (hxS : x < S₀)
    (hS : S₀ ≤ S) (hm : 0 ≤ m) (hmM : m ≤ M) :
    min x m/(x*(S-x)) ≤ min x M/(x*(S₀-x)) := by
  rcases hx.eq_or_lt with hx | hx
  · subst x
    simp
  apply div_le_div₀ (le_min hx.le (hm.trans hmM)) (min_le_min le_rfl hmM)
    (mul_pos hx (sub_pos.mpr hxS))
  exact mul_le_mul_of_nonneg_left (by linarith) hx.le

/-- A whole cap fibre is enclosed by a larger interval and one pair of
parameter endpoints. This pays the curved fibre edges before cubature. -/
theorem cap_integral_mono_parameters {a₀ a b b₀ S₀ S m M : ℝ}
    (ha₀ : 0 ≤ a₀) (haa : a₀ ≤ a) (hab : a ≤ b) (hbb : b ≤ b₀)
    (hbS : b₀ < S₀) (hS : S₀ ≤ S) (hm : 0 ≤ m) (hmM : m ≤ M) :
    (∫ x : ℝ in a..b, min x m/(x*(S-x))) ≤
      ∫ x : ℝ in a₀..b₀, min x M/(x*(S₀-x)) := by
  have ha := ha₀.trans haa
  have hbS₀ := hbb.trans_lt hbS
  apply (intervalIntegral.integral_mono_on hab
    (cap_integrable_nonneg ha hab (hbS₀.trans_le hS) hm)
    (cap_integrable_nonneg ha hab hbS₀ (hm.trans hmM)) ?_).trans
  · apply intervalIntegral.integral_mono_interval haa hab hbb
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 := ha₀.trans hx.1.le
      exact div_nonneg (le_min hx0 (hm.trans hmM))
        (mul_nonneg hx0 (by linarith [hx.2]))
    · exact cap_integrable_nonneg ha₀ (haa.trans (hab.trans hbb)) hbS (hm.trans hmM)
  · intro x hx
    exact cap_density_mono (ha.trans hx.1) (hx.2.trans_lt hbS₀) hS hm hmM

/-- The harmonic large-pair logarithm is monotone in the directions
used by a common five-prime supply cell. -/
theorem pair_log_mono {v₀ v d d₀ : ℝ} (hd : 0 < d) (hdd : d ≤ d₀)
    (hvd : 2*d₀ < v₀) (hvv : v₀ ≤ v) :
    0 ≤ Real.log ((v₀-d₀)/d₀) ∧
      Real.log ((v₀-d₀)/d₀) ≤ Real.log ((v-d)/d) := by
  have hd₀ : 0 < d₀ := hd.trans_le hdd
  have hv₀ : 0 < v₀ := by linarith
  have hratio : 1 ≤ (v₀-d₀)/d₀ := (le_div_iff₀ hd₀).mpr (by linarith)
  refine ⟨Real.log_nonneg hratio,Real.log_le_log (zero_lt_one.trans_le hratio) ?_⟩
  have hdiv : v₀/d₀ ≤ v/d :=
    div_le_div₀ (hv₀.le.trans hvv) hvv hd hdd
  linarith [show (v₀-d₀)/d₀ = v₀/d₀-1 by field_simp,
    show (v-d)/d = v/d-1 by field_simp]

/-- A complete five-prime fibre has this lower budget. Its moving
large-pair boundary remains inside the integrand, while one common cell
endpoint supplies the logarithm and the exact cap integral. -/
theorem five_fibre_lower {a b S S₁ m m₀ v v₀ z lo d₀ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbS : b < S) (hS : S ≤ S₁)
    (hm₀ : 0 ≤ m₀) (hmm : m₀ ≤ m) (hvv : v₀ ≤ v)
    (hd₁ : S-a ≤ d₀) (hd₂ : 1-lo-z ≤ d₀) (hd₃ : v-1/2 ≤ d₀)
    (hvd : 2*d₀ < v₀) :
    Real.log ((v₀-d₀)/d₀)*(∫ r : ℝ in a..b, min r m₀/(r*(S₁-r))) ≤
      ∫ r : ℝ in a..b, min r m/(r*(S-r))*
        Real.log ((v-max (S-r) (max (1-lo-z) (v-1/2)))/
          max (S-r) (max (1-lo-z) (v-1/2))) := by
  let d : ℝ → ℝ := fun r => max (S-r) (max (1-lo-z) (v-1/2))
  have hdc : Continuous d := by dsimp [d]; fun_prop
  have hdb (r : ℝ) (hr : r ∈ Set.Icc a b) : 0 < d r ∧ d r ≤ d₀ := by
    refine ⟨lt_of_lt_of_le (by linarith [hr.2]) (le_max_left _ _),?_⟩
    exact max_le (by linarith [hr.1]) (max_le hd₂ hd₃)
  have hratio : ContinuousOn (fun r => (v-d r)/d r) (Set.Icc a b) := by
    apply ContinuousOn.div (by fun_prop) hdc.continuousOn
    intro r hr
    exact (hdb r hr).1.ne'
  have hlog : ContinuousOn (fun r => Real.log ((v-d r)/d r)) (Set.Icc a b) := by
    apply hratio.log
    intro r hr
    exact (div_pos (by linarith [(hdb r hr).2]) (hdb r hr).1).ne'
  have hcap : ContinuousOn (fun r : ℝ => min r m/(r*(S-r))) (Set.Icc a b) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro r hr
    exact mul_ne_zero (ne_of_gt (ha.trans_le hr.1)) (ne_of_gt (by linarith [hr.2]))
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab
    ((cap_integrable ha hab (hbS.trans_le hS) m₀).const_mul _)
    ((hcap.mul hlog).intervalIntegrable_of_Icc hab)
  intro r hr
  have hlogb := pair_log_mono (hdb r hr).1 (hdb r hr).2 hvd hvv
  have hc := cap_density_mono (ha.le.trans hr.1) (hr.2.trans_lt hbS) hS hm₀ hmm
  have hpos : 0 ≤ min r m/(r*(S-r)) :=
    div_nonneg (le_min (ha.le.trans hr.1) (hm₀.trans hmm))
      (mul_nonneg (ha.le.trans hr.1) (by linarith [hr.2]))
  calc
    _ = (min r m₀/(r*(S₁-r)))*Real.log ((v₀-d₀)/d₀) := mul_comm _ _
    _ ≤ _ := mul_le_mul hc hlogb.2 hlogb.1 hpos

/-- Every positive ordered four-prime cap lies in the complete outer
rectangle used by the debit computation. No least-share lower bound is
needed for this support restriction. -/
theorem four_positive_in_root_box {p q a r lam lo P : ℝ}
    (hsum : p+q+a+r = 1) (hra : r ≤ a) (haq : a ≤ q)
    (hp : p ≤ P) (hlam : lo ≤ lam)
    (hcap : 0 < min r (max 0 (min (lam-p) (min (1-lam-q) (1+p-2*lam))))) :
    2*lo-1 < p ∧ (1-P)/3 ≤ q ∧ q < 1-lo := by
  have hm : 0 < min (lam-p) (min (1-lam-q) (1+p-2*lam)) := by
    have h := lt_of_lt_of_le hcap (min_le_right _ _)
    exact (lt_max_iff.mp h).resolve_left (lt_irrefl _)
  have hq : 0 < 1-lam-q := (lt_min_iff.mp (lt_min_iff.mp hm).2).1
  have hpl : 0 < 1+p-2*lam := (lt_min_iff.mp (lt_min_iff.mp hm).2).2
  exact ⟨by linarith,by linarith,by linarith⟩

/-- The second-smallest share stays away from zero on the positive cap.
This bounds even a coarse debit cell whose enclosing small-share interval
crosses the apparent harmonic singularity. -/
theorem four_cap_density_le {p q r lam lo P : ℝ} (hr : 0 < r)
    (hra : r ≤ 1-p-q-r) (hp : p ≤ P) (hP : P < lo) (hlam : lo ≤ lam) :
    min r (max 0 (min (lam-p) (min (1-lam-q) (1+p-2*lam)))) /
      (r*(1-p-q-r)) ≤ 2/(lo-P) := by
  let m := max 0 (min (lam-p) (min (1-lam-q) (1+p-2*lam)))
  have hm : 0 ≤ m := le_max_left _ _
  change min r m/(r*(1-p-q-r)) ≤ _
  rcases hm.eq_or_lt with hm | hm
  · rw [← hm,min_eq_right hr.le,zero_div]
    positivity
  have hmin : 0 < min (lam-p) (min (1-lam-q) (1+p-2*lam)) := by
    exact (lt_max_iff.mp hm).resolve_left (lt_irrefl _)
  have hq : 0 < 1-lam-q := (lt_min_iff.mp (lt_min_iff.mp hmin).2).1
  have ha : 0 < 1-p-q-r := hr.trans_le hra
  have hgap : lo-P < 2*(1-p-q-r) := by linarith
  calc
    _ ≤ r/(r*(1-p-q-r)) := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
    _ = 1/(1-p-q-r) := by field_simp
    _ ≤ 2/(lo-P) := (div_le_div_iff₀ ha (sub_pos.mpr hP)).mpr (by linarith)

/-- The least-log cancellation also gives this cap-independent upper
envelope; the singular harmonic factor at the least prime is cancelled
before integration. -/
theorem cap_integral_le_log {a b S : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbS : b < S) (m : ℝ) :
    (∫ x : ℝ in a..b, min x m/(x*(S-x))) ≤ Real.log ((S-a)/(S-b)) := by
  rw [← integral_inverse_sub hab hbS]
  have hi : IntervalIntegrable (fun x : ℝ => 1/(S-x)) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ContinuousOn.div continuous_const.continuousOn (by fun_prop)
    intro x hx
    exact ne_of_gt (by linarith [hx.2])
  apply intervalIntegral.integral_mono_on hab (cap_integrable ha hab hbS m) hi
  intro x hx
  have hx0 : 0 < x := ha.trans_le hx.1
  have hxS : 0 < S-x := by linarith [hx.2]
  calc
    _ ≤ x/(x*(S-x)) := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
    _ = _ := by field_simp

/-- Rational upper and lower log approximants for the two positive
logarithms in `cap_integral_eq`. Their inputs can be rational; no numerical
oracle or floating-point assumption enters the bounds. -/
theorem log_rational_bounds {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    let z := (x-1)/(x+1)
    2*(∑ j ∈ Finset.range n, z^(2*j+1)/(2*(j : ℝ)+1)) ≤ Real.log x ∧
      Real.log x ≤ 2*((∑ j ∈ Finset.range n, z^(2*j+1)/(2*(j : ℝ)+1))+
        z^(2*n+1)/(1-z^2)) := by
  dsimp only
  have hx1 : 0 < x+1 := by linarith
  have hz0 : 0 ≤ (x-1)/(x+1) := div_nonneg (by linarith) hx1.le
  have hz1 : (x-1)/(x+1) < 1 := (div_lt_one hx1).mpr (by linarith)
  have he : (1+(x-1)/(x+1))/(1-(x-1)/(x+1)) = x := by
    field_simp
    ring
  have hl := Real.sum_range_le_log_div hz0 hz1 n
  have hu := Real.log_div_le_sum_range_add hz0 hz1 n
  rw [he] at hl hu
  constructor <;> linarith

/-- The decreasing odd denominators improve the rational upper error
by `2*n+1`. This is the tighter bound used by the capacity calculation. -/
theorem log_rational_bounds_sharp {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    let z := (x-1)/(x+1)
    2*(∑ j ∈ Finset.range n, z^(2*j+1)/(2*(j : ℝ)+1)) ≤ Real.log x ∧
      Real.log x ≤ 2*((∑ j ∈ Finset.range n, z^(2*j+1)/(2*(j : ℝ)+1))+
        z^(2*n+1)/((2*(n : ℝ)+1)*(1-z^2))) := by
  let z := (x-1)/(x+1)
  change 2*(∑ j ∈ Finset.range n, z^(2*j+1)/(2*(j : ℝ)+1)) ≤ Real.log x ∧ _
  refine ⟨(log_rational_bounds hx n).1,?_⟩
  have hx1 : 0 < x+1 := by linarith
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hx1.le
  have hz1 : z < 1 := (div_lt_one hx1).mpr (by linarith)
  have hratio : (1+z)/(1-z) = x := by dsimp [z]; field_simp; ring
  have hsum : HasSum (fun k : ℕ => 2*z^(2*k+1)/(2*(k : ℝ)+1)) (Real.log x) := by
    have h := Real.hasSum_log_sub_log_of_abs_lt_one (by rwa [abs_of_nonneg hz0])
    rw [← Real.log_div (by linarith : 1+z ≠ 0) (by linarith : 1-z ≠ 0),hratio] at h
    convert! h using 1
    ext k
    ring
  have htail := (hasSum_nat_add_iff' n).mpr hsum
  have hz2 : z^2 < 1 := by nlinarith
  have hgeo := (hasSum_geometric_of_lt_one (sq_nonneg z) hz2).mul_left
    (2*z^(2*n+1)/(2*(n : ℝ)+1))
  have hpoint (k : ℕ) : 2*z^(2*(k+n)+1)/(2*((k+n : ℕ) : ℝ)+1) ≤
      (2*z^(2*n+1)/(2*(n : ℝ)+1))*(z^2)^k := by
    have he : z^(2*(k+n)+1) = z^(2*n+1)*(z^2)^k := by
      rw [← pow_mul,← pow_add]
      congr 1
      omega
    rw [he]
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ 2*(z^(2*n+1)*(z^2)^k) by positivity)
      (show 0 < 2*(n : ℝ)+1 by positivity)
      (show 2*(n : ℝ)+1 ≤ 2*((k+n : ℕ) : ℝ)+1 by push_cast; linarith)
    exact hh.trans_eq (by ring)
  have ht := Summable.tsum_le_tsum hpoint htail.summable hgeo.summable
  rw [htail.tsum_eq,hgeo.tsum_eq] at ht
  have he : (∑ j ∈ Finset.range n, 2*z^(2*j+1)/(2*(j : ℝ)+1)) =
      2*(∑ j ∈ Finset.range n, z^(2*j+1)/(2*(j : ℝ)+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at ht
  change Real.log x ≤ 2*((∑ j ∈ Finset.range n, z^(2*j+1)/(2*(j : ℝ)+1))+
    z^(2*n+1)/((2*(n : ℝ)+1)*(1-z^2)))
  rw [div_mul_eq_div_div]
  convert sub_le_iff_le_add.mp ht using 1 <;> first | rfl | ring

/-- The remaining pair of large-prime harmonic denominators can also
be integrated exactly. The ordered five-prime three-tent symmetry can
therefore use a two-dimensional angular cover. -/
theorem symmetric_pair_integral {a S : ℝ} (ha : 0 < a) (haS : 2*a ≤ S) :
    (∫ x : ℝ in a..S-a, 1/(x*(S-x))) =
      (2/S)*Real.log ((S-a)/a) := by
  have hb : 0 < S-a := by linarith
  rw [integral_inverse_product ha (by linarith) (by linarith),
    show S-(S-a) = a by ring,
    Real.log_div (mul_ne_zero hb.ne' hb.ne') (mul_ne_zero ha.ne' ha.ne'),
    Real.log_mul hb.ne' hb.ne',Real.log_mul ha.ne' ha.ne',
    Real.log_div hb.ne' ha.ne']
  ring

/-- Across a fixed-width phase arc, the ORIGINAL radial factorial
kernel changes by at most this relative factor. The moment is not frozen
or replaced by a nearby radial order. -/
theorem radial_kernel_le_exp {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : (39/20 : ℝ)*N ≤ a) (ha' : a ≤ (203/100 : ℝ)*N)
    (hb : (39/20 : ℝ)*N ≤ b) (_hb' : b ≤ (203/100 : ℝ)*N) :
    Real.exp (-b/2)*b^N/N.factorial ≤
      Real.exp (|b-a|/78)*(Real.exp (-a/2)*a^N/N.factorial) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 < a := by nlinarith
  have hb0 : 0 < b := by nlinarith
  have hn0 : (0 : ℝ) ≤ N := hn.le
  have hlow : (100/203 : ℝ) ≤ (N : ℝ)/a := (le_div_iff₀ ha0).mpr (by nlinarith)
  have hhigh : (N : ℝ)/a ≤ (20/39 : ℝ) := (div_le_iff₀ ha0).mpr (by nlinarith)
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hb0 ha0)) hn0
  rw [Real.log_div hb0.ne' ha0.ne'] at hlog
  have halg : (N : ℝ)*(b/a-1)-(b-a)/2 = (b-a)*((N : ℝ)/a-1/2) := by
    field_simp
  have hexp : -b/2+(N : ℝ)*Real.log b ≤
      |b-a|/78+(-a/2+(N : ℝ)*Real.log a) := by
    have he : (b-a)*((N : ℝ)/a-1/2) ≤ |b-a|/78 := by
      rcases le_total a b with hab | hba
      · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
        nlinarith
      · rw [abs_of_nonpos (sub_nonpos.mpr hba)]
        nlinarith
    linarith
  have hpow (x : ℝ) (hx : 0 < x) : x^N = Real.exp ((N : ℝ)*Real.log x) := by
    rw [Real.exp_nat_mul,Real.exp_log hx]
  rw [hpow a ha0,hpow b hb0,← Real.exp_add,← Real.exp_add]
  calc
    _ ≤ Real.exp (|b-a|/78+(-a/2+(N : ℝ)*Real.log a))/N.factorial :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-- Even the full short phase arc costs less than two tenths of one
percent of a favorable supply. This is a relative comparison, not an
absolute error multiplied by the growing source envelope. -/
theorem radial_kernel_le_phase_arc {N : ℕ} (hN : 0 < N) {a b : ℝ}
    (ha : (39/20 : ℝ)*N ≤ a) (ha' : a ≤ (203/100 : ℝ)*N)
    (hb : (39/20 : ℝ)*N ≤ b) (hb' : b ≤ (203/100 : ℝ)*N)
    (hd : |b-a| ≤ 1/8) :
    Real.exp (-b/2)*b^N/N.factorial ≤
      (501/500 : ℝ)*(Real.exp (-a/2)*a^N/N.factorial) := by
  have hr : Real.exp (|b-a|/78) ≤ (501/500 : ℝ) := by
    apply (Real.exp_le_exp.mpr (show |b-a|/78 ≤ (1/624 : ℝ) by linarith)).trans
    exact (Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/624)
      (by norm_num : (1/624 : ℝ) < 1)).trans (by norm_num)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 < a := by nlinarith
  exact (radial_kernel_le_exp hN ha ha' hb hb').trans
    (mul_le_mul_of_nonneg_right hr (by positivity))

/-- The moving cutoff changes by only `1/(20*N)` across a short phase
arc in the core. Overlapping cutoff bins can therefore keep the entire
arc instead of discarding its boundary contributions. -/
theorem cutoff_ratio_variation {N : ℕ} (hN : 0 < N) {L a b : ℝ}
    (hL : 0 ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (ha : (39/20 : ℝ)*N ≤ a) (hb : (39/20 : ℝ)*N ≤ b)
    (hd : |b-a| ≤ 1/8) : |L/a-L/b| ≤ 1/(20*(N : ℝ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 < a := by nlinarith
  have hb0 : 0 < b := by nlinarith
  have he : L/a-L/b = L*(b-a)/(a*b) := by field_simp
  rw [he,abs_div,abs_mul,abs_of_nonneg hL,abs_of_pos (mul_pos ha0 hb0)]
  apply (div_le_div_iff₀ (mul_pos ha0 hb0) (by positivity : 0 < 20*(N : ℝ))).mpr
  have hprod := mul_le_mul ha hb (by positivity : (0 : ℝ) ≤ (39/20)*N) ha0.le
  have hld := mul_le_mul hLu hd (abs_nonneg (b-a))
    (show (0 : ℝ) ≤ (7/5)*N by positivity)
  have hm := mul_le_mul_of_nonneg_right hld (show (0 : ℝ) ≤ 20*N by positivity)
  nlinarith

/-- The literal Riesz length remains in the same padded cutoff bin
throughout a phase arc, including arcs crossing an unpadded bin boundary.
No source-scale boundary term is deleted. -/
theorem moving_cutoff_stays_in_padded_bin {N : ℕ} (hN : 5000 ≤ N)
    {u a b lo hi : ℝ} (hu : 1/2 ≤ u)
    (ha : (39/20 : ℝ)*N ≤ a) (hb : (39/20 : ℝ)*N ≤ b)
    (hd : |b-a| ≤ 1/8)
    (hlo : lo ≤ SquarefreeVaughanLogSource.length u N/a)
    (hhi : SquarefreeVaughanLogSource.length u N/a ≤ hi) :
    lo-1/100000 ≤ SquarefreeVaughanLogSource.length u N/b ∧
      SquarefreeVaughanLogSource.length u N/b ≤ hi+1/100000 := by
  have hLu : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    apply (ZetaRieszHeadOrders.length_le_two_log_two hu (by omega : 2 ≤ N)).trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
    linarith [Real.log_two_lt_d9]
  have he := cutoff_ratio_variation (by omega : 0 < N)
    (SquarefreeVaughanLogSource.length_pos u N).le hLu ha hb hd
  have hNR : (5000 : ℝ) ≤ N := by exact_mod_cast hN
  have hf : (1 : ℝ)/(20*(N : ℝ)) ≤ 1/100000 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hh := abs_le.mp (he.trans hf)
  constructor <;> linarith

end
end RiemannGaussian.ZetaRieszOrderedCapacity
