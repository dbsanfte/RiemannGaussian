/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCrossingOrbitCancellation

/-!
# Pair the two sides of an unpaid Riesz hinge

Two adjacent based divisor blocks keep the SAME original physical label
and observation. Their eight incidences cancel across cofactor parities.
The other Riesz hinge is retained explicitly; it cannot be dropped just
because the second-hinge tents meet at their midpoint.

When both first hinges are saturated, the paired crossing costs its
distance from the exact midpoint. On the middle half of the overlap this
halves the separate block allowance. The prime-row floor uses the joined
SIGNED prime moment, retaining every factorial, allocation and phase.
No numerical bound on the aggregate remaining floor cost is inferred.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical Pointwise ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszHingePairCancellation
open ZetaRieszSignedConvolution ZetaRieszPrimeEndpoint ZetaRieszParityPacket
open ZetaRieszShortDivisorCancellation ZetaRieszShortDivisorOrbits
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime

private theorem tent_rising {a b x : ℝ} (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hxa : x ≤ a) (hxb : x ≤ b) :
    primePairTent a b x=x := by
  rw [primePairTent,max_eq_right hx,max_eq_left (by linarith : x-a ≤ 0),
    max_eq_left (by linarith : x-b ≤ 0),max_eq_left (by linarith : x-a-b ≤ 0)]
  ring

private theorem tent_falling {a b x : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbx : b ≤ x) : primePairTent a b x=max 0 (a+b-x) := by
  unfold primePairTent
  rw [max_eq_right (by linarith : 0 ≤ x),
    max_eq_right (by linarith : 0 ≤ x-a),
    max_eq_right (by linarith : 0 ≤ x-b)]
  by_cases hx : x ≤ a+b
  · rw [max_eq_left (by linarith : x-a-b ≤ 0),
      max_eq_right (by linarith : 0 ≤ a+b-x)]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ x-a-b),
      max_eq_left (by linarith : a+b-x ≤ 0)]
    ring

/-- The adjacent blocks keep the counter-term from the OTHER hinge.
Only the two second-hinge ramps cancel at their midpoint. -/
theorem crossing_difference_eq {a b c P D : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hcP : c ≤ P)
    (hcD : c ≤ D) (hD : D ≤ a+b) :
    tripleDifference a b c (P+D)-tripleDifference a b c D =
      -(a+b+c-2*D+max 0 (a+b+c-P-D)) := by
  have hzero := primePairTent_eq_zero_of_outside ha (by linarith : 0 ≤ b)
    (Or.inr (by linarith : a+b ≤ P+D))
  have hfirst := tent_falling ha hab (show b ≤ P+D-c by linarith)
  have hsecond := tent_falling ha hab (show b ≤ D by linarith)
  have hrise := tent_rising (by linarith : 0 ≤ b)
    (show 0 ≤ D-c by linarith) (show D-c ≤ a by linarith)
    (show D-c ≤ b by linarith)
  rw [tripleDifference,tripleDifference,hzero,hfirst,hsecond,hrise,
    max_eq_right (by linarith : 0 ≤ a+b-D)]
  rw [show a+b-(P+D-c)=a+b+c-P-D by ring]
  ring

/-- Once both FIRST hinges are saturated, the original eight-incidence
response is exactly the signed distance between the two crossing ramps. -/
theorem crossing_difference_eq_of_first_full {a b c P D : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hcP : c ≤ P)
    (hcD : c ≤ D) (hD : D ≤ a+b) (hfull : a+b+c ≤ P+D) :
    tripleDifference a b c (P+D)-tripleDifference a b c D =
      -(a+b+c-2*D) := by
  rw [crossing_difference_eq ha hab hbc hcP hcD hD,
    max_eq_left (by linarith : a+b+c-P-D ≤ 0),add_zero]

/-- The OTHER hinge moves the exact cancellation centre. This formula
includes it, rather than assigning a separate positive boundary allowance. -/
theorem two_hinge_cancellation_center (S P : ℝ) :
    S-2*(S/2+max 0 (S-2*P)/6)+
      max 0 (S-P-(S/2+max 0 (S-2*P)/6))=0 := by
  by_cases h : S-2*P ≤ 0
  · rw [max_eq_left h,max_eq_left (by linarith : S-P-(S/2+0/6) ≤ 0)]
    ring
  · have hh : 0 ≤ S-2*P := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right hh,max_eq_right (by linarith : 0 ≤ S-P-(S/2+(S-2*P)/6))]
    ring

/-- Near the TRUE cancellation centre, the FULL two-hinge coefficient
costs at most half the overlap width, even when the first hinge crosses.
This is a bound on the original signed coefficient, not on either hinge. -/
theorem two_hinge_cancellation_le_half {S P D W : ℝ}
    (hnear : |D-(S/2+max 0 (S-2*P)/6)| ≤ W/6) :
    |S-2*D+max 0 (S-P-D)| ≤ W/2 := by
  let M := S/2+max 0 (S-2*P)/6
  have hz : S-2*M+max 0 (S-P-M)=0 := two_hinge_cancellation_center S P
  have hc : |max 0 (S-P-D)-max 0 (S-P-M)| ≤ |D-M| := by
    have h := abs_max_sub_max_le_abs (S-P-D) (S-P-M) 0
    rw [show S-P-D-(S-P-M)= -(D-M) by ring,abs_neg] at h
    simpa only [max_comm] using h
  have he : S-2*D+max 0 (S-P-D)=
      -2*(D-M)+(max 0 (S-P-D)-max 0 (S-P-M)) := by linarith
  calc
    _ = |-2*(D-M)+(max 0 (S-P-D)-max 0 (S-P-M))| := congrArg abs he
    _ ≤ |-2*(D-M)|+|max 0 (S-P-D)-max 0 (S-P-M)| := abs_add_le _ _
    _ ≤ 3*|D-M| := by rw [abs_mul]; norm_num; linarith
    _ ≤ W/2 := by change |D-M| ≤ W/6 at hnear; linarith

/-- The adaptive centre stays strictly inside BOTH original crossing
ramps. No first-hinge saturation or discarded boundary is assumed. -/
theorem two_hinge_band_strict_overlap {a b c P D : ℝ}
    (hw : c < a+b) (hcP : c ≤ P)
    (hnear : |D-((a+b+c)/2+max 0 (a+b+c-2*P)/6)| ≤ (a+b-c)/6) :
    c < D ∧ D < a+b := by
  have h0 : 0 ≤ max 0 (a+b+c-2*P) := le_max_left _ _
  have h1 : max 0 (a+b+c-2*P) ≤ a+b-c := max_le (by linarith) (by linarith)
  have hh := abs_le.mp hnear
  constructor <;> linarith [hh.1,hh.2]

/-- A complete based block remains at its ORIGINAL label. This exact
identity has no affinity, saturation or factorial-order hypothesis. -/
theorem weighted_orbit_eq_riesz_difference {a p R e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (he : e ∣ a/R) (L : ℝ) (w : ℂ) :
    (∑ db ∈ orbitDivisors a R e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      w*(μ (a/e) : ℂ)*
        ((VaughanLogAverage.riesz (log (p*(a/e) : ℕ)-L) R-
          VaughanLogAverage.riesz (log (a/e : ℕ)-L) R : ℝ) : ℂ) := by
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos (base_dvd hRa he)
    (Nat.pos_of_ne_zero ha.ne_zero)
  have hb := ha.squarefree_of_dvd (Nat.div_dvd_of_dvd (base_dvd hRa he))
  have hh := congrArg (fun x : ℝ => w*(x : ℂ))
    (signed_block_riesz_difference hb hp (block_dvd_quotient hRa he) L)
  push_cast at hh
  rw [orbitDivisors,Finset.sum_image (by
    intro d _ f _ h
    exact Nat.mul_left_cancel he0 (congrArg Prod.fst h))]
  simpa only [Nat.div_div_eq_div_mul,Finset.mul_sum,mul_assoc,Nat.cast_mul,
    Complex.ofReal_sub] using hh

/-- The literal paired crossing, including the other hinge. Every
cofactor parity and the original common complex observation survive. -/
theorem weighted_paired_crossing_eq {a p r s q e : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q) (hqple : log q ≤ log p)
    (hlo : log q ≤ log (a/e : ℕ)-L)
    (hhi : log (a/e : ℕ)-L ≤ log r+log s) (w : ℂ) :
    (∑ db ∈ orbitDivisors a (r*s*q) e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      -w*(μ (a/e) : ℂ)*
        ((log r+log s+log q-2*(log (a/e : ℕ)-L)+
          max 0 (log r+log s+log q-log p-(log (a/e : ℕ)-L)) : ℝ) : ℂ) := by
  have hb := ha.squarefree_of_dvd (Nat.div_dvd_of_dvd (base_dvd hRa he))
  have hl : log (p*(a/e) : ℕ)=log p+log (a/e : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hb.ne_zero)]
  rw [weighted_orbit_eq_riesz_difference ha hp hRa he L w]
  have hv (x : ℝ) : VaughanLogAverage.riesz x (r*s*q)=
      tripleDifference (log r) (log s) (log q) x := by
    rw [mul_assoc]
    exact riesz_three_primes_eq_difference x hr hs hq hrs hrq hsq
  rw [hv,hv,hl]
  have hh := crossing_difference_eq (log_natCast_nonneg r) hrsle hsqle hqple hlo hhi
  rw [show log p+log (a/e : ℕ)-L=log p+(log (a/e : ℕ)-L) by ring,hh]
  push_cast
  ring

/-- The unchanged original eight incidences, with both first hinges
saturated, have only the exact midpoint displacement left. -/
theorem weighted_paired_crossing_eq_of_first_full {a p r s q e : ℕ}
    (ha : Squarefree a) (hp : p.Prime) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q) (hqple : log q ≤ log p)
    (hlo : log q ≤ log (a/e : ℕ)-L)
    (hhi : log (a/e : ℕ)-L ≤ log r+log s)
    (hfull : log r+log s+log q ≤ log p+(log (a/e : ℕ)-L)) (w : ℂ) :
    (∑ db ∈ orbitDivisors a (r*s*q) e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      -w*(μ (a/e) : ℂ)*((log r+log s+log q-2*(log (a/e : ℕ)-L) : ℝ) : ℂ) := by
  rw [weighted_paired_crossing_eq ha hp hr hs hq hrs hrq hsq hRa he
    hrsle hsqle hqple hlo hhi w,
    max_eq_left (by linarith : log r+log s+log q-log p-(log (a/e : ℕ)-L) ≤ 0),
    add_zero]

/-- Half-cost cancellation for the literal eight incidences at their
true, owner-dependent centre. BOTH hinges, the original weight and phase
are included, so this also covers the close-owner boundary. -/
theorem norm_paired_two_hinges_le_half {a p r s q e : ℕ}
    (ha : Squarefree a) (hp : p.Prime) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q) (hqple : log q ≤ log p)
    (hlo : log q ≤ log (a/e : ℕ)-L)
    (hhi : log (a/e : ℕ)-L ≤ log r+log s)
    (hnear : |log (a/e : ℕ)-L-((log r+log s+log q)/2+
      max 0 (log r+log s+log q-2*log p)/6)| ≤ (log r+log s-log q)/6) (w : ℂ) :
    ‖∑ db ∈ orbitDivisors a (r*s*q) e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)‖ ≤ ‖w‖*((log r+log s-log q)/2) := by
  have hm : ‖(μ (a/e) : ℂ)‖ ≤ 1 := by
    have h : |(μ (a/e) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a/e)
    simpa only [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs] using h
  rw [weighted_paired_crossing_eq ha hp hr hs hq hrs hrq hsq hRa he
    hrsle hsqle hqple hlo hhi w,
    norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖w‖*|log r+log s+log q-2*(log (a/e : ℕ)-L)+
        max 0 (log r+log s+log q-log p-(log (a/e : ℕ)-L))| :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg w) hm) (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (two_hinge_cancellation_le_half hnear) (norm_nonneg _)

/-- A clipped prime boundary is EXACTLY the joined constant/log moment
over its ORIGINAL prime mask. No prime-density or positive debit replaces it. -/
theorem clipped_prime_sum_eq_signed_moments (P : Finset ℕ) (w : ℕ → ℂ) (H : ℝ) :
    (∑ p ∈ P, w p*((max 0 (H-log (p : ℝ)) : ℝ) : ℂ)) =
      (H : ℂ)*(∑ p ∈ P.filter (fun p : ℕ => log (p : ℝ) < H), w p)-
        ∑ p ∈ P.filter (fun p : ℕ => log (p : ℝ) < H), ((log (p : ℝ) : ℝ) : ℂ)*w p := by
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : log p < H
  · rw [if_pos h,max_eq_right (by linarith : 0 ≤ H-log p)]
    push_cast
    ring
  · rw [if_neg h,max_eq_left (by linarith [le_of_not_gt h] : H-log p ≤ 0),
      Complex.ofReal_zero,mul_zero]

/-- Join the full original paired response, INCLUDING its other hinge,
before observing a prime moment. The counter-term keeps its exact signed
constant and logarithmic moments on the literal clipped prime subset. -/
theorem prime_paired_two_hinges_eq_signed_moments (P : Finset ℕ) {a r s q e : ℕ}
    (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hlo : log q ≤ log (a/e : ℕ)-L)
    (hhi : log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ p ∈ P, p.Prime ∧ log q ≤ log p) (w : ℕ → ℂ) :
    let S := log r+log s+log q
    let D := log (a/e : ℕ)-L
    let B := P.filter (fun p : ℕ => log (p : ℝ) < S-D)
    (∑ p ∈ P, ∑ db ∈ orbitDivisors a (r*s*q) e,
      w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      -(μ (a/e) : ℂ)*
        (((S-2*D : ℝ) : ℂ)*(∑ p ∈ P, w p)+
          ((S-D : ℝ) : ℂ)*(∑ p ∈ B, w p)-∑ p ∈ B, ((log (p : ℝ) : ℝ) : ℂ)*w p) := by
  dsimp only
  calc
    _ = ∑ p ∈ P, -(μ (a/e) : ℂ)*
        (((log r+log s+log q-2*(log (a/e : ℕ)-L) : ℝ) : ℂ)*w p+
          w p*((max 0 (log r+log s+log q-(log (a/e : ℕ)-L)-log p) : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [weighted_paired_crossing_eq ha (hP p hp).1 hr hs hq hrs hrq hsq hRa he
        hrsle hsqle (hP p hp).2 hlo hhi (w p),
        show log r+log s+log q-log p-(log (a/e : ℕ)-L)=
          log r+log s+log q-(log (a/e : ℕ)-L)-log p by ring]
      push_cast
      ring
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum,
        clipped_prime_sum_eq_signed_moments]
      ring

/-- A DIRECT floor on the same full literal two-hinge prime row. The
constant moment and BOTH clipped moments are joined BEFORE the single
absolute value. First-hinge crossings do not acquire a separate debit. -/
theorem re_prime_paired_two_hinges_floor (P : Finset ℕ) {a r s q e : ℕ}
    (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hlo : log q ≤ log (a/e : ℕ)-L)
    (hhi : log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ p ∈ P, p.Prime ∧ log q ≤ log p) (w : ℕ → ℂ) :
    let S := log r+log s+log q
    let D := log (a/e : ℕ)-L
    let B := P.filter (fun p : ℕ => log (p : ℝ) < S-D)
    let V : ℂ := ((S-2*D : ℝ) : ℂ)*(∑ p ∈ P, w p)+
      ((S-D : ℝ) : ℂ)*(∑ p ∈ B, w p)-(∑ p ∈ B, ((log (p : ℝ) : ℝ) : ℂ)*w p);
    - |V.re| ≤
      (∑ p ∈ P, ∑ db ∈ orbitDivisors a (r*s*q) e,
        w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)).re := by
  have hm : |(μ (a/e) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a/e)
  dsimp only
  rw [prime_paired_two_hinges_eq_signed_moments P ha hr hs hq hrs hrq hsq hRa he
    hrsle hsqle hlo hhi hP w,
    show (μ (a/e) : ℂ)=((μ (a/e) : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,
    Complex.neg_im,neg_zero,zero_mul,sub_zero]
  have hh (x : ℝ) : |-(μ (a/e) : ℝ)*x| ≤ |x| := by
    rw [abs_mul,abs_neg]
    exact mul_le_of_le_one_left (abs_nonneg x) hm
  exact (abs_le.mp (hh _)).1

/-- The source-scaled literal row floor retains the full original
factorial kernel, allocation and phase INSIDE the three signed moments.
No first-hinge saturation, prime-density replacement or zero premise. -/
theorem re_source_scaled_literal_two_hinge_floor (P : Finset ℕ) (A : ℕ → Finset ℕ)
    {a r s q e : ℕ} (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hlo : log q ≤ log (a/e : ℕ)-L)
    (hhi : log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ p ∈ P, p.Prime ∧ log q ≤ log p) (u y : ℝ) (N : ℕ) :
    let S := log r+log s+log q
    let D := log (a/e : ℕ)-L
    let B := P.filter (fun p : ℕ => log (p : ℝ) < S-D)
    let V : ℂ := ((S-2*D : ℝ) : ℂ)*(∑ p ∈ P, phaseWeight (A (p*a)) L N y a p)+
      ((S-D : ℝ) : ℂ)*(∑ p ∈ B, phaseWeight (A (p*a)) L N y a p)-
      (∑ p ∈ B, ((log (p : ℝ) : ℝ) : ℂ)*phaseWeight (A (p*a)) L N y a p);
    - |((u : ℂ)^(N+1)*V).re| ≤
      ((u : ℂ)^(N+1)*
        (∑ p ∈ P, ∑ db ∈ orbitDivisors a (r*s*q) e,
          phaseWeight (A (p*a)) L N y a p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ))).re := by
  simpa only [Finset.mul_sum,mul_add,mul_sub,mul_assoc,mul_left_comm] using
    re_prime_paired_two_hinges_floor P ha hr hs hq hrs hrq hsq hRa he
      hrsle hsqle hlo hhi hP
      (fun p => (u : ℂ)^(N+1)*phaseWeight (A (p*a)) L N y a p)

/-- Summing the two overlapping second-hinge ramps first pays at most
HALF their separate allowance in the middle half of the overlap. -/
theorem midpoint_displacement_le_half {a b c D : ℝ}
    (hmid : |D-(a+b+c)/2| ≤ (a+b-c)/4) :
    |a+b+c-2*D| ≤ (a+b-c)/2 := by
  have he : a+b+c-2*D= -2*(D-(a+b+c)/2) := by ring
  rw [he,abs_mul]
  norm_num
  linarith

/-- The OLD separate ramp allowances add to the full overlap width.
The midpoint bound above therefore gives an actual factor-two saving. -/
theorem two_ramps_sum_eq_overlap_width {a b c D : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hcD : c ≤ D) (hD : D ≤ a+b) :
    primePairTent a b D+primePairTent a b (D-c)=a+b-c := by
  rw [tent_falling ha hab (show b ≤ D by linarith),
    max_eq_right (by linarith : 0 ≤ a+b-D),
    tent_rising (by linarith : 0 ≤ b) (show 0 ≤ D-c by linarith)
      (show D-c ≤ a by linarith) (show D-c ≤ b by linarith)]
  ring

/-- An independent bound for the ORIGINAL eight incidences. The gain
comes from their opposite signed ramps BEFORE taking a norm. -/
theorem norm_paired_crossing_le_half {a p r s q e : ℕ}
    (ha : Squarefree a) (hp : p.Prime) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q) (hqple : log q ≤ log p)
    (hlo : log q ≤ log (a/e : ℕ)-L)
    (hhi : log (a/e : ℕ)-L ≤ log r+log s)
    (hfull : log r+log s+log q ≤ log p+(log (a/e : ℕ)-L))
    (hmid : |log (a/e : ℕ)-L-(log r+log s+log q)/2| ≤
      (log r+log s-log q)/4) (w : ℂ) :
    ‖∑ db ∈ orbitDivisors a (r*s*q) e,
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)‖ ≤
      ‖w‖*((log r+log s-log q)/2) := by
  have hm : ‖(μ (a/e) : ℂ)‖ ≤ 1 := by
    have h : |(μ (a/e) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a/e)
    simpa only [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs] using h
  rw [weighted_paired_crossing_eq_of_first_full ha hp hr hs hq hrs hrq hsq hRa he
    hrsle hsqle hqple hlo hhi hfull w,
    norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖w‖*|log r+log s+log q-2*(log (a/e : ℕ)-L)| :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg w) hm) (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (midpoint_displacement_le_half hmid) (norm_nonneg _)

/-- Join ALL retained marked primes and periods before observing the
paired crossing. The observation may contain every literal mask unchanged. -/
theorem prime_paired_crossing_sum_eq (P : Finset ℕ) {a r s q e : ℕ}
    (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hlo : log q ≤ log (a/e : ℕ)-L)
    (hhi : log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ p ∈ P, p.Prime ∧ log q ≤ log p ∧
      log r+log s+log q ≤ log p+(log (a/e : ℕ)-L)) (w : ℕ → ℂ) :
    (∑ p ∈ P, ∑ db ∈ orbitDivisors a (r*s*q) e,
      w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      -(∑ p ∈ P, w p)*(μ (a/e) : ℂ)*
        ((log r+log s+log q-2*(log (a/e : ℕ)-L) : ℝ) : ℂ) := by
  calc
    _ = ∑ p ∈ P, -w p*(μ (a/e) : ℂ)*
        ((log r+log s+log q-2*(log (a/e : ℕ)-L) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact weighted_paired_crossing_eq_of_first_full ha (hP p hp).1 hr hs hq
        hrs hrq hsq hRa he hrsle hsqle (hP p hp).2.1 hlo hhi (hP p hp).2.2 (w p)
    _ = _ := by rw [← Finset.sum_mul,← Finset.sum_mul,Finset.sum_neg_distrib]

/-- A DIRECT signed floor for the joined crossing. Its price is half
the overlap width times the actual signed prime moment, never a sum of
absolute prime observations or separate prime-count allowances. -/
theorem re_prime_paired_crossing_floor (P : Finset ℕ) {a r s q e : ℕ}
    (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hlo : log q ≤ log (a/e : ℕ)-L)
    (hhi : log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ p ∈ P, p.Prime ∧ log q ≤ log p ∧
      log r+log s+log q ≤ log p+(log (a/e : ℕ)-L))
    (hmid : |log (a/e : ℕ)-L-(log r+log s+log q)/2| ≤
      (log r+log s-log q)/4) (w : ℕ → ℂ) :
    -((log r+log s-log q)/2)*|(∑ p ∈ P, w p).re| ≤
      (∑ p ∈ P, ∑ db ∈ orbitDivisors a (r*s*q) e,
        w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)).re := by
  have hm : |(μ (a/e) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a/e)
  have hab : |-(μ (a/e) : ℝ)*(log r+log s+log q-2*(log (a/e : ℕ)-L))*
      (∑ p ∈ P, w p).re| ≤ ((log r+log s-log q)/2)*|(∑ p ∈ P, w p).re| := by
    rw [abs_mul,abs_mul,abs_neg]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_left (abs_nonneg _) hm).trans (midpoint_displacement_le_half hmid))
      (abs_nonneg _)
  have hlo' := (abs_le.mp hab).1
  rw [prime_paired_crossing_sum_eq P ha hr hs hq hrs hrq hsq hRa he
    hrsle hsqle hlo hhi hP w,
    show (μ (a/e) : ℂ)=((μ (a/e) : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im,mul_zero,sub_zero]
  convert hlo' using 1 <;> first | rfl | ring

/-- The literal current factorial/allocation prime-row floor. Every
physical, owner, count, radial and phase condition may stay in `P`.
The weight is evaluated at the original `p*a`, NOT at `p*(a/e)`. -/
theorem re_literal_paired_crossing_floor (P : Finset ℕ) (A : ℕ → Finset ℕ)
    {a r s q e : ℕ} (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hlo : log q ≤ log (a/e : ℕ)-L)
    (hhi : log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ p ∈ P, p.Prime ∧ log q ≤ log p ∧
      log r+log s+log q ≤ log p+(log (a/e : ℕ)-L))
    (hmid : |log (a/e : ℕ)-L-(log r+log s+log q)/2| ≤
      (log r+log s-log q)/4) (N : ℕ) (y : ℝ) :
    -((log r+log s-log q)/2)*|(∑ p ∈ P, phaseWeight (A (p*a)) L N y a p).re| ≤
      (∑ p ∈ P, ∑ db ∈ orbitDivisors a (r*s*q) e,
        phaseWeight (A (p*a)) L N y a p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)).re :=
  re_prime_paired_crossing_floor P ha hr hs hq hrs hrq hsq hRa he
    hrsle hsqle hlo hhi hP hmid (fun p => phaseWeight (A (p*a)) L N y a p)

/-- The source-scaled literal signed floor. Scaling stays INSIDE the
joined prime moment; no selected resonance is paid by an absolute envelope. -/
theorem re_source_scaled_literal_paired_floor (P : Finset ℕ) (A : ℕ → Finset ℕ)
    {a r s q e : ℕ} (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q)
    (hRa : r*s*q ∣ a) (he : e ∣ a/(r*s*q)) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hlo : log q ≤ log (a/e : ℕ)-L)
    (hhi : log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ p ∈ P, p.Prime ∧ log q ≤ log p ∧
      log r+log s+log q ≤ log p+(log (a/e : ℕ)-L))
    (hmid : |log (a/e : ℕ)-L-(log r+log s+log q)/2| ≤
      (log r+log s-log q)/4) (u y : ℝ) (N : ℕ) :
    -((log r+log s-log q)/2)*
      |((u : ℂ)^(N+1)*(∑ p ∈ P, phaseWeight (A (p*a)) L N y a p)).re| ≤
      ((u : ℂ)^(N+1)*
        (∑ p ∈ P, ∑ db ∈ orbitDivisors a (r*s*q) e,
          phaseWeight (A (p*a)) L N y a p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ))).re := by
  simpa only [Finset.mul_sum,mul_assoc] using
    re_prime_paired_crossing_floor P ha hr hs hq hrs hrq hsq hRa he
      hrsle hsqle hlo hhi hP hmid
      (fun p => (u : ℂ)^(N+1)*phaseWeight (A (p*a)) L N y a p)

/-- Sum the entire selected cofactor parity profile BEFORE observing
the joined prime moment. There is no absolute value or count allowance
inside the signed arithmetic scalar. The prime set is common to these
bases; this theorem does not remove cofactor-dependent prime holes. -/
theorem paired_family_sum_eq (E P : Finset ℕ) {a r s q : ℕ}
    (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q) (hRa : r*s*q ∣ a) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hE : ∀ e ∈ E, e ∣ a/(r*s*q) ∧ log q ≤ log (a/e : ℕ)-L ∧
      log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ e ∈ E, ∀ p ∈ P, p.Prime ∧ log q ≤ log p ∧
      log r+log s+log q ≤ log p+(log (a/e : ℕ)-L)) (w : ℕ → ℂ) :
    (∑ e ∈ E, ∑ p ∈ P, ∑ db ∈ orbitDivisors a (r*s*q) e,
      w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      -(∑ p ∈ P, w p)*
        ((∑ e ∈ E, (μ (a/e) : ℝ)*
          (log r+log s+log q-2*(log (a/e : ℕ)-L)) : ℝ) : ℂ) := by
  calc
    _ = ∑ e ∈ E, -(∑ p ∈ P, w p)*(μ (a/e) : ℂ)*
        ((log r+log s+log q-2*(log (a/e : ℕ)-L) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro e he
      exact prime_paired_crossing_sum_eq P ha hr hs hq hrs hrq hsq hRa
        (hE e he).1 hrsle hsqle (hE e he).2.1 (hE e he).2.2 (hP e he) w
    _ = _ := by push_cast; simp only [Finset.mul_sum,mul_assoc]

/-- The complete selected cofactor profile has one signed constant
moment and one signed log moment. Their cancellation remains EXACT. -/
theorem paired_profile_eq_joint_moments (E : Finset ℕ) (a r s q : ℕ) (L : ℝ)
    (he : ∀ e ∈ E, 0 < e ∧ e ∣ a) (ha : 0 < a) :
    (∑ e ∈ E, (μ (a/e) : ℝ)*(log r+log s+log q-2*(log (a/e : ℕ)-L))) =
      (log r+log s+log q-2*(log a-L))*(∑ e ∈ E, (μ (a/e) : ℝ))+
        2*(∑ e ∈ E, (μ (a/e) : ℝ)*log e) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he'
  have he0 := (he e he').1
  have hd := (he e he').2
  have hb0 : 0 < a/e := Nat.div_pos (Nat.le_of_dvd ha hd) he0
  have hl : log a=log e+log (a/e : ℕ) := by
    conv_lhs => rw [← Nat.mul_div_cancel' hd]
    rw [Nat.cast_mul,log_mul (by exact_mod_cast he0.ne') (by exact_mod_cast hb0.ne')]
  rw [hl]
  ring

/-- A DIRECT floor for ALL selected bases/counts and prime periods
together. Its cost is the JOINT signed profile times the JOINT signed
prime moment; neither is replaced by its termwise absolute sum. -/
theorem re_paired_family_floor (E P : Finset ℕ) {a r s q : ℕ}
    (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q) (hRa : r*s*q ∣ a) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hE : ∀ e ∈ E, e ∣ a/(r*s*q) ∧ log q ≤ log (a/e : ℕ)-L ∧
      log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ e ∈ E, ∀ p ∈ P, p.Prime ∧ log q ≤ log p ∧
      log r+log s+log q ≤ log p+(log (a/e : ℕ)-L)) (w : ℕ → ℂ) :
    -|(∑ e ∈ E, (μ (a/e) : ℝ)*(log r+log s+log q-2*(log (a/e : ℕ)-L)))| *
      |(∑ p ∈ P, w p).re| ≤
      (∑ e ∈ E, ∑ p ∈ P, ∑ db ∈ orbitDivisors a (r*s*q) e,
        w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)).re := by
  rw [paired_family_sum_eq E P ha hr hs hq hrs hrq hsq hRa hrsle hsqle hE hP w]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,
    mul_zero,sub_zero]
  have hh := (abs_le.mp (le_refl |(∑ p ∈ P, w p).re*
    (∑ e ∈ E, (μ (a/e) : ℝ)*(log r+log s+log q-2*(log (a/e : ℕ)-L)))|)).2
  rw [abs_mul] at hh
  nlinarith

/-- The source-normalized LITERAL floor joins every selected divisor
base and every retained prime period before bounding the real part.
Its remaining cost is fully signed on both sides of the factorization. -/
theorem re_source_scaled_literal_family_floor (E P : Finset ℕ) (A : ℕ → Finset ℕ)
    {a r s q : ℕ} (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q) (hRa : r*s*q ∣ a) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hE : ∀ e ∈ E, e ∣ a/(r*s*q) ∧ log q ≤ log (a/e : ℕ)-L ∧
      log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ e ∈ E, ∀ p ∈ P, p.Prime ∧ log q ≤ log p ∧
      log r+log s+log q ≤ log p+(log (a/e : ℕ)-L)) (u y : ℝ) (N : ℕ) :
    -|(∑ e ∈ E, (μ (a/e) : ℝ)*(log r+log s+log q-2*(log (a/e : ℕ)-L)))| *
      |((u : ℂ)^(N+1)*(∑ p ∈ P, phaseWeight (A (p*a)) L N y a p)).re| ≤
      ((u : ℂ)^(N+1)*
        (∑ e ∈ E, ∑ p ∈ P, ∑ db ∈ orbitDivisors a (r*s*q) e,
          phaseWeight (A (p*a)) L N y a p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ))).re := by
  simpa only [Finset.mul_sum,mul_assoc] using
    re_paired_family_floor E P ha hr hs hq hrs hrq hsq hRa hrsle hsqle hE hP
      (fun p => (u : ℂ)^(N+1)*phaseWeight (A (p*a)) L N y a p)

/-- Keep COFACTOR-DEPENDENT prime masks exactly. All constant/log
moments and boundary holes remain inside one signed complex aggregate;
the common-prime-set factorization is not assumed. -/
theorem correlated_paired_sum_eq (E : Finset ℕ) (P : ℕ → Finset ℕ) {a r s q : ℕ}
    (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q) (hRa : r*s*q ∣ a) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hE : ∀ e ∈ E, e ∣ a/(r*s*q) ∧ log q ≤ log (a/e : ℕ)-L ∧
      log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ e ∈ E, ∀ p ∈ P e, p.Prime ∧ log q ≤ log p ∧
      log r+log s+log q ≤ log p+(log (a/e : ℕ)-L)) (w : ℕ → ℂ) :
    (∑ e ∈ E, ∑ p ∈ P e, ∑ db ∈ orbitDivisors a (r*s*q) e,
      w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      -∑ e ∈ E, (∑ p ∈ P e, w p)*
        (((μ (a/e) : ℝ)*(log r+log s+log q-2*(log (a/e : ℕ)-L)) : ℝ) : ℂ) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [prime_paired_crossing_sum_eq (P e) ha hr hs hq hrs hrq hsq hRa
    (hE e he).1 hrsle hsqle (hE e he).2.1 (hE e he).2.2 (hP e he) w]
  push_cast
  ring

/-- The factor-two saving applies to ALL matched rows together even
with correlated prime endpoints and holes. The price retains each actual
SIGNED prime-period aggregate. No source-scale bound for its sum is hidden. -/
theorem re_correlated_paired_floor (E : Finset ℕ) (P : ℕ → Finset ℕ) {a r s q : ℕ}
    (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q) (hRa : r*s*q ∣ a) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hE : ∀ e ∈ E, e ∣ a/(r*s*q) ∧ log q ≤ log (a/e : ℕ)-L ∧
      log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ e ∈ E, ∀ p ∈ P e, p.Prime ∧ log q ≤ log p ∧
      log r+log s+log q ≤ log p+(log (a/e : ℕ)-L))
    (hmid : ∀ e ∈ E, |log (a/e : ℕ)-L-(log r+log s+log q)/2| ≤
      (log r+log s-log q)/4) (w : ℕ → ℂ) :
    -((log r+log s-log q)/2)*(∑ e ∈ E, |(∑ p ∈ P e, w p).re|) ≤
      (∑ e ∈ E, ∑ p ∈ P e, ∑ db ∈ orbitDivisors a (r*s*q) e,
        w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)).re := by
  rw [Finset.mul_sum,Complex.re_sum]
  apply Finset.sum_le_sum
  intro e he
  exact re_prime_paired_crossing_floor (P e) ha hr hs hq hrs hrq hsq hRa
    (hE e he).1 hrsle hsqle (hE e he).2.1 (hE e he).2.2 (hP e he) (hmid e he) w

/-- The actual source-scaled correlated literal family has the same
HALF-WIDTH floor, with every prime mask and original phase retained.
This is a sector inequality; the total arithmetic price is still open. -/
theorem re_source_scaled_correlated_literal_floor (E : Finset ℕ) (P : ℕ → Finset ℕ)
    (A : ℕ → Finset ℕ) {a r s q : ℕ} (ha : Squarefree a)
    (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hrs : r ≠ s) (hrq : r ≠ q) (hsq : s ≠ q) (hRa : r*s*q ∣ a) {L : ℝ}
    (hrsle : log r ≤ log s) (hsqle : log s ≤ log q)
    (hE : ∀ e ∈ E, e ∣ a/(r*s*q) ∧ log q ≤ log (a/e : ℕ)-L ∧
      log (a/e : ℕ)-L ≤ log r+log s)
    (hP : ∀ e ∈ E, ∀ p ∈ P e, p.Prime ∧ log q ≤ log p ∧
      log r+log s+log q ≤ log p+(log (a/e : ℕ)-L))
    (hmid : ∀ e ∈ E, |log (a/e : ℕ)-L-(log r+log s+log q)/2| ≤
      (log r+log s-log q)/4) (u y : ℝ) (N : ℕ) :
    -((log r+log s-log q)/2)*
      (∑ e ∈ E, |((u : ℂ)^(N+1)*(∑ p ∈ P e, phaseWeight (A (p*a)) L N y a p)).re|) ≤
      ((u : ℂ)^(N+1)*
        (∑ e ∈ E, ∑ p ∈ P e, ∑ db ∈ orbitDivisors a (r*s*q) e,
          phaseWeight (A (p*a)) L N y a p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ))).re := by
  simpa only [Finset.mul_sum,mul_assoc] using
    re_correlated_paired_floor E P ha hr hs hq hrs hrq hsq hRa hrsle hsqle hE hP hmid
      (fun p => (u : ℂ)^(N+1)*phaseWeight (A (p*a)) L N y a p)

/-- The narrow middle-half profile cannot contain BOTH ends of another
prime insertion. Such a pairing must retain an exterior boundary; no
iterated affinity or masked completion is licensed by the first saving. -/
theorem middle_half_no_prime_shift {a b c D v : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hc : 0 < c) (hcv : c ≤ v)
    (hfirst : |D-(a+b+c)/2| ≤ (a+b-c)/4)
    (hsecond : |D-v-(a+b+c)/2| ≤ (a+b-c)/4) : False := by
  have h1 := abs_le.mp hfirst
  have h2 := abs_le.mp hsecond
  linarith [h1.1,h1.2,h2.1,h2.2]

/-- The eight-member block is EXACTLY the two adjacent old four-member
orbits. No new labels or prime incidences are added by the pairing. -/
theorem paired_orbit_eq_union (a R e : ℕ) {q : ℕ} (hq : q.Prime) :
    orbitDivisors a (R*q) e = orbitDivisors a R e ∪ orbitDivisors a R (e*q) := by
  ext db
  constructor
  · intro hdb
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hdb
    rw [Nat.divisors_mul,hq.divisors,Finset.mul_def] at hd
    obtain ⟨⟨δ,θ⟩,hδθ,hprod⟩ := Finset.mem_image.mp hd
    obtain ⟨hδ,hθ⟩ := Finset.mem_product.mp hδθ
    change δ ∈ R.divisors at hδ
    change θ ∈ ({1,q} : Finset ℕ) at hθ
    change δ*θ=d at hprod
    rcases Finset.mem_insert.mp hθ with hθ | hθ
    · subst θ
      simp only [mul_one] at hprod
      subst d
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨δ,hδ,rfl⟩)
    · have hθ : θ=q := Finset.mem_singleton.mp hθ
      subst θ
      subst d
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨δ,hδ,?_⟩
      have hh : e*q*δ=e*(δ*q) := by ring
      simp only [hh]
  · intro hdb
    rcases Finset.mem_union.mp hdb with hdb | hdb
    · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hdb
      refine Finset.mem_image.mpr ⟨d,?_,rfl⟩
      exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans (dvd_mul_right R q),
        mul_ne_zero (Nat.ne_zero_of_mem_divisors hd) hq.ne_zero⟩
    · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hdb
      refine Finset.mem_image.mpr ⟨d*q,?_,?_⟩
      · exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hd) (dvd_refl q),
          mul_ne_zero (Nat.ne_zero_of_mem_divisors hd) hq.ne_zero⟩
      · have hh : e*(d*q)=e*q*d := by ring
        simp only [hh]

private theorem adjacent_bases {a R q e : ℕ} (hRa : R*q ∣ a)
    (he : e ∣ a/(R*q)) : e ∣ a/R ∧ e*q ∣ a/R := by
  have hR : R ∣ a := (dvd_mul_right R q).trans hRa
  have hq : q ∣ a/R := (Nat.dvd_div_iff_mul_dvd hR).mpr (by
    simpa only [mul_comm] using hRa)
  have he' : e ∣ (a/R)/q := by simpa only [Nat.div_div_eq_div_mul] using he
  exact ⟨base_dvd hq he',by
    simpa only [mul_comm] using (Nat.dvd_div_iff_mul_dvd hq).mp he'⟩

/-- Squarefreeness makes the two adjacent four-member orbits disjoint.
Thus no original incidence is charged twice by the joint bound. -/
theorem paired_orbits_disjoint {a R q e : ℕ} (ha : Squarefree a)
    (hq : q.Prime) (hRa : R*q ∣ a) (he : e ∣ a/(R*q)) :
    Disjoint (orbitDivisors a R e) (orbitDivisors a R (e*q)) := by
  have hR : R ∣ a := (dvd_mul_right R q).trans hRa
  have hcop : R.Coprime (a/R) :=
    Nat.coprime_of_squarefree_mul ((Nat.mul_div_cancel' hR).symm ▸ ha)
  have hb := adjacent_bases hRa he
  have hzero := (ha.squarefree_of_dvd (Nat.div_dvd_of_dvd hR)).ne_zero
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos hb.1 (Nat.pos_of_ne_zero hzero)
  exact orbitDivisors_disjoint hcop (Nat.mem_divisors.mpr ⟨hb.1,hzero⟩)
    (Nat.mem_divisors.mpr ⟨hb.2,hzero⟩) (by
      intro hh
      have hq1 : q=1 := Nat.mul_left_cancel he0 (by simpa only [mul_one] using hh.symm)
      exact hq.ne_one hq1)

/-- A genuinely crossing canonical orbit was NOT removed by either
affine zero payment. This is a saving on retained incidences. -/
theorem genuine_hinge_orbit_disjoint {u : ℝ} {N K n e : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hlo : 0 < log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N)
    (hhi : log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N <
      log (leastPairBlock (n/largestPrime n))) :
    Disjoint (orbitDivisors (n/largestPrime n) (leastPairBlock (n/largestPrime n)) e)
      (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n) := by
  have hd := core_data hn hs
  have hb := canonical_block_data hn hs
  have hT : log (largestPrime n*(n/largestPrime n) : ℕ)=
      log (largestPrime n)+log (n/largestPrime n : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hd.1.ne_zero)
      (by exact_mod_cast hd.2.1.ne_zero)]
  have hl := base_log hd.2.1 hd.1 (base_dvd hb.1 (Nat.dvd_of_mem_divisors he))
  have hB : log ((n/largestPrime n)/e : ℕ)=log (n/largestPrime n : ℕ)-log e := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hd.1.ne_zero)
      (by exact_mod_cast (hd.2.1.squarefree_of_dvd
        (Nat.div_dvd_of_dvd (base_dvd hb.1 (Nat.dvd_of_mem_divisors he)))).ne_zero),hT] at hl
    linarith
  have hbad : ¬(log (largestPrime n*(n/largestPrime n) : ℕ)-
      SquarefreeVaughanLogSource.length u N-log e ≤ log (largestPrime n) ∨
    log (largestPrime n)+log e+log (leastPairBlock (n/largestPrime n)) ≤
      log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N) := by
    rw [hT]
    rw [hB] at hlo hhi
    rintro (h | h) <;> linarith
  apply Finset.disjoint_left.mpr
  intro db hdb hpaid
  have hsame {f : ℕ}
      (hf : f ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
      (hmatch : db ∈ orbitDivisors (n/largestPrime n) (leastPairBlock (n/largestPrime n)) f) :
      f=e := by
    by_contra hne
    exact Finset.disjoint_left.mp (orbitDivisors_disjoint hb.2.2 hf he hne) hmatch hdb
  rcases Finset.mem_union.mp hpaid with hpaid | hpaid
  · unfold cancelledOrbitDivisors at hpaid
    dsimp only at hpaid
    rw [if_pos ⟨hb.1,by omega⟩] at hpaid
    obtain ⟨f,hf,hmatch⟩ := Finset.mem_biUnion.mp hpaid
    have hf' := (Finset.mem_filter.mp hf).1
    have hgeom := (Finset.mem_filter.mp hf).2
    have hh := hsame hf' hmatch
    rw [hh] at hgeom
    exact hbad hgeom.2.2.1
  · unfold ZetaRieszCrossingOrbitCancellation.affineDivisors at hpaid
    dsimp only at hpaid
    rw [if_pos ⟨hb.1,by omega⟩] at hpaid
    obtain ⟨f,hf,hmatch⟩ := Finset.mem_biUnion.mp hpaid
    have hf' := (Finset.mem_filter.mp hf).1
    have hgeom := (Finset.mem_filter.mp hf).2
    have hh := hsame hf' hmatch
    rw [hh] at hgeom
    exact hbad hgeom.2.1

/-- The middle-half condition puts BOTH old blocks strictly across the
actual cofactor hinge. Neither side is an old affine endpoint. -/
theorem midpoint_half_strict_crossings {a b c D : ℝ} (hc : 0 ≤ c)
    (hw : c < a+b) (hmid : |D-(a+b+c)/2| ≤ (a+b-c)/4) :
    (0 < D ∧ D < a+b) ∧ (0 < D-c ∧ D-c < a+b) := by
  have hh := abs_le.mp hmid
  constructor <;> constructor <;> linarith [hh.1,hh.2]

/-- Every original paired incidence really survives the CURRENT
zero deletion. This connects the half-cost bound to the retained central
sum, rather than counting a previously cancelled block a second time. -/
theorem paired_crossing_subset_retained_of_overlap {u : ℝ} {N K n r s q e : ℕ}
    (hn : n ∈ coreBand u N K) (hsf : Squarefree n)
    (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hcanonical : leastPairBlock (n/largestPrime n)=r*s)
    (hRa : r*s*q ∣ n/largestPrime n) (he : e ∣ (n/largestPrime n)/(r*s*q))
    (hlo : log q < log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N)
    (hhi : log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N < log r+log s) :
    orbitDivisors (n/largestPrime n) (r*s*q) e ⊆
      (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n) := by
  have hd := core_data hn hsf
  have hb := adjacent_bases hRa he
  have hR : r*s ∣ n/largestPrime n := (dvd_mul_right (r*s) q).trans hRa
  have hzero : (n/largestPrime n)/(r*s) ≠ 0 :=
    (hd.2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd hR)).ne_zero
  have he' : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors := by
    rw [hcanonical]
    exact Nat.mem_divisors.mpr ⟨hb.1,hzero⟩
  have heq' : e*q ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors := by
    rw [hcanonical]
    exact Nat.mem_divisors.mpr ⟨hb.2,hzero⟩
  have hlogR : log (leastPairBlock (n/largestPrime n))=log r+log s := by
    rw [hcanonical,Nat.cast_mul,log_mul (by exact_mod_cast hr.ne_zero)
      (by exact_mod_cast hs.ne_zero)]
  have hB := hd.2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd (base_dvd hR hb.1))
  have hqB : q ∣ (n/largestPrime n)/e :=
    (dvd_mul_left q (r*s)).trans (block_dvd_quotient hRa he)
  have hBq := hB.squarefree_of_dvd (Nat.div_dvd_of_dvd hqB)
  have hlogB : log ((n/largestPrime n)/(e*q) : ℕ)=
      log ((n/largestPrime n)/e : ℕ)-log q := by
    rw [← Nat.div_div_eq_div_mul]
    have hh : log ((n/largestPrime n)/e : ℕ)=
        log q+log ((n/largestPrime n)/e/q : ℕ) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hqB]
      rw [Nat.cast_mul,log_mul (by exact_mod_cast hq.ne_zero)
        (by exact_mod_cast hBq.ne_zero)]
    linarith
  have hc : (0 < log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N ∧
      log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N < log r+log s) ∧
      (0 < log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N-log q ∧
       log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N-log q < log r+log s) :=
    ⟨⟨by linarith [log_natCast_nonneg q],hhi⟩,⟨by linarith,by linarith [log_natCast_nonneg q]⟩⟩
  have hecancel := genuine_hinge_orbit_disjoint hn hsf he' hc.1.1 (hlogR ▸ hc.1.2)
  have heqcancel := genuine_hinge_orbit_disjoint hn hsf heq'
    (by rw [hlogB]; linarith [hc.2.1]) (by rw [hlogB,hlogR]; linarith [hc.2.2])
  rw [hcanonical] at hecancel heqcancel
  intro db hdb
  apply Finset.mem_sdiff.mpr
  refine ⟨orbitDivisors_subset (Nat.pos_of_ne_zero hd.2.1.ne_zero) hRa he hdb,?_⟩
  rw [paired_orbit_eq_union _ _ _ hq] at hdb
  rcases Finset.mem_union.mp hdb with hdb | hdb
  · exact fun hh => Finset.disjoint_left.mp hecancel hdb hh
  · exact fun hh => Finset.disjoint_left.mp heqcancel hdb hh

/-- The middle-half saving is on CURRENT unpaid original incidences. -/
theorem paired_crossing_subset_retained {u : ℝ} {N K n r s q e : ℕ}
    (hn : n ∈ coreBand u N K) (hsf : Squarefree n)
    (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hcanonical : leastPairBlock (n/largestPrime n)=r*s)
    (hRa : r*s*q ∣ n/largestPrime n) (he : e ∣ (n/largestPrime n)/(r*s*q))
    (hw : log q < log r+log s)
    (hmid : |log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N-
        (log r+log s+log q)/2| ≤ (log r+log s-log q)/4) :
    orbitDivisors (n/largestPrime n) (r*s*q) e ⊆
      (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n) := by
  have hh := midpoint_half_strict_crossings (log_natCast_nonneg q) hw hmid
  exact paired_crossing_subset_retained_of_overlap hn hsf hr hs hq hcanonical hRa he
    (by linarith [hh.2.1]) hh.1.2

/-- The adaptive TWO-hinge cancellation band also belongs to the
CURRENT unpaid population, including the unsaturated close-owner case. -/
theorem two_hinge_band_subset_retained {u : ℝ} {N K n r s q e : ℕ}
    (hn : n ∈ coreBand u N K) (hsf : Squarefree n)
    (hr : r.Prime) (hs : s.Prime) (hq : q.Prime)
    (hcanonical : leastPairBlock (n/largestPrime n)=r*s)
    (hRa : r*s*q ∣ n/largestPrime n) (he : e ∣ (n/largestPrime n)/(r*s*q))
    (hw : log q < log r+log s) (hqP : log q ≤ log (largestPrime n))
    (hnear : |log ((n/largestPrime n)/e : ℕ)-SquarefreeVaughanLogSource.length u N-
      ((log r+log s+log q)/2+
        max 0 (log r+log s+log q-2*log (largestPrime n))/6)| ≤
      (log r+log s-log q)/6) :
    orbitDivisors (n/largestPrime n) (r*s*q) e ⊆
      (n/largestPrime n).divisorsAntidiagonal \
        (cancelledOrbitDivisors u N n ∪ ZetaRieszCrossingOrbitCancellation.affineDivisors u N n) := by
  have hh := two_hinge_band_strict_overlap hw hqP hnear
  exact paired_crossing_subset_retained_of_overlap hn hsf hr hs hq hcanonical hRa he hh.1 hh.2

/-- Failure of the whole-window owner gap holds for EVERY member of a
based orbit, including both sides of a genuine hinge. -/
theorem failed_owner_orbit_outer_le {u : ℝ} {N K n e d b : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hgap : log (largestPrime n*(n/largestPrime n) : ℕ)-log e+log (largestPrime n) ≤
      (203/100 : ℝ)*N)
    (hdb : (d,b) ∈ orbitDivisors (n/largestPrime n) (leastPairBlock (n/largestPrime n)) e) :
    log (largestPrime n*b : ℕ)+log (largestPrime n) ≤ (203/100 : ℝ)*N := by
  have hd := core_data hn hs
  have hb := canonical_block_data hn hs
  obtain ⟨δ,hδ,hpair⟩ := Finset.mem_image.mp hdb
  have heδ : e*δ ∣ n/largestPrime n :=
    (Nat.dvd_div_iff_mul_dvd (base_dvd hb.1 (Nat.dvd_of_mem_divisors he))).mp
      ((Nat.dvd_of_mem_divisors hδ).trans (block_dvd_quotient hb.1 (Nat.dvd_of_mem_divisors he)))
  have hl := base_log hd.2.1 hd.1 heδ
  have hsecond := congrArg Prod.snd hpair
  change (n/largestPrime n)/(e*δ)=b at hsecond
  rw [hsecond] at hl
  have hlog : log (e*δ : ℕ)=log e+log δ := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast (Nat.pos_of_mem_divisors he).ne')
      (by exact_mod_cast (Nat.pos_of_mem_divisors hδ).ne')]
  rw [hlog] at hl
  linarith [log_natCast_nonneg δ]

/-- The remaining paired crossing cannot reuse an old owner-gap row. -/
theorem failed_owner_orbit_not_ownerGapRows {u : ℝ} {N K n e d b : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (he : e ∈ ((n/largestPrime n)/leastPairBlock (n/largestPrime n)).divisors)
    (hgap : log (largestPrime n*(n/largestPrime n) : ℕ)-log e+log (largestPrime n) ≤
      (203/100 : ℝ)*N)
    (hdb : (d,b) ∈ orbitDivisors (n/largestPrime n) (leastPairBlock (n/largestPrime n)) e) :
    (largestPrime n,b) ∉ ZetaRieszOwnerGapRows.ownerGapRows u N := by
  intro hpaid
  have hh := (Finset.mem_filter.mp hpaid).2.2.2.2.2.2.2.1
  linarith [failed_owner_orbit_outer_le hn hs he hgap hdb]

/-- The original owner ceiling keeps these surviving hinge labels
outside the already paid whole-large-owner population. -/
theorem owner_ceiling_not_largeOwner {u : ℝ} {N K n : ℕ}
    (hP : log (largestPrime n) < (243/200 : ℝ)*N) :
    n ∉ ZetaRieszUnifiedSignedRows.largeOwnerLabels u N K := by
  intro hlarge
  have hcut := (Finset.mem_filter.mp hlarge).2.2.2.2.1
  linarith

/-- A canonical polynomial-cutoff paid row has the opposite based-owner
gap. It cannot intersect ANY failed-gap original orbit, even if that orbit
crosses a genuine hinge and so is not affine. -/
theorem polynomial_paid_incidence_not_failed_orbit {u : ℝ} {N K : ℕ} (hN : 32 ≤ N)
    {pb : ℕ×ℕ} (hr : pb ∈ ZetaRieszPolynomialCutoffRows.cutoffRows u N) {e δ f : ℕ}
    (he : e ∈ Finset.Icc (ZetaRieszFineDivisorRows.lower N pb.1 pb.2)
      (ZetaRieszFineDivisorRows.upper N pb.1 pb.2))
    (hsieve : ZetaRieszUnsignedDivisorError.sieve (ZetaRieszRoughCutoffRows.forbidden pb.1 pb.2) e ≠ 0)
    (hδ : δ ∈ ZetaRieszRoughCutoffRows.cutoffDivisors N pb.1 pb.2)
    (hn : pb.1*(pb.2*e) ∈ coreBand u N K)
    (hf : f ∈ ((pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))/
      leastPairBlock (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))).divisors)
    (hfailed : log (pb.1*(pb.2*e) : ℕ)-log f+log (largestPrime (pb.1*(pb.2*e))) ≤
      (203/100 : ℝ)*N) :
    (e*δ,pb.2/δ) ∉ orbitDivisors (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))
      (leastPairBlock (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))) f := by
  have hi := ZetaRieszPolynomialCutoffRows.cutoff_original_incidence hN hr he hsieve hδ
  have hg := ZetaRieszPolynomialCutoffRows.cutoff_row_geometry hr
  have he0 : 0 < e := hg.2.2.2.2.2.2.1.trans_le (Finset.mem_Icc.mp he).1
  obtain ⟨_,hB,_,_,_,_,_,hgap,_,hcount,_,_,_⟩ := Finset.mem_filter.mp hr
  have htag : ZetaRieszRoughCutoffRows.roughTag pb.2 e ≠ 0 :=
    (mul_ne_zero_iff.mp ((ZetaRieszRoughCutoffRows.sieve_forbidden pb.1 pb.2 e) ▸ hsieve)).2
  have hcanon := ZetaRieszRoughCutoffRows.leastPairBlock_original hB hcount he0 htag
  have hRB : leastPairBlock (pb.2*e) ∣ pb.2 :=
    hcanon ▸ (leastPairBlock_data hB hcount).1
  have hδR : δ ∈ (leastPairBlock (pb.2*e)).divisors := by
    rw [hcanon]
    exact (Finset.mem_filter.mp hδ).1
  have hBe := (Nat.squarefree_mul_iff.mp hi.1).2.2
  have hbdata := ZetaRieszCrossingOrbitCancellation.based_orbit_data
    (Nat.pos_of_ne_zero hBe.ne_zero) rfl hRB hδR
  have hblock := canonical_block_data hn hi.1
  have hemost : e ∈ ((pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))/
      leastPairBlock (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))).divisors := by
    simpa only [hi.2.1,Nat.mul_div_cancel_left _ hg.1.pos] using hbdata.1
  have heinc : (e*δ,pb.2/δ) ∈ orbitDivisors (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))
      (leastPairBlock (pb.1*(pb.2*e)/largestPrime (pb.1*(pb.2*e)))) e := by
    simpa only [hi.2.1,Nat.mul_div_cancel_left _ hg.1.pos] using hbdata.2
  intro hnew
  have hfe : f=e := by
    by_contra hne
    exact Finset.disjoint_left.mp (orbitDivisors_disjoint hblock.2.2 hf hemost hne) hnew heinc
  rw [hfe,hi.2.1] at hfailed
  have hlog : log (pb.1*(pb.2*e) : ℕ)=log (pb.1*pb.2 : ℕ)+log e := by
    rw [← mul_assoc,Nat.cast_mul,log_mul
      (by exact_mod_cast (Nat.mul_pos hg.1.pos (Nat.pos_of_ne_zero hB.ne_zero)).ne')
      (by exact_mod_cast he0.ne')]
  linarith

end RiemannGaussian.ZetaRieszHingePairCancellation
