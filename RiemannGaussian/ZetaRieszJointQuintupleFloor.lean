/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointSmoothFloor

/-!
# Signed five-prime bounds after small-factor cancellation

Three prime insertions against a saturated small composite leave only
the pair-boundary responses. For a two-prime small factor these responses
are nonnegative tents. The core length excludes simultaneous activity of
all three, giving a signed coefficient bound with two least-log costs.
The actual phase is retained; no whole-core arithmetic floor is claimed.
-/

namespace RiemannGaussian.ZetaRieszJointQuintupleFloor
noncomputable section
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows

/-- Three exact prime insertions leave only the pair-boundary terms
when the small composite and all single-prime extensions are saturated.
This identity is used immediately in the signed bound below. -/
theorem riesz_three_primes_small_composite {p q r a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : Squarefree (p*(q*(r*a)))) (ha1 : a ≠ 1) (hap : ¬a.Prime)
    {L : ℝ} (hpa : Real.log p+Real.log a ≤ L)
    (hqa : Real.log q+Real.log a ≤ L) (hra : Real.log r+Real.log a ≤ L)
    (hpqr : L ≤ Real.log p+Real.log q+Real.log r) :
    VaughanLogAverage.riesz L (p*(q*(r*a))) =
      VaughanLogAverage.riesz (L-Real.log p-Real.log q) a+
      VaughanLogAverage.riesz (L-Real.log p-Real.log r) a+
      VaughanLogAverage.riesz (L-Real.log q-Real.log r) a := by
  have ha := hs.of_mul_right.of_mul_right.of_mul_right
  have hpnd : ¬p ∣ q*(r*a) :=
    hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  have hqnd : ¬q ∣ r*a :=
    hq.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs.of_mul_right)
  have hrnd : ¬r ∣ a :=
    hr.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs.of_mul_right.of_mul_right)
  rw [riesz_prime_mul L hp hpnd,riesz_prime_mul L hq hqnd,
    riesz_prime_mul (L-Real.log p) hq hqnd,riesz_prime_mul L hr hrnd,
    riesz_prime_mul (L-Real.log q) hr hrnd,riesz_prime_mul (L-Real.log p) hr hrnd,
    riesz_prime_mul (L-Real.log p-Real.log q) hr hrnd,
    ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1 hap
      (show Real.log a ≤ L by linarith [Real.log_natCast_nonneg p]),
    ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1 hap
      (show Real.log a ≤ L-Real.log p by linarith),
    ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1 hap
      (show Real.log a ≤ L-Real.log q by linarith),
    ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1 hap
      (show Real.log a ≤ L-Real.log r by linarith),
    ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos
      (show L-Real.log p-Real.log q-Real.log r ≤ 0 by linarith)]
  ring

/-- The radial length gap rules out three simultaneously active pair
boundaries. This retains both edges of every tent, including equality. -/
theorem three_pair_tents_bounds {a b p q r L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgap : 2*(p+q+r)+3*(a+b) ≤ 3*L) :
    0 ≤ primePairTent a b (L-p-q)+primePairTent a b (L-p-r)+primePairTent a b (L-q-r) ∧
      primePairTent a b (L-p-q)+primePairTent a b (L-p-r)+primePairTent a b (L-q-r) ≤
        2*min a b := by
  have h1 := primePairTent_bounds ha hb (L-p-q)
  have h2 := primePairTent_bounds ha hb (L-p-r)
  have h3 := primePairTent_bounds ha hb (L-q-r)
  constructor
  · linarith
  · by_cases hx : a+b ≤ L-p-q
    · rw [primePairTent_eq_zero_of_outside ha hb (Or.inr hx)]
      linarith
    · by_cases hy : a+b ≤ L-p-r
      · rw [primePairTent_eq_zero_of_outside ha hb (Or.inr hy)]
        linarith
      · have hz : a+b ≤ L-q-r := by linarith
        rw [primePairTent_eq_zero_of_outside ha hb (Or.inr hz)]
        linarith

/-- A literal five-prime coefficient has a fixed negative arithmetic
sign and pays at most two least-prime logarithms on this saturated class.
There is no prime-pair separation hypothesis or phase averaging. -/
theorem five_coefficient_bounds {p q r a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (ha : a.Prime) (hb : b.Prime)
    (hs : Squarefree (p*(q*(r*(a*b))))) {L : ℝ} (hL : 0 < L)
    (hpa : Real.log p+Real.log (a*b : ℕ) ≤ L)
    (hqa : Real.log q+Real.log (a*b : ℕ) ≤ L)
    (hra : Real.log r+Real.log (a*b : ℕ) ≤ L)
    (hpqr : L ≤ Real.log p+Real.log q+Real.log r)
    (hgap : 2*Real.log (p*(q*(r*(a*b))) : ℕ)+Real.log (a*b : ℕ) ≤ 3*L) :
    -(Real.log (p*(q*(r*(a*b))) : ℕ)/L)*(2*min (Real.log a) (Real.log b)) ≤
        (SquarefreeVaughanLogSource.coefficient L (p*(q*(r*(a*b))))).re ∧
      (SquarefreeVaughanLogSource.coefficient L (p*(q*(r*(a*b))))).re ≤ 0 := by
  have habs := hs.of_mul_right.of_mul_right.of_mul_right
  have hab : a ≠ b := by
    intro he
    have hd : ¬a ∣ b := ha.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul habs)
    exact hd (he ▸ dvd_refl a)
  have hab1 : a*b ≠ 1 := fun he => ha.ne_one (mul_eq_one.mp he).1
  have habp : ¬(a*b).Prime := Nat.not_prime_mul ha.ne_one hb.ne_one
  have hlogab : Real.log (a*b : ℕ) = Real.log a+Real.log b := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast ha.ne_zero) (by exact_mod_cast hb.ne_zero)]
  have hlogn : Real.log (p*(q*(r*(a*b))) : ℕ) =
      Real.log p+Real.log q+Real.log r+Real.log (a*b : ℕ) := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hs.of_mul_right.ne_zero),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hs.of_mul_right.of_mul_right.ne_zero),
      Nat.cast_mul,Real.log_mul (by exact_mod_cast hr.ne_zero) (by exact_mod_cast habs.ne_zero)]
    ring
  have hbnd := three_pair_tents_bounds (Real.log_natCast_nonneg a) (Real.log_natCast_nonneg b)
    (p := Real.log p) (q := Real.log q) (r := Real.log r) (L := L) (by
      rw [hlogn,hlogab] at hgap
      linarith)
  have he := riesz_three_primes_small_composite hp hq hr hs hab1 habp hpa hqa hra hpqr
  rw [ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ ha hb hab,
    ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ ha hb hab,
    ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ ha hb hab] at he
  have hnonprime : ¬(p*(q*(r*(a*b)))).Prime := Nat.not_prime_mul hp.ne_one
    (fun he => hq.ne_one (mul_eq_one.mp he).1)
  rw [SquarefreeVaughanLogSource.coefficient,if_pos ⟨hs,hnonprime⟩,Complex.ofReal_re,he]
  have ht : 0 ≤ Real.log (p*(q*(r*(a*b))) : ℕ)/L :=
    div_nonneg (Real.log_natCast_nonneg _) hL.le
  constructor
  · have h := mul_le_mul_of_nonneg_left hbnd.2 ht
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  · have h := mul_nonneg ht hbnd.1
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]

/-- The literal core geometry supplies every saturation and pair-gap
condition. No ordering or distinguished owner above sqrt(n) is needed. -/
theorem five_coefficient_bounds_of_geometry {N p q r a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (ha : a.Prime) (hb : b.Prime)
    (hs : Squarefree (p*(q*(r*(a*b))))) {L : ℝ} (hL : 0 < L)
    (hLlo : (137/100 : ℝ)*N ≤ L) (hLhi : L ≤ (7/5 : ℝ)*N)
    (hsmall : Real.log (a*b : ℕ) ≤ (N : ℝ)/2048)
    (hlo : (39/20 : ℝ)*N ≤ Real.log (p*(q*(r*(a*b))) : ℕ))
    (hhi : Real.log (p*(q*(r*(a*b))) : ℕ) ≤ (203/100 : ℝ)*N)
    (hplog : Real.log p ≤ (601/1000 : ℝ)*Real.log (p*(q*(r*(a*b))) : ℕ))
    (hqlog : Real.log q ≤ (601/1000 : ℝ)*Real.log (p*(q*(r*(a*b))) : ℕ))
    (hrlog : Real.log r ≤ (601/1000 : ℝ)*Real.log (p*(q*(r*(a*b))) : ℕ)) :
    -(Real.log (p*(q*(r*(a*b))) : ℕ)/L)*(2*min (Real.log a) (Real.log b)) ≤
        (SquarefreeVaughanLogSource.coefficient L (p*(q*(r*(a*b))))).re ∧
      (SquarefreeVaughanLogSource.coefficient L (p*(q*(r*(a*b))))).re ≤ 0 := by
  have hlogn : Real.log (p*(q*(r*(a*b))) : ℕ) =
      Real.log p+Real.log q+Real.log r+Real.log (a*b : ℕ) := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hs.of_mul_right.ne_zero),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hs.of_mul_right.of_mul_right.ne_zero),
      Nat.cast_mul,Real.log_mul (by exact_mod_cast hr.ne_zero)
        (by exact_mod_cast hs.of_mul_right.of_mul_right.of_mul_right.ne_zero)]
    ring
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact five_coefficient_bounds hp hq hr ha hb hs hL (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)

open ZetaRieszPrimeCountFrequency ZetaRieszJointAllocation ZetaRieszParityPacket
open ZetaRieszAnnulusJoint ZetaRieszWideOwnerAudit ZetaRieszJointCountFloor

/-- A two-sided arithmetic bound on the ACTUAL retained five-prime
coefficient. All count, support and prime-share tests are discharged
from the existing core; the literal unassigned multiplier is retained. -/
theorem five_residual_bounds_core (j : ℕ) (hj : 64 ≤ j) {u : ℝ} (hu : 1/2 ≤ u)
    (hL : (137/100 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {n p q r a b : ℕ}
    (hnB : n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount (j-9))).filter (fun n =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u (dyadicMomentOrder j) ∧
          eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p)))
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (ha : a.Prime) (hb : b.Prime)
    (he : n = p*(q*(r*(a*b))))
    (haN : a ≤ (dyadicMomentOrder j)^2) (hbN : b ≤ (dyadicMomentOrder j)^2) :
    -(Real.log n/SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))*
        (1-boundedShare (intermediatePrimes u (dyadicMomentOrder j)) (dyadicMomentOrder j) n)*
          (2*min (Real.log a) (Real.log b)) ≤
      (residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n).re ∧
      (residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n).re ≤ 0 := by
  have ht : 0 ≤ 1-boundedShare (intermediatePrimes u (dyadicMomentOrder j)) (dyadicMomentOrder j) n := by
    linarith [(boundedShare_bounds (intermediatePrimes u (dyadicMomentOrder j)) (dyadicMomentOrder j) n).2]
  have hlen0 := SquarefreeVaughanLogSource.length_pos u (dyadicMomentOrder j)
  have hnonneg : 0 ≤ Real.log n/SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) :=
    div_nonneg (Real.log_natCast_nonneg _) hlen0.le
  have hm : 0 ≤ 2*min (Real.log a) (Real.log b) := by
    positivity
  by_cases hz : residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n = 0
  · rw [hz,Complex.zero_re]
    exact ⟨mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnonneg) ht) hm,le_rfl⟩
  obtain ⟨hn,hc,hwlo,hwhi,hall⟩ :=
    ZetaRieszJointSmoothFloor.reduced_core_geometry j hj hnB hz
  have hdiv : a*b ∣ n := by
    rw [he]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_left (a*b) r) q) p
  have hsmall := reduced_smooth_divisor_log_le j hj hn hdiv hc (by
    intro v hv
    simp only [Nat.primeFactors_mul ha.ne_zero hb.ne_zero,ha.primeFactors,hb.primeFactors,
      Finset.singleton_union,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact haN
    · exact hbN)
  have hN : 2 ≤ dyadicMomentOrder j := by
    have hk := four_le_dyadicPrimeCount j
    unfold dyadicMomentOrder
    nlinarith
  have hlen : SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) ≤
      (7/5 : ℝ)*dyadicMomentOrder j := by
    have hh := ZetaRieszHeadOrders.length_le_two_log_two hu hN
    have hlog : 2*Real.log 2 ≤ (7/5 : ℝ) := by linarith [Real.log_two_lt_d9]
    exact hh.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  have hpdiv : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp,by rw [he]; exact dvd_mul_right _ _,hn.ne_zero⟩
  have hqdiv : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hq,by rw [he]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _,hn.ne_zero⟩
  have hrdiv : r ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hr,by rw [he]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _,hn.ne_zero⟩
  have hbound := five_coefficient_bounds_of_geometry hp hq hr ha hb (he ▸ hn) hlen0 hL hlen
    hsmall (he ▸ hwlo.le) (he ▸ hwhi) (he ▸ (hall p hpdiv).le)
      (he ▸ (hall q hqdiv).le) (he ▸ (hall r hrdiv).le)
  rw [← he] at hbound
  simp only [residualCoefficient,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  constructor
  · convert mul_le_mul_of_nonneg_left hbound.1 ht using 1 <;> first | rfl | ring
  · exact mul_nonpos_of_nonneg_of_nonpos ht hbound.2

/-- The stronger literal length premise holds eventually on the
restricted radius interval; it is not a new arithmetic assumption. -/
theorem eventually_length_lower {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling) :
    ∀ᶠ j : ℕ in Filter.atTop,
      (137/100 : ℝ)*dyadicMomentOrder j ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by
  have hh : u < Real.exp (-(137/200 : ℝ)) := (hU.trans_lt radius_lt_source).trans
    (Real.exp_lt_exp.mpr (by norm_num))
  have h := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
    (by norm_num : (0 : ℝ) ≤ 137/200) hh
  simpa only [show (2 : ℝ)*(137/200) = 137/100 by norm_num] using
    tendsto_dyadicMomentOrder.eventually h

/-- A genuine one-sided sign estimate for the retained complex atom.
Its complete observation may include the factorial kernel and source
scaling. The opposite phase sector remains in the joint carrier and is
not charged an absolute-cosine allowance. -/
theorem re_five_residual_nonneg_core (j : ℕ) (hj : 64 ≤ j) {u : ℝ} (hu : 1/2 ≤ u)
    (hL : (137/100 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {n p q r a b : ℕ}
    (hnB : n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount (j-9))).filter (fun n =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u (dyadicMomentOrder j) ∧
          eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p)))
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (ha : a.Prime) (hb : b.Prime)
    (he : n = p*(q*(r*(a*b))))
    (haN : a ≤ (dyadicMomentOrder j)^2) (hbN : b ≤ (dyadicMomentOrder j)^2)
    (z : ℂ) (hz : z.re ≤ 0) :
    0 ≤ (residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*z).re := by
  have h := (five_residual_bounds_core j hj hu hL hnB hp hq hr ha hb he haN hbN).2
  have him : (residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n).im = 0 := by
    simp only [residualCoefficient,Complex.mul_im,Complex.ofReal_im,zero_mul,
      ZetaRieszCosineCarrier.coefficient_im_eq_zero,mul_zero,add_zero]
  rw [Complex.mul_re,him,zero_mul,sub_zero]
  exact mul_nonneg_of_nonpos_of_nonpos h hz

/-- The scalar two-tent cost can be attained with all five logarithmic
shares in the stated geometry. This is a real-logarithm certificate,
not an assertion that rational shares are actual prime logarithms. -/
theorem three_pair_tents_sharp :
    primePairTent (1/8192 : ℝ) (3/8192)
        (137/100-37/50-(63/100-3/16384))+
      primePairTent (1/8192 : ℝ) (3/8192)
        (137/100-37/50-(63/100-5/16384))+
      primePairTent (1/8192 : ℝ) (3/8192)
        (137/100-(63/100-3/16384)-(63/100-5/16384)) = 1/4096 := by
  norm_num [primePairTent]

end
end RiemannGaussian.ZetaRieszJointQuintupleFloor
