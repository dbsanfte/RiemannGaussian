/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCompensation

/-!
# Signed compensation bounds for the literal Riesz coefficient

These inequalities use the existing Riesz coefficient. They introduce no
new carrier. Below the reflected midpoint its positive part costs only the
unsaturated two-smallest-prime gap. Its negative part costs at most twice
the least prime logarithm, or once before the largest cofactor threshold.
The all-count pair-separated bound retains the opposing prime tents as
credits in a signed finite-sum inequality. No cross-label cancellation or
source-scale floor for the whole retained carrier is asserted.
-/

namespace RiemannGaussian.ZetaRieszSignedCompensationBounds
noncomputable section
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime ZetaRieszCutoffProfile

private theorem clip_eq {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    max 0 t-max 0 (t-a) = min a (max 0 t) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

private theorem clipped_difference {a x y : ℝ} (hxy : x ≤ y) :
    0 ≤ min a (max 0 y)-min a (max 0 x) ∧
      min a (max 0 y)-min a (max 0 x) ≤ y-x := by
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

private theorem triple_clipped {a b c t : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (ht : t ≤ a+c) :
    tripleDifference a b c t = min a (max 0 t)-
      min a (max 0 (t-b))-max 0 (t-c) := by
  simp only [tripleDifference, primePairTent]
  rw [max_eq_left (show t-c-a ≤ 0 by linarith),
    max_eq_left (show t-c-b ≤ 0 by linarith),
    max_eq_left (show t-c-a-b ≤ 0 by linarith)]
  have h1 := clip_eq ha t
  have h2 := clip_eq ha (t-b)
  rw [show t-b-a = t-a-b by ring] at h2
  linarith

/-- A direct signed secant bound for the existing three-prime profile.
The positive increment vanishes once the two smallest primes saturate.
The negative increment is retained and bounded separately. -/
theorem triple_increment_bounds {a b c r D : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hr : 0 ≤ r)
    (hmid : 2*D ≤ a+b+c) :
    -2*r ≤ tripleDifference a b c D-tripleDifference a b c (D-r) ∧
      tripleDifference a b c D-tripleDifference a b c (D-r) ≤
        min r (max 0 (r+a-D)) := by
  have hD : D ≤ a+c := by linarith
  have he1 := triple_clipped ha hab hD
  have he2 := triple_clipped ha hab (show D-r ≤ a+c by linarith)
  have h0 := clipped_difference (a := a) (show D-r ≤ D by linarith)
  have h1 := clipped_difference (a := a) (show D-r-b ≤ D-b by linarith)
  have h2 : 0 ≤ max 0 (D-c)-max 0 (D-r-c) ∧
      max 0 (D-c)-max 0 (D-r-c) ≤ r := by
    simp only [max_def]
    split_ifs <;> constructor <;> linarith
  have hgap : min a (max 0 D)-min a (max 0 (D-r)) ≤ max 0 (r+a-D) := by
    simp only [min_def, max_def]
    split_ifs <;> linarith
  rw [he1,he2]
  constructor
  · linarith
  · exact le_min (by linarith) (by linarith)

/-- Before the largest cofactor prime enters, only one decreasing tent
is present. This improves the negative bound from two least logs to one. -/
theorem triple_increment_ge_neg {a b c r D : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hr : 0 ≤ r) (hD : D ≤ c) :
    -r ≤ tripleDifference a b c D-tripleDifference a b c (D-r) := by
  rw [triple_clipped ha hab (show D ≤ a+c by linarith),
    triple_clipped ha hab (show D-r ≤ a+c by linarith),
    max_eq_left (show D-c ≤ 0 by linarith),
    max_eq_left (show D-r-c ≤ 0 by linarith)]
  have h0 := clipped_difference (a := a) (show D-r ≤ D by linarith)
  have h1 := clipped_difference (a := a) (show D-r-b ≤ D-b by linarith)
  linarith

/-- Bounds on the genuine four-prime cofactor, with every hinge endpoint
and subset sign retained. There is no prime-pair separation assumption. -/
theorem riesz_four_bounds {r a b c : ℕ}
    (hr : r.Prime) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) (hs : Squarefree (r*(a*(b*c))))
    {D : ℝ} (hmid : 2*D ≤ Real.log a+Real.log b+Real.log c) :
    -2*Real.log r ≤ VaughanLogAverage.riesz D (r*(a*(b*c))) ∧
      VaughanLogAverage.riesz D (r*(a*(b*c))) ≤
        min (Real.log r) (max 0 (Real.log r+Real.log a-D)) := by
  have hrm : ¬r ∣ a*(b*c) :=
    hr.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  rw [riesz_prime_mul D hr hrm,
    riesz_three_primes_eq_difference D ha hb hc hab.ne (hab.trans hbc).ne hbc.ne,
    riesz_three_primes_eq_difference (D-Real.log r) ha hb hc
      hab.ne (hab.trans hbc).ne hbc.ne]
  exact triple_increment_bounds (Real.log_natCast_nonneg a)
    (Real.log_le_log (by exact_mod_cast ha.pos) (by exact_mod_cast hab.le))
    (Real.log_le_log (by exact_mod_cast hb.pos) (by exact_mod_cast hbc.le))
    (Real.log_natCast_nonneg r) hmid

/-- The bounds apply to the original saturated five-prime coefficient.
Its positive allowance vanishes at the exact small-pair threshold;
negative arithmetic contributions are not replaced by that allowance. -/
theorem five_coefficient_bounds {P r a b c : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) (hs : Squarefree (P*(r*(a*(b*c)))))
    {L : ℝ} (hL : 0 < L) (hsat : Real.log (r*(a*(b*c)) : ℕ) ≤ L)
    (hmid : 2*(L-Real.log P) ≤ Real.log a+Real.log b+Real.log c) :
    -(Real.log (P*(r*(a*(b*c))) : ℕ)/L)*(2*Real.log r) ≤
        (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*(b*c))))).re ∧
      (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*(b*c))))).re ≤
        (Real.log (P*(r*(a*(b*c))) : ℕ)/L)*
          min (Real.log r) (max 0 (Real.log P+Real.log r+Real.log a-L)) := by
  have hrm : r*(a*(b*c)) ≠ 1 := fun he => hr.ne_one (mul_eq_one.mp he).1
  have ham : a*(b*c) ≠ 1 := fun he => ha.ne_one (mul_eq_one.mp he).1
  have hnp : ¬(r*(a*(b*c))).Prime := Nat.not_prime_mul hr.ne_one ham
  have hpa : ¬P ∣ r*(a*(b*c)) :=
    hP.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  have hn : ¬(P*(r*(a*(b*c)))).Prime := Nat.not_prime_mul hP.ne_one hrm
  rw [ZetaRieszContinuumCascade.coefficient_saturated_prime hP hpa hs.of_mul_right
    hrm hnp ⟨hs,hn⟩ hsat, ZetaRieszContinuumCascade.kernel_primeFactors hs.of_mul_right]
  simp only [Complex.ofReal_re]
  have he := riesz_four_bounds hr ha hb hc hab hbc hs.of_mul_right hmid
  have ht : 0 ≤ Real.log (P*(r*(a*(b*c))) : ℕ)/L :=
    div_nonneg (Real.log_natCast_nonneg _) hL.le
  rw [show Real.log r+Real.log a-(L-Real.log P) =
    Real.log P+Real.log r+Real.log a-L by ring] at he
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left he.1 ht]
  · exact mul_le_mul_of_nonneg_left he.2 ht

/-- On the literal core, saturation and the midpoint condition follow
from the existing length, owner, least-prime and physical masks. The
remaining bound measures an actual two-small-prime deficit. -/
theorem five_coefficient_bounds_core {u : ℝ} (hu : 1/2 ≤ u)
    {N P r a b c : ℕ} (hN : 2 ≤ N)
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) (hs : Squarefree (P*(r*(a*(b*c)))))
    (howner : Real.log (P*(r*(a*(b*c))) : ℕ)/2 ≤ Real.log P)
    (hleast : Real.log r ≤ (3/50 : ℝ)*Real.log (P*(r*(a*(b*c))) : ℕ))
    (hphysical : Real.log P ≤ SquarefreeVaughanLogSource.length u N)
    (hcore : (39/20 : ℝ)*N ≤ Real.log (P*(r*(a*(b*c))) : ℕ)) :
    -(Real.log (P*(r*(a*(b*c))) : ℕ)/SquarefreeVaughanLogSource.length u N)*
        (2*Real.log r) ≤
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N)
          (P*(r*(a*(b*c))))).re ∧
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N)
          (P*(r*(a*(b*c))))).re ≤
        (Real.log (P*(r*(a*(b*c))) : ℕ)/SquarefreeVaughanLogSource.length u N)*
          min (Real.log r) (max 0 (Real.log P+Real.log r+Real.log a-
            SquarefreeVaughanLogSource.length u N)) := by
  have hlog : Real.log (P*(r*(a*(b*c))) : ℕ) =
      Real.log P+Real.log (r*(a*(b*c)) : ℕ) := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hP.ne_zero)
      (by exact_mod_cast hs.of_mul_right.ne_zero)]
  have hmiddle : Real.log (r*(a*(b*c)) : ℕ) =
      Real.log r+Real.log a+Real.log b+Real.log c := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hr.ne_zero)
      (by exact_mod_cast hs.of_mul_right.of_mul_right.ne_zero),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast ha.ne_zero)
        (by exact_mod_cast (Nat.mul_ne_zero hb.ne_zero hc.ne_zero)),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hb.ne_zero) (by exact_mod_cast hc.ne_zero)]
    ring
  have hlen := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have hlog2 : Real.log 2 ≤ (7/10 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlen' : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    nlinarith [mul_le_mul_of_nonneg_right hlog2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  exact five_coefficient_bounds hP hr ha hb hc hab hbc hs
    (SquarefreeVaughanLogSource.length_pos u N) (by linarith) (by linarith)

/-- An independent signed inequality for an observed five-prime atom.
The original complex observation can contain the full factorial kernel,
allocation and phase. For a nonpositive real observation, only the
unsaturated small-pair gap can give a negative contribution. -/
theorem re_five_atom_ge_gap {P r a b c : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) (hs : Squarefree (P*(r*(a*(b*c)))))
    {L : ℝ} (hL : 0 < L) (hsat : Real.log (r*(a*(b*c)) : ℕ) ≤ L)
    (hmid : 2*(L-Real.log P) ≤ Real.log a+Real.log b+Real.log c)
    (z : ℂ) (hz : z.re ≤ 0) :
    (Real.log (P*(r*(a*(b*c))) : ℕ)/L)*
        min (Real.log r) (max 0 (Real.log P+Real.log r+Real.log a-L))*z.re ≤
      (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*(b*c))))*z).re := by
  have h := (five_coefficient_bounds hP hr ha hb hc hab hbc hs hL hsat hmid).2
  rw [Complex.mul_re,ZetaRieszCosineCarrier.coefficient_im_eq_zero,zero_mul,sub_zero]
  exact mul_le_mul_of_nonpos_right h hz

/-- The positive unit tent costs only its unsaturated reflected gap.
This estimate does not discard any of the opposing prime tents. -/
theorem primePairTent_le_gap {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (D : ℝ) :
    primePairTent r a D ≤ min r (max 0 (r+a-D)) := by
  apply le_min ((primePairTent_bounds hr ha D).2.trans (min_le_left _ _))
  simp only [primePairTent,max_def]
  split_ifs <;> linarith

/-- At arbitrary prime count, the same actual cofactor has a signed
upper bound retaining every opposing prime tent. Only the unit tent
has been bounded. No count, phase or prime measure is completed. -/
theorem riesz_le_gap_sub_prime_tents {r a b : ℕ}
    (hr : r.Prime) (ha : a.Prime) (hra : r ≠ a)
    (hrb : ¬r ∣ b) (hab : ¬a ∣ b) (hb : Squarefree b) {D : ℝ}
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → D ≤ Real.log p+Real.log q) :
    VaughanLogAverage.riesz D (r*(a*b)) ≤
      min (Real.log r) (max 0 (Real.log r+Real.log a-D))-
        ∑ p ∈ b.primeFactors,
          primePairTent (Real.log r) (Real.log a) (D-Real.log p) := by
  rw [ZetaRieszPrimeCompensation.riesz_eq_unit_sub_prime_tents hr ha hra hrb hab hb hpairs]
  exact sub_le_sub_right (primePairTent_le_gap (Real.log_natCast_nonneg r)
    (Real.log_natCast_nonneg a) D) _

/-- A signed sandwich for the actual coefficient after adding back its
exact opposing prime tents. Only the nonnegative unit response remains
between zero and the small-pair gap. -/
theorem coefficient_compensation_bounds {P r a b : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime)
    (hs : Squarefree (P*(r*(a*b)))) {L : ℝ} (hL : 0 < L)
    (hsat : Real.log (r*(a*b) : ℕ) ≤ L)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → L-Real.log P ≤ Real.log p+Real.log q) :
    0 ≤ (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*b)))).re+
        (Real.log (P*(r*(a*b)) : ℕ)/L)*
          ∑ p ∈ b.primeFactors, primePairTent (Real.log r) (Real.log a)
            (L-Real.log P-Real.log p) ∧
      (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*b)))).re+
        (Real.log (P*(r*(a*b)) : ℕ)/L)*
          (∑ p ∈ b.primeFactors, primePairTent (Real.log r) (Real.log a)
            (L-Real.log P-Real.log p)) ≤
        (Real.log (P*(r*(a*b)) : ℕ)/L)*
          min (Real.log r) (max 0 (Real.log P+Real.log r+Real.log a-L)) := by
  have hc := hs.of_mul_right
  have hab := hc.of_mul_right
  have hPr : ¬P ∣ r*(a*b) :=
    hP.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  have hrab : ¬r ∣ a*b := hr.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hc)
  have hrb : ¬r ∣ b := fun h => hrab (dvd_mul_of_dvd_right h _)
  have ha_b : ¬a ∣ b := ha.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hab)
  have hra : r ≠ a := fun h => hrab (by rw [h]; exact dvd_mul_right _ _)
  have hab1 : a*b ≠ 1 := fun h => ha.ne_one (mul_eq_one.mp h).1
  have hc1 : r*(a*b) ≠ 1 := fun h => hr.ne_one (mul_eq_one.mp h).1
  have hcp : ¬(r*(a*b)).Prime := Nat.not_prime_mul hr.ne_one hab1
  have hnp : ¬(P*(r*(a*b))).Prime := Nat.not_prime_mul hP.ne_one hc1
  rw [ZetaRieszContinuumCascade.coefficient_saturated_prime hP hPr hc hc1 hcp
    ⟨hs,hnp⟩ hsat,ZetaRieszContinuumCascade.kernel_primeFactors hc,Complex.ofReal_re]
  rw [ZetaRieszPrimeCompensation.riesz_eq_unit_sub_prime_tents
    hr ha hra hrb ha_b hab.of_mul_right hpairs]
  have ht : 0 ≤ Real.log (P*(r*(a*b)) : ℕ)/L :=
    div_nonneg (Real.log_natCast_nonneg _) hL.le
  have h := primePairTent_le_gap (Real.log_natCast_nonneg r)
    (Real.log_natCast_nonneg a) (L-Real.log P)
  rw [show Real.log r+Real.log a-(L-Real.log P) =
    Real.log P+Real.log r+Real.log a-L by ring] at h
  constructor
  · nlinarith [mul_nonneg ht (primePairTent_bounds (Real.log_natCast_nonneg r)
      (Real.log_natCast_nonneg a) (L-Real.log P)).1]
  · nlinarith [mul_le_mul_of_nonneg_left h ht]

/-- Signed compensation on the original arithmetic coefficient, including
the unsaturated small-pair boundary and the entire opposing prime sum. -/
theorem coefficient_le_gap_sub_prime_tents {P r a b : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime)
    (hs : Squarefree (P*(r*(a*b)))) {L : ℝ} (hL : 0 < L)
    (hsat : Real.log (r*(a*b) : ℕ) ≤ L)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → L-Real.log P ≤ Real.log p+Real.log q) :
    (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*b)))).re ≤
      (Real.log (P*(r*(a*b)) : ℕ)/L)*
        (min (Real.log r) (max 0 (Real.log P+Real.log r+Real.log a-L))-
          ∑ p ∈ b.primeFactors, primePairTent (Real.log r) (Real.log a)
            (L-Real.log P-Real.log p)) := by
  have h := (coefficient_compensation_bounds hP hr ha hs hL hsat hpairs).2
  nlinarith

/-- An observed signed inequality with positive compensation retained.
For the unchanged negative-real phase sector, each actual prime tent
provides credit against the explicit unit-gap debit. The complex
observation may contain all original factorial and allocation weights.
This theorem does not bound the complementary phase sector or count it
as already paid. -/
theorem re_atom_ge_signed_compensation {P r a b : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime)
    (hs : Squarefree (P*(r*(a*b)))) {L : ℝ} (hL : 0 < L)
    (hsat : Real.log (r*(a*b) : ℕ) ≤ L)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → L-Real.log P ≤ Real.log p+Real.log q)
    (z : ℂ) (hz : z.re ≤ 0) :
    (Real.log (P*(r*(a*b)) : ℕ)/L)*
        ((∑ p ∈ b.primeFactors, primePairTent (Real.log r) (Real.log a)
          (L-Real.log P-Real.log p))-
            min (Real.log r) (max 0 (Real.log P+Real.log r+Real.log a-L)))*(-z.re) ≤
      (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*b)))*z).re := by
  have h := coefficient_le_gap_sub_prime_tents hP hr ha hs hL hsat hpairs
  rw [Complex.mul_re,ZetaRieszCosineCarrier.coefficient_im_eq_zero,zero_mul,sub_zero]
  convert mul_le_mul_of_nonpos_right h hz using 1 <;> first | rfl | ring

/-- The signed compensation inequality summed on any literal finite
label mask. Each label keeps its complete complex observation and
opposing prime sum. No condition on the number of prime factors is used;
pair separation and the phase sector are explicit, unpaid restrictions. -/
theorem re_sum_ge_signed_compensation (S : Finset ℕ) (P r a b : ℕ → ℕ)
    (z : ℕ → ℂ) {L : ℝ} (hL : 0 < L)
    (he : ∀ n ∈ S, n = P n*(r n*(a n*b n)))
    (hP : ∀ n ∈ S, (P n).Prime) (hr : ∀ n ∈ S, (r n).Prime)
    (ha : ∀ n ∈ S, (a n).Prime) (hs : ∀ n ∈ S, Squarefree n)
    (hsat : ∀ n ∈ S, Real.log (r n*(a n*b n) : ℕ) ≤ L)
    (hpairs : ∀ n ∈ S, ∀ p ∈ (b n).primeFactors, ∀ q ∈ (b n).primeFactors,
      p ≠ q → L-Real.log (P n) ≤ Real.log p+Real.log q)
    (hz : ∀ n ∈ S, (z n).re ≤ 0) :
    (∑ n ∈ S, (Real.log n/L)*
      ((∑ p ∈ (b n).primeFactors, primePairTent (Real.log (r n)) (Real.log (a n))
        (L-Real.log (P n)-Real.log p))-
          min (Real.log (r n))
            (max 0 (Real.log (P n)+Real.log (r n)+Real.log (a n)-L)))*(-(z n).re)) ≤
      (∑ n ∈ S, SquarefreeVaughanLogSource.coefficient L n*z n).re := by
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro n hn
  have h := re_atom_ge_signed_compensation (hP n hn) (hr n hn) (ha n hn)
    (he n hn ▸ hs n hn) hL (hsat n hn) (hpairs n hn) (z n) (hz n hn)
  simpa only [← he n hn] using h

/-- A lower bound for every complex observation, without a phase-sector
restriction. The opposing prime sum keeps its FULL signed observation;
only the unit gap pays for a negative real observation. -/
theorem re_atom_ge_compensation_all_phases {P r a b : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime)
    (hs : Squarefree (P*(r*(a*b)))) {L : ℝ} (hL : 0 < L)
    (hsat : Real.log (r*(a*b) : ℕ) ≤ L)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → L-Real.log P ≤ Real.log p+Real.log q) (z : ℂ) :
    (Real.log (P*(r*(a*b)) : ℕ)/L)*
        (min (Real.log r) (max 0 (Real.log P+Real.log r+Real.log a-L))*min z.re 0-
          (∑ p ∈ b.primeFactors, primePairTent (Real.log r) (Real.log a)
            (L-Real.log P-Real.log p))*z.re) ≤
      (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*b)))*z).re := by
  have h := coefficient_compensation_bounds hP hr ha hs hL hsat hpairs
  rw [Complex.mul_re,ZetaRieszCosineCarrier.coefficient_im_eq_zero,zero_mul,sub_zero]
  by_cases hz : 0 ≤ z.re
  · rw [min_eq_right hz]
    nlinarith [mul_nonneg h.1 hz]
  · have hz' : z.re ≤ 0 := (le_of_not_ge hz)
    rw [min_eq_left hz']
    nlinarith [mul_le_mul_of_nonpos_right h.2 hz']

/-- A signed lower bound on the literal finite observed sum, retaining
all phases and every opposing prime term jointly. The prime-pair support
test remains explicit; no norm bound on this signed right-hand side or
on its complement is inferred. -/
theorem re_sum_ge_compensation_all_phases (S : Finset ℕ) (P r a b : ℕ → ℕ)
    (z : ℕ → ℂ) {L : ℝ} (hL : 0 < L)
    (he : ∀ n ∈ S, n = P n*(r n*(a n*b n)))
    (hP : ∀ n ∈ S, (P n).Prime) (hr : ∀ n ∈ S, (r n).Prime)
    (ha : ∀ n ∈ S, (a n).Prime) (hs : ∀ n ∈ S, Squarefree n)
    (hsat : ∀ n ∈ S, Real.log (r n*(a n*b n) : ℕ) ≤ L)
    (hpairs : ∀ n ∈ S, ∀ p ∈ (b n).primeFactors, ∀ q ∈ (b n).primeFactors,
      p ≠ q → L-Real.log (P n) ≤ Real.log p+Real.log q) :
    (∑ n ∈ S, (Real.log n/L)*
      (min (Real.log (r n))
          (max 0 (Real.log (P n)+Real.log (r n)+Real.log (a n)-L))*min (z n).re 0-
        (∑ p ∈ (b n).primeFactors, primePairTent (Real.log (r n)) (Real.log (a n))
          (L-Real.log (P n)-Real.log p))*(z n).re)) ≤
      (∑ n ∈ S, SquarefreeVaughanLogSource.coefficient L n*z n).re := by
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro n hn
  have h := re_atom_ge_compensation_all_phases (hP n hn) (hr n hn) (ha n hn)
    (he n hn ▸ hs n hn) hL (hsat n hn) (hpairs n hn) (z n)
  simpa only [← he n hn] using h

/-- The unit-gap upper bound loses only the rising edge below the
least-prime logarithm. Its exact defect is nonnegative and vanishes once
the cutoff has reached that logarithm. -/
theorem primePairTent_gap_identity {r a : ℝ} (hr : 0 ≤ r) (hra : r ≤ a) (D : ℝ) :
    primePairTent r a D = min r (max 0 (r+a-D))-max 0 (r-max 0 D) := by
  simp only [primePairTent,min_def,max_def]
  split_ifs <;> linarith

private theorem coefficient_compensation_eq_unit {P r a b : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime)
    (hs : Squarefree (P*(r*(a*b)))) {L : ℝ}
    (hsat : Real.log (r*(a*b) : ℕ) ≤ L)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → L-Real.log P ≤ Real.log p+Real.log q) :
    (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*b)))).re+
        (Real.log (P*(r*(a*b)) : ℕ)/L)*
          (∑ p ∈ b.primeFactors, primePairTent (Real.log r) (Real.log a)
            (L-Real.log P-Real.log p)) =
      (Real.log (P*(r*(a*b)) : ℕ)/L)*
        primePairTent (Real.log r) (Real.log a) (L-Real.log P) := by
  have hc := hs.of_mul_right
  have hab := hc.of_mul_right
  have hPr : ¬P ∣ r*(a*b) :=
    hP.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  have hrab : ¬r ∣ a*b := hr.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hc)
  have hrb : ¬r ∣ b := fun h => hrab (dvd_mul_of_dvd_right h _)
  have ha_b : ¬a ∣ b := ha.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hab)
  have hra : r ≠ a := fun h => hrab (by rw [h]; exact dvd_mul_right _ _)
  have hab1 : a*b ≠ 1 := fun h => ha.ne_one (mul_eq_one.mp h).1
  have hc1 : r*(a*b) ≠ 1 := fun h => hr.ne_one (mul_eq_one.mp h).1
  have hcp : ¬(r*(a*b)).Prime := Nat.not_prime_mul hr.ne_one hab1
  have hnp : ¬(P*(r*(a*b))).Prime := Nat.not_prime_mul hP.ne_one hc1
  rw [ZetaRieszContinuumCascade.coefficient_saturated_prime hP hPr hc hc1 hcp
    ⟨hs,hnp⟩ hsat,ZetaRieszContinuumCascade.kernel_primeFactors hc,Complex.ofReal_re,
    ZetaRieszPrimeCompensation.riesz_eq_unit_sub_prime_tents hr ha hra hrb ha_b hab.of_mul_right hpairs]
  ring

/-- Keeping positive unit observations never weakens the old clipped
bound. Its improvement is the nonnegative actual tent credit. -/
theorem unit_phase_lower_improved {r a : ℝ} (hr : 0 ≤ r) (hra : r ≤ a) (D x : ℝ) :
    min r (max 0 (r+a-D))*min x 0 ≤
      min r (max 0 (r+a-D))*x-max 0 (r-max 0 D)*max x 0 := by
  have ht := (primePairTent_bounds hr (show 0 ≤ a by linarith) D).1
  rw [primePairTent_gap_identity hr hra D] at ht
  have hx := min_add_max x 0
  have hp := mul_nonneg ht (le_max_right x 0)
  nlinarith [congrArg (fun v : ℝ => min r (max 0 (r+a-D))*v) hx]

/-- The exact information lost by the improved one-sided comparison is
the rising edge times the negative observation. In particular, restricting
the edge to finitely many prime counts does not bound this sum. -/
theorem re_atom_sub_compensation_keep_positive {P r a b : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime) (hra : r ≤ a)
    (hs : Squarefree (P*(r*(a*b)))) {L : ℝ}
    (hsat : Real.log (r*(a*b) : ℕ) ≤ L)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → L-Real.log P ≤ Real.log p+Real.log q) (z : ℂ) :
    (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*b)))*z).re-
      (Real.log (P*(r*(a*b)) : ℕ)/L)*
        ((min (Real.log r) (max 0 (Real.log P+Real.log r+Real.log a-L))-
            ∑ p ∈ b.primeFactors, primePairTent (Real.log r) (Real.log a)
              (L-Real.log P-Real.log p))*z.re-
          max 0 (Real.log r-max 0 (L-Real.log P))*max z.re 0) =
      (Real.log (P*(r*(a*b)) : ℕ)/L)*
        max 0 (Real.log r-max 0 (L-Real.log P))*max (-z.re) 0 := by
  have he := coefficient_compensation_eq_unit hP hr ha hs hsat hpairs
  rw [primePairTent_gap_identity (Real.log_natCast_nonneg r)
    (Real.log_le_log (by exact_mod_cast hr.pos) (by exact_mod_cast hra))] at he
  rw [show Real.log r+Real.log a-(L-Real.log P) =
    Real.log P+Real.log r+Real.log a-L by ring] at he
  rw [Complex.mul_re,ZetaRieszCosineCarrier.coefficient_im_eq_zero,zero_mul,sub_zero]
  have hx : max z.re 0-z.re = max (-z.re) 0 := by
    simp only [max_def]
    split_ifs <;> linarith
  nlinarith [congrArg (fun v : ℝ => v*z.re) he,
    congrArg (fun v : ℝ => (Real.log (P*(r*(a*b)) : ℕ)/L)*
      max 0 (Real.log r-max 0 (L-Real.log P))*v) hx]

/-- Retain the positive unit credit as well as the signed opposing prime
tents. Only the explicit rising-edge defect is charged, and only against
a positive observation. This strengthens the earlier clipped comparison. -/
theorem re_atom_ge_compensation_keep_positive {P r a b : ℕ}
    (hP : P.Prime) (hr : r.Prime) (ha : a.Prime) (hra : r ≤ a)
    (hs : Squarefree (P*(r*(a*b)))) {L : ℝ} (hL : 0 < L)
    (hsat : Real.log (r*(a*b) : ℕ) ≤ L)
    (hpairs : ∀ p ∈ b.primeFactors, ∀ q ∈ b.primeFactors,
      p ≠ q → L-Real.log P ≤ Real.log p+Real.log q) (z : ℂ) :
    (Real.log (P*(r*(a*b)) : ℕ)/L)*
      ((min (Real.log r) (max 0 (Real.log P+Real.log r+Real.log a-L))-
          ∑ p ∈ b.primeFactors, primePairTent (Real.log r) (Real.log a)
            (L-Real.log P-Real.log p))*z.re-
        max 0 (Real.log r-max 0 (L-Real.log P))*max z.re 0) ≤
      (SquarefreeVaughanLogSource.coefficient L (P*(r*(a*b)))*z).re := by
  have he := coefficient_compensation_eq_unit hP hr ha hs hsat hpairs
  rw [primePairTent_gap_identity (Real.log_natCast_nonneg r)
    (Real.log_le_log (by exact_mod_cast hr.pos) (by exact_mod_cast hra))] at he
  rw [show Real.log r+Real.log a-(L-Real.log P) =
    Real.log P+Real.log r+Real.log a-L by ring] at he
  rw [Complex.mul_re,ZetaRieszCosineCarrier.coefficient_im_eq_zero,zero_mul,sub_zero]
  have ht : 0 ≤ Real.log (P*(r*(a*b)) : ℕ)/L :=
    div_nonneg (Real.log_natCast_nonneg _) hL.le
  have hgap := mul_nonneg (mul_nonneg ht (le_max_left 0 (Real.log r-max 0 (L-Real.log P))))
    (sub_nonneg.mpr (le_max_left z.re 0))
  nlinarith [congrArg (fun v : ℝ => v*z.re) he]

/-- The improved lower comparison on any actual finite mask, with all
positive unit phases, opposing prime terms and complex observations kept
jointly. Pair-separation failures remain outside its stated support. -/
theorem re_sum_ge_compensation_keep_positive (S : Finset ℕ) (P r a b : ℕ → ℕ)
    (z : ℕ → ℂ) {L : ℝ} (hL : 0 < L)
    (he : ∀ n ∈ S, n = P n*(r n*(a n*b n)))
    (hP : ∀ n ∈ S, (P n).Prime) (hr : ∀ n ∈ S, (r n).Prime)
    (ha : ∀ n ∈ S, (a n).Prime) (hra : ∀ n ∈ S, r n ≤ a n)
    (hs : ∀ n ∈ S, Squarefree n)
    (hsat : ∀ n ∈ S, Real.log (r n*(a n*b n) : ℕ) ≤ L)
    (hpairs : ∀ n ∈ S, ∀ p ∈ (b n).primeFactors, ∀ q ∈ (b n).primeFactors,
      p ≠ q → L-Real.log (P n) ≤ Real.log p+Real.log q) :
    (∑ n ∈ S, (Real.log n/L)*
      ((min (Real.log (r n)) (max 0 (Real.log (P n)+Real.log (r n)+Real.log (a n)-L))-
          ∑ p ∈ (b n).primeFactors, primePairTent (Real.log (r n)) (Real.log (a n))
            (L-Real.log (P n)-Real.log p))*(z n).re-
        max 0 (Real.log (r n)-max 0 (L-Real.log (P n)))*max (z n).re 0)) ≤
      (∑ n ∈ S, SquarefreeVaughanLogSource.coefficient L n*z n).re := by
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro n hn
  have h := re_atom_ge_compensation_keep_positive (hP n hn) (hr n hn) (ha n hn)
    (hra n hn) (he n hn ▸ hs n hn) hL (hsat n hn) (hpairs n hn) (z n)
  simpa only [← he n hn] using h

end
end RiemannGaussian.ZetaRieszSignedCompensationBounds
