/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCutoffProfile
import RiemannGaussian.ZetaRieszReflectedLinear
import RiemannGaussian.ZetaRieszJointSmoothFloor

/-!
# A signed largest-prime gap bound for the whole four-prime class

The existing coefficient has the sign of `log P + log n - 2 L`, where
`P` is the largest prime factor and `2 log n <= 3 L <= 3 log n`.
The bounds below apply to actual integers and retain favorable phase
credit in their observed-sum lower bound. No new carrier is defined.
-/

namespace RiemannGaussian.ZetaRieszFourPrimeFloor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime ZetaRieszCutoffProfile
open ZetaRieszReflectedLinear ZetaRieszPrimeEndpoint

/-- Both sides of the three-prime reflection midpoint have a signed gap
bound. The original divisor sum, including all boundary cases, remains. -/
theorem riesz_three_signed_gap {a : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card = 3) (D : ℝ) :
    -max 0 (2*D-Real.log a) ≤ VaughanLogAverage.riesz D a ∧
      VaughanLogAverage.riesz D a ≤ max 0 (Real.log a-2*D) := by
  by_cases hmid : Real.log a ≤ 2*D
  · have hsign := (riesz_of_three_primeFactors_bounds ha hc hmid).2
    have hgap := neg_riesz_three_le_midpoint_gap ha hc hmid
    rw [max_eq_right (by linarith : 0 ≤ 2*D-Real.log a),
      max_eq_left (by linarith : Real.log a-2*D ≤ 0)]
    exact ⟨by linarith,hsign⟩
  · have ha1 : a ≠ 1 := by intro h; simp [h] at hc
    have hap : ¬a.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
    have hsign := riesz_three_nonneg_below_midpoint ha hc (by linarith : 2*D ≤ Real.log a)
    have hr := VaughanLogAverage.riesz_reflection D ha ha1 hap
    rw [moebius_eq_primeCount ha,hc] at hr
    norm_num at hr
    have hgap := neg_riesz_three_le_midpoint_gap (L := Real.log a-D) ha hc (by linarith)
    rw [hr] at hgap
    rw [max_eq_left (by linarith : 2*D-Real.log a ≤ 0),neg_zero,
      max_eq_right (by linarith : 0 ≤ Real.log a-2*D)]
    exact ⟨hsign,by linarith⟩

/-- If only singleton divisors meet the reflected cutoff, the four-leg
difference is affine. This is used only to prove the signed inequality. -/
theorem four_difference_singletons {a b c p D : ℝ}
    (hD : 0 ≤ D) (ha : a ≤ D) (hb : b ≤ D) (hc : c ≤ D) (hp : p ≤ D)
    (ht : 3*D ≤ a+b+c+p) :
    tripleDifference a b c D-tripleDifference a b c (D-p) = a+b+c+p-3*D := by
  simp only [tripleDifference,primePairTent]
  rw [max_eq_right hD,
    max_eq_right (by linarith : 0 ≤ D-a),
    max_eq_right (by linarith : 0 ≤ D-b),
    max_eq_right (by linarith : 0 ≤ D-c),
    max_eq_right (by linarith : 0 ≤ D-p),
    max_eq_left (by linarith : D-a-b ≤ 0),
    max_eq_left (by linarith : D-c-a ≤ 0),
    max_eq_left (by linarith : D-c-b ≤ 0),
    max_eq_left (by linarith : D-c-a-b ≤ 0),
    max_eq_left (by linarith : D-p-a ≤ 0),
    max_eq_left (by linarith : D-p-b ≤ 0),
    max_eq_left (by linarith : D-p-a-b ≤ 0),
    max_eq_left (by linarith : D-p-c ≤ 0),
    max_eq_left (by linarith : D-p-c-a ≤ 0),
    max_eq_left (by linarith : D-p-c-b ≤ 0),
    max_eq_left (by linarith : D-p-c-a-b ≤ 0)]
  ring

/-- The complete four-prime Riesz profile changes sign only across its
largest-prime gap. No linear-class or prime-imbalance restriction is used. -/
theorem riesz_four_signed_gap {n P : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) (hP : P ∈ n.primeFactors)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log P)
    {L : ℝ} (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) :
    -max 0 (Real.log P+Real.log n-2*L) ≤ VaughanLogAverage.riesz L n ∧
      VaughanLogAverage.riesz L n ≤ max 0 (2*L-Real.log n-Real.log P) := by
  let a := ∏ p ∈ n.primeFactors.erase P, p
  have hpa (p : ℕ) (hp : p ∈ n.primeFactors.erase P) : p.Prime :=
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have hfa : a.primeFactors = n.primeFactors.erase P := Nat.primeFactors_prod hpa
  have hac : a.primeFactors.card = 3 := by
    rw [hfa,Finset.card_erase_of_mem hP,hc]
  have he : n = P*a := by
    rw [← Nat.prod_primeFactors_of_squarefree hs]
    exact (Finset.mul_prod_erase _ _ hP).symm
  have hsp : Squarefree (P*a) := he ▸ hs
  have hp := Nat.prime_of_mem_primeFactors hP
  have hpn : ¬P ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsp)
  have hlog : Real.log n = Real.log P+Real.log a := by
    rw [he,Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hsp.of_mul_right.ne_zero)]
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
  have hr := VaughanLogAverage.riesz_reflection L hs hn1 hnp
  rw [moebius_eq_primeCount hs,hc] at hr
  norm_num at hr
  let D := Real.log n-L
  have hD : 0 ≤ D := sub_nonneg.mpr hLhi
  have hR : VaughanLogAverage.riesz L n =
      VaughanLogAverage.riesz D a-VaughanLogAverage.riesz (D-Real.log P) a := by
    exact hr.symm.trans (by simpa only [← he] using riesz_prime_mul D hp hpn)
  by_cases hlarge : D ≤ Real.log P
  · rw [hR,ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (by linarith : D-Real.log P ≤ 0),sub_zero]
    have hg := riesz_three_signed_gap hsp.of_mul_right hac D
    have hg1 : 2*D-Real.log a = Real.log P+Real.log n-2*L := by dsimp [D]; linarith
    have hg2 : Real.log a-2*D = 2*L-Real.log n-Real.log P := by dsimp [D]; linarith
    simpa only [hg1,hg2] using hg
  · have hsmall : Real.log P ≤ D := le_of_lt (lt_of_not_ge hlarge)
    obtain ⟨b,c,d,hb,hc',hd,hbc,hbd,hcd,haeq⟩ := exists_three_primes hsp.of_mul_right hac
    have hlogs : Real.log a = Real.log b+Real.log c+Real.log d := by
      rw [haeq,Nat.cast_mul,Real.log_mul (by exact_mod_cast hb.ne_zero)
        (by exact_mod_cast (Nat.mul_ne_zero hc'.ne_zero hd.ne_zero)),Nat.cast_mul,
        Real.log_mul (by exact_mod_cast hc'.ne_zero) (by exact_mod_cast hd.ne_zero)]
      ring
    have hbound (p : ℕ) (hp' : p.Prime) (hpdiv : p ∣ a) : Real.log p ≤ D := by
      have hdvd : p ∣ n := by rw [he]; exact dvd_mul_of_dvd_right hpdiv P
      exact (hmax p (Nat.mem_primeFactors.mpr ⟨hp',hdvd,hs.ne_zero⟩)).trans hsmall
    have hbD := hbound b hb (by rw [haeq]; exact dvd_mul_right _ _)
    have hcD := hbound c hc' (by rw [haeq]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
    have hdD := hbound d hd (by rw [haeq]; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
    have heq : VaughanLogAverage.riesz L n = 3*L-2*Real.log n := by
      rw [hR,haeq,
        riesz_three_primes_eq_difference D hb hc' hd hbc hbd hcd,
        riesz_three_primes_eq_difference (D-Real.log P) hb hc' hd hbc hbd hcd,
        four_difference_singletons hD hbD hcD hdD hsmall (by dsimp [D]; linarith)]
      dsimp [D]
      linarith
    rw [heq,max_eq_left (show Real.log P+Real.log n-2*L ≤ 0 by dsimp [D] at hsmall; linarith),
      neg_zero,max_eq_right (show 0 ≤ 2*L-Real.log n-Real.log P by dsimp [D] at hsmall; linarith)]
    exact ⟨by linarith,by dsimp [D] at hsmall; linarith⟩

/-- An independent signed coefficient inequality over the whole four-prime
class. Its zero and sign follow from the actual largest-prime geometry. -/
theorem coefficient_four_signed_gap {n P : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) (hP : P ∈ n.primeFactors)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log P)
    {L : ℝ} (hL : 0 < L) (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) :
    -(Real.log n/L)*max 0 (2*L-Real.log n-Real.log P) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        (Real.log n/L)*max 0 (Real.log P+Real.log n-2*L) := by
  have hr := riesz_four_signed_gap hs hc hP hmax hLhi hLlo
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
  have hgood : Squarefree n ∧ ¬n.Prime := ⟨hs,hnp⟩
  simp only [SquarefreeVaughanLogSource.coefficient,if_pos hgood,Complex.ofReal_re]
  rw [show -Real.log n*VaughanLogAverage.riesz L n/L =
    -(Real.log n/L)*VaughanLogAverage.riesz L n by ring]
  have hscale : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg n) hL.le
  constructor
  · have h := mul_le_mul_of_nonneg_left hr.2 hscale
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hr.1 hscale
    nlinarith

theorem largestPrime_mem_of_four {n : ℕ} (hc : n.primeFactors.card = 4) :
    largestPrime n ∈ n.primeFactors := by
  have hn : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  rw [largestPrime,dif_pos hn]
  exact Finset.max'_mem _ _

/-- The canonical largest-prime choice discharges the ordering hypotheses.
Nonsquarefree labels have zero coefficient and obey the same bounds. -/
theorem actual_four_signed_gap {n : ℕ} (hc : n.primeFactors.card = 4)
    {L : ℝ} (hL : 0 < L) (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) :
    -(Real.log n/L)*max 0 (2*L-Real.log n-Real.log (largestPrime n)) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        (Real.log n/L)*max 0 (Real.log (largestPrime n)+Real.log n-2*L) := by
  by_cases hs : Squarefree n
  · apply coefficient_four_signed_gap hs hc (largestPrime_mem_of_four hc) _ hL hLhi hLlo
    intro p hp
    have hn : n.primeFactors.Nonempty := ⟨p,hp⟩
    have hmax : p ≤ largestPrime n := by
      rw [largestPrime,dif_pos hn]
      exact Finset.le_max' _ _ hp
    exact Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      (by exact_mod_cast hmax)
  · have hz : SquarefreeVaughanLogSource.coefficient L n = 0 := by
      simp [SquarefreeVaughanLogSource.coefficient,hs]
    rw [hz,Complex.zero_re]
    have ht := div_nonneg (Real.log_natCast_nonneg n) hL.le
    constructor
    · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (le_max_left _ _)
    · exact mul_nonneg ht (le_max_left _ _)

/-- The entire four-prime coefficient is zero on the exact moving
largest-prime transition, before any phase or allocation is applied. -/
theorem coefficient_four_eq_zero_at_gap {n : ℕ} (hc : n.primeFactors.card = 4)
    {L : ℝ} (hL : 0 < L) (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L)
    (hgap : Real.log (largestPrime n)+Real.log n = 2*L) :
    SquarefreeVaughanLogSource.coefficient L n = 0 := by
  have hb := actual_four_signed_gap hc hL hLhi hLlo
  rw [show 2*L-Real.log n-Real.log (largestPrime n) = 0 by linarith,
    show Real.log (largestPrime n)+Real.log n-2*L = 0 by linarith] at hb
  simp only [max_self,mul_zero] at hb
  apply Complex.ext
  · exact le_antisymm hb.2 hb.1
  · exact ZetaRieszCosineCarrier.coefficient_im_eq_zero L n

/-- The coefficient and its largest-prime gap never have opposite signs.
Either can vanish: this is not a claim of strict sign away from the gap. -/
theorem coefficient_four_sign {n : ℕ} (hc : n.primeFactors.card = 4)
    {L : ℝ} (hL : 0 < L) (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) :
    0 ≤ (Real.log (largestPrime n)+Real.log n-2*L)*
      (SquarefreeVaughanLogSource.coefficient L n).re := by
  have hb := actual_four_signed_gap hc hL hLhi hLlo
  by_cases hg : 0 ≤ Real.log (largestPrime n)+Real.log n-2*L
  · rw [max_eq_left (show 2*L-Real.log n-Real.log (largestPrime n) ≤ 0 by linarith),
      mul_zero] at hb
    exact mul_nonneg hg hb.1
  · rw [max_eq_left (le_of_not_ge hg),mul_zero] at hb
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hg) hb.2

/-- Rational bounds on the moving sign threshold throughout the original
core, once the already proved length bounds hold. -/
theorem gap_transition_bounds {N : ℕ} {L T : ℝ}
    (hLlo : (137/100 : ℝ)*N ≤ L) (hLhi : L ≤ (7/5 : ℝ)*N)
    (hTlo : (39/20 : ℝ)*N ≤ T) (hThi : T ≤ (203/100 : ℝ)*N) :
    (71/203 : ℝ)*T ≤ 2*L-T ∧ 2*L-T ≤ (17/39 : ℝ)*T := by
  constructor <;> linarith

/-- The signed interval of possible coefficients charges only an
oppositely signed observation. All actual positive credit is retained. -/
theorem real_gap_credit {c g s : ℝ} (hs : 0 ≤ s)
    (hlo : -s*max 0 (-g) ≤ c) (hhi : c ≤ s*max 0 g) (x : ℝ) :
    max (c*x) 0-s*max 0 (-g*x) ≤ c*x := by
  have hcost : max 0 (-c*x) ≤ s*max 0 (-g*x) := by
    by_cases hx : 0 ≤ x
    · have hm := mul_le_mul_of_nonneg_right hlo hx
      have hb : -c*x ≤ s*max 0 (-g)*x := by nlinarith only [hm]
      calc
        _ ≤ max 0 (s*max 0 (-g)*x) := max_le_max le_rfl hb
        _ = s*max 0 (-g*x) := by
          rw [max_eq_right (by positivity),mul_assoc,max_mul_of_nonneg _ _ hx,zero_mul]
    · have hx' : 0 ≤ -x := by linarith
      have hm := mul_le_mul_of_nonpos_right hhi (le_of_not_ge hx)
      have hb : -c*x ≤ s*max 0 g*(-x) := by nlinarith only [hm]
      calc
        _ ≤ max 0 (s*max 0 g*(-x)) := max_le_max le_rfl hb
        _ = s*max 0 (-g*x) := by
          rw [max_eq_right (by positivity),mul_assoc,max_mul_of_nonneg _ _ hx',zero_mul]
          congr 2
          ring
  apply sub_le_iff_le_add.mpr
  apply max_le
  · have := mul_nonneg hs (le_max_left 0 (-g*x))
    linarith
  · have := (le_max_right 0 (-c*x)).trans hcost
    linarith

open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation

/-- A signed lower bound for every actual four-prime residual atom.
Its full positive contribution remains; the debit retains the exact
largest-prime gap and the original cosine rather than `abs(cos)`. -/
theorem re_four_atom_ge_keep_positive (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hc : n.primeFactors.card = 4) {L : ℝ} (hL : 0 < L)
    (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) (y : ℝ) :
    max (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re 0-
      weight A N n*(Real.log n/L)*
        max 0 (-(Real.log (largestPrime n)+Real.log n-2*L)*Real.cos (y*Real.log n)) ≤
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hb := actual_four_signed_gap hc hL hLhi hLlo
  have hg : 2*L-Real.log n-Real.log (largestPrime n) =
      -(Real.log (largestPrime n)+Real.log n-2*L) := by ring
  rw [hg] at hb
  have h := mul_le_mul_of_nonneg_left
    (real_gap_credit (div_nonneg (Real.log_natCast_nonneg n) hL.le) hb.1 hb.2
      (Real.cos (y*Real.log n))) (weight_nonneg A N n)
  rw [mul_sub,mul_max_of_nonneg _ _ (weight_nonneg A N n),mul_zero] at h
  simpa only [re_residual_atom,mul_assoc] using h

/-- Favorable phases of any four-prime label cost nothing, on either
side of the moving sign transition. -/
theorem re_four_atom_nonneg (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hc : n.primeFactors.card = 4) {L : ℝ} (hL : 0 < L)
    (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) (y : ℝ)
    (hphase : 0 ≤ (Real.log (largestPrime n)+Real.log n-2*L)*Real.cos (y*Real.log n)) :
    0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have h := re_four_atom_ge_keep_positive A N hc hL hLhi hLlo y
  rw [max_eq_left (show -(Real.log (largestPrime n)+Real.log n-2*L)*
    Real.cos (y*Real.log n) ≤ 0 by nlinarith only [hphase]),mul_zero,sub_zero] at h
  exact (le_max_right _ _).trans h

/-- The complete signed complement and every favorable four-prime term
remain in this actual finite-sum lower bound. -/
theorem re_sum_ge_four_credit (S A : Finset ℕ) (N : ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (hwindow : ∀ n ∈ S, n.primeFactors.card = 4 →
      L ≤ Real.log n ∧ 2*Real.log n ≤ 3*L) :
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    (∑ n ∈ S.filter (fun n => n.primeFactors.card ≠ 4), f n).re+
      ∑ n ∈ S.filter (fun n => n.primeFactors.card = 4),
        (max (f n).re 0-weight A N n*(Real.log n/L)*
          max 0 (-(Real.log (largestPrime n)+Real.log n-2*L)*Real.cos (y*Real.log n))) ≤
      (∑ n ∈ S, f n).re := by
  dsimp only
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hb := Finset.sum_le_sum (s := S.filter (fun n => n.primeFactors.card = 4))
    (fun n hn => re_four_atom_ge_keep_positive A N (Finset.mem_filter.mp hn).2 hL
      (hwindow n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2).1
      (hwindow n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2).2 y)
  have he := congrArg Complex.re (Finset.sum_filter_add_sum_filter_not S
    (fun n => n.primeFactors.card = 4) f)
  simp only [Complex.add_re,Complex.re_sum] at he
  rw [Complex.re_sum,Complex.re_sum]
  dsimp [f] at he
  linarith

open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint

/-- The literal length and core window discharge all geometric premises
for the whole four-prime class. The original allocation, phase and
signed non-four-prime complement are unchanged. This is a comparison
with an explicit unpaid signed budget, not the terminal joint floor. -/
theorem eventually_re_core_ge_four_credit {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ),
      let L := SquarefreeVaughanLogSource.length u N
      let A := intermediatePrimes u N
      let S := coreBand u N K
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*((∑ n ∈ S.filter (fun n => n.primeFactors.card ≠ 4), f n).re+
        ∑ n ∈ S.filter (fun n => n.primeFactors.card = 4),
          (max (f n).re 0-weight A N n*(Real.log n/L)*
            max 0 (-(Real.log (largestPrime n)+Real.log n-2*L)*Real.cos (y*Real.log n)))) ≤
        ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200)
    (hsource.trans (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(137/200 : ℝ))))
  filter_upwards [hL,eventually_ge_atTop (2 : ℕ)] with N hlow hN K y
  have hupp : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) N]
  have hwindow (n : ℕ) (hn : n ∈ coreBand u N K) (_hc : n.primeFactors.card = 4) :
      SquarefreeVaughanLogSource.length u N ≤ Real.log n ∧
        2*Real.log n ≤ 3*SquarefreeVaughanLogSource.length u N := by
    have hw := (Finset.mem_filter.mp hn).2
    constructor <;> nlinarith [hw.1,hw.2,Nat.cast_nonneg (α := ℝ) N]
  have hb := re_sum_ge_four_credit (coreBand u N K) (intermediatePrimes u N) N
    (SquarefreeVaughanLogSource.length_pos u N) y hwindow
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  simpa only [coreResponse,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using hm

end
end RiemannGaussian.ZetaRieszFourPrimeFloor
