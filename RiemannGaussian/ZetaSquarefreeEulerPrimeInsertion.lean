/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerQuadratic
import RiemannGaussian.ZetaRoughPrimeLogLcmBound
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Prime insertion and the derivative of the full Euler matrix

Inserting a small prime into every lcm entry has two exact parts: a
common local factor and the derivative of the complete complex matrix.
The latter cancels in the large-prime logarithmic response. No matrix
entry or divisor channel is replaced by its absolute value here.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius LSeries.notation

/-- At a prime, the marked weight is the literal local Euler factor. -/
theorem atom_prime {p : ℕ} (hp : p.Prime) (s : ℂ) :
    atom s p = zetaPrimeFeature s p / (1 + zetaPrimeFeature s p) := by
  rw [atom, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
    Finset.prod_singleton]

private theorem local_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    1 + zetaPrimeFeature s p ≠ 0 := by
  have h := atom_ne_zero hs hp.ne_zero
  rw [atom_prime hp] at h
  exact (div_ne_zero_iff.mp h).2

private theorem feature_hasDerivAt (s : ℂ) (n : ℕ) :
    HasDerivAt (fun z ↦ zetaPrimeFeature z n)
      (-(Real.log n : ℂ) * zetaPrimeFeature s n) s := by
  have h := (((hasDerivAt_id s).mul_const (Real.log n : ℂ)).neg).cexp
  convert! h using 1
  all_goals simp only [zetaPrimeFeature, Pi.neg_apply, id_eq, one_mul]
  ring

/-- Differentiating one marked prime preserves its complementary
local factor. This exact factor is needed for the insertion identity. -/
theorem atom_prime_hasDerivAt {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z ↦ atom z p)
      (-(Real.log p : ℂ) * atom s p * (1 - atom s p)) s := by
  have h := (feature_hasDerivAt s p).div ((hasDerivAt_const s 1).add (feature_hasDerivAt s p))
    (local_ne_zero hp hs)
  convert! h using 1
  · funext z
    exact atom_prime hp z
  · simp only [atom_prime hp, Pi.add_apply, zero_add]
    field_simp [local_ne_zero hp hs]
    ring

/-- Every mark is a finite product of its prime atoms. -/
theorem atom_eq_prod_prime_atoms {P : ℕ} (hP : P ≠ 0) (s : ℂ) :
    atom s P = ∏ p ∈ P.primeFactors, atom s p := by
  rw [atom, ArithmeticFunction.prodPrimeFactors_apply hP]
  exact Finset.prod_congr rfl (fun p hp ↦ (atom_prime (Nat.prime_of_mem_primeFactors hp) s).symm)

/-- The logarithmic derivative keeps each prime of the mark, with
its full complex complementary local factor. -/
theorem atom_hasDerivAt {P : ℕ} (hP : P ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z ↦ atom z P)
      (-(atom s P * ∑ p ∈ P.primeFactors, (Real.log p : ℂ) * (1 - atom s p))) s := by
  have hd : ∀ p ∈ P.primeFactors, DifferentiableAt ℂ (fun z ↦ atom z p) s :=
    fun p hp ↦ (atom_prime_hasDerivAt (Nat.prime_of_mem_primeFactors hp) hs).differentiableAt
  have hn : ∀ p ∈ P.primeFactors, atom s p ≠ 0 :=
    fun p hp ↦ atom_ne_zero hs (Nat.prime_of_mem_primeFactors hp).ne_zero
  have he : (fun z ↦ atom z P) = fun z ↦ ∏ p ∈ P.primeFactors, atom z p := by
    funext z
    exact atom_eq_prod_prime_atoms hP z
  have hdiff : DifferentiableAt ℂ (fun z ↦ atom z P) s := by
    rw [he]
    exact .fun_finsetProd hd
  have hl := logDeriv_prod hn hd
  rw [← he, logDeriv_apply] at hl
  have hlocal (p : ℕ) (hp : p ∈ P.primeFactors) :
      logDeriv (fun z ↦ atom z p) s = -(Real.log p : ℂ) * (1 - atom s p) := by
    rw [logDeriv_apply, (atom_prime_hasDerivAt (Nat.prime_of_mem_primeFactors hp) hs).deriv]
    field_simp [hn p hp]
  have he' : deriv (fun z ↦ atom z P) s =
      -(atom s P * ∑ p ∈ P.primeFactors, (Real.log p : ℂ) * (1 - atom s p)) := by
    rw [Finset.sum_congr rfl hlocal] at hl
    have hv := (div_eq_iff (atom_ne_zero hs hP)).mp hl
    rw [hv]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  exact he' ▸ hdiff.hasDerivAt

/-- A prime insertion preserves a marked prime already present and
otherwise contributes its single new local factor. -/
theorem atom_prime_insertion {p P : ℕ} (hp : p.Prime) (s : ℂ) :
    atom s (Nat.lcm p P) =
      atom s P * (atom s p + if p ∣ P then 1 - atom s p else 0) := by
  by_cases hd : p ∣ P
  · rw [Nat.lcm_eq_right hd, if_pos hd]
    ring
  · have hc : p.Coprime P := hp.coprime_iff_not_dvd.mpr hd
    rw [hc.lcm_eq_mul, (atom_multiplicative s).map_mul_of_coprime hc, if_neg hd]
    ring

/-- The complete prime-inserted bilinear Euler matrix. -/
def insertion (T : Finset ℕ) (w v : ℕ → ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ T, ∑ e ∈ T, w d * v e * atom s (Nat.lcm p (Nat.lcm d e))

/-- The finite logarithmic sum of local prime factors, retaining
all their phases and excluding the original sieve primes. -/
def smallPrimeSum (D : ℕ) (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ zetaSquarePrimesThrough D \ S, (Real.log p : ℂ) * atom s p

/-- The prime-logarithmic insertion into every entry of the full matrix. -/
def smallInsertion (D : ℕ) (S T : Finset ℕ) (w v : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ p ∈ zetaSquarePrimesThrough D \ S, (Real.log p : ℂ) * insertion T w v p s

/-- The small-prime insertion into a complete mark is its common
prime sum minus the full derivative of that mark. -/
theorem atom_small_insertion (D : ℕ) (S : Finset ℕ) {P : ℕ} (hP : P ≠ 0)
    (hPD : ∀ p ∈ P.primeFactors, p ≤ D) (hPS : ∀ p ∈ P.primeFactors, p ∉ S)
    {s : ℂ} (hs : 0 < s.re) :
    (∑ p ∈ zetaSquarePrimesThrough D \ S, (Real.log p : ℂ) * atom s (Nat.lcm p P)) =
      atom s P * smallPrimeSum D S s - deriv (fun z ↦ atom z P) s := by
  let A := zetaSquarePrimesThrough D \ S
  have hAprime (p : ℕ) (hp : p ∈ A) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
  have he : A.filter (fun p ↦ p ∣ P) = P.primeFactors := by
    ext p
    constructor
    · intro hp
      exact Nat.mem_primeFactors.mpr ⟨hAprime p (Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2, hP⟩
    · intro hp
      refine Finset.mem_filter.mpr ⟨?_, Nat.dvd_of_mem_primeFactors hp⟩
      apply Finset.mem_sdiff.mpr
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primeFactors hp).pos, hPD p hp⟩,
          Nat.prime_of_mem_primeFactors hp⟩, hPS p hp⟩
  calc
    _ = atom s P * smallPrimeSum D S s + atom s P *
        ∑ p ∈ A, if p ∣ P then (Real.log p : ℂ) * (1 - atom s p) else 0 := by
      simp only [smallPrimeSum, A, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [atom_prime_insertion (hAprime p hp)]
      by_cases h : p ∣ P <;> simp [h] <;> ring
    _ = atom s P * smallPrimeSum D S s + atom s P *
        ∑ p ∈ P.primeFactors, (Real.log p : ℂ) * (1 - atom s p) := by
      rw [← Finset.sum_filter, he]
    _ = _ := by
      rw [(atom_hasDerivAt hP hs).deriv]
      ring

/-- Differentiation keeps the complete finite bilinear matrix. -/
theorem form_hasDerivAt (T : Finset ℕ) (hT : ∀ d ∈ T, d ≠ 0) (w v : ℕ → ℂ)
    {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (form T w v)
      (∑ d ∈ T, ∑ e ∈ T, w d * v e * deriv (fun z ↦ atom z (Nat.lcm d e)) s) s := by
  have h (d : ℕ) (hd : d ∈ T) (e : ℕ) (he : e ∈ T) :=
    (atom_hasDerivAt (Nat.lcm_pos (Nat.pos_of_ne_zero (hT d hd))
      (Nat.pos_of_ne_zero (hT e he))).ne' hs).differentiableAt.hasDerivAt.const_mul (w d * v e)
  exact HasDerivAt.fun_sum (fun d hd ↦ HasDerivAt.fun_sum (fun e he ↦ h d hd e he))

/-- Inserting every small prime gives the common prime sum times the
full matrix minus its full derivative. This retains every signed pair
and every shared-prime overlap until the cancellation is used. -/
theorem smallInsertion_eq (D : ℕ) (S T : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    (hT : ∀ d ∈ T, Squarefree d ∧ d ≤ D ∧ (¬∃ a ∈ S, a ∣ d)) (w v : ℕ → ℂ)
    {s : ℂ} (hs : 0 < s.re) :
    smallInsertion D S T w v s = form T w v s * smallPrimeSum D S s - deriv (form T w v) s := by
  have hlocal (d : ℕ) (hd : d ∈ T) (e : ℕ) (he : e ∈ T) :
      (∑ p ∈ zetaSquarePrimesThrough D \ S,
        (Real.log p : ℂ) * atom s (Nat.lcm p (Nat.lcm d e))) =
        atom s (Nat.lcm d e) * smallPrimeSum D S s - deriv (fun z ↦ atom z (Nat.lcm d e)) s := by
    have hL := lcm_squarefree (hT d hd).1 (hT e he).1
    apply atom_small_insertion D S hL.ne_zero _ (lcm_rough S hS (hT d hd).2.2 (hT e he).2.2) hs
    intro p hp
    have hdiv := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.lcm_dvd_mul d e)
    rcases (Nat.prime_of_mem_primeFactors hp).dvd_mul.mp hdiv with h | h
    · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (hT d hd).1.ne_zero) h).trans (hT d hd).2.1
    · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (hT e he).1.ne_zero) h).trans (hT e he).2.1
  calc
    _ = ∑ d ∈ T, ∑ e ∈ T, (w d * v e) *
        ∑ p ∈ zetaSquarePrimesThrough D \ S,
          (Real.log p : ℂ) * atom s (Nat.lcm p (Nat.lcm d e)) := by
      simp only [smallInsertion, insertion, Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_comm)]
      exact Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_congr rfl (fun _ _ ↦
        Finset.sum_congr rfl (fun _ _ ↦ by ring)))
    _ = ∑ d ∈ T, ∑ e ∈ T, (w d * v e) *
        (atom s (Nat.lcm d e) * smallPrimeSum D S s - deriv (fun z ↦ atom z (Nat.lcm d e)) s) := by
      exact Finset.sum_congr rfl (fun d hd ↦ Finset.sum_congr rfl (fun e he ↦ by rw [hlocal d hd e he]))
    _ = _ := by
      rw [(form_hasDerivAt T (fun d hd ↦ (hT d hd).1.ne_zero) w v hs).deriv]
      simp only [form, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]

/-- The prime-weighted arithmetic coefficient has the exact triple
incidence expansion, with excluded sieve primes vanishing pointwise. -/
theorem small_coefficient_eq_insertions (D : ℕ) (S T : Finset ℕ) (w v : ℕ → ℂ) (n : ℕ) :
    coefficient S T w v n * RoughPrimeLog.smallLog D n =
      ∑ p ∈ zetaSquarePrimesThrough D \ S, ∑ d ∈ T, ∑ e ∈ T,
        (w d * v e * (Real.log p : ℂ)) *
          RoughSquarefreeBare.coefficient S (Nat.lcm p (Nat.lcm d e)) n := by
  rw [RoughPrimeLog.smallLog, Finset.mul_sum]
  have hrestrict : (∑ p ∈ zetaSquarePrimesThrough D,
      coefficient S T w v n * (if p ∣ n then (Real.log p : ℂ) else 0)) =
      ∑ p ∈ zetaSquarePrimesThrough D \ S,
        coefficient S T w v n * (if p ∣ n then (Real.log p : ℂ) else 0) := by
    symm
    apply Finset.sum_subset Finset.sdiff_subset
    intro p hp hpnot
    have hpS : p ∈ S := by simpa only [Finset.mem_sdiff, hp, true_and, not_not] using hpnot
    by_cases hpn : p ∣ n
    · have hr : ∃ a ∈ S, a ∣ n := ⟨p, hpS, hpn⟩
      simp [coefficient, RoughSquarefreeBare.coefficient, hr]
    · simp [hpn]
  rw [hrestrict]
  apply Finset.sum_congr rfl
  intro p _
  rw [coefficient_eq_lcm_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hsf : Squarefree n <;> by_cases hrough : ∃ a ∈ S, a ∣ n <;>
    by_cases hp : p ∣ n <;> by_cases hd : Nat.lcm d e ∣ n <;>
      simp [RoughSquarefreeBare.coefficient, Nat.lcm_dvd_iff, hsf, hrough, hp, hd]

/-- The complete small-prime insertion is the genuine L-series of
the original weighted coefficient, retaining every matrix entry. -/
theorem LSeriesHasSum_smallInsertion (D : ℕ) (S T : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime)
    (hT : ∀ d ∈ T, Squarefree d ∧ (¬∃ a ∈ S, a ∣ d)) (w v : ℕ → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ coefficient S T w v n * RoughPrimeLog.smallLog D n) s
      (base S s * smallInsertion D S T w v s) := by
  have hm (p : ℕ) (hp : p ∈ zetaSquarePrimesThrough D \ S)
      (d : ℕ) (hd : d ∈ T) (e : ℕ) (he : e ∈ T) :
      LSeriesHasSum (RoughSquarefreeBare.coefficient S (Nat.lcm p (Nat.lcm d e))) s
        (base S s * atom s (Nat.lcm p (Nat.lcm d e))) := by
    have hpp : p.Prime := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
    have hpS : p ∉ S := (Finset.mem_sdiff.mp hp).2
    have hL := lcm_squarefree hpp.squarefree (lcm_squarefree (hT d hd).1 (hT e he).1)
    have hLS : ∀ a ∈ (Nat.lcm p (Nat.lcm d e)).primeFactors, a ∉ S := by
      intro a ha haS
      have haP := hS a haS
      have had := (Nat.dvd_of_mem_primeFactors ha).trans (Nat.lcm_dvd_mul p (Nat.lcm d e))
      rcases haP.dvd_mul.mp had with haDiv | haDiv
      · have hap : a = p := (Nat.prime_dvd_prime_iff_eq haP hpp).mp haDiv
        exact hpS (hap ▸ haS)
      · rcases haP.dvd_mul.mp (haDiv.trans (Nat.lcm_dvd_mul d e)) with haDiv | haDiv
        · exact (hT d hd).2 ⟨a, haS, haDiv⟩
        · exact (hT e he).2 ⟨a, haS, haDiv⟩
    convert LSeriesHasSum_markedSquarefreeEuler S hS hL hLS hs using 1
    rw [multiplier_eq S hL hLS, base]
    ring
  have h := LSeriesHasSum.sum (S := zetaSquarePrimesThrough D \ S) (fun p hp ↦
    LSeriesHasSum.sum (S := T) (fun d hd ↦ LSeriesHasSum.sum (S := T)
      (fun e he ↦ (hm p hp d hd e he).smul (w d * v e * (Real.log p : ℂ)))))
  convert h using 1
  · funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact small_coefficient_eq_insertions D S T w v n
  · simp only [smallInsertion, insertion, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_congr rfl (fun _ _ ↦
      Finset.sum_congr rfl (fun _ _ ↦ by ring)))

/-- The exact small-prime correction in the current RH carrier is
the common quotient times the matrix insertion identity. -/
theorem LSeriesHasSum_actualSmall (D : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (RoughPrimeLog.smallCoefficient D S) s
      (base S s * (form (eligible D S) (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) s *
        smallPrimeSum D S s - deriv (form (eligible D S) (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ))) s)) := by
  have he : RoughPrimeLog.smallCoefficient D S = fun n ↦
      coefficient S (eligible D S) (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) n * RoughPrimeLog.smallLog D n := by
    funext n
    have h := congrFun (coefficient_eq_eligible S (Finset.Icc 1 D)
      (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ))) n
    change _ = coefficient S (eligible D S) _ _ n at h
    rw [← h, coefficient_moebius_self]
    rfl
  rw [he]
  have hT : ∀ d ∈ eligible D S, Squarefree d ∧ (¬∃ a ∈ S, a ∣ d) :=
    fun _ hd ↦ (Finset.mem_filter.mp hd).2
  have hb : ∀ d ∈ eligible D S, Squarefree d ∧ d ≤ D ∧ (¬∃ a ∈ S, a ∣ d) := by
    intro d hd
    exact ⟨(hT d hd).1, (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2, (hT d hd).2⟩
  have h := LSeriesHasSum_smallInsertion D S (eligible D S) hS hT
    (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) hs
  rwa [smallInsertion_eq D S _ hS hb _ _ (by linarith)] at h

private theorem base_analyticAt (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ (base S) s := by
  have hs2 : 1 < (2 * s).re := by norm_num; linarith
  have hn1 : s ≠ 1 := by intro h; subst s; norm_num at hs
  have hn2 : 2 * s ≠ 1 := by
    intro h
    rw [h] at hs2
    norm_num at hs2
  have hnum := analyticOn_riemannZeta s (by simpa using hn1)
  have hden := (analyticOn_riemannZeta (2 * s) (by simpa using hn2)).comp
    (analyticAt_const.mul analyticAt_id)
  have hQ : AnalyticAt ℂ squarefreeEulerResponse s :=
    hnum.div hden (riemannZeta_ne_zero_of_one_lt_re hs2)
  have he : base S = fun z ↦ squarefreeEulerMultiplier S 1 z * squarefreeEulerResponse z := by
    funext z
    simp [base, squarefreeEulerMultiplier, zetaPrimeFeature]
  rw [he]
  exact (analyticAt_squarefreeEulerMultiplier S hS 1 (by linarith)).mul hQ

/-- The diagonal and full matrix have the same derivative locally.
The quotient and finite matrix remain separate analytic factors. -/
theorem deriv_diagonal_eq (D : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    (w v : ℕ → ℂ) {s : ℂ} (hs : 1 < s.re) :
    deriv (diagonal D S w v) s =
      deriv (base S) s * form (eligible D S) w v s +
        base S s * deriv (form (eligible D S) w v) s := by
  have hT : ∀ d ∈ eligible D S, Squarefree d ∧ d ≤ D := by
    intro d hd
    exact ⟨(Finset.mem_filter.mp hd).2.1, (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2⟩
  have he : diagonal D S w v =ᶠ[𝓝 s] (fun z ↦ base S z * form (eligible D S) w v z) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds
      (show 0 < s.re by linarith)] with z hz
    rw [form_eq_divisor_coordinates _ D hT w v hz]
    rfl
  rw [he.deriv_eq]
  exact deriv_mul (base_analyticAt S hS hs).differentiableAt
    (form_hasDerivAt _ (fun d hd ↦ (hT d hd).1.ne_zero) w v (by linarith)).differentiableAt

/-- The exact large-prime expression has one finite complex matrix
factor. Its derivative has cancelled against the small-prime insertion;
the original ordinary-prime tail remains explicit. This expression is
identified with the arithmetic series in the Euler half-plane below. -/
def largeResponse (D : ℕ) (S : Finset ℕ) (s : ℂ) : ℂ :=
  (-deriv (base S) s - base S s * smallPrimeSum D S s) *
    form (eligible D S) (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) s -
      primeCorrection D S s

/-- In the literal remaining large-prime arithmetic carrier, the
derivative of the entire finite matrix cancels exactly. This is a
convergent series identity for the actual coefficients, not a norm bound
or an assumed cancellation hypothesis. -/
theorem LSeriesHasSum_largeResponse (D : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (RoughPrimeLog.coefficient D S) s (largeResponse D S s) := by
  have h := (LSeriesHasSum_squareCoefficient D S hS hs).sub
    (LSeriesHasSum_actualSmall D S hS hs)
  convert h using 1
  · funext n
    exact RoughPrimeLog.coefficient_eq_square_sub_small D S n
  · rw [deriv_diagonal_eq D S hS _ _ hs]
    unfold largeResponse
    ring

/-- The cancellation continues to every factorial moment of the
original large-prime sum. No derivative of a finite cutoff has been
discarded or treated as constant during this transport. -/
theorem hasSum_large_moment (D : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ RoughPrimeLog.coefficient D S n *
      ((Real.log n : ℂ) ^ N / (N.factorial : ℂ)) * zetaPrimeFeature s n)
      (signedTaylorMoment N (largeResponse D S) s) := by
  have hab : LSeries.abscissaOfAbsConv (RoughPrimeLog.coefficient D S) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro y hy
    exact (LSeriesHasSum_largeResponse D S hS (by simpa using hy)).LSeriesSummable
  have he : largeResponse D S =ᶠ[𝓝 s] LSeries (RoughPrimeLog.coefficient D S) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (LSeriesHasSum_largeResponse D S hS hz).LSeries_eq.symm
  rw [signedTaylorMoment_congr N he]
  exact hasSum_signedTaylorMoment_LSeries _ (by simp [RoughPrimeLog.coefficient])
    (lt_of_le_of_lt hab (by exact_mod_cast hs)) N

/-- The complete original polynomial-filtered large-prime arithmetic
sum equals the same moments of the factored expression, with the signed
complex matrix and prime correction both retained. -/
theorem hasSum_large_filter (D : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    (p : Polynomial ℂ) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ RoughPrimeLog.coefficient D S n * zetaPrimeFilterKernel p N s n)
      (zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k (largeResponse D S) s) N) := by
  have h := hasSum_sum (s := p.support) (fun k _ ↦
    (hasSum_large_moment D S hS (N + k) hs).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ ↦ by ring)

/-- The original arithmetic response is exactly recovered from the
factored expression at every polynomial and moment order. -/
theorem large_filter_eq (D : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    (p : Polynomial ℂ) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    RoughPrimeLog.response p D S N s =
      zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k (largeResponse D S) s) N :=
  (hasSum_large_filter D S hS p N hs).tsum_eq

/-- The currently used normalized large-prime source, at every common
divisor and prime cutoff, is the identical filtered Euler expression.
The selected zero, original sieve, polynomial and normalization are unchanged. -/
theorem normalized_large_source_eq (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N D : ℕ) :
    RoughPrimeLogLcm.normalizedLargeResponse rho hrho N D =
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaMomentSequenceFilter (zetaRightHalfPoleJetFilter rho hrho)
          (fun k ↦ signedTaylorMoment k
            (largeResponse D (zetaRightHalfPrimePatternPrimes rho N))
              (3 / 2 + I * rho.1.im)) N := by
  rw [RoughPrimeLogLcm.normalizedLargeResponse, large_filter_eq D _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) _ _ (by norm_num)]

end
end RiemannGaussian.SquarefreeEulerQuadratic
