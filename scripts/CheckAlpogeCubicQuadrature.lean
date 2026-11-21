import CheckAlpogeCubicWindowMass
import AlpogeIntegerPrimeBand
import Mathlib.NumberTheory.AbelSummation

/-! # Chebyshev quadrature for the averaged cubic prime tail -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real MeasureTheory

open scoped ArithmeticFunction.vonMangoldt

/-- The cumulative sum of an arithmetic coefficient, including the right endpoint. -/
def coefficientPrefix (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Icc 0 ⌊t⌋₊, c j

private def primeLog (p : ℕ) : ℝ := if p.Prime then log p else 0

private theorem primeLog_sum (t : ℝ) : coefficientPrefix primeLog t = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

private theorem floor_div_nat (M : ℕ) {j : ℕ} (hj : 0 < j) :
    ⌊(M:ℝ)/j⌋₊ = M/j := by
  have hjR : 0 < (j:ℝ) := by exact_mod_cast hj
  have h1 := Nat.div_mul_le_self M j
  have h2 := Nat.lt_mul_div_succ M hj
  apply (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg M) hjR.le)).mpr
  constructor
  · exact (le_div_iff₀ hjR).mpr (by exact_mod_cast h1)
  · apply (div_lt_iff₀ hjR).mpr
    rw [mul_comm]
    exact_mod_cast h2

theorem coefficientPrefix_sub (c : ℕ → ℝ) {D X : ℕ} (hDX : D ≤ X) :
    coefficientPrefix c X - coefficientPrefix c D = ∑ p ∈ Ioc D X, c p := by
  simp only [coefficientPrefix, Nat.floor_natCast]
  rw [show Icc 0 X = Icc 0 D ∪ Ioc D X by
    ext p
    simp only [mem_Icc, zero_le, true_and, mem_union, mem_Ioc]
    omega]
  rw [sum_union]
  · ring
  · exact disjoint_left.mpr fun p hp hq => not_lt_of_ge (mem_Icc.mp hp).2 (mem_Ioc.mp hq).1

private theorem coefficient_quotient_sum (c : ℕ → ℝ) {M D : ℕ} (hD : 0 < D) :
    ∑ p ∈ Ioc D M, c p * (M/p:ℕ) =
      ∑ j ∈ Icc 1 (M/D), (coefficientPrefix c ((M:ℝ)/j) - coefficientPrefix c D) := by
  let J := Icc 1 (M/D)
  calc
    _ = ∑ p ∈ Ioc D M, ∑ j ∈ J, if j*p ≤ M then c p else 0 := by
      apply sum_congr rfl
      intro p hp
      have hDp := (mem_Ioc.mp hp).1
      have hp0 := hD.trans hDp
      have hdiv : M/p ≤ M/D := Nat.div_le_div_left hDp.le hD
      rw [← sum_filter, show J.filter (fun j => j*p ≤ M) = Icc 1 (M/p) by
        ext j
        simp only [J, mem_filter, mem_Icc, ← Nat.le_div_iff_mul_le hp0]
        omega]
      simp [Nat.card_Icc, nsmul_eq_mul, mul_comm]
    _ = ∑ j ∈ J, ∑ p ∈ Ioc D M, if j*p ≤ M then c p else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      obtain ⟨hj0,hjM⟩ := mem_Icc.mp hj
      have hjp : 0 < j := by omega
      have hDj : D ≤ M/j := (Nat.le_div_iff_mul_le hjp).mpr
        (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hD).mp hjM)
      have hcut : M/j ≤ M := Nat.div_le_self ..
      have he : coefficientPrefix c ((M:ℝ)/j) = coefficientPrefix c (M/j:ℕ) := by
        simp only [coefficientPrefix, floor_div_nat M hjp, Nat.floor_natCast]
      rw [he, coefficientPrefix_sub c hDj, ← sum_filter]
      congr 1
      ext p
      have hcell : j*p ≤ M ↔ p ≤ M/j := by
        rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hjp).symm
      simp only [mem_filter, mem_Ioc]
      constructor
      · rintro ⟨⟨hDp,_⟩,h⟩
        exact ⟨hDp,hcell.mp h⟩
      · rintro ⟨hDp,hp⟩
        exact ⟨⟨hDp,hp.trans hcut⟩,hcell.mpr hp⟩

/-- The quotient in each reciprocal weight can be counted by transposing
the finite array of prime rows and positive integer multiples. -/
theorem prime_quotient_sum {M D : ℕ} (hD : 0 < D) :
    ∑ p ∈ (Ioc D M).filter Nat.Prime, log p * (M/p:ℕ) =
      ∑ j ∈ Icc 1 (M/D), (Chebyshev.theta ((M:ℝ)/j) - Chebyshev.theta D) := by
  rw [sum_filter]
  simp_rw [← primeLog_sum]
  rw [← coefficient_quotient_sum primeLog hD]
  exact sum_congr rfl fun p _ => by by_cases hp : p.Prime <;> simp [primeLog,hp]

private theorem inv_deriv_integrable {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (deriv (fun x : ℝ => x⁻¹)) (Set.Icc a b) := by
  have h : ContinuousOn (fun x : ℝ => -(x^2)⁻¹) (Set.Icc a b) :=
    ((continuousOn_id.pow 2).inv₀ fun x hx => pow_ne_zero _ (ha.trans_le hx.1).ne').neg
  exact h.integrableOn_Icc.congr_fun
    (fun x hx => (hasDerivAt_inv (ha.trans_le hx.1).ne').deriv.symm) measurableSet_Icc

theorem coefficient_kernel_integrable (c : ℕ → ℝ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun x => coefficientPrefix c x / x^2) volume a b := by
  have h := integrableOn_mul_sum_Icc c (m := 0) ha.le (inv_deriv_integrable (b := b) ha)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply h.neg.congr_fun _ measurableSet_Icc
  intro x hx
  change -(deriv (fun t : ℝ => t⁻¹) x * coefficientPrefix c x) = _
  rw [(hasDerivAt_inv (ha.trans_le hx.1).ne').deriv]
  ring

private theorem theta_kernel_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => Chebyshev.theta x / x^2) volume a b := by
  simpa only [primeLog_sum] using coefficient_kernel_integrable primeLog ha hab

theorem coefficient_reciprocal_sum (c : ℕ → ℝ) {M D : ℕ}
    (hD : 0 < D) (hDM : D ≤ M) :
    ∑ p ∈ Ioc D M, c p / p =
      coefficientPrefix c M / M - coefficientPrefix c D / D +
        ∫ x in (D:ℝ)..(M:ℝ), coefficientPrefix c x / x^2 := by
  have hD0 : (0:ℝ) < D := by exact_mod_cast hD
  have hle : (D:ℝ) ≤ M := by exact_mod_cast hDM
  have h := sum_mul_eq_sub_sub_integral_mul (f := fun x : ℝ => x⁻¹) c hD0.le hle
    (fun x hx => (hasDerivAt_inv (hD0.trans_le hx.1).ne').differentiableAt)
    (inv_deriv_integrable hD0)
  have hint : (∫ x in Set.Ioc (D:ℝ) M, deriv (fun t : ℝ => t⁻¹) x * coefficientPrefix c x) =
      ∫ x in Set.Ioc (D:ℝ) M, -(coefficientPrefix c x / x^2) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    change deriv (fun t : ℝ => t⁻¹) x * coefficientPrefix c x = _
    rw [(hasDerivAt_inv (hD0.trans hx.1).ne').deriv]
    ring
  change (∑ p ∈ Ioc ⌊(D:ℝ)⌋₊ ⌊(M:ℝ)⌋₊, (p:ℝ)⁻¹*c p) =
    (M:ℝ)⁻¹*coefficientPrefix c M - (D:ℝ)⁻¹*coefficientPrefix c D -
      ∫ x in Set.Ioc (D:ℝ) M, deriv (fun t : ℝ => t⁻¹) x * coefficientPrefix c x at h
  rw [Nat.floor_natCast, Nat.floor_natCast, hint, integral_neg, ← intervalIntegral.integral_of_le hle,
    sub_neg_eq_add] at h
  simpa only [div_eq_mul_inv,mul_comm] using h

/-- The sum at quotient samples minus the integral with reciprocal weights. -/
def tailQuadratureSumIntegral (M D : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∑ j ∈ Icc 1 (M/D), f ((M:ℝ)/j)) -
    (M:ℝ)*(∫ x in (D:ℝ)..(M:ℝ), f x / x^2)

/-- The quadrature with the endpoint half-weight at the cutoff D. -/
def tailQuadrature (M D : ℕ) (f : ℝ → ℝ) : ℝ :=
  tailQuadratureSumIntegral M D f - (((M/D:ℕ):ℝ) + 1/2 - (M:ℝ)/D)*f D

/-- The sum and integral together are exactly a finite weighted sum
of the underlying coefficients. The weights, including the low cutoff
coefficient, all lie between zero and one. -/
theorem coefficient_tailQuadratureSumIntegral (c : ℕ → ℝ) {M D : ℕ}
    (hD : 0 < D) (hDM : D ≤ M) :
    tailQuadratureSumIntegral M D (coefficientPrefix c) =
      weight M D * coefficientPrefix c D + ∑ p ∈ Ioc D M, c p * weight M p := by
  have hM : (M:ℝ) ≠ 0 := by exact_mod_cast (hD.trans_le hDM).ne'
  have hweight (p : ℕ) (hp : 0 < p) :
      weight M p = 1 + ((M/p:ℕ):ℝ) - (M:ℝ)/p := by
    have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have hmod : ((M%p:ℕ):ℝ) + (p:ℝ)*(M/p:ℕ) = M := by exact_mod_cast Nat.mod_add_div M p
    have hf : ((M%p:ℕ):ℝ)/p = (M:ℝ)/p - ((M/p:ℕ):ℝ) := by
      apply (div_eq_iff hp0).mpr
      rw [sub_mul,div_mul_cancel₀ _ hp0,mul_comm ((M/p:ℕ):ℝ)]
      linarith only [hmod]
    rw [weight,hf]
    ring
  have he : (∑ p ∈ Ioc D M, c p * weight M p) =
      (∑ p ∈ Ioc D M, c p) +
        (∑ p ∈ Ioc D M, c p * (M/p:ℕ)) -
        (M:ℝ)*(∑ p ∈ Ioc D M, c p / p) := by
    rw [Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    rw [hweight p (hD.trans (mem_Ioc.mp hp).1)]
    ring
  rw [he, ← coefficientPrefix_sub c hDM, coefficient_quotient_sum c hD,
    coefficient_reciprocal_sum c hD hDM, hweight D hD]
  simp only [sum_sub_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul, tailQuadratureSumIntegral]
  field_simp
  ring

/-- The high-prime tail and its low-prime half-weight are exactly the
quotient-cell quadrature of the Chebyshev counting function. -/
theorem theta_tailQuadrature {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    tailQuadrature M D Chebyshev.theta = Chebyshev.theta D/2 + upperPrimeSum M D := by
  have hcoeff : ((M/D:ℕ):ℝ) + 1/2 - (M:ℝ)/D = weight M D-1/2 := by
    have hD0 : (D:ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have hm : ((M%D:ℕ):ℝ)+(D:ℝ)*(M/D:ℕ)=M := by exact_mod_cast Nat.mod_add_div M D
    unfold weight
    field_simp
    nlinarith only [hm]
  have h := coefficient_tailQuadratureSumIntegral primeLog hD hDM
  have hfun : coefficientPrefix primeLog = Chebyshev.theta := funext primeLog_sum
  rw [hfun] at h
  rw [tailQuadrature, h, hcoeff, upperPrimeSum, sum_filter]
  have hs : (∑ p ∈ Ioc D M, primeLog p * weight M p) =
      ∑ p ∈ Ioc D M, if p.Prime then log p * weight M p else 0 := by
    apply sum_congr rfl
    intro p _
    by_cases hp : p.Prime <;> simp [primeLog,hp]
  rw [hs]
  ring

/-- Nonnegative coefficients remain nonnegative after the entire sum and
integral are combined. Each retained coefficient is counted at most once. -/
theorem coefficient_tailQuadratureSumIntegral_bounds (c : ℕ → ℝ)
    (hc : ∀ p, 0 ≤ c p) {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    0 ≤ tailQuadratureSumIntegral M D (coefficientPrefix c) ∧
      tailQuadratureSumIntegral M D (coefficientPrefix c) ≤ coefficientPrefix c M := by
  rw [coefficient_tailQuadratureSumIntegral c hD hDM]
  have hlo : 0 ≤ coefficientPrefix c D := sum_nonneg fun p _ => hc p
  refine ⟨add_nonneg (mul_nonneg (weight_mem hD).1 hlo)
    (sum_nonneg fun p hp => mul_nonneg (hc p) (weight_mem (hD.trans (mem_Ioc.mp hp).1)).1),?_⟩
  have hhi : ∑ p ∈ Ioc D M, c p*weight M p ≤ ∑ p ∈ Ioc D M, c p := by
    apply sum_le_sum
    intro p hp
    exact mul_le_of_le_one_right (hc p) (weight_mem (hD.trans (mem_Ioc.mp hp).1)).2
  rw [← coefficientPrefix_sub c hDM] at hhi
  linarith only [hhi, mul_le_of_le_one_left hlo (weight_mem (N := M) hD).2]

private theorem coefficientPrefix_sub_fun (a b : ℕ → ℝ) (x : ℝ) :
    coefficientPrefix (fun p => a p-b p) x = coefficientPrefix a x-coefficientPrefix b x := by
  simp only [coefficientPrefix, sum_sub_distrib]

private theorem psi_prefix : coefficientPrefix (fun p => Λ p) = Chebyshev.psi :=
  funext fun x => (Chebyshev.psi_eq_sum_Icc x).symm

/-- The contribution of proper prime powers to the combined expression
is nonnegative and bounded by their entire mass at the observation. -/
theorem psi_theta_tailQuadrature_bounds {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    0 ≤ tailQuadratureSumIntegral M D (fun x => Chebyshev.psi x-Chebyshev.theta x) ∧
      tailQuadratureSumIntegral M D (fun x => Chebyshev.psi x-Chebyshev.theta x) ≤
        Chebyshev.psi M-Chebyshev.theta M := by
  let c := fun p => Λ p-primeLog p
  have hc (p : ℕ) : 0 ≤ c p := by
    by_cases hp : p.Prime
    · simp [c,primeLog,hp,ArithmeticFunction.vonMangoldt_apply_prime hp]
    · change 0 ≤ Λ p-primeLog p
      rw [primeLog,ite_eq_right (fun h => (hp h).elim),sub_zero]
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hfun : coefficientPrefix c = fun x => Chebyshev.psi x-Chebyshev.theta x := by
    funext x
    rw [show coefficientPrefix c x = coefficientPrefix (fun p => Λ p) x -
      coefficientPrefix primeLog x from coefficientPrefix_sub_fun _ _ _, psi_prefix,primeLog_sum]
  simpa only [hfun] using coefficient_tailQuadratureSumIntegral_bounds c hc hD hDM

theorem tailQuadratureSumIntegral_sub (M D : ℕ) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable (fun x => f x/x^2) volume D M)
    (hg : IntervalIntegrable (fun x => g x/x^2) volume D M) :
    tailQuadratureSumIntegral M D (fun x => f x-g x) =
      tailQuadratureSumIntegral M D f-tailQuadratureSumIntegral M D g := by
  simp only [tailQuadratureSumIntegral, sum_sub_distrib, sub_div,
    intervalIntegral.integral_sub hf hg]
  ring

private def unitCoefficient (p : ℕ) : ℝ := if p = 0 then 0 else 1

private theorem unitCoefficient_prefix (x : ℝ) :
    coefficientPrefix unitCoefficient x = (⌊x⌋₊:ℝ) := by
  unfold coefficientPrefix
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
  have hs : ∑ p ∈ Ioc 0 ⌊x⌋₊, unitCoefficient p = ∑ _p ∈ Ioc 0 ⌊x⌋₊, (1:ℝ) := by
    apply sum_congr rfl
    intro p hp
    simp [unitCoefficient, (mem_Ioc.mp hp).1.ne']
  rw [hs]
  simp [unitCoefficient, Nat.card_Ioc]

private theorem id_kernel_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => x/x^2) volume a b :=
  (continuousOn_id.div (continuousOn_id.pow 2) fun _ hx =>
    pow_ne_zero 2 (ha.trans_le hx.1).ne').intervalIntegrable_of_Icc hab

private theorem inv_sq_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, (x^2)⁻¹) = a⁻¹-b⁻¹ := by
  have hInvCont : ContinuousOn (fun x : ℝ => (x^2)⁻¹) (Set.Icc a b) :=
    (continuousOn_id.pow 2).inv₀ fun _ hx => pow_ne_zero _ (ha.trans_le hx.1).ne'
  have hDeriv (x : ℝ) (hx : x ∈ Set.uIcc a b) :
      HasDerivAt (fun x : ℝ => -x⁻¹) ((x^2)⁻¹) x := by
    rw [Set.uIcc_of_le hab] at hx
    change HasDerivAt (-(fun y : ℝ => y⁻¹)) ((x^2)⁻¹) x
    simpa only [neg_neg] using (hasDerivAt_inv (ha.trans_le hx.1).ne').neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv (hInvCont.intervalIntegrable_of_Icc hab)]
  ring

/-- A uniform bound on the cumulative error is incurred only once per
quotient row, including the corresponding integral. -/
theorem tailQuadratureSumIntegral_abs_le {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M)
    {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : IntervalIntegrable (fun x => f x/x^2) volume D M)
    (h : ∀ x ∈ Set.Icc (D:ℝ) M, |f x| ≤ C) :
    |tailQuadratureSumIntegral M D f| ≤ 2*C*((M:ℝ)/D) := by
  have ha : 0 < (D:ℝ) := by exact_mod_cast hD
  have hab : (D:ℝ) ≤ M := by exact_mod_cast hDM
  have hq : ((M/D:ℕ):ℝ) ≤ (M:ℝ)/D := (le_div_iff₀ ha).mpr
    (by exact_mod_cast Nat.div_mul_le_self M D)
  have hsum : |∑ j ∈ Icc 1 (M/D), f ((M:ℝ)/j)| ≤ C*((M:ℝ)/D) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ j ∈ Icc 1 (M/D), C := by
        apply sum_le_sum
        intro j hj
        have hj1 : (1:ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
        have hj0 := zero_lt_one.trans_le hj1
        apply h
        constructor
        · apply (le_div_iff₀ hj0).mpr
          have hmul : D*j ≤ M := by
            rw [Nat.mul_comm]
            exact (Nat.le_div_iff_mul_le hD).mp (mem_Icc.mp hj).2
          exact_mod_cast hmul
        · exact div_le_self (Nat.cast_nonneg M) hj1
      _ ≤ _ := by
        simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
        exact (mul_le_mul_of_nonneg_right hq hC).trans_eq (mul_comm _ _)
  have hInvCont : ContinuousOn (fun x : ℝ => (x^2)⁻¹) (Set.Icc (D:ℝ) M) :=
    (continuousOn_id.pow 2).inv₀ fun _ hx => pow_ne_zero _ (ha.trans_le hx.1).ne'
  have hInt : |∫ x in (D:ℝ)..(M:ℝ), f x/x^2| ≤ C*(D:ℝ)⁻¹ := by
    apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
    have hcomp := intervalIntegral.integral_mono_on (μ := volume) hab hf.abs
      ((continuousOn_const.mul hInvCont).intervalIntegrable_of_Icc hab) fun x hx => by
        change |f x/x^2| ≤ C*(x^2)⁻¹
        rw [div_eq_mul_inv,abs_mul,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg x))]
        exact mul_le_mul_of_nonneg_right (h x hx) (inv_nonneg.mpr (sq_nonneg x))
    change (∫ x in (D:ℝ)..(M:ℝ), |f x/x^2|) ≤ ∫ x in (D:ℝ)..(M:ℝ), C*(x^2)⁻¹ at hcomp
    rw [intervalIntegral.integral_const_mul,inv_sq_integral ha hab] at hcomp
    exact hcomp.trans (mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) hC)
  unfold tailQuadratureSumIntegral
  apply (abs_sub _ _).trans
  rw [abs_mul,show |(M:ℝ)| = (M:ℝ) from abs_of_nonneg (Nat.cast_nonneg M)]
  exact (add_le_add hsum (mul_le_mul_of_nonneg_left hInt (Nat.cast_nonneg M))).trans_eq
    (by rw [div_eq_mul_inv]; ring)

private theorem floor_tailQuadrature_error {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    |tailQuadratureSumIntegral M D (fun x => (⌊x⌋₊:ℝ)-x)| ≤ (M:ℝ)/D := by
  let e := fun x : ℝ => (⌊x⌋₊:ℝ)-x
  have ha : 0 < (D:ℝ) := by exact_mod_cast hD
  have hab : (D:ℝ) ≤ M := by exact_mod_cast hDM
  have hfloor (x : ℝ) (hx : 0 ≤ x) : -1 ≤ e x ∧ e x ≤ 0 := by
    dsimp [e]
    constructor
    · linarith only [Nat.lt_floor_add_one x]
    · exact sub_nonpos.mpr (Nat.floor_le hx)
  have hsum : -(↑(M/D:ℕ):ℝ) ≤ ∑ j ∈ Icc 1 (M/D), e ((M:ℝ)/j) ∧
      (∑ j ∈ Icc 1 (M/D), e ((M:ℝ)/j)) ≤ 0 := by
    constructor
    · have hl := sum_le_sum (s := Finset.Icc 1 (M/D)) (f := fun _ => (-1:ℝ))
          (g := fun j : ℕ => e ((M:ℝ)/j)) fun j _ =>
        (hfloor _ (by positivity)).1
      simpa [Nat.card_Icc,nsmul_eq_mul] using hl
    · exact sum_nonpos fun j _ => (hfloor _ (by positivity)).2
  have hi : IntervalIntegrable (fun x => e x/x^2) volume D M := by
    simp only [e,sub_div,← unitCoefficient_prefix]
    exact (coefficient_kernel_integrable unitCoefficient ha hab).sub (id_kernel_integrable ha hab)
  have hInvCont : ContinuousOn (fun x : ℝ => (x^2)⁻¹) (Set.Icc (D:ℝ) M) :=
    (continuousOn_id.pow 2).inv₀ fun _ hx => pow_ne_zero _ (ha.trans_le hx.1).ne'
  have hlo := intervalIntegral.integral_mono_on (μ := volume) hab
    (hInvCont.neg.intervalIntegrable_of_Icc hab) hi fun x hx => by
      change -(x^2)⁻¹ ≤ e x/x^2
      rw [← one_div, ← neg_div]
      exact div_le_div_of_nonneg_right (hfloor x (ha.trans_le hx.1).le).1 (sq_nonneg x)
  change (∫ x in (D:ℝ)..(M:ℝ), -(x^2)⁻¹) ≤ ∫ x in (D:ℝ)..(M:ℝ), e x/x^2 at hlo
  rw [intervalIntegral.integral_neg, inv_sq_integral ha hab] at hlo
  have hhi : (∫ x in (D:ℝ)..(M:ℝ), e x/x^2) ≤ 0 := by
    calc
      _ ≤ (∫ _x : ℝ in (D:ℝ)..(M:ℝ), (0:ℝ)) := intervalIntegral.integral_mono_on
        hab hi intervalIntegrable_const fun x hx =>
          div_nonpos_of_nonpos_of_nonneg (hfloor x (ha.trans_le hx.1).le).2 (sq_nonneg x)
      _ = _ := intervalIntegral.integral_zero
  have hq : ((M/D:ℕ):ℝ) ≤ (M:ℝ)/D := (le_div_iff₀ ha).mpr
    (by exact_mod_cast Nat.div_mul_le_self M D)
  have hm0 := (ha.trans_le hab).le
  change |(∑ j ∈ Icc 1 (M/D), e ((M:ℝ)/j))-(M:ℝ)*(∫ x in (D:ℝ)..(M:ℝ), e x/x^2)| ≤ _
  apply abs_le.mpr
  constructor
  · linarith only [hsum.1, hq, mul_nonpos_of_nonneg_of_nonpos hm0 hhi]
  · rw [div_eq_mul_inv]
    linarith only [hsum.2, mul_le_mul_of_nonneg_left hlo hm0,
      mul_nonneg hm0 (inv_nonneg.mpr hm0)]

/-- The same reciprocal weights applied to the signed arithmetic
coefficient 1 minus the von Mangoldt weight. -/
def weightedMangoldtDiscrepancy (M D : ℕ) : ℝ :=
  weight M D * ((D:ℝ)-Chebyshev.psi D) +
    ∑ p ∈ Ioc D M, (1-Λ p)*weight M p

/-- Exact signed quadrature for the uniform count minus the von Mangoldt count. -/
theorem mangoldtDiscrepancy_quadrature {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    tailQuadratureSumIntegral M D (fun x => (⌊x⌋₊:ℝ)-Chebyshev.psi x) =
      weightedMangoldtDiscrepancy M D := by
  let c := fun p => unitCoefficient p - Λ p
  have hfun : coefficientPrefix c = fun x => (⌊x⌋₊:ℝ)-Chebyshev.psi x := by
    funext x
    rw [show coefficientPrefix c x = coefficientPrefix unitCoefficient x -
      coefficientPrefix (fun p => Λ p) x from coefficientPrefix_sub_fun _ _ _,
      unitCoefficient_prefix,psi_prefix]
  rw [← hfun, coefficient_tailQuadratureSumIntegral c hD hDM, hfun,
    weightedMangoldtDiscrepancy]
  simp only [Nat.floor_natCast]
  congr 1
  apply sum_congr rfl
  intro p hp
  simp [c,unitCoefficient,(hD.trans (mem_Ioc.mp hp).1).ne']

/-- The centered Chebyshev expression differs from a wholly finite
Mangoldt sum by only the proper prime powers and the unit-density floor loss. -/
theorem chebyshev_sum_integral_mangoldt_error {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    |-tailQuadratureSumIntegral M D (fun x => Chebyshev.theta x-x) -
      weightedMangoldtDiscrepancy M D| ≤
        Chebyshev.psi M-Chebyshev.theta M+(M:ℝ)/D := by
  have he := mangoldtDiscrepancy_quadrature hD hDM
  have ha : 0 < (D:ℝ) := by exact_mod_cast hD
  have hab : (D:ℝ) ≤ M := by exact_mod_cast hDM
  have hψ : IntervalIntegrable (fun x => Chebyshev.psi x/x^2) volume D M := by
    simpa only [psi_prefix] using coefficient_kernel_integrable (fun p => Λ p) ha hab
  have hfloor : IntervalIntegrable (fun x => (⌊x⌋₊:ℝ)/x^2) volume D M := by
    simpa only [unitCoefficient_prefix] using coefficient_kernel_integrable unitCoefficient ha hab
  have hθ := theta_kernel_integrable ha hab
  have hId := id_kernel_integrable ha hab
  have hdiff : -tailQuadratureSumIntegral M D (fun x => Chebyshev.theta x-x) -
      weightedMangoldtDiscrepancy M D =
        tailQuadratureSumIntegral M D (fun x => Chebyshev.psi x-Chebyshev.theta x) -
          tailQuadratureSumIntegral M D (fun x => (⌊x⌋₊:ℝ)-x) := by
    rw [← he, tailQuadratureSumIntegral_sub M D hθ hId, tailQuadratureSumIntegral_sub M D hfloor hψ,
      tailQuadratureSumIntegral_sub M D hψ hθ, tailQuadratureSumIntegral_sub M D hfloor hId]
    ring
  obtain ⟨hlo,hhi⟩ := psi_theta_tailQuadrature_bounds hD hDM
  rw [hdiff]
  exact (abs_sub _ _).trans
    (add_le_add (by rwa [abs_of_nonneg hlo]) (floor_tailQuadrature_error hD hDM))

theorem id_kernel_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, x / x^2) = log (b/a) := by
  rw [← integral_one_div_of_pos ha (ha.trans_le hab)]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  field_simp [(ha.trans_le hx.1).ne']

theorem id_tailQuadrature_formula {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    tailQuadrature M D id = (M:ℝ)*(harmonic (M/D)-log ((M:ℝ)/D)) -
      (((M/D:ℕ):ℝ)+1/2-(M:ℝ)/D)*D := by
  have hsum : (∑ j ∈ Icc 1 (M/D), (M:ℝ)/j) = (M:ℝ)*(harmonic (M/D):ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.mul_sum]
    simp only [div_eq_mul_inv, Rat.cast_inv, Rat.cast_natCast]
  unfold tailQuadrature tailQuadratureSumIntegral
  simp only [id_eq]
  rw [hsum, id_kernel_integral (by exact_mod_cast hD) (by exact_mod_cast hDM)]
  ring

/-- The Euler-constant main term of the constant-density quadrature
has error at most twice M divided by the square of the number of rows. -/
private theorem id_tailQuadrature_bound_by_rows {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    |tailQuadrature M D id - eulerMascheroniConstant*M| ≤
      2*(M:ℝ)/((M/D:ℕ):ℝ)^2 := by
  let q := M/D
  let r : ℝ := (M:ℝ)/D
  have hq : 0 < q := Nat.div_pos hDM hD
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq
  have hq1 : 1 ≤ (q:ℝ) := by exact_mod_cast hq
  have hD0 : 0 < (D:ℝ) := by exact_mod_cast hD
  have hM0 : 0 < (M:ℝ) := by exact_mod_cast hD.trans_le hDM
  have hrq : (q:ℝ) ≤ r := by
    dsimp [r,q]
    apply (le_div_iff₀ hD0).mpr
    exact_mod_cast Nat.div_mul_le_self M D
  have hr1 : r ≤ (q:ℝ)+1 := by
    dsimp [r,q]
    apply (div_le_iff₀ hD0).mpr
    exact_mod_cast (by simpa [mul_comm] using (Nat.lt_mul_div_succ M hD).le :
      M ≤ (M/D+1)*D)
  have hr0 := hq0.trans_le hrq
  have hsum : (∑ j ∈ Icc 1 q, (M:ℝ)/j) = (M:ℝ)*(harmonic q:ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.mul_sum]
    simp only [div_eq_mul_inv, Rat.cast_inv, Rat.cast_natCast]
  have he : tailQuadrature M D id - eulerMascheroniConstant*M =
      (M:ℝ)*((harmonic q:ℝ)-log q-eulerMascheroniConstant -
        1/(2*r) + ((r-q)/r-log (r/q))) := by
    change (∑ j ∈ Icc 1 q, (M:ℝ)/j) - (M:ℝ)*(∫ x in (D:ℝ)..(M:ℝ), x/x^2) -
      ((q:ℝ)+1/2-r)*D - eulerMascheroniConstant*M = _
    rw [hsum, id_kernel_integral hD0 (by exact_mod_cast hDM), ← show r = (M:ℝ)/D from rfl,
      log_div hr0.ne' hq0.ne']
    dsimp only [r]
    field_simp
    ring
  have hlog_upper : log (r/q) ≤ (r-q)/q := by
    have h := log_le_sub_one_of_pos (div_pos hr0 hq0)
    rwa [sub_div, div_self hq0.ne']
  have hlog_lower : (r-q)/r ≤ log (r/q) := by
    have h := log_le_sub_one_of_pos (div_pos hq0 hr0)
    rw [log_div hq0.ne' hr0.ne'] at h
    rw [log_div hr0.ne' hq0.ne']
    rw [sub_div, div_self hr0.ne']
    linarith only [h]
  have hgap : (r-q)/q-(r-q)/r ≤ 1/(q:ℝ)^2 := by
    have ht : 0 ≤ 1-(r-q) := by linarith only [hr1]
    have hu : (r-q)^2 ≤ 1 := by
      nlinarith only [hr1, mul_nonneg (sub_nonneg.mpr hrq) ht]
    calc
      _ = (r-q)^2/(q*r) := by field_simp
      _ ≤ 1/(q*r) := div_le_div_of_nonneg_right hu (by positivity)
      _ ≤ _ := one_div_le_one_div_of_le (by positivity)
        (by nlinarith only [mul_le_mul_of_nonneg_left hrq hq0.le])
  have hlo : 1/(2*(q+1:ℝ))-1/(2*r) ≥ -1/(2*(q:ℝ)^2) := by
    have h := one_div_le_one_div_of_le (show 0 < 2*(q:ℝ) by positivity)
      (show 2*(q:ℝ) ≤ 2*r by linarith only [hrq])
    have h' : -1/(2*(q:ℝ)^2) ≤ 1/(2*(q+1:ℝ))-1/(2*(q:ℝ)) := by
      field_simp
      nlinarith only [hq0]
    linarith only [h,h']
  have hup : 1/(2*(q:ℝ))-1/(2*r) ≤ 1/(2*(q:ℝ)^2) := by
    have h := one_div_le_one_div_of_le (show 0 < 2*r by positivity)
      (show 2*r ≤ 2*(q+1:ℝ) by linarith only [hr1])
    linarith only [h,hlo,show 1/(2*(q:ℝ))-1/(2*(q+1:ℝ)) ≤ 1/(2*(q:ℝ)^2) by
      field_simp
      nlinarith only [hq0]]
  obtain ⟨hl,hu⟩ := harmonic_half_remainder hq
  rw [he, abs_mul, abs_of_pos hM0]
  change _ ≤ 2*(M:ℝ)/(q:ℝ)^2
  rw [show 2*(M:ℝ)/(q:ℝ)^2 = (M:ℝ)*(2*(1/(q:ℝ)^2)) by ring]
  apply mul_le_mul_of_nonneg_left _ hM0.le
  apply abs_le.mpr
  rw [neg_div] at hlo
  rw [show 1/(2*(q:ℝ)^2) = (1/2)*(1/(q:ℝ)^2) by ring] at hlo hup
  have hpos : 0 ≤ 1/(q:ℝ)^2 := by positivity
  constructor <;> linarith only [hl,hu,hlo,hup,hgap,hlog_upper,hlog_lower,hpos]

/-- The constant-density quadrature pays its Euler-constant main term
with an error governed by the square of the cutoff scale. -/
theorem id_tailQuadrature_error {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    |tailQuadrature M D id-eulerMascheroniConstant*M| ≤ 8*(D:ℝ)^2/M := by
  have ha : 0 < (D:ℝ) := by exact_mod_cast hD
  have hM : 0 < (M:ℝ) := by exact_mod_cast hD.trans_le hDM
  apply (id_tailQuadrature_bound_by_rows hD hDM).trans
  let q := M/D
  have hq : 0 < q := Nat.div_pos hDM hD
  have hq1 : 1 ≤ (q:ℝ) := by exact_mod_cast hq
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq
  have hMt : (M:ℝ) ≤ (D:ℝ)*(q+1) := by exact_mod_cast (Nat.lt_mul_div_succ M hD).le
  have hM2 : (M:ℝ) ≤ 2*(D:ℝ)*q := by
    calc
      _ ≤ (D:ℝ)*(q+1) := hMt
      _ ≤ (D:ℝ)*(2*q) := mul_le_mul_of_nonneg_left (by linarith only [hq1]) ha.le
      _ = _ := by ring
  have hsq := pow_le_pow_left₀ hM.le hM2 2
  change 2*(M:ℝ)/(q:ℝ)^2 ≤ _
  apply (div_le_div_iff₀ (sq_pos_of_pos hq0) hM).mpr
  nlinarith only [hsq]

/-- Subtracting the constant-density model leaves the actual signed
Chebyshev error, with an elementary error of order D squared over M. -/
theorem prime_tail_chebyshev_error {M D : ℕ} (hD : 0 < D) (hDM : D ≤ M) :
    |eulerMascheroniConstant*(M:ℝ) - Chebyshev.theta D/2 - upperPrimeSum M D +
      tailQuadrature M D (fun x => Chebyshev.theta x-x)| ≤ 8*(D:ℝ)^2/M := by
  have ha : 0 < (D:ℝ) := by exact_mod_cast hD
  have hb : (D:ℝ) ≤ M := by exact_mod_cast hDM
  have hθ := theta_kernel_integrable ha hb
  have hId : IntervalIntegrable (fun x : ℝ => x/x^2) volume D M :=
    (continuousOn_id.div (continuousOn_id.pow 2) fun x hx =>
      pow_ne_zero 2 (ha.trans_le hx.1).ne').intervalIntegrable_of_Icc hb
  have hsub : tailQuadrature M D (fun x => Chebyshev.theta x-x) =
      tailQuadrature M D Chebyshev.theta - tailQuadrature M D id := by
    simp only [tailQuadrature, tailQuadratureSumIntegral, id_eq, sum_sub_distrib, sub_div,
      intervalIntegral.integral_sub hθ hId]
    ring
  rw [hsub, theta_tailQuadrature hD hDM]
  rw [show eulerMascheroniConstant*(M:ℝ) - Chebyshev.theta D/2 - upperPrimeSum M D +
      (Chebyshev.theta D/2 + upperPrimeSum M D - tailQuadrature M D id) =
      -(tailQuadrature M D id - eulerMascheroniConstant*M) by ring, abs_neg]
  exact id_tailQuadrature_error hD hDM

/-- Average the negative Chebyshev-error quadrature at the exact cubic-tail
observations, with the original cutoff and averaging order. -/
def cubicChebyshevTail (n : ℕ) : ℝ :=
  let k := Nat.log 2 n+1
  repeatedMean (2*n^3+1) k (fun M =>
    -tailQuadrature M (n^3) (fun x => Chebyshev.theta x-x)) (n^4-k*n^3)

/-- The original cubic tail and the centered Chebyshev quadrature agree
to within sixteen times the square-root scale at every late index. -/
theorem cubic_tail_chebyshev_error {n : ℕ} (hn : 8 ≤ n) :
    |repeatedTailAt (Nat.log 2 n+1) n (n^3) - cubicChebyshevTail n| ≤ 16*(n:ℝ)^2 := by
  let k := Nat.log 2 n+1
  let D := n^3
  let A := n^4-k*D
  let W := 2*D+1
  let L := repeatedMean W k
  let B : ℝ := 16*(n:ℝ)^2
  let original (M : ℕ) := eulerMascheroniConstant*(M:ℝ) - Chebyshev.theta D/2 - upperPrimeSum M D
  let centered (M : ℕ) := -tailQuadrature M D (fun x => Chebyshev.theta x-x)
  obtain ⟨hk,_⟩ := cubic_tail_parameters hn
  have hW : 0 < W := by dsimp [W]; omega
  have hD : 0 < D := by dsimp [D]; positivity
  have hhalf : 2*(k*D) ≤ n^4 := by
    simpa only [D, ← Nat.mul_assoc, show n^4=n*n^3 by ring] using Nat.mul_le_mul_right (n^3) hk
  have hD2 : 2*D ≤ n^4 :=
    (Nat.mul_le_mul_right D (by omega : 2 ≤ n)).trans_eq (by dsimp [D]; ring)
  have hDA : D ≤ A := by dsimp [A]; omega
  have hcenter : A+k*D = n^4 := by dsimp [A]; omega
  have hfirst : L (fun M : ℕ => (M:ℝ)) A = (n:ℝ)^4 :=
    (repeat_first_moment _ _ _).trans (by exact_mod_cast hcenter)
  have hmean : repeatedTailAt k n D = L original A := by
    change repeatedTailAt k n D =
      L (eulerMascheroniConstant • (fun M : ℕ => (M:ℝ)) -
        (fun _ => Chebyshev.theta D/2) - (fun M => upperPrimeSum M D)) A
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfirst, show L (fun _ => Chebyshev.theta D/2) A = Chebyshev.theta D/2 from
      repeat_const hW k A _]
    rfl
  have hpoint (M : ℕ) (hAM : A ≤ M) : |(original-centered) M| ≤ B := by
    have hDM := hDA.trans hAM
    have hMn : n^4 ≤ 2*M := by dsimp [A] at hAM; omega
    have hMR : (n:ℝ)^4 ≤ 2*(M:ℝ) := by exact_mod_cast hMn
    have hM0 : 0 < (M:ℝ) := by exact_mod_cast hD.trans_le hDM
    have h : |original M-centered M| ≤ 8*(D:ℝ)^2/M := by
      simpa only [original,centered,sub_neg_eq_add] using prime_tail_chebyshev_error hD hDM
    apply h.trans
    apply (div_le_iff₀ hM0).mpr
    dsimp [B,D]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hMR (show 0 ≤ 8*(n:ℝ)^2 by positivity)]
  have hhi := repeat_mono W k A (f := original-centered) (g := fun _ => B) fun M hAM _ =>
    (abs_le.mp (hpoint M hAM)).2
  have hlo := repeat_mono W k A (f := fun _ => -B) (g := original-centered) fun M hAM _ =>
    (abs_le.mp (hpoint M hAM)).1
  change |repeatedTailAt k n D-L centered A| ≤ B
  rw [hmean, ← Pi.sub_apply, ← L.map_sub]
  apply abs_le.mpr
  exact ⟨by simpa only [L,repeat_const hW k A] using hlo,
    by simpa only [L,repeat_const hW k A] using hhi⟩

/-- The same averaged Chebyshev error with only the sum and integral retained. -/
def cubicChebyshevSumIntegral (n : ℕ) : ℝ :=
  let k := Nat.log 2 n+1
  repeatedMean (2*n^3+1) k (fun M =>
    -tailQuadratureSumIntegral M (n^3) (fun x => Chebyshev.theta x-x)) (n^4-k*n^3)

/-- The coefficient at the lower cutoff has almost zero mean. Averaging
therefore removes the entire cutoff term at square-root cost. -/
theorem cubic_chebyshev_cutoff_error {n : ℕ} (hn : 8 ≤ n) :
    |cubicChebyshevTail n-cubicChebyshevSumIntegral n| ≤ 16*(n:ℝ)^2 := by
  let k := Nat.log 2 n+1
  let D := n^3
  let A := n^4-k*D
  let W := 2*D+1
  let L := repeatedMean W k
  let E := Chebyshev.theta D-(D:ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hD0 : 0 < (D:ℝ) := by exact_mod_cast hD
  have hW : 0 < W := by dsimp [W]; omega
  have hcoeff (M : ℕ) : ((M/D:ℕ):ℝ)+1/2-(M:ℝ)/D = weight M D-1/2 := by
    have hm : ((M%D:ℕ):ℝ)+(D:ℝ)*(M/D:ℕ)=M := by exact_mod_cast Nat.mod_add_div M D
    unfold weight
    field_simp
    nlinarith only [hm]
  have hav :
      cubicChebyshevTail n-cubicChebyshevSumIntegral n =
        E*(L (fun M => weight M D) A-1/2) := by
    change L (fun M => -tailQuadrature M D (fun x => Chebyshev.theta x-x)) A -
      L (fun M => -tailQuadratureSumIntegral M D (fun x => Chebyshev.theta x-x)) A = _
    rw [← Pi.sub_apply, ← L.map_sub]
    have he :
        (fun M => -tailQuadrature M D (fun x => Chebyshev.theta x-x)) -
          (fun M => -tailQuadratureSumIntegral M D (fun x => Chebyshev.theta x-x)) =
            E • ((fun M => weight M D) - (fun _ => (1/2:ℝ))) := by
      funext M
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, tailQuadrature, hcoeff, E]
      ring
    rw [he, map_smul, map_sub]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show L (fun _ => (1/2:ℝ)) A = 1/2 from repeat_const hW k A _]
  have hE : |E| ≤ 8*(D:ℝ) := by
    have h1 := (Chebyshev.theta_le_psi D).trans (Chebyshev.psi_le_const_mul_self hD0.le)
    have h2 := Chebyshev.theta_nonneg (x := (D:ℝ))
    have h3 := mul_le_mul_of_nonneg_right
      (log_le_sub_one_of_pos (by norm_num : 0 < (4:ℝ))) hD0.le
    dsimp only [E]
    apply abs_le.mpr
    constructor <;> linarith only [h1,h2,h3,hD0.le]
  have hweight :
      |L (fun M => weight M D) A-1/2| ≤ ((D:ℝ)/W)^k+1/(2*(D:ℝ)) := by
    rw [show L (fun M => weight M D) A-1/2 =
      (L (fun M => weight M D) A-(1/2+1/(2*(D:ℝ)))) + 1/(2*(D:ℝ)) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (by positivity : 0 ≤ 1/(2*(D:ℝ)))]
    exact add_le_add_left (repeated_weight_error hD hW k A) _
  obtain ⟨_,hsize⟩ := cubic_tail_parameters hn
  have hcost : (D:ℝ)*((D:ℝ)/W)^k ≤ (n:ℝ)^2 := by
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (W:ℝ)^k)]
    rw [← pow_succ']
    simpa only [D, W, k, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
      using hsize
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  rw [hav, abs_mul]
  calc
    _ ≤ (8*(D:ℝ))*(((D:ℝ)/W)^k+1/(2*(D:ℝ))) :=
      mul_le_mul hE hweight (abs_nonneg _) (by positivity)
    _ = 8*((D:ℝ)*((D:ℝ)/W)^k+1/2) := by field_simp
    _ ≤ _ := by nlinarith only [hcost, hn1, sq_nonneg ((n:ℝ)-1)]

/-- Removing the model and the lower cutoff costs at most 32 square-root units. -/
theorem cubic_tail_sum_integral_error {n : ℕ} (hn : 8 ≤ n) :
    |repeatedTailAt (Nat.log 2 n+1) n (n^3) - cubicChebyshevSumIntegral n| ≤ 32*(n:ℝ)^2 := by
  rw [show repeatedTailAt (Nat.log 2 n+1) n (n^3) - cubicChebyshevSumIntegral n =
    (repeatedTailAt (Nat.log 2 n+1) n (n^3) - cubicChebyshevTail n) +
      (cubicChebyshevTail n-cubicChebyshevSumIntegral n) by ring]
  apply (abs_add_le _ _).trans
  linarith only [cubic_tail_chebyshev_error hn, cubic_chebyshev_cutoff_error hn]

/-- The positive part of the centered quadrature after the original averaging. -/
def cubicChebyshevMassOn (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (cubicChebyshevSumIntegral n) 0 / (n:ℝ)^3

private theorem positive_mass_error (f g : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ n ≥ 8, |f n-g n| ≤ K*(n:ℝ)^2) {m b : ℕ} (hm : 8 ≤ m) :
    |(∑ n ∈ Icc m b, max (f n) 0/(n:ℝ)^3) -
      (∑ n ∈ Icc m b, max (g n) 0/(n:ℝ)^3)| ≤ K*(1+log b) := by
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  have hterm (n : ℕ) (hn : n ∈ Icc m b) :
      |max (f n) 0/(n:ℝ)^3 - max (g n) 0/(n:ℝ)^3| ≤ K*(n:ℝ)⁻¹ := by
    have hn8 := hm.trans (mem_Icc.mp hn).1
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hpos := (abs_max_sub_max_le_abs (f n) (g n) 0).trans (h n hn8)
    rw [← sub_div, abs_div, abs_of_pos (pow_pos hn0 3)]
    exact (div_le_div_of_nonneg_right hpos (by positivity)).trans_eq (by field_simp)
  calc
    _ ≤ ∑ n ∈ Icc m b, K*(n:ℝ)⁻¹ := sum_le_sum hterm
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (primeWindow_harmonic_le (by omega : 1 ≤ m)) hK

/-- On a complete fourth-power window the two mass functions differ by at
most a logarithmic cost. -/
theorem cubicMassOn_chebyshev_error {m b : ℕ} (hm : 8 ≤ m) :
    |cubicMassOn m b-cubicChebyshevMassOn m b| ≤ 32*(1+log b) :=
  positive_mass_error (fun n => repeatedTailAt (Nat.log 2 n+1) n (n^3))
    cubicChebyshevSumIntegral (by norm_num) (fun _ hn => cubic_tail_sum_integral_error hn) hm

private theorem rh_of_cubicMassOn_le_window_error {mass : ℕ → ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hcompare : ∀ {m b : ℕ}, 8 ≤ m → cubicMassOn m b ≤ mass m b+C*(1+log b))
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, mass m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicMassOn_powerWindows
  apply subpowerWindows_of_log_cube_error hC _ h
  intro m b hm
  apply (hcompare hm).trans (add_le_add_right ?_ _)
  exact mul_le_mul_of_nonneg_left (le_self_pow₀ (by linarith only [log_natCast_nonneg b]) (by decide)) hC

/-- An independent subpower upper bound for the centered quadrature on
arbitrarily late power windows suffices for the short RH route. -/
theorem rh_of_cubicChebyshevMassOn_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicChebyshevMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis :=
  rh_of_cubicMassOn_le_window_error (C := 32) (by norm_num)
    (fun {m b} hm => by linarith only [(abs_le.mp (cubicMassOn_chebyshev_error (m := m) (b := b) hm)).2]) h

/-- The cubic averaging depth grows at most twice the natural logarithm plus two. -/
theorem cubic_depth_le_twice_log {n : ℕ} (hn : 0 < n) :
    ((Nat.log 2 n+1:ℕ):ℝ) ≤ 2*(1+log n) := by
  have h := log_le_log (by positivity : (0:ℝ) < 2^(Nat.log 2 n))
    (show (2:ℝ)^(Nat.log 2 n) ≤ n by exact_mod_cast Nat.pow_log_le_self 2 hn.ne')
  rw [log_pow] at h
  have hh := mul_le_mul_of_nonneg_left
    (show (1/2:ℝ) ≤ log 2 by linarith only [Real.log_two_gt_d9]) (Nat.cast_nonneg (Nat.log 2 n))
  push_cast
  linarith only [h,hh]

/-- The arithmetic analogue of the averaged centered Chebyshev expression. -/
def cubicMangoldtTail (n : ℕ) : ℝ :=
  let k := Nat.log 2 n+1
  repeatedMean (2*n^3+1) k (fun M => weightedMangoldtDiscrepancy M (n^3)) (n^4-k*n^3)

/-- A block of width 2d+1 consists of two full periods and one observation
with the starting residue. Iteration scales the remaining fluctuation exactly. -/
theorem repeated_weight_two_periods {d : ℕ} (hd : 0 < d) (k A : ℕ) :
    let c : ℝ := 1/2+1/(2*(d:ℝ))
    repeatedMean (2*d+1) k (fun M => weight M d) A =
      c + (weight A d-c)/((2*d+1:ℕ):ℝ)^k := by
  let W := 2*d+1
  let c : ℝ := 1/2+1/(2*(d:ℝ))
  have hW : (W:ℝ) ≠ 0 := by dsimp [W]; positivity
  have hs (a : ℕ) : (∑ j ∈ range W, weight (a+j) d) = (W:ℝ)*c + (weight a d-c) := by
    have hr : (a+2*d)%d = a%d := by simp
    have hx : residueTerm (a+2*d) d = residueTerm a d := by simp [residueTerm,hr]
    have hw : weight (a+2*d) d = weight a d := by simp [weight,hr]
    dsimp only [W]
    rw [sum_range_succ,weight_block_identity a (2*d) hd,hx,hw]
    dsimp only [c]
    push_cast
    ring
  change repeatedMean W k (fun M => weight M d) A = c+(weight A d-c)/(W:ℝ)^k
  induction k generalizing A with
  | zero => simp [repeatedMean]
  | succ k ih =>
    change blockMean A W (repeatedMean W k (fun M => weight M d)) = _
    simp only [blockMean,ih,sum_add_distrib,← sum_div,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,hs]
    rw [pow_succ]
    field_simp
    ring

/-- All upper terms retain their moving weights. The cutoff term has a
closed scalar coefficient. -/
def cubicMangoldtUpperTail (n : ℕ) : ℝ :=
  let D := n^3
  let k := Nat.log 2 n+1
  repeatedMean (2*D+1) k (fun M => ∑ p ∈ Ioc D M, (1-Λ p)*weight M p) (n^4-k*D)

theorem cubicMangoldtTail_boundary {n : ℕ} (hn : 0 < n) :
    let D := n^3
    let k := Nat.log 2 n+1
    let c : ℝ := 1/2+1/(2*(D:ℝ))
    cubicMangoldtTail n = (c+(1-c)/((2*D+1:ℕ):ℝ)^k)*((D:ℝ)-Chebyshev.psi D) +
      cubicMangoldtUpperTail n := by
  let D := n^3
  let k := Nat.log 2 n+1
  let W := 2*D+1
  let a := n^4-k*D
  let P : ℝ := (D:ℝ)-Chebyshev.psi D
  let w := fun M => weight M D
  let u := fun M => ∑ p ∈ Ioc D M, (1-Λ p)*weight M p
  have hf : (fun M => weightedMangoldtDiscrepancy M D) = P • w + u := by
    funext M
    simp only [weightedMangoldtDiscrepancy,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    dsimp only [P,w,u]
    ring
  have ha : a = (n-k)*D := by dsimp [a,D]; rw [Nat.sub_mul]; ring_nf
  have hw : weight a D = 1 := by simp [ha,weight]
  change repeatedMean W k (fun M => weightedMangoldtDiscrepancy M D) a = _*P+repeatedMean W k u a
  rw [hf,map_add,map_smul]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  dsimp only [W,w]
  rw [repeated_weight_two_periods (show 0 < D by dsimp [D]; positivity),hw,mul_comm P]

/-- Rounding the explicit boundary weight to one half costs at most eight
per sample, uniformly for all positive n. -/
theorem cubicMangoldtTail_half_boundary {n : ℕ} (hn : 0 < n) :
    |cubicMangoldtTail n - (((n^3:ℕ):ℝ)-Chebyshev.psi (n^3:ℕ))/2 -
      cubicMangoldtUpperTail n| ≤ 8 := by
  let D := n^3
  let k := Nat.log 2 n+1
  let W := 2*D+1
  let c := 1/2+1/(2*(D:ℝ))
  have hd : 0 < D := pow_pos hn 3
  have hd1 : 1 ≤ (D:ℝ) := by exact_mod_cast hd
  have hdR := zero_lt_one.trans_le hd1
  have hw1 : 1 ≤ (W:ℝ) := by exact_mod_cast (show 1 ≤ W by dsimp [W]; omega)
  have hwpos := zero_lt_one.trans_le hw1
  have hw : 2*(D:ℝ) ≤ (W:ℝ)^k := by
    apply le_trans _ (le_self_pow₀ hw1 (by dsimp [k]; omega))
    dsimp [W]; push_cast; linarith
  have hsmall : 1/(2*(D:ℝ)) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hc : 0 ≤ c ∧ c ≤ 1 := ⟨by dsimp [c]; positivity,by dsimp [c]; linarith only [hsmall]⟩
  let h := c+(1-c)/(W:ℝ)^k-1/2
  have hh0 : 0 ≤ h := by
    dsimp only [h]
    have hh : 1/2 ≤ c := le_add_of_nonneg_right (by positivity)
    linarith only [hh,div_nonneg (sub_nonneg.mpr hc.2) (pow_pos hwpos k).le]
  have hh : h ≤ (D:ℝ)⁻¹ := by
    have hb : (1-c)/(W:ℝ)^k ≤ 1/(2*(D:ℝ)) := div_le_div₀
      zero_le_one (sub_le_self _ hc.1) (by positivity) hw
    dsimp only [h,c] at hb ⊢
    have he : 1/(2*(D:ℝ))+1/(2*(D:ℝ)) = (D:ℝ)⁻¹ := by ring
    linarith only [hb,he]
  have hpsi := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) D)
  have hh4 : log 4+4 ≤ 7 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hp : |(D:ℝ)-Chebyshev.psi D| ≤ 8*D := by
    have he := abs_sub (D:ℝ) (Chebyshev.psi D)
    rw [abs_of_pos hdR,abs_of_nonneg (Chebyshev.psi_nonneg _)] at he
    linarith only [he,hpsi,mul_le_mul_of_nonneg_right hh4 hdR.le]
  rw [cubicMangoldtTail_boundary hn]
  change |(c+_)*((D:ℝ)-Chebyshev.psi D)+_ - _/2 - _| ≤ _
  rw [show (c+(1-c)/(W:ℝ)^k)*((D:ℝ)-Chebyshev.psi D)+cubicMangoldtUpperTail n -
      ((D:ℝ)-Chebyshev.psi D)/2-cubicMangoldtUpperTail n = h*((D:ℝ)-Chebyshev.psi D) by dsimp [h]; ring,
    abs_mul,abs_of_nonneg hh0]
  exact (mul_le_mul hh hp (abs_nonneg _) (inv_nonneg.mpr hdR.le)).trans_eq (by field_simp)


/-- The prime-power and density-floor losses stay on square-root scale
after averaging over the actual observation interval. -/
theorem cubic_chebyshev_mangoldt_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n ≥ 8, |cubicChebyshevSumIntegral n-cubicMangoldtTail n| ≤ K*(n:ℝ)^2 := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K := 2*|C|+2
  refine ⟨K,by dsimp only [K]; positivity,fun n hn => ?_⟩
  let k := Nat.log 2 n+1
  let D := n^3
  let A := n^4-k*D
  let W := 2*D+1
  let L := repeatedMean W k
  let E (M : ℕ) := -tailQuadratureSumIntegral M D (fun x => Chebyshev.theta x-x)
  let F (M : ℕ) := weightedMangoldtDiscrepancy M D
  let B := K*(n:ℝ)^2
  obtain ⟨hk,_⟩ := cubic_tail_parameters hn
  have hW : 0 < W := by dsimp [W]; omega
  have hD : 0 < D := by dsimp [D]; positivity
  have hd : 0 < (D:ℝ) := by exact_mod_cast hD
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hhalf : 2*(k*D) ≤ n^4 := by
    simpa only [D,← Nat.mul_assoc,show n^4=n*n^3 by ring] using Nat.mul_le_mul_right (n^3) hk
  have hD2 : 2*D ≤ n^4 :=
    (Nat.mul_le_mul_right D (by omega : 2 ≤ n)).trans_eq (by dsimp [D]; ring)
  have hDA : D ≤ A := by dsimp [A]; omega
  have hmax : A+k*(W-1) ≤ 2*n^4 := by
    dsimp [A,W]
    rw [show k*(2*D)=2*(k*D) by ring]
    omega
  have hpoint (M : ℕ) (hAM : A ≤ M) (hM : M ≤ A+k*(W-1)) : |(E-F) M| ≤ B := by
    have hb : (M:ℝ) ≤ 2*(n:ℝ)^4 := by exact_mod_cast hM.trans hmax
    have hs : sqrt (M:ℝ) ≤ 2*(n:ℝ)^2 := by
      apply (sqrt_le_iff).mpr
      exact ⟨by positivity,by nlinarith only [hb,pow_nonneg (show 0 ≤ (n:ℝ) by positivity) 4]⟩
    have hdiv : (M:ℝ)/D ≤ 2*(n:ℝ) := by
      apply (div_le_iff₀ hd).mpr
      dsimp only [D]
      push_cast
      nlinarith only [hb]
    have hc := (hC (M:ℝ)).trans (mul_le_mul (le_abs_self C) hs (sqrt_nonneg _) (abs_nonneg _))
    apply (chebyshev_sum_integral_mangoldt_error hD (hDA.trans hAM)).trans
    dsimp only [B,K]
    nlinarith only [hc,hdiv,mul_nonneg (sub_nonneg.mpr hn1) (show 0 ≤ (n:ℝ) by positivity)]
  have hhi := repeat_mono W k A (f := E-F) (g := fun _ => B) fun M hAM hM =>
    (abs_le.mp (hpoint M hAM hM)).2
  have hlo := repeat_mono W k A (f := fun _ => -B) (g := E-F) fun M hAM hM =>
    (abs_le.mp (hpoint M hAM hM)).1
  change |L E A-L F A| ≤ B
  rw [← Pi.sub_apply, ← L.map_sub]
  exact abs_le.mpr ⟨by simpa only [L,repeat_const hW k A] using hlo,
    by simpa only [L,repeat_const hW k A] using hhi⟩

/-- The remaining positive mass expressed entirely as finite arithmetic sums. -/
def cubicMangoldtMassOn (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (cubicMangoldtTail n) 0 / (n:ℝ)^3

theorem cubicMassOn_mangoldt_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {m b : ℕ}, 8 ≤ m →
      |cubicMassOn m b-cubicMangoldtMassOn m b| ≤ K*(1+log b) := by
  obtain ⟨K,hK,h⟩ := cubic_chebyshev_mangoldt_error
  refine ⟨32+K,by positivity,fun {m b} hm => ?_⟩
  rw [show cubicMassOn m b-cubicMangoldtMassOn m b =
    (cubicMassOn m b-cubicChebyshevMassOn m b) +
      (cubicChebyshevMassOn m b-cubicMangoldtMassOn m b) by ring]
  apply (abs_add_le _ _).trans
  have hmass := positive_mass_error cubicChebyshevSumIntegral cubicMangoldtTail hK h (b := b) hm
  exact (add_le_add (cubicMassOn_chebyshev_error hm) hmass).trans_eq (by ring)

/-- Cofinal subpower positive mass of the purely arithmetic discrepancy
is sufficient for the shorter window proof. -/
theorem rh_of_cubicMangoldtMassOn_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicMangoldtMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  obtain ⟨K,hK,hcost⟩ := cubicMassOn_mangoldt_error
  exact rh_of_cubicMassOn_le_window_error hK
    (fun {m b} hm => by linarith only [(abs_le.mp (hcost (m := m) (b := b) hm)).2]) h

/-- Apply the same quadratic allowance directly to the averaged discrepancy
of the finite coefficients 1-Λ. -/
def cubicMangoldtExcessOn (C : ℝ) (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (cubicMangoldtTail n-C*(n:ℝ)^2*(1+log n)^2) 0/(n:ℝ)^3

/-- Direct endpoint for an upper bound on the excess of the signed sum of
1-Λ on arbitrarily late windows. -/
theorem rh_of_cubicMangoldtExcessOn_powerWindows {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicMangoldtExcessOn C m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicMangoldtMassOn_powerWindows
  exact subpowerWindows_of_log_cube_error hC
    (fun hm => (cubicAllowance_bounds cubicMangoldtTail hC (by omega : 1 ≤ _)).2) h


/-- The window mass with the boundary at n³ given its constant half weight. -/
def cubicHalfBoundaryExcessOn (C : ℝ) (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max ((((n^3:ℕ):ℝ)-Chebyshev.psi (n^3:ℕ))/2 +
    cubicMangoldtUpperTail n - C*(n:ℝ)^2*(1+log n)^2) 0/(n:ℝ)^3

/-- The boundary replacement has vanishing total cost even on unboundedly
long finite windows, for any value of the allowance. -/
theorem cubicMangoldtExcessOn_half_error (C : ℝ) {m b : ℕ} (hm : 2 ≤ m) (hmb : m ≤ b) :
    |cubicMangoldtExcessOn C m b-cubicHalfBoundaryExcessOn C m b| ≤ 8/(m:ℝ)^2 := by
  unfold cubicMangoldtExcessOn cubicHalfBoundaryExcessOn
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc m b, 8*(1/(n:ℝ)^3) := by
      apply sum_le_sum
      intro n hn
      rw [← sub_div,abs_div,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3),mul_one_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (abs_max_sub_max_le_abs _ _ 0).trans
      rw [sub_sub_sub_cancel_right]
      simpa only [sub_add_eq_sub_sub] using
        (cubicMangoldtTail_half_boundary (by have := (mem_Icc.mp hn).1; omega : 0 < n))
    _ ≤ _ := by
      rw [← mul_sum,← mul_one_div]
      exact mul_le_mul_of_nonneg_left (primeWindow_inv_cube_le hm hmb) (by norm_num)

/-- It suffices to bound the positive excess of half the elementary
Chebyshev discrepancy at n³ plus the signed moving sum strictly above n³. -/
theorem rh_of_cubicHalfBoundaryExcessOn_powerWindows {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicHalfBoundaryExcessOn C m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicMangoldtExcessOn_powerWindows hC
  apply subpowerWindows_of_log_cube_error (by norm_num : (0:ℝ) ≤ 8) _ h
  intro m b hm
  by_cases hmb : m ≤ b
  · have hh := (abs_le.mp (cubicMangoldtExcessOn_half_error C (by omega : 2 ≤ m) hmb)).2
    have hm1 : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    have hc : (8:ℝ)/(m:ℝ)^2 ≤ 8 := div_le_self (by norm_num) (one_le_pow₀ hm1)
    have hl : 1 ≤ (1+log b)^3 := one_le_pow₀ (by linarith only [log_natCast_nonneg b])
    linarith only [hh,hc,hl]
  · simp [cubicMangoldtExcessOn,cubicHalfBoundaryExcessOn,Icc_eq_empty_of_lt (lt_of_not_ge hmb)]
    positivity [log_natCast_nonneg b]

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.theta_tailQuadrature,
      ``RiemannGaussian.AlpogeMined.cubic_tail_sum_integral_error,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicChebyshevMassOn_powerWindows,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicMangoldtMassOn_powerWindows,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicMangoldtExcessOn_powerWindows,
      ``RiemannGaussian.AlpogeMined.cubicMangoldtTail_boundary,
      ``RiemannGaussian.AlpogeMined.cubicMangoldtTail_half_boundary,
      ``RiemannGaussian.AlpogeMined.cubicMangoldtExcessOn_half_error,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicHalfBoundaryExcessOn_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
