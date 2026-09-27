/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPhaseBudget

/-!
# Signed prime-window bounds with an exact moving cofactor

The last-prime interval follows the exact cofactor so that every actual
product has its total logarithm in one fixed interval. Three favorable
five-prime hinge caps, the original allocation, the cosine and all core
support masks give an explicit retained signed lower bound. Strict
largest-prime ownership prevents repeated spending. The outer four/five
population comparison and the whole-core floor remain open.
-/

namespace RiemannGaussian.ZetaRieszCoupledWindow
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic

/-- The final prime window depends on the exact cofactor. Every resulting
integer lies in the same total-log interval, before any phase estimate. -/
theorem product_log_bounds {m p : ℕ} (hm : m ≠ 0) {t h : ℝ}
    (hp : p ∈ logPrimes (t-Real.log m) h) :
    p.Prime ∧ t < Real.log (m*p : ℕ) ∧ Real.log (m*p : ℕ) ≤ t+h := by
  have hb := logPrimes_bounds hp
  have he : Real.log (m*p : ℕ) = Real.log m+Real.log p := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hb.1.ne_zero)]
  refine ⟨hb.1,?_,?_⟩ <;> rw [he] <;> linarith [hb.2.1,hb.2.2]

private theorem amplitude_radial {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    amplitude N n =
      (Real.exp (-Real.log n/2)*(Real.log n)^N/N.factorial)*(n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : Real.exp (-(3/2 : ℝ)*Real.log n) =
      Real.exp (-Real.log n/2)*(n : ℝ)⁻¹ := by
    have hi : (n : ℝ)⁻¹ = Real.exp (-Real.log n) := by rw [Real.exp_neg,Real.exp_log hnR]
    rw [hi,← Real.exp_add]
    congr 1
    ring
  rw [amplitude,he]
  ring

/-- An explicit signed lower bound for the actual moving last-prime sum.
The original phase is `cos(y*log(m*p))`; the window is centered at the
exact cofactor logarithm and no independent total-log approximation enters.
The local coefficient/allocation score premise remains explicit. -/
theorem eventually_cofactor_lower {h α : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (t L y B : ℝ) (A : Finset ℕ),
      m ≠ 0 → α*N ≤ t-Real.log m → 0 ≤ B →
      (∀ p ∈ logPrimes (t-Real.log m) h,
        B ≤ (1-boundedShare A N (m*p))*
          ((SquarefreeVaughanLogSource.coefficient L (m*p)).re*
            Real.cos (y*Real.log (m*p : ℕ)))) →
      (B*(Real.exp (-(t+h)/2)*t^N/N.factorial)/(m : ℝ))*
        ((9999/10000 : ℝ)*h/(t-Real.log m)) ≤
      (∑ p ∈ logPrimes (t-Real.log m) h,
        residualCoefficient A L N (m*p)*zetaPrimeLogKernel N (3/2+Complex.I*y) (m*p)).re := by
  filter_upwards [ZetaRieszPhaseBudget.eventually_phase_window_mass hh hhu hα]
    with N hN m t L y B A hm ha hB hscore
  have ht : 0 ≤ t := by
    have hn : 0 ≤ α*(N : ℝ) := mul_nonneg hα.le (Nat.cast_nonneg N)
    linarith [Real.log_natCast_nonneg m]
  let V := Real.exp (-(t+h)/2)*t^N/N.factorial
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hpoint (p : ℕ) (hp : p ∈ logPrimes (t-Real.log m) h) :
      (B*V/(m : ℝ))*(p : ℝ)⁻¹ ≤
        (residualCoefficient A L N (m*p)*zetaPrimeLogKernel N (3/2+Complex.I*y) (m*p)).re := by
    have hb := product_log_bounds hm hp
    have hmp : m*p ≠ 0 := mul_ne_zero hm hb.1.ne_zero
    have hrad : V ≤ Real.exp (-Real.log (m*p : ℕ)/2)*
        (Real.log (m*p : ℕ))^N/N.factorial := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [hb.2.2]))
        (pow_le_pow_left₀ ht hb.2.1.le N) (by positivity) (Real.exp_nonneg _)
    have hbr := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrad hB)
      (inv_nonneg.mpr (Nat.cast_nonneg (m*p)))
    have hsc := mul_le_mul_of_nonneg_right (hscore p hp)
      (show 0 ≤ amplitude N (m*p) from ZetaRieszCosineCarrier.factorial_envelope_nonneg _ _)
    rw [amplitude_radial hmp N] at hsc
    rw [re_residual_atom,weight,amplitude_radial hmp N]
    have hbr' : (B*V/(m : ℝ))*(p : ℝ)⁻¹ ≤
        B*((Real.exp (-Real.log (m*p : ℕ)/2)*(Real.log (m*p : ℕ))^N/N.factorial)*
          ((m*p : ℕ) : ℝ)⁻¹) := by
      simpa only [Nat.cast_mul,mul_inv_rev,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hbr
    exact (hbr'.trans hsc).trans_eq (by ring)
  have hmass := mul_le_mul_of_nonneg_left (hN (t-Real.log m) ha).1
    (div_nonneg (mul_nonneg hB hV) hmR.le)
  calc
    _ ≤ (B*V/(m : ℝ))*(∑ p ∈ logPrimes (t-Real.log m) h, (p : ℝ)⁻¹) := hmass
    _ = ∑ p ∈ logPrimes (t-Real.log m) h, (B*V/(m : ℝ))*(p : ℝ)⁻¹ := Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ logPrimes (t-Real.log m) h,
        (residualCoefficient A L N (m*p)*zetaPrimeLogKernel N (3/2+Complex.I*y) (m*p)).re :=
      Finset.sum_le_sum hpoint
    _ = _ := (Complex.re_sum _ _).symm

/-- A strictly largest prime determines its cofactor uniquely. This
prevents the dependent final-prime windows from multiplying a supply. -/
theorem largest_prime_product_unique {m n p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hmp : ∀ r : ℕ, r.Prime → r ∣ m → r < p)
    (hnq : ∀ r : ℕ, r.Prime → r ∣ n → r < q)
    (he : m*p = n*q) : m = n ∧ p = q := by
  have hpd : p ∣ n*q := by rw [← he]; exact dvd_mul_left p m
  have hqd : q ∣ m*p := by rw [he]; exact dvd_mul_left q n
  have hpq : p = q := by
    rcases hp.dvd_mul.mp hpd with hpn | hpq
    · have hlt := hnq p hp hpn
      rcases hq.dvd_mul.mp hqd with hqm | hqp
      · exact False.elim ((lt_asymm hlt) (hmp q hq hqm))
      · have heq := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  refine ⟨?_,hpq⟩
  apply Nat.eq_of_mul_eq_mul_right hp.pos
  simpa only [← hpq] using he

/-- A union of cofactor-dependent largest-prime windows counts every
actual integer exactly once. All finite support sets remain literal. -/
theorem sum_owned_products (M : Finset ℕ) (P : ℕ → Finset ℕ) (f : ℕ → ℂ)
    (hm : ∀ m ∈ M, m ≠ 0)
    (hP : ∀ m ∈ M, ∀ p ∈ P m,
      p.Prime ∧ ∀ r : ℕ, r.Prime → r ∣ m → r < p) :
    (∑ n ∈ M.biUnion (fun m => (P m).image (fun p => m*p)), f n) =
      ∑ m ∈ M, ∑ p ∈ P m, f (m*p) := by
  have hd : (M : Set ℕ).Pairwise (fun m n =>
      Disjoint ((P m).image (fun p => m*p)) ((P n).image (fun q => n*q))) := by
    intro m hm' n hn' hmn
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨p,hp,hpz⟩ := Finset.mem_image.mp hz
    obtain ⟨q,hq,hqz⟩ := Finset.mem_image.mp hz'
    exact hmn (largest_prime_product_unique (hP m hm' p hp).1 (hP n hn' q hq).1
      (hP m hm' p hp).2 (hP n hn' q hq).2 (hpz.trans hqz.symm)).1
  rw [Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro m hm'
  apply Finset.sum_image
  intro p _ q _ he
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (hm m hm')) he

/-- A numerical cap for the three surviving pair hinges, uniform in the
moving final-prime window `v < log p <= v+h`. -/
def fiveWindowCap (L v h : ℝ) (q a b r : ℕ) : ℝ :=
  min (Real.log r) (max 0 (min (L-(v+h)-Real.log q)
    (Real.log b+Real.log r-L+v+Real.log q)))+
  min (Real.log r) (max 0 (min (L-(v+h)-Real.log a)
    (Real.log b+Real.log r-L+v+Real.log a)))+
  min (Real.log r) (max 0 (min (L-Real.log q-Real.log a)
    (Real.log b+Real.log r-L+Real.log q+Real.log a)))

/-- Every common hinge cap is nonnegative, including cutoffs at its edges. -/
theorem fiveWindowCap_nonneg (L v h : ℝ) (q a b r : ℕ) :
    0 ≤ fiveWindowCap L v h q a b r := by
  unfold fiveWindowCap
  exact add_nonneg
    (add_nonneg (le_min (Real.log_natCast_nonneg r) (le_max_left _ _))
      (le_min (Real.log_natCast_nonneg r) (le_max_left _ _)))
    (le_min (Real.log_natCast_nonneg r) (le_max_left _ _))

/-- The exact five-prime coefficient pays all three common hinge caps.
No phase, allocation or prime-density hypothesis is used here. -/
theorem five_coefficient_window_lower {p q a b r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hb : b.Prime) (hr : r.Prime)
    (hs : Squarefree (p*(q*(a*(b*r))))) (hrb : r ≤ b)
    {L v h t : ℝ} (hL : 0 < L)
    (htn : t ≤ Real.log (p*(q*(a*(b*r))) : ℕ))
    (hplo : v ≤ Real.log p) (hphi : Real.log p ≤ v+h)
    (hpb : v+h+Real.log (b*r : ℕ) ≤ L)
    (hqb : Real.log q+Real.log (b*r : ℕ) ≤ L)
    (hab : Real.log a+Real.log (b*r : ℕ) ≤ L)
    (hpqa : L ≤ v+Real.log q+Real.log a) :
    (t/L)*fiveWindowCap L v h q a b r ≤
      -(SquarefreeVaughanLogSource.coefficient L (p*(q*(a*(b*r))))).re := by
  have hbr : b ≠ r := by
    intro he
    exact (hb.coprime_iff_not_dvd.mp
      (Nat.coprime_of_squarefree_mul hs.of_mul_right.of_mul_right.of_mul_right))
      (he ▸ dvd_refl b)
  have hR := ZetaRieszJointQuintupleFloor.riesz_three_primes_small_composite
    hp hq ha hs (fun he => hb.ne_one (mul_eq_one.mp he).1)
    (Nat.not_prime_mul hb.ne_one hr.ne_one) (by linarith) hqb hab (by linarith)
  rw [ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ hb hr hbr,
    ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ hb hr hbr,
    ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ hb hr hbr] at hR
  have horder : Real.log r ≤ Real.log b :=
    Real.log_le_log (by exact_mod_cast hr.pos) (by exact_mod_cast hrb)
  have h₁ := ZetaRieszOrderedCapacity.pair_tent_ge_interval_cap
    (Real.log_natCast_nonneg r) horder
    (show L-(v+h)-Real.log q ≤ L-Real.log p-Real.log q by linarith)
    (show L-Real.log p-Real.log q ≤ L-v-Real.log q by linarith)
  have h₂ := ZetaRieszOrderedCapacity.pair_tent_ge_interval_cap
    (Real.log_natCast_nonneg r) horder
    (show L-(v+h)-Real.log a ≤ L-Real.log p-Real.log a by linarith)
    (show L-Real.log p-Real.log a ≤ L-v-Real.log a by linarith)
  have h₃ := ZetaRieszOrderedCapacity.pair_tent_ge_interval_cap
    (Real.log_natCast_nonneg r) horder
    (le_refl (L-Real.log q-Real.log a)) (le_refl (L-Real.log q-Real.log a))
  have hc : fiveWindowCap L v h q a b r ≤ VaughanLogAverage.riesz L (p*(q*(a*(b*r)))) := by
    rw [hR]
    unfold fiveWindowCap
    have e₁ : Real.log b+Real.log r-(L-v-Real.log q) =
        Real.log b+Real.log r-L+v+Real.log q := by ring
    have e₂ : Real.log b+Real.log r-(L-v-Real.log a) =
        Real.log b+Real.log r-L+v+Real.log a := by ring
    have e₃ : Real.log b+Real.log r-(L-Real.log q-Real.log a) =
        Real.log b+Real.log r-L+Real.log q+Real.log a := by ring
    rw [e₁] at h₁
    rw [e₂] at h₂
    rw [e₃] at h₃
    linarith only [h₁,h₂,h₃]
  have hnp : ¬(p*(q*(a*(b*r)))).Prime := Nat.not_prime_mul hp.ne_one
    (fun he => hq.ne_one (mul_eq_one.mp he).1)
  rw [SquarefreeVaughanLogSource.coefficient,if_pos ⟨hs,hnp⟩,Complex.ofReal_re]
  have hh := mul_le_mul
    (div_le_div_of_nonneg_right htn hL.le) hc
    (fiveWindowCap_nonneg L v h q a b r)
    (div_nonneg (Real.log_natCast_nonneg _) hL.le)
  simpa only [neg_div,neg_mul,neg_neg,div_mul_eq_mul_div] using hh


private theorem five_primeFactors {p q a b r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hb : b.Prime) (hr : r.Prime) :
    (p*(q*(a*(b*r)))).primeFactors = {p,q,a,b,r} := by
  rw [Nat.primeFactors_mul hp.ne_zero
    (mul_ne_zero hq.ne_zero (mul_ne_zero ha.ne_zero (mul_ne_zero hb.ne_zero hr.ne_zero))),
    Nat.primeFactors_mul hq.ne_zero (mul_ne_zero ha.ne_zero (mul_ne_zero hb.ne_zero hr.ne_zero)),
    Nat.primeFactors_mul ha.ne_zero (mul_ne_zero hb.ne_zero hr.ne_zero),
    Nat.primeFactors_mul hb.ne_zero hr.ne_zero,
    hp.primeFactors,hq.primeFactors,ha.primeFactors,hb.primeFactors,hr.primeFactors]
  ext x
  simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_insert]

/-- Strict ordering pays squarefreeness and uniqueness; it is not an
independence assumption on the cofactor and the moving prime interval. -/
theorem squarefree_five_of_order {p q a b r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hb : b.Prime) (hr : r.Prime)
    (hqp : q < p) (haq : a < q) (hba : b < a) (hrb : r < b) :
    Squarefree (p*(q*(a*(b*r)))) := by
  have cpq : p.Coprime q := hp.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hp hq]; omega)
  have cpa : p.Coprime a := hp.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hp ha]; omega)
  have cpb : p.Coprime b := hp.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hp hb]; omega)
  have cpr : p.Coprime r := hp.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hp hr]; omega)
  have cqa : q.Coprime a := hq.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hq ha]; omega)
  have cqb : q.Coprime b := hq.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hq hb]; omega)
  have cqr : q.Coprime r := hq.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hq hr]; omega)
  have cab : a.Coprime b := ha.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq ha hb]; omega)
  have car : a.Coprime r := ha.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq ha hr]; omega)
  have cbr : b.Coprime r := hb.coprime_iff_not_dvd.mpr (by
    rw [Nat.prime_dvd_prime_iff_eq hb hr]; omega)
  exact Nat.squarefree_mul_iff.mpr ⟨cpq.mul_right (cpa.mul_right (cpb.mul_right cpr)),
    hp.squarefree,Nat.squarefree_mul_iff.mpr ⟨cqa.mul_right (cqb.mul_right cqr),
      hq.squarefree,Nat.squarefree_mul_iff.mpr ⟨cab.mul_right car,ha.squarefree,
        Nat.squarefree_mul_iff.mpr ⟨cbr,hb.squarefree,hr.squarefree⟩⟩⟩⟩

/-- A single fixed total-log interval gives a common signed phase credit.
The cosine is evaluated at every actual product, not replaced by a density. -/
theorem cofactor_phase_lower {m p : ℕ} (hm : m ≠ 0) {t h y : ℝ}
    (hp : p ∈ logPrimes (t-Real.log m) h) :
    -Real.cos (y*t)- |y| * h ≤ -Real.cos (y*Real.log (m*p : ℕ)) := by
  have hb := product_log_bounds hm hp
  have he : |y*Real.log (m*p : ℕ)-y*t| ≤ |y| * h := by
    rw [← mul_sub,abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg y)
    rw [abs_of_nonneg (by linarith [hb.2.1] : 0 ≤ Real.log (m*p : ℕ)-t)]
    linarith [hb.2.2]
  have hc := abs_le.mp ((Real.abs_cos_sub_cos_le (y*Real.log (m*p : ℕ)) (y*t)).trans he)
  linarith [hc.2]


/-- An actual signed prime-sum lower bound on the saturated five-prime
population. Ordering, squarefreeness, coefficient sign, old allocation and
phase variation are paid from explicit log inequalities. The final-prime
interval depends on the exact four-prime cofactor. -/
theorem eventually_five_cofactor_lower {h α : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (q a b r : ℕ) (t L y : ℝ),
      q.Prime → a.Prime → b.Prime → r.Prime → a < q → b < a → r < b →
      let m := q*(a*(b*r))
      let v := t-Real.log m
      0 < L → α*N ≤ v → Real.log q ≤ v → v+h ≤ (9/16 : ℝ)*t →
      v+h+Real.log (b*r : ℕ) ≤ L → L ≤ v+Real.log q+Real.log a →
      Real.cos (y*t)+|y| * h ≤ 0 →
      (((999/1000 : ℝ)*(t/L)*fiveWindowCap L v h q a b r*
          (-Real.cos (y*t)- |y| * h))*
          (Real.exp (-(t+h)/2)*t^N/N.factorial)/(m : ℝ))*
        ((9999/10000 : ℝ)*h/v) ≤
      (∑ p ∈ logPrimes v h,
        residualCoefficient A L N (m*p)*zetaPrimeLogKernel N (3/2+Complex.I*y) (m*p)).re := by
  filter_upwards [eventually_cofactor_lower hh hhu hα,
    ZetaRieszFivePrimePairSupply.eventually_unassigned_ge 5
      (by norm_num : (0 : ℝ) < 1/1000)]
    with N hN halloc A q a b r t L y hq ha hb hr haq hba hrb
  dsimp only
  intro hL hv hqv hvu hpb hpqa hphase
  let m := q*(a*(b*r))
  let v := t-Real.log m
  have hm : m ≠ 0 := mul_ne_zero hq.ne_zero (mul_ne_zero ha.ne_zero (mul_ne_zero hb.ne_zero hr.ne_zero))
  have ht : 0 ≤ t := by
    have hn : 0 ≤ α*(N : ℝ) := mul_nonneg hα.le (Nat.cast_nonneg N)
    linarith [Real.log_natCast_nonneg (q*(a*(b*r)))]
  have hφ : 0 ≤ -Real.cos (y*t)- |y| * h := by linarith
  apply hN m t L y _ A hm hv (by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg ht hL.le)) (fiveWindowCap_nonneg L v h q a b r)) hφ)
  intro p hp
  have hbnd := logPrimes_bounds hp
  have hp' := hbnd.1
  have hqp : q < p := by
    have hl : Real.log q < Real.log p := hqv.trans_lt hbnd.2.1
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hq.pos)
      (by exact_mod_cast hp'.pos)).mp hl
  have hs := squarefree_five_of_order hp' hq ha hb hr hqp haq hba hrb
  have hprod : m*p = p*(q*(a*(b*r))) := Nat.mul_comm _ _
  have hpf := five_primeFactors hp' hq ha hb hr
  have hmax : ∀ z ∈ (m*p).primeFactors, Real.log z ≤ (9/16 : ℝ)*Real.log (m*p : ℕ) := by
    intro z hz
    have hzp : z ≤ p := by
      rw [hprod,hpf] at hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> omega
    have hzlog : Real.log z ≤ Real.log p := Real.log_le_log
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hz).pos) (by exact_mod_cast hzp)
    have hbprod := product_log_bounds hm hp
    linarith [hbnd.2.2,hbprod.2.1]
  have hcard : (m*p).primeFactors.card ≤ 5 := by
    rw [hprod,hpf]
    exact Finset.card_le_five
  have hu := halloc A (m*p) hcard hmax
  have hc := five_coefficient_window_lower hp' hq ha hb hr hs hrb.le hL
    (show t ≤ Real.log (p*(q*(a*(b*r))) : ℕ) by
      rw [← hprod]; exact (product_log_bounds hm hp).2.1.le)
    hbnd.2.1.le hbnd.2.2 hpb
    (show Real.log q+Real.log (b*r : ℕ) ≤ L by linarith)
    (show Real.log a+Real.log (b*r : ℕ) ≤ L by
      have hqa : Real.log a ≤ Real.log q := Real.log_le_log
        (by exact_mod_cast ha.pos) (by exact_mod_cast haq.le)
      linarith)
    hpqa
  rw [← hprod] at hc
  have hph := cofactor_phase_lower hm hp (y := y)
  have hc0 : 0 ≤ (t/L)*fiveWindowCap L v h q a b r :=
    mul_nonneg (div_nonneg ht hL.le) (fiveWindowCap_nonneg L v h q a b r)
  have hu0 : 0 ≤ 1-boundedShare A N (m*p) := by linarith
  have hsc := mul_le_mul
    (mul_le_mul (show (999/1000 : ℝ) ≤ 1-boundedShare A N (m*p) by linarith)
      hc hc0 hu0) hph hφ (mul_nonneg hu0 (hc0.trans hc))
  simpa only [mul_assoc,neg_mul,mul_neg,neg_neg] using hsc


/-- The small fixed-count population remains in the literal original
core whenever its largest prime share is at most 9/16. This checks the
physical upper cutoff, all inherited masks, and both core edges. -/
theorem mem_core_of_prime_share_le (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (5/4 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    {n : ℕ} (hs : Squarefree n) (hc : 3 ≤ n.primeFactors.card)
    (hK : n.primeFactors.card < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
    (hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j < Real.log n)
    (hhi : Real.log n ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ (9/16 : ℝ)*Real.log n) :
    n ∈ ZetaRieszParityPacket.coreBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
      (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  have hN : (0 : ℝ) < N := by
    dsimp [N,ZetaRieszPrimeCountFrequency.dyadicMomentOrder,
      ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
    positivity
  have ht : 0 < Real.log n := by change (39/20 : ℝ)*N < _ at hlo; linarith
  have hW : n ∈ literalWindow N := (mem_literalWindow N n).mpr
    (by constructor <;> dsimp [N] at * <;> nlinarith)
  have hpX : ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 := by
    intro p hp
    have hplog : Real.log p < SquarefreeVaughanLogSource.length u N := by
      have hm := hmax p hp
      change Real.log n ≤ (203/100 : ℝ)*N at hhi
      change (5/4 : ℝ)*N ≤ _ at hL
      nlinarith
    have he : Real.log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ) =
        SquarefreeVaughanLogSource.length u N := by
      simp only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      (by positivity)).mp (he ▸ hplog)
  have hm := ZetaRieszMaskSupport.window_mem_originalMask j hj hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le) hL hW hs hc hK hpX
  have hdom (p : ℕ) (hp : p ∈ n.primeFactors) :
      Real.log p < (13/20 : ℝ)*Real.log n := by linarith [hmax p hp]
  have hcancel : n ∉ cancellingSector u N K := by
    intro hh
    obtain ⟨_,_,_,_,_,p,hp,_,_,_,hshare⟩ := Finset.mem_filter.mp hh
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd : Real.log (n/p : ℕ) = Real.log n-Real.log p := by
      rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp) (by exact_mod_cast hpp.ne_zero),
        Real.log_div (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hpp.ne_zero)]
    have hh := (div_le_iff₀ ht).mp hshare
    rw [hd] at hh
    nlinarith [hdom p hp]
  have hret : n ∈ ZetaRieszMaskSupport.retainedBand u N K :=
    Finset.mem_sdiff.mpr ⟨hm,hcancel⟩
  have hnd : n ∈ ZetaRieszDominantAllocation.nondominantBand u N K := by
    refine Finset.mem_sdiff.mpr ⟨hret,?_⟩
    intro hd
    obtain ⟨_,_,_,_,p,hp,_,_,hl⟩ := Finset.mem_filter.mp hd
    exact (hdom p hp).not_ge hl
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hnd,by constructor <;> dsimp [N] at * <;> nlinarith⟩,hlo,hhi⟩


private theorem five_count_of_order {p q a b r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : a.Prime) (hb : b.Prime) (hr : r.Prime)
    (hqp : q < p) (haq : a < q) (hba : b < a) (hrb : r < b) :
    (p*(q*(a*(b*r)))).primeFactors.card = 5 := by
  have h₁ : p ∉ ({q,a,b,r} : Finset ℕ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]; omega
  have h₂ : q ∉ ({a,b,r} : Finset ℕ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]; omega
  have h₃ : a ∉ ({b,r} : Finset ℕ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]; omega
  have h₄ : b ∉ ({r} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
  rw [five_primeFactors hp hq ha hb hr,Finset.card_insert_of_notMem h₁,
    Finset.card_insert_of_notMem h₂,Finset.card_insert_of_notMem h₃,
    Finset.card_insert_of_notMem h₄,Finset.card_singleton]

/-- Every point of an ordered cofactor-dependent prime window has the
exact count, squarefree support, largest-prime ownership and safe prime
shares. No hypothetical-zero assumption is needed. -/
theorem five_window_geometry {q a b r p : ℕ}
    (hq : q.Prime) (ha : a.Prime) (hb : b.Prime) (hr : r.Prime)
    (haq : a < q) (hba : b < a) (hrb : r < b) {t h : ℝ}
    (hqv : Real.log q ≤ t-Real.log (q*(a*(b*r)) : ℕ))
    (hvu : t-Real.log (q*(a*(b*r)) : ℕ)+h ≤ (9/16 : ℝ)*t)
    (hp : p ∈ logPrimes (t-Real.log (q*(a*(b*r)) : ℕ)) h) :
    Squarefree ((q*(a*(b*r)))*p) ∧ ((q*(a*(b*r)))*p).primeFactors.card = 5 ∧
      (∀ z ∈ ((q*(a*(b*r)))*p).primeFactors,
        Real.log z ≤ (9/16 : ℝ)*Real.log ((q*(a*(b*r)))*p : ℕ)) ∧
      (∀ z : ℕ, z.Prime → z ∣ q*(a*(b*r)) → z < p) := by
  have hp' := (logPrimes_bounds hp).1
  have hqp : q < p := by
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hq.pos)
      (by exact_mod_cast hp'.pos)).mp (hqv.trans_lt (logPrimes_bounds hp).2.1)
  have he : (q*(a*(b*r)))*p = p*(q*(a*(b*r))) := Nat.mul_comm _ _
  refine ⟨he ▸ squarefree_five_of_order hp' hq ha hb hr hqp haq hba hrb,
    he ▸ five_count_of_order hp' hq ha hb hr hqp haq hba hrb,?_,?_⟩
  · intro z hz
    have hzp : z ≤ p := by
      rw [he,five_primeFactors hp' hq ha hb hr] at hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> omega
    have hzlog : Real.log z ≤ Real.log p := Real.log_le_log
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hz).pos) (by exact_mod_cast hzp)
    have hbprod := product_log_bounds
      (mul_ne_zero hq.ne_zero (mul_ne_zero ha.ne_zero (mul_ne_zero hb.ne_zero hr.ne_zero))) hp
    linarith [(logPrimes_bounds hp).2.2,hbprod.2.1]
  · intro z hz hzd
    rcases hz.dvd_mul.mp hzd with hzq | hzad
    · have heq := (Nat.prime_dvd_prime_iff_eq hz hq).mp hzq
      omega
    rcases hz.dvd_mul.mp hzad with hza | hzbr
    · have heq := (Nat.prime_dvd_prime_iff_eq hz ha).mp hza
      omega
    rcases hz.dvd_mul.mp hzbr with hzb | hzr
    · have heq := (Nat.prime_dvd_prime_iff_eq hz hb).mp hzb
      omega
    · have heq := (Nat.prime_dvd_prime_iff_eq hz hr).mp hzr
      omega

/-- Independent population lower bounds can be spent once inside any
literal finite carrier. Ownership proves disjointness, and the entire
complement remains signed. -/
theorem owned_sum_lower (S M : Finset ℕ) (P : ℕ → Finset ℕ) (f : ℕ → ℂ) (B : ℕ → ℝ)
    (hm : ∀ m ∈ M, m ≠ 0)
    (hP : ∀ m ∈ M, ∀ p ∈ P m,
      p.Prime ∧ (∀ r : ℕ, r.Prime → r ∣ m → r < p) ∧ m*p ∈ S)
    (hB : ∀ m ∈ M, B m ≤ (∑ p ∈ P m, f (m*p)).re) :
    (∑ n ∈ S\(M.biUnion (fun m => (P m).image (fun p => m*p))), f n).re+
      ∑ m ∈ M, B m ≤ (∑ n ∈ S, f n).re := by
  let D := M.biUnion (fun m => (P m).image (fun p => m*p))
  have hDS : D ⊆ S := by
    intro n hn
    obtain ⟨m,hm',hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact (hP m hm' p hp).2.2
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hDS)
  rw [Complex.add_re] at he
  change (∑ n ∈ S\D, f n).re+_ ≤ (∑ n ∈ S, f n).re
  rw [← he]
  apply add_le_add le_rfl
  rw [sum_owned_products M P f hm (fun m hm' p hp =>
    ⟨(hP m hm' p hp).1,(hP m hm' p hp).2.1⟩),Complex.re_sum]
  exact Finset.sum_le_sum hB


/-- The explicit favorable five-prime credit is now a lower bound inside
the actual retained core, for any finite collection of ordered cofactors.
All coefficient, phase, allocation, ownership and original support obligations
are discharged. The remaining angular population comparison is not assumed. -/
theorem eventually_owned_five_core_lower {u h α : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) :
    ∀ᶠ j : ℕ in atTop, ∀ (M : Finset ℕ) (q a b r : ℕ → ℕ) (t y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let P := fun m : ℕ => logPrimes (t-Real.log m) h
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      Real.cos (y*t)+|y| * h ≤ 0 →
      (∀ m ∈ M, m = q m*(a m*(b m*r m)) ∧
        (q m).Prime ∧ (a m).Prime ∧ (b m).Prime ∧ (r m).Prime ∧
        a m < q m ∧ b m < a m ∧ r m < b m ∧
        α*N ≤ t-Real.log m ∧ Real.log (q m) ≤ t-Real.log m ∧
        t-Real.log m+h ≤ (9/16 : ℝ)*t ∧
        t-Real.log m+h+Real.log (b m*r m : ℕ) ≤ L ∧
        L ≤ t-Real.log m+Real.log (q m)+Real.log (a m)) →
      (∑ n ∈ ZetaRieszParityPacket.coreBand u N K\
          (M.biUnion (fun m => (P m).image (fun p => m*p))),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
      (∑ m ∈ M,
        (((999/1000 : ℝ)*(t/L)*fiveWindowCap L (t-Real.log m) h (q m) (a m) (b m) (r m)*
            (-Real.cos (y*t)- |y| * h))*(Real.exp (-(t+h)/2)*t^N/N.factorial)/(m : ℝ))*
          ((9999/10000 : ℝ)*h/(t-Real.log m))) ≤
      (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hroom : u < Real.exp (-(5/8 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  have hlength := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 5/8) hroom
  filter_upwards [eventually_ge_atTop 32,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlength,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_five_cofactor_lower hh hhu hα)] with j hj hL hbound M q a b r t y
  dsimp only
  intro hlo hhi hphase hM
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let P := fun m : ℕ => logPrimes (t-Real.log m) h
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hm : ∀ m ∈ M, m ≠ 0 := by
    intro m hm'
    obtain ⟨he,hq,ha,hb,hr,_⟩ := hM m hm'
    rw [he]
    exact mul_ne_zero hq.ne_zero (mul_ne_zero ha.ne_zero (mul_ne_zero hb.ne_zero hr.ne_zero))
  apply owned_sum_lower (ZetaRieszParityPacket.coreBand u N K) M P f _ hm
  · intro m hm' p hp
    obtain ⟨he,hq,ha,hb,hr,haq,hba,hrb,hv,hqv,hvu,_hpb,_hpqa⟩ := hM m hm'
    have hg := five_window_geometry hq ha hb hr haq hba hrb
      (by simpa only [← he] using hqv) (by simpa only [← he] using hvu) (by simpa only [← he] using hp)
    have hs : Squarefree (m*p) := by simpa only [← he] using hg.1
    have hc : (m*p).primeFactors.card = 5 := by simpa only [← he] using hg.2.1
    have hmax : ∀ z ∈ (m*p).primeFactors,
        Real.log z ≤ (9/16 : ℝ)*Real.log (m*p : ℕ) := by simpa only [← he] using hg.2.2.1
    refine ⟨(logPrimes_bounds hp).1,by simpa only [← he] using hg.2.2.2,?_⟩
    have hK : 5 < K := by
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show 3 ≤ j+3 by omega)
      dsimp [K,ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
      norm_num at hh
      omega
    have hprod := product_log_bounds (hm m hm') hp
    apply mem_core_of_prime_share_le j hj hu hU (by linarith) hs
      (by rw [hc]; decide) (by rw [hc]; exact hK)
      (lt_of_le_of_lt hlo hprod.2.1) (hprod.2.2.trans hhi) hmax
  · intro m hm'
    obtain ⟨he,hq,ha,hb,hr,haq,hba,hrb,hv,hqv,hvu,hpb,hpqa⟩ := hM m hm'
    have h := hbound A (q m) (a m) (b m) (r m) t L y hq ha hb hr haq hba hrb
      (SquarefreeVaughanLogSource.length_pos u N)
      (by simpa only [← he] using hv) (by simpa only [← he] using hqv) (by simpa only [← he] using hvu) (by simpa only [← he] using hpb) (by simpa only [← he] using hpqa) hphase
    simpa only [← he] using h

end
end RiemannGaussian.ZetaRieszCoupledWindow
