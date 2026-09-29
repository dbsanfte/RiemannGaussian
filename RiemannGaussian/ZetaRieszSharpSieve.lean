/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSieveMean
import RiemannGaussian.MoebiusHarmonicCancellation
import RiemannGaussian.NatDivisorSquareDirichlet

/-!
# Sharp Möbius cutoff estimates for Riesz variation

The signed harmonic rows are estimated with their logarithmic decay before
the common-divisor quadratic form is summed. All prime exclusions remain
explicit. This targets the derivative of the original Riesz cutoff.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSharpSieve

/-- The proved cubic-scale cancellation supplies a uniform inverse-square
logarithmic bound, including fractional physical endpoints. -/
theorem exists_harmonic_log_weight_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, ∀ x : ℝ, 1 ≤ x → (M : ℝ) ≤ x → x < M+1 →
      (4+Real.log x)^2*|moebiusHarmonicPrefix M| ≤ C := by
  obtain ⟨H,hH,hbound⟩ := exists_moebiusHarmonicPrefix_cubic_rate
  let A : ℝ := 2000000000000000
  let B : ℝ := (5+A)^2*(8^6*720)
  let C : ℝ := 1+2*(5+A*H^3)^2+moebiusHarmonicCancellationConstant*B
  have hA : 0 < A := by norm_num [A]
  have hB : 0 < B := by dsimp [B]; positivity
  have hC0 : 0 < C := by
    have := moebiusHarmonicCancellationConstant_pos
    dsimp [C]
    positivity
  refine ⟨C,hC0,fun M x hx hlo hhi => ?_⟩
  have hM : 0 < M := by
    by_contra h
    have : M = 0 := by omega
    simp only [this,Nat.cast_zero,zero_add] at hhi
    linarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hx0 : 0 < x := by linarith
  have hlogx : Real.log x ≤ Real.log M+1 := by
    have hr : x/M ≤ 2 := (div_le_iff₀ hMR).mpr (by linarith)
    have hb := Real.log_le_sub_one_of_pos (div_pos hx0 hMR)
    rw [Real.log_div hx0.ne' hMR.ne'] at hb
    linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  by_cases hlarge : A*H^3 ≤ Real.log M
  · let h := (Real.log (M : ℝ)/A)^((3 : ℝ)⁻¹)
    have hh0 : 0 ≤ h := Real.rpow_nonneg (by positivity [Real.log_nonneg hM1]) _
    have hcube : h^3 = Real.log (M : ℝ)/A :=
      Real.rpow_inv_natCast_pow (by positivity [Real.log_nonneg hM1])
        (by decide : (3 : ℕ) ≠ 0)
    have hlogM : Real.log (M : ℝ) = A*h^3 := by rw [hcube]; field_simp
    have hHh : H ≤ h := (pow_le_pow_iff_left₀ (by linarith) hh0
      (by decide : (3 : ℕ) ≠ 0)).mp ((mul_le_mul_iff_right₀ hA).mp (by
        simpa [hlogM,mul_comm] using hlarge))
    have hh1 : 1 ≤ h := by linarith
    have hc : 2*moebiusFiniteContourCenter h = Real.log M := by
      rw [hlogM]
      dsimp [moebiusFiniteContourCenter,A]
      ring
    have hm := hbound h hHh M (by rw [hc,Real.exp_log hMR])
    have hh3 : 1 ≤ h^3 := one_le_pow₀ hh1
    have hpoly : (4+Real.log x)^2 ≤ (5+A)^2*h^6 := by
      have hb : 4+Real.log x ≤ (5+A)*h^3 := by rw [hlogM] at hlogx; nlinarith
      have hp := pow_le_pow_left₀ (by positivity [hlx] : 0 ≤ 4+Real.log x) hb 2
      calc
        _ ≤ ((5+A)*h^3)^2 := hp
        _ = _ := by ring
    have hex := Real.pow_div_factorial_le_exp (h/8) (by positivity) 6
    have hpow : h^6 ≤ (8^6*720 : ℝ)*Real.exp (h/8) := by
      norm_num [Nat.factorial] at hex
      nlinarith only [hex]
    have hcancel : Real.exp (h/8)*Real.exp (-h/8) = 1 := by
      rw [← Real.exp_add,show h/8+-h/8 = 0 by ring,Real.exp_zero]
    calc
      _ ≤ ((5+A)^2*h^6)*(moebiusHarmonicCancellationConstant*Real.exp (-h/8)) :=
        mul_le_mul hpoly hm (abs_nonneg _) (by positivity)
      _ ≤ ((5+A)^2*((8^6*720 : ℝ)*Real.exp (h/8)))*
          (moebiusHarmonicCancellationConstant*Real.exp (-h/8)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (sq_nonneg _))
          (mul_nonneg moebiusHarmonicCancellationConstant_pos.le (Real.exp_pos _).le)
      _ = moebiusHarmonicCancellationConstant*B := by
        dsimp [B]
        calc
          _ = moebiusHarmonicCancellationConstant*((5+A)^2*(8^6*720))*
              (Real.exp (h/8)*Real.exp (-h/8)) := by ring
          _ = _ := by rw [hcancel,mul_one]
      _ ≤ C := by dsimp [C]; nlinarith [sq_nonneg (5+A*H^3)]
  · have hl : 4+Real.log x ≤ 5+A*H^3 := by linarith
    have hs := pow_le_pow_left₀ (by positivity [hlx] : 0 ≤ 4+Real.log x) hl 2
    have hm := mul_le_mul hs (abs_moebiusHarmonicPrefix_le_two M)
      (abs_nonneg _) (sq_nonneg _)
    have hp : 0 ≤ moebiusHarmonicCancellationConstant*B := by
      exact mul_nonneg moebiusHarmonicCancellationConstant_pos.le hB.le
    dsimp [C]
    nlinarith only [hm,hp]

/-- The logarithmic weight grows by at most a square-root local factor
when the physical cutoff is divided by a prime. -/
theorem log_weight_div {x p : ℝ} (hp : 1 ≤ p) (hx : p ≤ x) :
    (4+Real.log x)^2 ≤ Real.sqrt p*(4+Real.log (x/p))^2 := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := hp0.trans_le hx
  have hq : 1 ≤ x/p := (one_le_div hp0).mpr hx
  have hlp : 0 ≤ Real.log p := Real.log_nonneg hp
  have hlq : 0 ≤ Real.log (x/p) := Real.log_nonneg hq
  have hl : Real.log x = Real.log (x/p)+Real.log p := by
    rw [Real.log_div hx0.ne' hp0.ne']; ring
  have he := Real.add_one_le_exp (Real.log p/4)
  have hb : 4+Real.log x ≤ (4+Real.log (x/p))*Real.exp (Real.log p/4) := by
    rw [hl]
    nlinarith [mul_nonneg hlp hlq]
  have hs := pow_le_pow_left₀ (by positivity [Real.log_nonneg (hp.trans hx)] :
    0 ≤ 4+Real.log x) hb 2
  have heq : (Real.exp (Real.log p/4))^2 = Real.sqrt p := by
    rw [pow_two,← Real.exp_add,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hp0]
    congr 1
    ring
  simpa only [mul_pow,heq,mul_comm] using hs

/-- The sharp signed harmonic row with literal prime exclusions. -/
def harmonicPrefix (S : Finset ℕ) (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, if ∀ p ∈ S, ¬p ∣ n then (μ n : ℝ)/n else 0

@[simp] theorem harmonicPrefix_zero (S : Finset ℕ) : harmonicPrefix S 0 = 0 := by
  simp [harmonicPrefix]

/-- Prime exclusion keeps its exact smaller-cutoff correction. -/
theorem harmonicPrefix_insert (S : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hpS : p ∉ S) (hS : ∀ q ∈ S, q.Prime) (M : ℕ) :
    harmonicPrefix (insert p S) M = harmonicPrefix S M+
      (1/(p : ℝ))*harmonicPrefix (insert p S) (M/p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hdiv : harmonicPrefix S M = harmonicPrefix (insert p S) M+
      ∑ n ∈ Finset.Icc 1 M, if p ∣ n then
        (if ∀ q ∈ S, ¬q ∣ n then (μ n : ℝ)/n else 0) else 0 := by
    simp only [harmonicPrefix,← Finset.sum_add_distrib,Finset.forall_mem_insert]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hd : p ∣ n <;> by_cases h : ∀ q ∈ S, ¬q ∣ n <;> simp [hd,h]
  rw [sum_Icc_dvd_eq hp.pos] at hdiv
  have he : (∑ n ∈ Finset.Icc 1 (M/p), if ∀ q ∈ S, ¬q ∣ p*n then
      (μ (p*n) : ℝ)/(p*n : ℕ) else 0) =
      -(1/(p : ℝ))*harmonicPrefix (insert p S) (M/p) := by
    simp only [harmonicPrefix,Finset.mul_sum,Finset.forall_mem_insert]
    apply Finset.sum_congr rfl
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hsame : (∀ q ∈ S, ¬q ∣ p*n) ↔ (∀ q ∈ S, ¬q ∣ n) := by
      apply forall₂_congr
      intro q hq
      have hqp : ¬q ∣ p := by
        intro hd
        have heq : q = p := ((Nat.dvd_prime hp).mp hd).resolve_left (hS q hq).ne_one
        exact hpS (heq ▸ hq)
      simp [(hS q hq).dvd_mul,hqp]
    simp only [hsame,moebius_prime_mul_eq_not_dvd hp]
    by_cases hd : p ∣ n
    · simp [hd]
    rw [if_neg hd,Int.cast_neg]
    by_cases h : ∀ q ∈ S, ¬q ∣ n
    · rw [if_pos h,if_pos ⟨hd,h⟩]
      simp only [Nat.cast_mul,div_mul_eq_div_div]
      ring
    · rw [if_neg h,if_neg (fun hh => h hh.2)]
      simp
  rw [he] at hdiv
  linarith

/-- Local factors used only to pay exclusion in the signed harmonic row. -/
def halfExclusionCost (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, (1-(Real.sqrt p)⁻¹)⁻¹

/-- Every local exclusion factor is positive. -/
theorem halfExclusionCost_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 < halfExclusionCost S := by
  apply Finset.prod_pos
  intro p hp
  have h : (1 : ℝ) < Real.sqrt p := (Real.lt_sqrt (by norm_num)).mpr (by
    simpa using (show (1 : ℝ) < p by exact_mod_cast (hS p hp).one_lt))
  exact inv_pos.mpr (sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr h))

/-- Arbitrary prime exclusions preserve inverse-square logarithmic decay.
The same constant controls every cutoff and every finite prime set. -/
theorem exists_excluded_log_weight_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      ∀ M : ℕ, ∀ x : ℝ, 1 ≤ x → (M : ℝ) ≤ x → x < M+1 →
        (4+Real.log x)^2*|harmonicPrefix S M| ≤ C*halfExclusionCost S := by
  obtain ⟨C,hC,hbase⟩ := exists_harmonic_log_weight_bound
  refine ⟨C,hC,?_⟩
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ M x hx hlo hhi
    simpa [harmonicPrefix,halfExclusionCost,moebiusHarmonicPrefix] using hbase M x hx hlo hhi
  | @insert p S hpS ih =>
    intro hSP
    have hp := hSP p (Finset.mem_insert_self _ _)
    have hS : ∀ q ∈ S, q.Prime := fun q hq => hSP q (Finset.mem_insert_of_mem hq)
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hsq : (1 : ℝ) < Real.sqrt p := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hpR)
    have ht0 : 0 < 1-(Real.sqrt p)⁻¹ := sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr hsq)
    have hcost : halfExclusionCost (insert p S) =
        halfExclusionCost S/(1-(Real.sqrt p)⁻¹) := by
      simp only [halfExclusionCost,Finset.prod_insert hpS,div_eq_mul_inv,mul_comm]
    have hB : 0 < halfExclusionCost S := halfExclusionCost_pos S hS
    have hmono : C*halfExclusionCost S ≤ C*halfExclusionCost (insert p S) := by
      rw [hcost]
      apply mul_le_mul_of_nonneg_left ?_ hC.le
      apply (le_div_iff₀ ht0).mpr
      nlinarith [mul_nonneg hB.le (inv_nonneg.mpr (Real.sqrt_nonneg (p : ℝ)))]
    intro M
    induction M using Nat.strong_induction_on with
    | h M rec =>
      intro x hx hlo hhi
      have hM : 0 < M := by
        by_contra h
        have : M = 0 := by omega
        simp only [this,Nat.cast_zero,zero_add] at hhi
        linarith
      have hquot : M/p < M := Nat.div_lt_self hM hp.one_lt
      rw [harmonicPrefix_insert S hp hpS hS M]
      by_cases hpM : p ≤ M
      · have hx' : 1 ≤ x/p := (one_le_div (by linarith : (0 : ℝ) < p)).mpr
          ((by exact_mod_cast hpM : (p : ℝ) ≤ M).trans hlo)
        have hlo' : ((M/p : ℕ) : ℝ) ≤ x/p := by
          apply (le_div_iff₀ (by linarith : (0 : ℝ) < p)).mpr
          exact (show ((M/p : ℕ) : ℝ)*p ≤ M by exact_mod_cast Nat.div_mul_le_self M p).trans hlo
        have hhi' : x/p < (M/p : ℕ)+1 := by
          apply (div_lt_iff₀ (by linarith : (0 : ℝ) < p)).mpr
          exact hhi.trans_le (by
            exact_mod_cast (show M+1 ≤ (M/p+1)*p by
              have hh := Nat.lt_mul_div_succ M hp.pos
              simpa only [Nat.mul_comm] using Nat.succ_le_of_lt hh))
        have hrec := rec (M/p) hquot (x/p) hx' hlo' hhi'
        have hlog := log_weight_div hpR.le
          ((by exact_mod_cast hpM : (p : ℝ) ≤ M).trans hlo)
        have hroot : Real.sqrt (p : ℝ)/p = (Real.sqrt p)⁻¹ := by
          apply (div_eq_iff (by linarith : (p : ℝ) ≠ 0)).mpr
          have hs := Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
          field_simp [(by positivity : Real.sqrt (p : ℝ) ≠ 0)]
          nlinarith
        calc
          _ ≤ (4+Real.log x)^2*(|harmonicPrefix S M|+
              (1/(p : ℝ))*|harmonicPrefix (insert p S) (M/p)|) := by
            apply mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            simpa only [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(p : ℝ))] using abs_add_le
              (harmonicPrefix S M) ((1/(p : ℝ))*harmonicPrefix (insert p S) (M/p))
          _ ≤ C*halfExclusionCost S+
              (Real.sqrt p)⁻¹*(C*halfExclusionCost (insert p S)) := by
            rw [mul_add]
            apply add_le_add (ih hS M x hx hlo hhi)
            calc
              _ ≤ (Real.sqrt p*(4+Real.log (x/p))^2)*
                  ((1/(p : ℝ))*|harmonicPrefix (insert p S) (M/p)|) :=
                mul_le_mul_of_nonneg_right hlog (by positivity)
              _ = (Real.sqrt p/p)*((4+Real.log (x/p))^2*
                  |harmonicPrefix (insert p S) (M/p)|) := by ring
              _ ≤ _ := by rw [hroot]; exact mul_le_mul_of_nonneg_left hrec (by positivity)
          _ = C*halfExclusionCost (insert p S) := by
            rw [hcost]
            field_simp [ht0.ne',(show Real.sqrt (p : ℝ) ≠ 0 by linarith),
              (show Real.sqrt (p : ℝ)-1 ≠ 0 by linarith)]
            ring
      · rw [Nat.div_eq_of_lt (by omega : M < p),harmonicPrefix_zero,mul_zero,add_zero]
        exact (ih hS M x hx hlo hhi).trans hmono

private theorem half_factor_one_le {p : ℝ} (hp : 1 < p) :
    1 ≤ (1-(Real.sqrt p)⁻¹)⁻¹ := by
  have hs : (1 : ℝ) < Real.sqrt p := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hp)
  have ht : 0 < 1-(Real.sqrt p)⁻¹ := sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr hs)
  apply (one_le_inv₀ ht).mpr
  linarith [inv_nonneg.mpr (Real.sqrt_nonneg p)]

private theorem half_factor_square_le {p : ℝ} (hp : 16 ≤ p) :
    ((1-(Real.sqrt p)⁻¹)⁻¹)^2 ≤ 1+4/Real.sqrt p := by
  have hs : 4 ≤ Real.sqrt p := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by norm_num; exact hp)
  have hs0 : 0 < Real.sqrt p := by linarith
  let a := (Real.sqrt p)⁻¹
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha : a ≤ 1/4 := by
    dsimp [a]
    exact (inv_le_comm₀ hs0 (by norm_num)).mpr (by simpa using hs)
  have ht : 0 < 1-a := by linarith
  have hprod : 1 ≤ (1+4*a)*(1-a)^2 := by
    have hq : 0 ≤ a^2*(1-4*a) := mul_nonneg (sq_nonneg _) (by linarith)
    have hh : 0 ≤ a*(2-7*a) := mul_nonneg ha0 (by linarith)
    nlinarith [mul_nonneg ha0 (sq_nonneg a)]
  change ((1-a)⁻¹)^2 ≤ 1+4*a
  rw [inv_pow]
  apply (inv_le_iff_one_le_mul₀ (sq_pos_of_pos ht)).mpr
  nlinarith only [hprod]

/-- The finitely many small local factors are a fixed positive cost. -/
def smallPrimeCost : ℝ :=
  ∏ p ∈ Finset.Icc (2 : ℕ) 15, ((1-(Real.sqrt p)⁻¹)⁻¹)^2

/-- The fixed small-factor cost is at least one. -/
theorem smallPrimeCost_one_le : 1 ≤ smallPrimeCost := by
  unfold smallPrimeCost
  apply Finset.one_le_prod
  intro p hp
  have h := half_factor_one_le (p := (p : ℝ)) (by
    have := (Finset.mem_Icc.mp hp).1
    exact_mod_cast (by omega : 1 < p))
  nlinarith only [h,sq_nonneg ((1-(Real.sqrt (p : ℝ))⁻¹)⁻¹-1)]

/-- The squared exclusion cost has a divisor-square majorant whose
Dirichlet average is summable; there is no prime-count constant. -/
theorem halfExclusionCost_sq_le_divisors {g : ℕ} (hg : g ≠ 0) :
    (halfExclusionCost g.primeFactors)^2 ≤
      smallPrimeCost*(∑ d ∈ g.divisors, (d.divisors.card : ℝ)^2/Real.sqrt d) := by
  let S := g.primeFactors
  let U := S.filter (fun p => p < 16)
  let f := fun p : ℕ => ((1-(Real.sqrt p)⁻¹)⁻¹)^2
  have hSp p (hp : p ∈ S) := Nat.prime_of_mem_primeFactors hp
  have hUf : U ⊆ Finset.Icc 2 15 := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨(hSp p h.1).two_le,by omega⟩
  have hU : (∏ p ∈ U, f p) ≤ smallPrimeCost := by
    change (∏ p ∈ U, f p) ≤ ∏ p ∈ Finset.Icc 2 15, f p
    apply Finset.prod_le_prod_of_subset_of_one_le hUf
    · intro p _
      exact sq_nonneg _
    · intro p hp _
      have h := half_factor_one_le (p := (p : ℝ)) (by
        have := (Finset.mem_Icc.mp hp).1
        exact_mod_cast (by omega : 1 < p))
      dsimp [f]
      nlinarith only [h,sq_nonneg ((1-(Real.sqrt (p : ℝ))⁻¹)⁻¹-1)]
  have hf : (∏ p ∈ S, f p) ≤
      (∏ p ∈ U, f p)*(∏ p ∈ S, (1+4/Real.sqrt p)) := by
    rw [Finset.prod_filter]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro p _
      exact sq_nonneg _
    · intro p hp
      have hp0 : 0 < Real.sqrt (p : ℝ) := by positivity [(hSp p hp).pos]
      by_cases h : p < 16
      · simp only [if_pos h]
        have hh : 0 ≤ f p*(4/Real.sqrt p) := mul_nonneg (sq_nonneg _) (by positivity)
        nlinarith only [hh]
      · simp only [if_neg h,one_mul]
        exact half_factor_square_le (by exact_mod_cast (by omega : 16 ≤ p))
  have he := Nat.sum_divisors_filter_squarefree hg
    (f := fun d => (d.divisors.card : ℝ)^2/Real.sqrt d)
  rw [Nat.factors_eq] at he
  have hprod : (∏ p ∈ S, (1+4/Real.sqrt p)) =
      ∑ d ∈ g.divisors with Squarefree d, (d.divisors.card : ℝ)^2/Real.sqrt d := by
    rw [he,Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro T hT
    have hTP : ∀ p ∈ T, p.Prime := fun p hp => hSp p (Finset.mem_powerset.mp hT hp)
    have hsf : Squarefree (∏ p ∈ T, p) := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        exact Nat.coprime_iff_isRelPrime.mp ((hTP p hp).coprime_iff_not_dvd.mpr
          (fun hd => hpq (((hTP q hq).dvd_iff_eq (hTP p hp).ne_one).mp hd).symm))
      · intro p hp
        exact (hTP p hp).squarefree
    rw [show T.val.prod = ∏ p ∈ T, p by
      simp only [Finset.prod_eq_multiset_prod,Multiset.map_id']]
    rw [ZetaRieszSmoothHead.card_divisors_of_squarefree hsf,Nat.primeFactors_prod hTP]
    simp only [Finset.prod_div_distrib,Finset.prod_const,Nat.cast_pow,Nat.cast_ofNat,
      Nat.cast_prod,Real.sqrt_prod T (fun _ _ => Nat.cast_nonneg _)]
    rw [← pow_mul,show T.card*2 = 2*T.card by omega,pow_mul]
    norm_num
  have hbig : (∏ p ∈ S, (1+4/Real.sqrt p)) ≤
      ∑ d ∈ g.divisors, (d.divisors.card : ℝ)^2/Real.sqrt d := by
    rw [hprod]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
  calc
    _ = ∏ p ∈ S, f p := by simp only [halfExclusionCost,Finset.prod_pow,S,f]
    _ ≤ (∏ p ∈ U, f p)*(∏ p ∈ S, (1+4/Real.sqrt p)) := hf
    _ ≤ smallPrimeCost*(∑ d ∈ g.divisors, (d.divisors.card : ℝ)^2/Real.sqrt d) :=
      mul_le_mul hU hbig (by positivity) (le_trans (by norm_num) smallPrimeCost_one_le)

/-- The decaying logarithmic row weights have a uniform harmonic sum.
This is the summation step that removes the earlier growing logarithm. -/
theorem logarithmic_row_sum_le_two (M : ℕ) {x : ℝ} (hx : 0 < x)
    (hMx : (M : ℝ) ≤ x) :
    (∑ n ∈ Finset.Icc 1 M, 1/((n : ℝ)*(4+Real.log (x/n))^4)) ≤ 2 := by
  rcases M.eq_zero_or_pos with rfl | hM
  · simp
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  let H := fun t : ℝ => 4+Real.log x-Real.log t
  let f := fun t : ℝ => t⁻¹*(H t^4)⁻¹
  let F := fun t : ℝ => (H t^3)⁻¹/3
  have hH t (ht : t ∈ Set.Icc (1 : ℝ) M) : 4 ≤ H t := by
    have ht0 : 0 < t := by linarith [ht.1]
    have hl := Real.log_le_log ht0 (ht.2.trans hMx)
    dsimp [H]
    linarith
  have hder t (ht : t ∈ Set.Icc (1 : ℝ) M) :
      HasDerivAt f ((4-H t)/(t^2*H t^5)) t := by
    have ht0 : 0 < t := by linarith [ht.1]
    have hHt : 0 < H t := by linarith [hH t ht]
    have hh : HasDerivAt H (-t⁻¹) t := by
      simpa only [H,Pi.sub_apply,zero_sub] using!
        (hasDerivAt_const t (4+Real.log x)).sub (Real.hasDerivAt_log ht0.ne')
    have hd := ((hasDerivAt_id t).inv ht0.ne').mul ((hh.pow 4).inv (pow_ne_zero 4 hHt.ne'))
    apply hd.congr_deriv
    dsimp only [Pi.inv_apply,Pi.pow_apply,id_eq]
    change -1/t^2*(H t^4)⁻¹+t⁻¹*(-(4*H t^3*(-t⁻¹))/(H t^4)^2) = _
    field_simp [ht0.ne',hHt.ne']
    ring
  have hc : ContinuousOn f (Set.Icc (1 : ℝ) M) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hanti : AntitoneOn f (Set.Icc (1 : ℝ) M) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc
    · intro t ht
      exact (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hder t (interior_subset ht)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hH t (interior_subset ht)])
        (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith [hH t (interior_subset ht)]) _))
  have hprim t (ht : t ∈ Set.Icc (1 : ℝ) M) : HasDerivAt F (f t) t := by
    have ht0 : 0 < t := by linarith [ht.1]
    have hHt : 0 < H t := by linarith [hH t ht]
    have hh : HasDerivAt H (-t⁻¹) t := by
      simpa only [H,Pi.sub_apply,zero_sub] using!
        (hasDerivAt_const t (4+Real.log x)).sub (Real.hasDerivAt_log ht0.ne')
    have hd := ((hh.pow 3).inv (pow_ne_zero 3 hHt.ne')).div_const 3
    apply hd.congr_deriv
    dsimp only [f,Pi.inv_apply,Pi.pow_apply]
    field_simp [ht0.ne',hHt.ne']
    ring
  have hint : IntervalIntegrable f MeasureTheory.volume 1 M := hc.intervalIntegrable_of_Icc hM1
  have hi : (∫ t in (1 : ℝ)..M, f t) = F M-F 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hprim t
      (by simpa only [Set.uIcc_of_le hM1] using ht)) hint
  have hF0 : 0 ≤ F 1 := by
    dsimp [F]
    positivity [show 0 ≤ H 1 by linarith [hH 1 ⟨le_rfl,hM1⟩]]
  have hFM : F M ≤ 1 := by
    have hHp : 0 < H M := by linarith [hH M ⟨hM1,le_rfl⟩]
    have hb : (H M^3)⁻¹ ≤ 1 := (inv_le_one₀ (pow_pos hHp _)).mpr
      (one_le_pow₀ (by linarith [hH M ⟨hM1,le_rfl⟩]))
    dsimp [F]
    linarith
  have hf1 : f 1 ≤ 1 := by
    have hHp : 0 < H 1 := by linarith [hH 1 ⟨le_rfl,hM1⟩]
    dsimp only [f]
    rw [inv_one,one_mul]
    exact (inv_le_one₀ (pow_pos hHp _)).mpr (one_le_pow₀ (by linarith [hH 1 ⟨le_rfl,hM1⟩]))
  have hsum := AntitoneOn.sum_le_integral_Ico (f := f) (a := 1) (b := M)
    (by omega) (by simpa only [Nat.cast_one] using hanti)
  rw [Finset.sum_Ico_add' (fun n : ℕ => f n) 1 M 1] at hsum
  have hset : Finset.Ico (1+1) (M+1) = Finset.Icc 2 M := by
    ext n
    simp only [Finset.mem_Ico,Finset.mem_Icc]
    omega
  rw [hset] at hsum
  simp only [Nat.cast_one] at hsum
  have he : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext n
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hs : (∑ n ∈ Finset.Icc 1 M, f n) ≤ 2 := by
    rw [he,Finset.sum_insert (by simp)]
    simp only [Nat.cast_one]
    linarith only [hsum,hi,hF0,hFM,hf1]
  convert hs using 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  dsimp [f,H]
  rw [Real.log_div hx.ne' hn0.ne',show 4+(Real.log x-Real.log n) =
    4+Real.log x-Real.log n by ring]
  simp only [one_div,mul_inv_rev]
  ring

/-- Averaging the complete squared exclusion factors together with the
signed-row decay costs one fixed divisor Dirichlet mass. -/
theorem excluded_row_square_sum_bound (R : ℕ) :
    (∑ g ∈ Finset.Icc 1 R, (halfExclusionCost g.primeFactors)^2/
      ((g : ℝ)*(4+Real.log ((R : ℝ)/g))^4)) ≤
        2*smallPrimeCost*divisorSquareDirichletMass (3/2) := by
  rcases R.eq_zero_or_pos with rfl | hR
  · simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),Finset.sum_empty]
    positivity [smallPrimeCost_one_le,divisorSquareDirichletMass_nonneg (3/2)]
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  let a := fun d : ℕ => (d.divisors.card : ℝ)^2/Real.sqrt d
  let w := fun g : ℕ => 1/((g : ℝ)*(4+Real.log ((R : ℝ)/g))^4)
  have hw g : 0 ≤ w g := by dsimp [w]; positivity
  have hmain : (∑ g ∈ Finset.Icc 1 R, ∑ d ∈ g.divisors, a d*w g) =
      ∑ d ∈ Finset.Icc 1 R, (a d/d)*
        ∑ n ∈ Finset.Icc 1 (R/d), 1/((n : ℝ)*(4+Real.log (((R : ℝ)/d)/n))^4) := by
    have he g : (∑ d ∈ g.divisors, a d*w g) =
        ∑ ab ∈ g.divisorsAntidiagonal, a ab.1*w (ab.1*ab.2) := by
      rw [Nat.sum_divisorsAntidiagonal (fun d n => a d*w (d*n))]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    simp_rw [he]
    rw [ZetaRieszGlobalCurvature.weighted_hyperbola (fun d n => a d*w (d*n))]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [w]
    simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
    ring
  have hmass : (∑ d ∈ Finset.Icc 1 R, a d/d) ≤ divisorSquareDirichletMass (3/2) := by
    have he d (hd : d ∈ Finset.Icc 1 R) : a d/d =
        (d.divisors.card : ℝ)^2*(d : ℝ)^(-(3/2 : ℝ)) := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      dsimp [a]
      rw [Real.sqrt_eq_rpow,show -(3/2 : ℝ) = -(1/2+1) by ring,
        Real.rpow_neg hd0.le,Real.rpow_add hd0,Real.rpow_one]
      ring
    rw [Finset.sum_congr rfl he]
    exact (summable_card_divisors_sq_mul_rpow_neg (by norm_num : (1 : ℝ) < 3/2)).sum_le_tsum
      _ (fun _ _ => by positivity)
  calc
    _ = ∑ g ∈ Finset.Icc 1 R, (halfExclusionCost g.primeFactors)^2*w g := by
      simp only [w,div_eq_mul_inv,one_mul]
    _ ≤ ∑ g ∈ Finset.Icc 1 R, smallPrimeCost*(∑ d ∈ g.divisors, a d)*w g := by
      apply Finset.sum_le_sum
      intro g hg
      exact mul_le_mul_of_nonneg_right
        (halfExclusionCost_sq_le_divisors (Nat.ne_of_gt (Finset.mem_Icc.mp hg).1)) (hw g)
    _ = smallPrimeCost*(∑ g ∈ Finset.Icc 1 R, ∑ d ∈ g.divisors, a d*w g) := by
      simp only [← Finset.mul_sum,Finset.sum_mul,mul_assoc]
    _ ≤ smallPrimeCost*(2*∑ d ∈ Finset.Icc 1 R, a d/d) := by
      apply mul_le_mul_of_nonneg_left ?_ (by linarith [smallPrimeCost_one_le])
      rw [hmain,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hfloor : ((R/d : ℕ) : ℝ) ≤ (R : ℝ)/d := (le_div_iff₀ hd0).mpr
        (by exact_mod_cast Nat.div_mul_le_self R d)
      have hb := logarithmic_row_sum_le_two (R/d) (div_pos hRR hd0) hfloor
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb
        (show 0 ≤ a d/d by dsimp [a]; positivity)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 2*smallPrimeCost by linarith [smallPrimeCost_one_le])
      nlinarith only [h]

private theorem coprime_iff_excluded {g : ℕ} (hg : g ≠ 0) (n : ℕ) :
    g.Coprime n ↔ ∀ p ∈ g.primeFactors, ¬p ∣ n := by
  constructor
  · intro hc p hp hd
    exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one
      ((Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hd).trans (by rw [hc.gcd_eq_one]))
  · intro h
    by_contra hc
    obtain ⟨p,hp,hpg,hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact h p (hp.mem_primeFactors hpg hg) hpn

/-- A common-divisor harmonic row keeps the exact excluded-prime prefix. -/
theorem harmonic_row_eq (R g : ℕ) (hg : 0 < g) :
    (∑ d ∈ Finset.Icc 1 R, if g ∣ d then (μ d : ℝ)/d else 0) =
      (μ g : ℝ)/g*harmonicPrefix g.primeFactors (R/g) := by
  rw [sum_Icc_dvd_eq hg]
  simp only [harmonicPrefix,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hsf : Squarefree g
  · by_cases hc : g.Coprime n
    · rw [if_pos ((coprime_iff_excluded hg.ne' n).mp hc),
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc]
      simp only [Int.cast_mul,Nat.cast_mul,div_mul_eq_div_div]
      ring
    · rw [if_neg (fun h => hc ((coprime_iff_excluded hg.ne' n).mpr h)),
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree
          (fun hs => hc (Nat.coprime_of_squarefree_mul hs))]
      simp
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun hs => hsf hs.of_mul_left)]
    simp

/-- The actual sharp Möbius lcm quadratic form is bounded by one fixed
constant at every cutoff. All common-divisor rows and prime counts are
included; no external arithmetic estimate is assumed. -/
theorem exists_sharp_quadratic_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ R : ℕ,
      (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        (μ d : ℝ)*(μ e : ℝ)/(Nat.lcm d e : ℝ)) ≤ E := by
  obtain ⟨C,hC,hbound⟩ := exists_excluded_log_weight_bound
  let E := 1+2*C^2*smallPrimeCost*divisorSquareDirichletMass (3/2)
  have hsmall : 0 ≤ smallPrimeCost := by linarith [smallPrimeCost_one_le]
  have hmass := divisorSquareDirichletMass_nonneg (3/2)
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨E,hE,fun R => ?_⟩
  rw [ZetaRieszSieveQuadratic.quadratic_eq_diagonal]
  have hrow g (hg : g ∈ Finset.Icc 1 R) :
      (g.totient : ℝ)*(∑ d ∈ Finset.Icc 1 R, if g ∣ d then (μ d : ℝ)/d else 0)^2 ≤
        C^2*((halfExclusionCost g.primeFactors)^2/
          ((g : ℝ)*(4+Real.log ((R : ℝ)/g))^4)) := by
    have hg0 : 0 < g := (Finset.mem_Icc.mp hg).1
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
    have hx : 1 ≤ (R : ℝ)/g := (one_le_div hgR).mpr (by exact_mod_cast (Finset.mem_Icc.mp hg).2)
    have hl : 0 < 4+Real.log ((R : ℝ)/g) := by positivity [Real.log_nonneg hx]
    have hb := hbound g.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)
      (R/g) ((R : ℝ)/g) hx
      ((le_div_iff₀ hgR).mpr (by exact_mod_cast Nat.div_mul_le_self R g)) (by
        apply (div_lt_iff₀ hgR).mpr
        exact_mod_cast (show R < (R/g+1)*g by
          simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ R hg0))
    have hw : (4+Real.log ((R : ℝ)/g))^2*
        |∑ d ∈ Finset.Icc 1 R, if g ∣ d then (μ d : ℝ)/d else 0| ≤
          C*halfExclusionCost g.primeFactors/g := by
      rw [harmonic_row_eq R g hg0,abs_mul,abs_div,abs_of_pos hgR]
      calc
        _ ≤ (4+Real.log ((R : ℝ)/g))^2*
            ((1/(g : ℝ))*|harmonicPrefix g.primeFactors (R/g)|) := by
          apply mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (abs_real_moebius_le_one g) hgR.le) (abs_nonneg _)
        _ = ((4+Real.log ((R : ℝ)/g))^2*|harmonicPrefix g.primeFactors (R/g)|)/g := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hb hgR.le
    have habs : |∑ d ∈ Finset.Icc 1 R, if g ∣ d then (μ d : ℝ)/d else 0| ≤
        (C*halfExclusionCost g.primeFactors/g)/(4+Real.log ((R : ℝ)/g))^2 :=
      (le_div_iff₀ (sq_pos_of_pos hl)).mpr (by simpa only [mul_comm] using hw)
    have hs := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hs
    have ht : (g.totient : ℝ) ≤ g := by exact_mod_cast Nat.totient_le g
    calc
      _ ≤ (g : ℝ)*((C*halfExclusionCost g.primeFactors/g)/
          (4+Real.log ((R : ℝ)/g))^2)^2 :=
        mul_le_mul ht hs (sq_nonneg _) hgR.le
      _ = _ := by field_simp [hgR.ne',hl.ne']
  calc
    _ ≤ ∑ g ∈ Finset.Icc 1 R, C^2*((halfExclusionCost g.primeFactors)^2/
        ((g : ℝ)*(4+Real.log ((R : ℝ)/g))^4)) := Finset.sum_le_sum hrow
    _ = C^2*∑ g ∈ Finset.Icc 1 R, (halfExclusionCost g.primeFactors)^2/
        ((g : ℝ)*(4+Real.log ((R : ℝ)/g))^4) := by rw [Finset.mul_sum]
    _ ≤ C^2*(2*smallPrimeCost*divisorSquareDirichletMass (3/2)) :=
      mul_le_mul_of_nonneg_left (excluded_row_square_sum_bound R) (sq_nonneg _)
    _ ≤ E := by dsimp [E]; linarith

/-- The literal sharp divisor response has a uniform mean-square main
term. The exact finite floor error remains displayed as `R^2`. -/
theorem exists_sharp_mean_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ X R : ℕ,
      (∑ n ∈ Finset.Icc 1 X,
        (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤ E*X+R^2 := by
  obtain ⟨E,hE,hbound⟩ := exists_sharp_quadratic_bound
  refine ⟨E,hE,fun X R => ?_⟩
  have h := ZetaRieszSieveMean.mean_square_le X R (fun d => (μ d : ℝ))
  have hm : (∑ d ∈ Finset.Icc 1 R, |(μ d : ℝ)|) ≤ R := by
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 R, (1 : ℝ) :=
        Finset.sum_le_sum (fun d _ => abs_real_moebius_le_one d)
      _ = _ := by simp
  have hs := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hm 2
  have hb := mul_le_mul_of_nonneg_left (hbound R) (Nat.cast_nonneg (α := ℝ) X)
  nlinarith only [h,hs,hb]

/-- The same signed quadratic controls any integer interval. The two
floor errors differ by at most one, so there is still only one coefficient
mass squared, independently of the location of the interval. -/
theorem interval_mean_square_le (X Y R : ℕ) (hYX : Y ≤ X) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc Y X, (∑ d ∈ Finset.Icc 1 R, if d ∣ n then f d else 0)^2) ≤
      ((X : ℝ)-Y)*(∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        f d*f e/(Nat.lcm d e : ℝ))+(∑ d ∈ Finset.Icc 1 R, |f d|)^2 := by
  have hset : Finset.Icc 1 X \ Finset.Icc 1 Y = Finset.Ioc Y X := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have he : (∑ n ∈ Finset.Ioc Y X,
      (∑ d ∈ Finset.Icc 1 R, if d ∣ n then f d else 0)^2) =
        ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          f d*f e*(((X/Nat.lcm d e : ℕ) : ℝ)-(Y/Nat.lcm d e : ℕ)) := by
    have h := Finset.sum_sdiff (f := fun n =>
      (∑ d ∈ Finset.Icc 1 R, if d ∣ n then f d else 0)^2)
        (Finset.Icc_subset_Icc (show (1 : ℕ) ≤ 1 from le_rfl) hYX)
    rw [hset,ZetaRieszSieveMean.mean_square_eq,ZetaRieszSieveMean.mean_square_eq] at h
    simp only [mul_sub,Finset.sum_sub_distrib]
    linarith only [h]
  rw [he]
  have hp d (hd : d ∈ Finset.Icc 1 R) e (he : e ∈ Finset.Icc 1 R) :
      f d*f e*(((X/Nat.lcm d e : ℕ) : ℝ)-(Y/Nat.lcm d e : ℕ)) ≤
        ((X : ℝ)-Y)*(f d*f e/(Nat.lcm d e : ℝ))+|f d| * |f e| := by
    let l := Nat.lcm d e
    have hl : 0 < l := Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    have hlR : (0 : ℝ) < l := by exact_mod_cast hl
    have hlo (T : ℕ) : ((T/l : ℕ) : ℝ) ≤ (T : ℝ)/l := by
      apply (le_div_iff₀ hlR).mpr
      exact_mod_cast Nat.div_mul_le_self T l
    have hhi (T : ℕ) : (T : ℝ)/l ≤ (T/l : ℕ)+1 := by
      apply (div_le_iff₀ hlR).mpr
      exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ T hl).le)
    have hb : |((X/l : ℕ) : ℝ)-(Y/l : ℕ)-((X : ℝ)-Y)/l| ≤ 1 := by
      rw [sub_div]
      exact abs_le.mpr (by constructor <;> linarith only [hlo X,hlo Y,hhi X,hhi Y])
    have hh := mul_le_mul_of_nonneg_left hb (abs_nonneg (f d*f e))
    rw [← abs_mul,mul_one] at hh
    have hu := (abs_le.mp hh).2
    rw [abs_mul] at hu
    dsimp only [l] at hu
    calc
      _ = f d*f e*(((X/Nat.lcm d e : ℕ) : ℝ)-(Y/Nat.lcm d e : ℕ)-
          ((X : ℝ)-Y)/(Nat.lcm d e : ℝ))+
            ((X : ℝ)-Y)*(f d*f e/(Nat.lcm d e : ℝ)) := by ring
      _ ≤ |f d| * |f e|+((X : ℝ)-Y)*(f d*f e/(Nat.lcm d e : ℝ)) := by
        linarith only [hu]
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        (((X : ℝ)-Y)*(f d*f e/(Nat.lcm d e : ℝ))+|f d| * |f e|) :=
      Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hp d hd e he))
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
      ring

/-- All intervals and all prime counts share one constant. No subtraction
of two upper bounds is used: the interval's literal counting error is paid. -/
theorem exists_sharp_interval_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ X Y R : ℕ, Y ≤ X →
      (∑ n ∈ Finset.Ioc Y X,
        (∑ d ∈ Finset.Icc 1 R, if d ∣ n then (μ d : ℝ) else 0)^2) ≤
          E*((X : ℝ)-Y)+R^2 := by
  obtain ⟨E,hE,hbound⟩ := exists_sharp_quadratic_bound
  refine ⟨E,hE,fun X Y R hYX => ?_⟩
  have h := interval_mean_square_le X Y R hYX (fun d => (μ d : ℝ))
  have hm : (∑ d ∈ Finset.Icc 1 R, |(μ d : ℝ)|) ≤ R := by
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 R, (1 : ℝ) :=
        Finset.sum_le_sum (fun d _ => abs_real_moebius_le_one d)
      _ = _ := by simp
  have hs := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hm 2
  have hb := mul_le_mul_of_nonneg_left (hbound R)
    (sub_nonneg.mpr (by exact_mod_cast hYX : (Y : ℝ) ≤ X))
  nlinarith only [h,hs,hb]

end RiemannGaussian.ZetaRieszSharpSieve
