/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorPrimeGcdContrast

/-!
# All nontrivial integer dilations of a Mangoldt label lose the source

The full finite hyperbola contains EVERY ordinary integer factor and
EVERY proper prime power. A nonzero Mangoldt label with two factors
larger than one is a proper power of a single prime. All moving coded
dilations join into a square-root-supported family, INCLUDING equal
factor powers. Polynomial-logarithmic matrix budgets are source-o(1)
for every beta greater than one half. The two unit-factor boundaries
retain the original arbitrary-weight prime sum and are NOT paid.

This fails the extra-source gate, not the RH theorem. Products of two
separate Mangoldt weights, dense divisor rows, and amplitudes that grow
faster than the stated budget are outside the audit.
-/

namespace RiemannGaussian.ArithmeticOperatorDilationPowerAudit
noncomputable section
open Complex Filter ArithmeticOperatorFloorInverseAudit
open scoped BigOperators Topology ArithmeticFunction.vonMangoldt

/-- Literal total-product cutoff, including equal factor pairs. -/
def factorPairs (J : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 (2^(2*J))).product (Finset.Icc 2 (2^(2*J)))).filter
    (fun ab => ab.1*ab.2≤2^(2*J))

/-- Entire nontrivial dilation packet; phases and correlated codes are
kept inside the matrix, not assigned to either factor separately. -/
def nontrivial (J : ℕ) (K : ℕ → ℕ → ℂ) : ℂ :=
  ∑ ab ∈ factorPairs J, (Λ (ab.1*ab.2) : ℂ)*K ab.1 ab.2

/-- Full positive-factor hyperbola before the unit boundaries are joined. -/
def full (J : ℕ) (K : ℕ → ℕ → ℂ) : ℂ :=
  ∑ a ∈ Finset.Icc 1 (2^(2*J)), ∑ b ∈ Finset.Icc 1 (2^(2*J)),
    if a*b≤2^(2*J) then (Λ (a*b) : ℂ)*K a b else 0

/-- Both exact unit-factor boundaries; no original source is removed. -/
def units (J : ℕ) (K : ℕ → ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (2^(2*J)), (Λ n : ℂ)*(K 1 n+K n 1)

private theorem split_rectangle {X : ℕ} (hX : 1≤X) (F : ℕ → ℕ → ℂ)
    (hF : F 1 1=0) :
    (∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X, F a b)=
      (∑ n ∈ Finset.Icc 1 X, (F 1 n+F n 1))+
      ∑ a ∈ Finset.Icc 2 X, ∑ b ∈ Finset.Icc 2 X, F a b := by
  have he : Finset.Icc 1 X=insert 1 (Finset.Icc 2 X) := by
    ext n
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hn : 1 ∉ Finset.Icc 2 X := by simp
  simp only [he,Finset.sum_insert hn,Finset.sum_add_distrib,hF,zero_add]
  ring

/-- Exact finite integer ledger before any norm. Unit-factor sources
and all remaining factor incidences have been kept, with no completion. -/
theorem full_eq_units_add_nontrivial (J : ℕ) (K : ℕ → ℕ → ℂ) :
    full J K=units J K+nontrivial J K := by
  classical
  unfold full
  rw [split_rectangle (Nat.one_le_pow (2*J) 2 (by norm_num))
    (fun a b => if a*b≤2^(2*J) then (Λ (a*b) : ℂ)*K a b else 0) (by simp)]
  congr 1
  · unfold units
    apply Finset.sum_congr rfl
    intro n hn
    have h := (Finset.mem_Icc.mp hn).2
    simp only [one_mul,mul_one,ite_eq_left h,mul_add]
  · unfold nontrivial factorPairs
    simp only [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]

/-- Exact active integer support, not an assumed model of primes.
Both factors of a nonzero Mangoldt label are powers of ONE prime. -/
theorem active_factors {a b : ℕ} (ha : 1<a) (hb : 1<b)
    (hactive : Λ (a*b)≠0) :
    ∃ p r s : ℕ, p.Prime ∧ 0<r ∧ 0<s ∧ a=p^r ∧ b=p^s := by
  obtain ⟨p,k,hp,hk,he⟩ := (isPrimePow_nat_iff (a*b)).mp
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hactive)
  obtain ⟨r,_,hr⟩ := (Nat.dvd_prime_pow hp).mp
    (show a ∣ p^k by rw [he]; exact dvd_mul_right a b)
  obtain ⟨s,_,hs⟩ := (Nat.dvd_prime_pow hp).mp
    (show b ∣ p^k by rw [he]; exact dvd_mul_left b a)
  have hr0 : 0<r := by
    by_contra hh
    have hz : r=0 := by omega
    have ha1 : a=1 := by simpa only [hz,pow_zero] using hr
    omega
  have hs0 : 0<s := by
    by_contra hh
    have hz : s=0 := by omega
    have hb1 : b=1 := by simpa only [hz,pow_zero] using hs
    omega
  exact ⟨p,r,s,hp,hr0,hs0,hr,hs⟩

/-- Finite exponent support for ALL coded nontrivial dilations together. -/
def supportImage (J : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.Icc 1 (2^J)).filter Nat.Prime).product
    ((Finset.Icc 1 (2*J)).product (Finset.Icc 1 (2*J)))).image
      (fun v => (v.1^v.2.1,v.1^v.2.2))

/-- Total-product geometry forces the base below the square-root cutoff.
The r=s diagonal is included; no cross-power exclusion is used. -/
theorem active_pair_mem {J : ℕ} {ab : ℕ × ℕ} (hab : ab ∈ factorPairs J)
    (hactive : Λ (ab.1*ab.2)≠0) : ab ∈ supportImage J := by
  obtain ⟨hab,hcut⟩ := Finset.mem_filter.mp hab
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  obtain ⟨p,r,s,hp,hr0,hs0,hr,hs⟩ :=
    active_factors (by have := (Finset.mem_Icc.mp ha).1; omega)
      (by have := (Finset.mem_Icc.mp hb).1; omega) hactive
  have hpow : p^(r+s)≤2^(2*J) := by rw [pow_add,←hr,←hs]; exact hcut
  have hsum : r+s≤2*J := (Nat.pow_le_pow_iff_right (by norm_num : 1<(2 : ℕ))).mp
    ((Nat.pow_le_pow_left hp.two_le _).trans hpow)
  have hpmax : p≤2^J := by
    by_contra hh
    have hlarge : 2^J<p := by omega
    have hsq : p^2≤2^(2*J) :=
      (pow_le_pow_right' hp.one_le (by omega : 2≤r+s)).trans hpow
    have hbad : 2^(2*J)<p^2 := by
      rw [show 2*J=J*2 by omega,pow_mul]
      exact Nat.pow_lt_pow_left hlarge (by norm_num)
    omega
  apply Finset.mem_image.mpr
  refine ⟨(p,(r,s)),Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le,hpmax⟩,hp⟩
  · change (r,s) ∈ (Finset.Icc 1 (2*J)).product (Finset.Icc 1 (2*J))
    have hrmax : r≤2*J := by omega
    have hsmax : s≤2*J := by omega
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hr0,hrmax⟩,Finset.mem_Icc.mpr ⟨hs0,hsmax⟩⟩
  · exact Prod.ext hr.symm hs.symm

/-- Exact support joining retains the full matrix and every active power. -/
theorem nontrivial_eq_supported (J : ℕ) (K : ℕ → ℕ → ℂ) :
    nontrivial J K=
      ∑ ab ∈ (factorPairs J).filter (fun ab => ab ∈ supportImage J),
        (Λ (ab.1*ab.2) : ℂ)*K ab.1 ab.2 := by
  classical
  unfold nontrivial
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro ab hab hnot
  by_cases ha : Λ (ab.1*ab.2)=0
  · simp [ha]
  exact False.elim (hnot (Finset.mem_filter.mpr ⟨hab,active_pair_mem hab ha⟩))

/-- All growing dilation incidences have at most square-root times
logarithmic exponent-square cardinality, even with arbitrary masks. -/
theorem supportImage_card_le (J : ℕ) :
    (supportImage J).card≤2^J*(2*J)^2 := by
  unfold supportImage
  apply (Finset.card_image_le).trans
  have hp : ((Finset.Icc 1 (2^J)).filter Nat.Prime).card≤2^J := by
    simpa using Finset.card_filter_le (Finset.Icc 1 (2^J)) Nat.Prime
  simpa [Finset.product_eq_sprod,Finset.card_product,pow_two] using
    Nat.mul_le_mul_right ((2*J)*(2*J)) hp

/-- Unconditional physical budget for the ENTIRE coded nontrivial
hyperbola. This estimate demonstrates source loss, not an RH floor. -/
theorem norm_nontrivial_le (J : ℕ) (K : ℕ → ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hK : ∀ ab ∈ factorPairs J, ‖K ab.1 ab.2‖≤B) :
    ‖nontrivial J K‖≤B*((2*J : ℕ) : ℝ)^3*Real.log 2*(2 : ℝ)^J := by
  classical
  rw [nontrivial_eq_supported]
  let S := (factorPairs J).filter (fun ab => ab ∈ supportImage J)
  have hcard : (S.card : ℝ)≤(2 : ℝ)^J*((2*J : ℕ) : ℝ)^2 := by
    have hs : S ⊆ supportImage J := fun _ h => (Finset.mem_filter.mp h).2
    exact_mod_cast (Finset.card_le_card hs).trans (supportImage_card_le J)
  have hterm (ab : ℕ × ℕ) (hab : ab ∈ S) :
      ‖(Λ (ab.1*ab.2) : ℂ)*K ab.1 ab.2‖≤((2*J : ℕ) : ℝ)*Real.log 2*B := by
    have hf := (Finset.mem_filter.mp hab).1
    obtain ⟨hpair,hprod⟩ := Finset.mem_filter.mp hf
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hpair
    have hpos : (0 : ℝ)<(ab.1*ab.2 : ℕ) := by
      exact_mod_cast Nat.mul_pos (by have := (Finset.mem_Icc.mp ha).1; omega)
        (by have := (Finset.mem_Icc.mp hb).1; omega)
    have hlog : Λ (ab.1*ab.2)≤((2*J : ℕ) : ℝ)*Real.log 2 :=
      ArithmeticFunction.vonMangoldt_le_log.trans (by
        have hh := Real.log_le_log hpos
          (show ((ab.1*ab.2 : ℕ) : ℝ)≤(2 : ℝ)^(2*J) by exact_mod_cast hprod)
        simpa only [Real.log_pow] using hh)
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul hlog (hK ab hf) (norm_nonneg _) (by positivity)
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ ab ∈ S, ((2*J : ℕ) : ℝ)*Real.log 2*B := Finset.sum_le_sum hterm
    _ = (S.card : ℝ)*(((2*J : ℕ) : ℝ)*Real.log 2*B) := by simp
    _ ≤ _ := by
      calc
        _ ≤ ((2 : ℝ)^J*((2*J : ℕ) : ℝ)^2)*(((2*J : ℕ) : ℝ)*Real.log 2*B) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring

/-- Every polynomial-logarithmic full dilation code has the original
unit-boundary source and no additional source above exponent one half. -/
theorem tendsto_scaled_full_sub_units (K : ℕ → ℕ → ℕ → ℂ) (d : ℕ)
    {C beta : ℝ} (hC : 0≤C) (hbeta : 1/2<beta)
    (hK : ∀ J ab, ab ∈ factorPairs J → ‖K J ab.1 ab.2‖≤C*((J+1 : ℕ) : ℝ)^d) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      (full J (K J)-units J (K J))) atTop (𝓝 0) := by
  let a := Real.exp (-2*beta*Real.log 2)
  let r := a*2
  have ha : 0<a := Real.exp_pos _
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r<1 := by
    have he : r=Real.exp ((1-2*beta)*Real.log 2) := by
      dsimp [r,a]
      calc
        _ = Real.exp (-2*beta*Real.log 2)*Real.exp (Real.log 2) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ)<2)]
        _ = _ := by rw [←Real.exp_add]; congr 1; ring
    rw [he]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith)
      (Real.log_pos (by norm_num)))
  have ht : Tendsto (fun J : ℕ =>
      (8*C*Real.log 2)*(((J+1 : ℕ) : ℝ)^(d+3)*r^J)) atTop (𝓝 0) := by
    simpa using (tendsto_shifted_polynomial_geometric (d+3) hr hr1).const_mul
      (8*C*Real.log 2)
  apply squeeze_zero_norm (fun J => ?_) ht
  rw [full_eq_units_add_nontrivial,add_sub_cancel_left,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_of_nonneg ha.le]
  calc
    _ ≤ a^J*(C*((J+1 : ℕ) : ℝ)^d*((2*J : ℕ) : ℝ)^3*Real.log 2*(2 : ℝ)^J) :=
      mul_le_mul_of_nonneg_left (norm_nontrivial_le J (K J) (by positivity) (hK J))
        (pow_nonneg ha.le J)
    _ ≤ a^J*(C*((J+1 : ℕ) : ℝ)^d*(2*((J+1 : ℕ) : ℝ))^3*Real.log 2*(2 : ℝ)^J) := by
      push_cast
      gcongr
      norm_cast
      omega
    _ = _ := by dsimp [r]; rw [mul_pow,pow_add]; push_cast; ring

/-- Exact source conservation: every cofinal finite limit of the full
coded hyperbola is the limit of its original unit-factor boundary,
and conversely. The new dilation interaction supplies no extra mode. -/
theorem tendsto_scaled_full_iff_units (K : ℕ → ℕ → ℕ → ℂ) (d : ℕ)
    {C beta : ℝ} (hC : 0≤C) (hbeta : 1/2<beta)
    (hK : ∀ J ab, ab ∈ factorPairs J → ‖K J ab.1 ab.2‖≤C*((J+1 : ℕ) : ℝ)^d)
    (v : ℂ) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*full J (K J))
      atTop (𝓝 v) ↔
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*units J (K J))
      atTop (𝓝 v) := by
  have he := tendsto_scaled_full_sub_units K d hC hbeta hK
  constructor
  · intro h
    have ht := h.sub he
    simp only [sub_zero] at ht
    convert ht using 1
    funext J
    ring
  · intro h
    have ht := h.add he
    simp only [add_zero] at ht
    convert ht using 1
    funext J
    ring

end
end RiemannGaussian.ArithmeticOperatorDilationPowerAudit
