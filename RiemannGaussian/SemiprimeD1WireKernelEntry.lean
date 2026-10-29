/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WireKernelFactors

/-! # Original-input integer-factor wire-kernel acquisition
The runtime record is an ordered list of integer linear factors, an explicit
power of two and an actually computed odd denominator. No rational answer or
coefficient/inverse table is supplied. Polynomials below specify those data.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1WireKernelEntry
open scoped BigOperators
open Polynomial SemiprimeD1WireKernel SemiprimeD1WireKernelFactors

/-- Original common derivative content, computed from the actual dyadic grid. -/
def content (k : ℕ) : ℕ := padicValNat 2 (2^k-1).factorial

/-- Original common derivative denominator after removing exactly its two-content. -/
def oddDenominator (k center : ℕ) : ℤ :=
  derivativeProduct (2^k) center/(2:ℤ)^content k

/-- The acquired normalizer reconstructs the actual original denominator. -/
theorem denominator_reconstruct (k center : ℕ) (hc : center<2^k) :
    oddDenominator k center*(2:ℤ)^content k=derivativeProduct (2^k) center := by
  apply Int.ediv_mul_cancel
  have hd := padicValInt_dvd (p:=2) (derivativeProduct (2^k) center)
  rw [derivativeProduct_content k center hc] at hd
  simpa only [content,Nat.cast_ofNat] using hd

/-- The original-derived denominator is genuinely odd; no unit hypothesis is input. -/
theorem denominator_not_two_dvd (k center : ℕ) (hc : center<2^k) :
    ¬(2:ℤ) ∣ oddDenominator k center := by
  intro h
  obtain ⟨u,hu⟩ := h
  have hrec := denominator_reconstruct k center hc
  have hd : (2:ℤ)^(content k+1) ∣ derivativeProduct (2^k) center := by
    refine ⟨u,?_⟩
    rw [← hrec,hu,pow_succ]
    ring
  have hv := (padicValInt_dvd_iff (p:=2) (content k+1) (derivativeProduct (2^k) center)).mp hd
  rcases hv with hz|hv
  · exact derivativeProduct_ne_zero (2^k) center hc hz
  · rw [derivativeProduct_content k center hc] at hv
    change content k+1≤content k at hv
    omega

/-- Oddness includes negative original grid normalizers. -/
theorem denominator_odd (k center : ℕ) (hc : center<2^k) : Odd (oddDenominator k center) := by
  apply Int.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  exact denominator_not_two_dvd k center hc

/-- No division by zero is hidden in the acquired odd normalizer. -/
theorem denominator_ne_zero (k center : ℕ) (hc : center<2^k) : oddDenominator k center≠0 := by
  intro hz
  apply denominator_not_two_dvd k center hc
  rw [hz]
  exact dvd_zero _

/-- Actual ordered original grid indices except the one D.7 cancelled factor. -/
def indices (k d : ℕ) : List ℕ := (List.range (2^k)).filter (fun q => decide (q≠d))

/-- The acquired list has the exact original omitted-factor set. -/
theorem indices_toFinset (k d : ℕ) : (indices k d).toFinset=(Finset.range (2^k)).erase d := by
  ext q
  simp [indices,and_comm]

/-- No repeated grid factor is inserted by acquisition. -/
theorem indices_nodup (k d : ℕ) : (indices k d).Nodup :=
  (List.nodup_range : (List.range (2^k)).Nodup).filter _

/-- Original finite factor acquisition is at most the actual grid cardinality. -/
theorem indices_length (k d : ℕ) : (indices k d).length≤2^k := by
  exact (List.length_filter_le _ _).trans (by simp)

/-- Original-derived executable integer-factor entry data. -/
structure Entry where
  /-- Exact ordered linear factors, not requested polynomial coefficients. -/
  factors : List Linear
  /-- Explicit power remaining after original denominator cancellation. -/
  power : ℕ
  /-- Actually acquired original odd denominator. -/
  denominator : ℤ

/-- Acquire the full entry directly from original grid parameters and cancelled index. -/
def acquire (k center j d : ℕ) : Entry :=
  ⟨(indices k d).map (normalizedFactor k j),excess k j d,oddDenominator k center⟩

/-- Integer polynomial interpretation of a physically unexpanded linear factor. -/
noncomputable def linearPolynomial (f : Linear) : ℤ[X] := C f.constant+C f.slope*X

/-- Integer polynomial interpreted from acquired data, not a runtime oracle. -/
noncomputable def numerator (entry : Entry) : ℤ[X] :=
  C ((2:ℤ)^entry.power)*(entry.factors.map linearPolynomial).prod

/-- Original unnormalized affine numerator after T=t+2^k*z. -/
noncomputable def rawPolynomial (k j d : ℕ) : ℤ[X] :=
  ∏ q∈(Finset.range (2^k)).erase d,
    (C (difference j q)+C ((2:ℤ)^k)*X)

/-- Every original affine factor is reconstructed from the acquired integer pair. -/
theorem linear_reconstruct (k j q : ℕ) (hj : j<2^k) (hq : q<2^k) :
    C ((2:ℤ)^factorOrder k j q)*linearPolynomial (normalizedFactor k j q)=
      C (difference j q)+C ((2:ℤ)^k)*X := by
  have hc := normalized_constant k j q
  have hs := normalized_slope k j q hj hq
  rw [← hc,← hs]
  simp only [linearPolynomial,C_mul]
  ring

/-- Actual omitted-factor numerator content and acquired integer factor product. -/
theorem rawPolynomial_content (k j d : ℕ) (hj : j<2^k) :
    rawPolynomial k j d=
      C ((2:ℤ)^(∑ q∈(Finset.range (2^k)).erase d,factorOrder k j q))*
        ∏ q∈(Finset.range (2^k)).erase d,linearPolynomial (normalizedFactor k j q) := by
  unfold rawPolynomial
  have he : (∏ q∈(Finset.range (2^k)).erase d,
      (C (difference j q)+C ((2:ℤ)^k)*X))=
      ∏ q∈(Finset.range (2^k)).erase d,
        C ((2:ℤ)^factorOrder k j q)*linearPolynomial (normalizedFactor k j q) := by
    apply Finset.prod_congr rfl
    intro q hq
    exact (linear_reconstruct k j q hj (Finset.mem_range.mp (Finset.mem_erase.mp hq).2)).symm
  rw [he,Finset.prod_mul_distrib,← map_prod C,Finset.prod_pow_eq_pow_sum]

/-- The ordered acquired data has exactly the original indexed factor product. -/
theorem acquired_product (k center j d : ℕ) :
    ((acquire k center j d).factors.map linearPolynomial).prod=
      ∏ q∈(Finset.range (2^k)).erase d,linearPolynomial (normalizedFactor k j q) := by
  simp only [acquire,List.map_map]
  rw [← List.prod_toFinset _ (indices_nodup k d),indices_toFinset]
  rfl

/-- COMPLETE original denominator cancellation: all remaining coefficients are
integers after multiplying only by the acquired ODD denominator. -/
theorem cancellation (k center j d : ℕ) (hc : center<2^k) (hj : j<2^k) (hd : d<2^k) :
    C (oddDenominator k center)*rawPolynomial k j d=
      C (derivativeProduct (2^k) center)*numerator (acquire k center j d) := by
  have hs : (∑ q∈(Finset.range (2^k)).erase d,factorOrder k j q)=content k+excess k j d := by
    have hle := omitted_content_ge k j d hj hd
    unfold excess content
    omega
  rw [rawPolynomial_content k j d hj,hs,pow_add,C_mul]
  unfold numerator
  rw [acquired_product,← denominator_reconstruct k center hc]
  simp only [acquire,C_mul]
  ring

end RiemannGaussian.SemiprimeD1WireKernelEntry
