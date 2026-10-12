/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFareyFourierAudit
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Inverse-residue correlation is self-adjoint, not positive

The literal two-point row keeps the modular inverse rather than replacing
it by a second independent primitive residue. Its complete Fourier
quadratic is exactly the inverse permutation quadratic. A nontrivial
inverse orbit has a negative, density-centered Fourier test. This is an
obstruction to generic whole-space PSD, not an estimate for a prescribed
signed packet or the Kloosterman Dirichlet series. The scattering
coordinate attached to an actual zero cannot be a self-adjoint eigenvalue.
No Kuznetsov formula or continuation is assumed or imported as an axiom.
-/

namespace RiemannGaussian.ArithmeticOperatorKloostermanPsdAudit
noncomputable section
open Complex Filter
open scoped BigOperators Topology ComplexConjugate

variable {q : ℕ} [NeZero q]

/-- Ordinary units modulo the actual integer denominator, including
every composite denominator and its proper prime powers. -/
def row (m n : ZMod q) : ℂ :=
  ∑ a : (ZMod q)ˣ, ZMod.stdAddChar
    (m*(a : ZMod q)-n*((a⁻¹ : (ZMod q)ˣ) : ZMod q))

/-- All frequency incidences are joined before taking real parts. -/
def quadratic (alpha : ZMod q → ℂ) : ℂ :=
  ∑ m : ZMod q, ∑ n : ZMod q, alpha m*conj (alpha n)*row m n

/-- Complete additive synthesis at one actual residue; this is evaluated
at both members of the inverse orbit before joining the quadratic. -/
def amplitude (alpha : ZMod q → ℂ) (x : ZMod q) : ℂ :=
  ∑ m : ZMod q, alpha m*ZMod.stdAddChar (m*x)

/-- This is a signed inverse-permutation pairing, not a sum of squares. -/
def inverseQuadratic (f : (ZMod q)ˣ → ℂ) : ℂ :=
  ∑ a : (ZMod q)ˣ, f a*conj (f a⁻¹)

private theorem character_conj (x : ZMod q) :
    conj (ZMod.stdAddChar x)=ZMod.stdAddChar (-x) := by
  simp only [ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

/-- Exact finite two-point Fourier identity, with the inverse correlated
with the first point and every complex coefficient kept intact. -/
theorem quadratic_eq_inverse (alpha : ZMod q → ℂ) :
    quadratic alpha=inverseQuadratic
      (fun (a : (ZMod q)ˣ) => amplitude alpha (a : ZMod q)) := by
  classical
  unfold quadratic row inverseQuadratic amplitude
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [map_sum, map_mul, character_conj, Finset.sum_mul, Finset.mul_sum,
    sub_eq_add_neg, AddChar.map_add_eq_mul]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The inverse pairing is real because inversion is an involution;
being real does not imply positivity. -/
theorem inverseQuadratic_conj (f : (ZMod q)ˣ → ℂ) :
    conj (inverseQuadratic f)=inverseQuadratic f := by
  classical
  simp only [inverseQuadratic, map_sum, map_mul, conj_conj]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun a => by simp [mul_comm])

theorem quadratic_conj (alpha : ZMod q → ℂ) :
    conj (quadratic alpha)=quadratic alpha := by
  rw [quadratic_eq_inverse, inverseQuadratic_conj]

theorem row_conj_swap (m n : ZMod q) : conj (row m n)=row n m := by
  classical
  simp only [row, map_sum, character_conj]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun a => by
    simp only [Equiv.inv_apply, inv_inv]
    congr 1
    ring)

/-- Exact Fourier coefficients of a literal residue function. -/
def coefficients (f : ZMod q → ℂ) (m : ZMod q) : ℂ :=
  (q : ℂ)⁻¹*ZMod.dft f m

theorem amplitude_coefficients (f : ZMod q → ℂ) (x : ZMod q) :
    amplitude (coefficients f) x=f x := by
  unfold amplitude coefficients
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  have h := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at h
  simpa only [smul_eq_mul, mul_comm] using h

theorem coefficients_zero (f : ZMod q → ℂ) :
    coefficients f 0=(q : ℂ)⁻¹*∑ x : ZMod q, f x := by
  rw [coefficients, ZMod.dft_apply_zero]

/-- A two-point inverse orbit, expressed on actual ordinary residues. -/
def orbitProbe (u : (ZMod q)ˣ) (x : ZMod q) : ℂ :=
  (if x=(u : ZMod q) then 1 else 0)-(if x=(u⁻¹ : (ZMod q)ˣ) then 1 else 0)

theorem orbitProbe_sum (u : (ZMod q)ˣ) :
    (∑ x : ZMod q, orbitProbe u x)=0 := by
  classical
  simp [orbitProbe, Finset.sum_sub_distrib]

omit [NeZero q] in
theorem orbitProbe_units (u a : (ZMod q)ˣ) :
    orbitProbe u (a : ZMod q)=(if a=u then 1 else 0)-(if a=u⁻¹ then 1 else 0) := by
  simp [orbitProbe, Units.val_inj]

/-- The full inverse orbit costs exactly -2, rather than a positive
diagonal budget. Both off-diagonal incidences are retained. -/
theorem orbitProbe_negative (u : (ZMod q)ˣ) (hu : u≠u⁻¹) :
    inverseQuadratic (fun (a : (ZMod q)ˣ) => orbitProbe u (a : ZMod q)) = -2 := by
  classical
  unfold inverseQuadratic
  have he (a : (ZMod q)ˣ) : orbitProbe u (a : ZMod q)*
      conj (orbitProbe u ((a⁻¹ : (ZMod q)ˣ) : ZMod q))=
      -(if a=u then 1 else 0)-(if a=u⁻¹ then 1 else 0) := by
    by_cases h1 : a=u
    · subst a
      simp [orbitProbe_units,hu,hu.symm]
    · by_cases h2 : a=u⁻¹
      · subst a
        simp [orbitProbe_units,hu,hu.symm]
      · have hi1 : a⁻¹≠u := fun h => h2 (inv_eq_iff_eq_inv.mp h)
        have hi2 : a⁻¹≠u⁻¹ := fun h => h1 (inv_inj.mp h)
        simp [orbitProbe_units,h1,h2,hi1,hi2]
  simp_rw [he]
  simp [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  norm_num

/-- Density centering removes the constant Fourier coefficient, but
does not remove this negative direction. -/
theorem exists_centered_negative (u : (ZMod q)ˣ) (hu : u≠u⁻¹) :
    ∃ alpha : ZMod q → ℂ, alpha 0=0 ∧ quadratic alpha = -2 := by
  refine ⟨coefficients (orbitProbe u),?_,?_⟩
  · rw [coefficients_zero, orbitProbe_sum, mul_zero]
  · rw [quadratic_eq_inverse]
    simp_rw [amplitude_coefficients]
    exact orbitProbe_negative u hu

/-- Exact classification of the generic density-centered PSD premise.
It holds precisely when modular inversion moves no ordinary unit. -/
theorem centered_psd_iff_inverse_fixed :
    (∀ alpha : ZMod q → ℂ, alpha 0=0 → 0≤(quadratic alpha).re) ↔
      ∀ u : (ZMod q)ˣ, u=u⁻¹ := by
  constructor
  · intro h u
    by_contra hu
    obtain ⟨alpha,ha,hq⟩ := exists_centered_negative u hu
    have hn := h alpha ha
    rw [hq] at hn
    norm_num at hn
  · intro h alpha _
    rw [quadratic_eq_inverse, inverseQuadratic, Complex.re_sum]
    apply Finset.sum_nonneg
    intro u _
    rw [←h u, mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _

/-- Every prime denominator above three has a genuinely nontrivial
inverse orbit. No equidistribution or floating spectral calculation is used. -/
theorem prime_centered_negative {p : ℕ} [NeZero p] (hp : p.Prime) (h3 : 3<p) :
    ∃ alpha : ZMod p → ℂ, alpha 0=0 ∧ quadratic alpha = -2 := by
  have hc : Nat.Coprime 2 p := Nat.coprime_comm.mp
    (hp.coprime_iff_not_dvd.mpr (fun hd => by
      have hh := Nat.le_of_dvd (by norm_num : 0<2) hd
      omega))
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime 2 hc
  have hu : u≠u⁻¹ := by
    intro he
    have hm : u*u=1 := by
      calc
        u*u=u*u⁻¹ := congrArg (fun a => u*a) he
        _=1 := mul_inv_cancel u
    have hv := congrArg (fun a : (ZMod p)ˣ => (a : ZMod p)) hm
    have h4 : (4 : ZMod p)=1 := by
      norm_num [u, ZMod.coe_unitOfCoprime] at hv
      exact hv
    have hz : (3 : ZMod p)=0 := by
      linear_combination h4
    have hd := (ZMod.natCast_eq_zero_iff 3 p).mp hz
    have hh := Nat.le_of_dvd (by norm_num : 0<3) hd
    omega
  exact exists_centered_negative u hu

/-- Failure occurs at unbounded actual denominators; it is not only
the first few small modular endpoints. -/
theorem exists_prime_centered_negative_above (H : ℕ) :
    ∃ p : ℕ, ∃ hp : p.Prime, H<p ∧ ∃ alpha : ZMod p → ℂ,
      alpha 0=0 ∧ @quadratic p ⟨hp.ne_zero⟩ alpha = -2 := by
  obtain ⟨p,hpH,hp⟩ := Nat.exists_infinite_primes (H+4)
  let : NeZero p := ⟨hp.ne_zero⟩
  exact ⟨p,hp,by omega,prime_centered_negative hp (by omega)⟩

/-- A genuine ordinary denominator, with no floating root computation. -/
def unitTwo : (ZMod 5)ˣ := ⟨2,3,by decide,by decide⟩

theorem unitTwo_ne_inverse : unitTwo≠unitTwo⁻¹ := by
  intro h
  have hv := congrArg (fun a : (ZMod 5)ˣ => (a : ZMod 5)) h
  change (2 : ZMod 5)=3 at hv
  exact (by decide : (2 : ZMod 5)≠3) hv

theorem actual_five_centered_negative :
    ∃ alpha : ZMod 5 → ℂ, alpha 0=0 ∧ quadratic alpha = -2 :=
  exists_centered_negative unitTwo unitTwo_ne_inverse

theorem not_centered_psd_at_five :
    ¬(∀ alpha : ZMod 5 → ℂ, alpha 0=0 → 0≤(quadratic alpha).re) := by
  intro h
  obtain ⟨alpha,ha,hq⟩ := actual_five_centered_negative
  have hp := h alpha ha
  rw [hq] at hp
  norm_num at hp

/-- Spectral coordinate of a pole at rho/2. This definition does not
claim a spectral expansion for the arithmetic Dirichlet series. -/
def scatteringValue (rho : ℂ) : ℂ := (rho/2)*(1-rho/2)

theorem scatteringValue_im (rho : ℂ) :
    (scatteringValue rho).im=rho.im*(1-rho.re)/2 := by
  simp only [scatteringValue, mul_im, sub_re, sub_im, div_ofNat_re, div_ofNat_im,
    one_re, one_im]
  ring

theorem actual_zero_scattering_nonreal (rho : NontrivialZetaZero) :
    (scatteringValue rho.1).im≠0 := by
  rw [scatteringValue_im]
  exact div_ne_zero (mul_ne_zero (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
    (sub_ne_zero.mpr (ne_of_gt rho.re_lt_one))) (by norm_num)

/-- An actual zero scattering pole cannot be excluded by treating it as
an eigenvalue of a self-adjoint Hilbert-space operator. -/
theorem actual_zero_not_selfAdjoint_eigenvalue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (rho : NontrivialZetaZero) :
    ¬Module.End.HasEigenvalue T (scatteringValue rho.1) := by
  intro he
  have h := congrArg Complex.im (hT.conj_eigenvalue_eq_self he)
  simp only [conj_im] at h
  exact actual_zero_scattering_nonreal rho (by linarith)

end
end RiemannGaussian.ArithmeticOperatorKloostermanPsdAudit
