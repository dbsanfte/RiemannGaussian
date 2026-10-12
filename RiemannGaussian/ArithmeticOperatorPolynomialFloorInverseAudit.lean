/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorNonlinearFloorAudit

/-!
# Nonlinear floor coding before the actual Gamma/Mobius inverse

Every zero-mean periodic code is an exact polynomial of ONE literal
quotient row. Consequently this entire unrestricted nonlinear class can
prescribe every nonunit decoded prefix, even though the original actual
Gamma logarithms and actual Mobius coefficients remain unaltered.

This is a class-level collapse gate, not a countermodel asserting arbitrary
decoded profiles are actual Mangoldt data. Polynomial coefficients and
degree grow with the period and are NOT given a uniform budget. A fixed
degree-one parity member preserves every actual zeta-zero multiplicity and
cancels the density pole, but its inverse is the already-unpaid actual
Mangoldt/dyadic sum. No independent estimate follows from nonlinear coding.
-/

namespace RiemannGaussian.ArithmeticOperatorPolynomialFloorInverseAudit
noncomputable section
open Complex Filter Topology SuzukiCarryCorrelation
open ArithmeticOperatorNonlinearFloorAudit ArithmeticOperatorPeriodicInverseAudit
open LSeries
open scoped BigOperators ComplexConjugate

/-- ALL nonunit rows on the entire prefix, not only one head witness,
are realizable by a polynomial of the exact native quotient row. -/
theorem exists_polynomial_for_prefix (X : ℕ) (w : ℕ → ℂ) (hw : w 1=0) :
    ∃ P : Polynomial ℂ,P.degree<(X+2 : WithBot ℕ) ∧
      (∑ a : ZMod (X+2),polynomialCode (X+2) P a=0) ∧
      ∀ n∈Finset.Icc 1 X,decoded (polynomialCode (X+2) P) n=w n := by
  obtain ⟨Phi,hmean,hrows⟩ := exists_zero_mean_code_for_prefix X w hw
  refine ⟨interpolant Phi,interpolant_degree_lt Phi,?_,?_⟩
  · simpa only [polynomialCode_interpolant] using hmean
  · simpa only [polynomialCode_interpolant] using hrows

/-- The full original height phase stays on each decoded integer. -/
theorem exists_phased_polynomial_for_prefix (X : ℕ) (w : ℕ → ℂ)
    (hw : w 1=0) (y : ℝ) :
    ∃ P : Polynomial ℂ,P.degree<(X+2 : WithBot ℕ) ∧
      (∑ a : ZMod (X+2),polynomialCode (X+2) P a=0) ∧
      ∀ n∈Finset.Icc 1 X,
        phasedDecoded (polynomialCode (X+2) P) y n=primePhase y n*w n := by
  obtain ⟨P,hdeg,hmean,hrows⟩ := exists_polynomial_for_prefix X w hw
  refine ⟨P,hdeg,hmean,?_⟩
  intro n hn
  rw [phasedDecoded_eq,hrows n hn]

/-- Any bound uniform over this whole polynomial class is possible
IFF the ENTIRE joined kernel is zero. All correlated masks, factorial
weights and original phases may remain in K; no termwise norm is taken. -/
theorem polynomial_bound_iff (X : ℕ) (D : Finset ℕ)
    (hD : ∀ n∈D,2≤n ∧ n≤X) (y : ℝ) (K : ℕ → ℂ) (B : ℝ) :
    (∀ P : Polynomial ℂ,P.degree<(X+2 : WithBot ℕ) →
      (∑ a : ZMod (X+2),polynomialCode (X+2) P a=0) →
      ‖∑ n∈D,K n*phasedDecoded (polynomialCode (X+2) P) y n‖≤B) ↔
      0≤B ∧ ∀ n∈D,K n=0 := by
  constructor
  · intro hh
    have hall : ∀ w : ℕ → ℂ,‖∑ n∈D,w n*(K n*primePhase y n)‖≤B := by
      intro w
      let v := fun n : ℕ => if n=1 then 0 else w n
      obtain ⟨P,hdeg,hmean,hrows⟩ := exists_phased_polynomial_for_prefix X v
        (by simp [v]) y
      have he : (∑ n∈D,K n*phasedDecoded (polynomialCode (X+2) P) y n)=
          ∑ n∈D,w n*(K n*primePhase y n) := by
        apply Finset.sum_congr rfl
        intro n hn
        obtain ⟨hn2,hnX⟩ := hD n hn
        rw [hrows n (Finset.mem_Icc.mpr ⟨by omega,hnX⟩)]
        simp only [v,ite_eq_right (show n≠1 by omega)]
        ring
      rw [←he]
      exact hh P hdeg hmean
    obtain ⟨hB,hK⟩ :=
      (ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff D _ B).mp hall
    refine ⟨hB,?_⟩
    intro n hn
    have hp : primePhase y n≠0 := norm_ne_zero_iff.mp (by rw [norm_primePhase]; norm_num)
    exact (mul_eq_zero.mp (hK n hn)).resolve_right hp
  · rintro ⟨hB,hK⟩ P _ _
    have he : (∑ n∈D,K n*phasedDecoded (polynomialCode (X+2) P) y n)=0 :=
      Finset.sum_eq_zero (fun n hn => by rw [hK n hn,zero_mul])
    simpa only [he,norm_zero] using hB

/-- All-prefix surjectivity also transports the ENTIRE phased quadratic.
Actual Gamma/Mobius bookkeeping adds no all-code PSD constraint beyond
ordinary PSD on arbitrary prefix vectors. -/
theorem polynomial_quadratic_nonnegative_iff (X : ℕ) (K : ℕ → ℕ → ℂ) (y : ℝ) :
    (∀ P : Polynomial ℂ,P.degree<(X+2 : WithBot ℕ) →
      (∑ a : ZMod (X+2),polynomialCode (X+2) P a=0) →
      0≤(∑ n∈Finset.Icc 2 X,∑ m∈Finset.Icc 2 X,
        K n m*phasedDecoded (polynomialCode (X+2) P) y n*
          conj (phasedDecoded (polynomialCode (X+2) P) y m)).re) ↔
      ∀ w : ℕ → ℂ,0≤(∑ n∈Finset.Icc 2 X,∑ m∈Finset.Icc 2 X,
        K n m*(primePhase y n*w n)*conj (primePhase y m*w m)).re := by
  rw [←coded_quadratic_nonnegative_iff X K y]
  constructor
  · intro hh Phi hmean
    simpa only [polynomialCode_interpolant] using
      hh (interpolant Phi) (interpolant_degree_lt Phi)
        (by simpa only [polynomialCode_interpolant] using hmean)
  · intro hh P _ hmean
    exact hh _ hmean

/-- The norm obstruction persists BEYOND EVERY head, while all rows
of that head can be zero exactly. This does not impose any coefficient
budget or claim the resulting decoded rows are actual Mangoldt. -/
theorem no_uniform_payment_beyond_head (H : ℕ) (y : ℝ) (B : ℝ) :
    ∃ P : Polynomial ℂ,P.degree<(H+4 : WithBot ℕ) ∧
      (∑ a : ZMod (H+4),polynomialCode (H+4) P a=0) ∧
      (∀ n∈Finset.Icc 1 H,decoded (polynomialCode (H+4) P) n=0) ∧
      B<‖phasedDecoded (polynomialCode (H+4) P) y (H+2)‖ := by
  let w : ℕ → ℂ := fun n => if n=H+2 then (|B|+1 : ℝ) else 0
  obtain ⟨P,hdeg,hmean,hrows⟩ := exists_polynomial_for_prefix (H+2) w
    (by simp [w])
  have hcast : (((H+2 : ℕ) : WithBot ℕ)+2)=(H : WithBot ℕ)+4 := by
    norm_cast
  refine ⟨P,by rwa [hcast] at hdeg,
    by simpa only [Nat.add_assoc] using hmean,?_,?_⟩
  · intro n hn
    obtain ⟨hn1,hnH⟩ := Finset.mem_Icc.mp hn
    have he := hrows n (Finset.mem_Icc.mpr ⟨hn1,by omega⟩)
    simpa [w,show n≠H+2 by omega,Nat.add_assoc] using he
  · have he := hrows (H+2) (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩)
    rw [phasedDecoded_eq]
    rw [show H+4=(H+2)+2 by omega,he,norm_mul,norm_primePhase]
    simp only [w,ite_eq_left rfl,one_mul,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : 0 < |B|+1)]
    linarith [le_abs_self B]

/-- A fixed degree-one member of this class. Its source detector is
the EXISTING parity inverse, not a new estimate or a new carrier. -/
def parityPolynomial : Polynomial ℂ := interpolant parityCode

theorem parityPolynomial_degree_lt : parityPolynomial.degree<(2 : WithBot ℕ) :=
  interpolant_degree_lt parityCode

theorem parityPolynomial_code : polynomialCode 2 parityPolynomial=parityCode :=
  polynomialCode_interpolant parityCode

theorem parityPolynomial_mean_zero :
    ∑ a : ZMod 2,polynomialCode 2 parityPolynomial a=0 := by
  rw [parityPolynomial_code]
  exact parityCode_mean_zero

/-- Every proper power and the finite dyadic head stay explicit: the
source-bearing inverse is exactly old Mangoldt and its old dilation. -/
theorem parityPolynomial_decoded (n : ℕ) :
    decoded (polynomialCode 2 parityPolynomial) n=
      2*zetaDilationCoefficient 2 (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) n-
        (ArithmeticFunction.vonMangoldt n : ℂ)+
        (if n=2 then 2*(Real.log 2 : ℂ) else 0) := by
  rw [parityPolynomial_code]
  exact parity_decoded n

/-- Exact convergent Euler identity on its genuine half-plane. -/
theorem parityPolynomial_euler_response {s : ℂ} (hs : 1<s.re) :
    LSeries (decoded (polynomialCode 2 parityPolynomial)) s=parityResponse s := by
  rw [parityPolynomial_code]
  exact parity_euler_response hs

/-- Source and density gates are simultaneous, at every actual
multiplicity. They do NOT supply a native cutoff or signed prime estimate. -/
theorem parityPolynomial_source_and_density (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*parityResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*parityMultiplier rho.1)) ∧
    -(analyticZetaZeroMultiplicity rho : ℂ)*parityMultiplier rho.1≠0 ∧
    Tendsto (fun s : ℂ => (s-1)*parityResponse s) (𝓝[≠] (1 : ℂ)) (𝓝 0) :=
  ⟨parity_actual_source rho,parity_actual_source_nonzero rho,parity_density_source_zero⟩

end
end RiemannGaussian.ArithmeticOperatorPolynomialFloorInverseAudit
