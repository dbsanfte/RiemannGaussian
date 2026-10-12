/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorSuccessorGammaAudit
import RiemannGaussian.ArithmeticOperatorTwistSourceAudit
import RiemannGaussian.ArithmeticOperatorIncidenceFreedom

/-!
# The nonlinear successor source is not paid by Gamma subtraction

The exact joined discrepancy consists of two linear Gamma cross terms
and a pure commutator quadratic. The linear terms have arbitrary-weight
divisor kernels. The pure quadratic has a nonzero matched power response,
but smooth coherent rows also have that response, even after exact
pointwise density subtraction. Finite integer incidence realizes such
rows by Möbius inversion. This does NOT replace actual Mangoldt weights,
prove a literal cutoff zero asymptotic, or close a prime-specific bound.
-/

namespace RiemannGaussian.ArithmeticOperatorSuccessorSourceAudit
noncomputable section
open Complex ArithmeticOperatorSuccessorGammaAudit
open ArithmeticOperatorGammaTwistAudit ArithmeticOperatorTwistSourceAudit
open ArithmeticOperatorKummerCutoff ArithmeticOperatorIncidenceFreedom
open scoped BigOperators ComplexConjugate

/-- Both literal successor endpoints are retained in the joined quadratic. -/
def successor (X : ℕ) (g : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, g n*conj (g (n+1))

/-- The two mixed terms, kept signed rather than separately norm-paid. -/
def mixed (X : ℕ) (b e : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    (e n*conj (b (n+1))+b n*conj (e (n+1)))

/-- Exact density/reference subtraction leaves a quadratic as well as
the mixed terms. There is no claim that either remainder is small. -/
theorem successor_add (X : ℕ) (b e : ℕ → ℂ) :
    successor X (b+e)-successor X b = mixed X b e+successor X e := by
  unfold successor mixed
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Pi.add_apply, map_add]
  ring

/-- The actual unpaid Gamma discrepancy has precisely this join,
with all prime powers and the original height phase retained. -/
theorem signedDiscrepancy_eq_mixed_add_quadratic (X : ℕ) (y : ℝ) :
    signedDiscrepancy X y =
      mixed X (coupledDivisor (SuzukiCarryCorrelation.primePhase y))
        (twistCommutator (SuzukiCarryCorrelation.primePhase y))+
      successor X (twistCommutator (SuzukiCarryCorrelation.primePhase y)) := by
  rw [← primeCross_sub_gammaCross]
  have he : primeLegDivisor (SuzukiCarryCorrelation.primePhase y) =
      coupledDivisor (SuzukiCarryCorrelation.primePhase y)+
        twistCommutator (SuzukiCarryCorrelation.primePhase y) := by
    funext n
    have hh := primeLegDivisor_sub_coupled (SuzukiCarryCorrelation.primePhase y) n
    simp only [Pi.add_apply]
    linear_combination hh
  change successor X (primeLegDivisor (SuzukiCarryCorrelation.primePhase y))-
    successor X (coupledDivisor (SuzukiCarryCorrelation.primePhase y)) = _
  rw [he, successor_add]

/-- Exact divisor kernel of a Gamma/reference cross term; it uses no
special property of the denominator array. -/
def linearKernel (X d : ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, if d ∈ n.divisors then conj (b (n+1)) else 0

/-- The first mixed orientation collapses to one linear divisor test.
The finite prefix, successor endpoint and reference phase are unchanged. -/
theorem linear_cross_eq_kernel (X : ℕ) (w b : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, divisorObservation w n*conj (b (n+1))) =
      ∑ d ∈ Finset.Icc 1 X, w d*linearKernel X d b := by
  classical
  have hd (n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
      n.divisors ⊆ Finset.Icc 1 X := by
    intro d hh
    have hh0 : 0 < n := (Finset.mem_Icc.mp hn).1
    have hv := Nat.dvd_of_mem_divisors hh
    exact Finset.mem_Icc.mpr
      ⟨Nat.pos_of_dvd_of_pos hv hh0,
        (Nat.le_of_dvd hh0 hv).trans (Finset.mem_Icc.mp hn).2⟩
  calc
    _ = ∑ n ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 X,
        if d ∈ n.divisors then w d*conj (b (n+1)) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      unfold divisorObservation
      rw [Finset.sum_mul]
      have he : (Finset.Icc 1 X).filter (fun d => d ∈ n.divisors) = n.divisors := by
        ext d
        simp only [Finset.mem_filter]
        exact ⟨fun hh => hh.2, fun hh => ⟨hd n hn hh,hh⟩⟩
      rw [← Finset.sum_filter, he]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      simp only [linearKernel, Finset.mul_sum, mul_ite, mul_zero]

/-- Kernel for the other orientation includes the successor endpoint
`X+1`; it is not replaced by the first kernel at a different cutoff. -/
def rightKernel (X d : ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, if d ∈ (n+1).divisors then b n else 0

theorem right_cross_eq_kernel (X : ℕ) (w b : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, b n*conj (divisorObservation w (n+1))) =
      ∑ d ∈ Finset.Icc 1 (X+1), conj (w d)*rightKernel X d b := by
  classical
  have hd (n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
      (n+1).divisors ⊆ Finset.Icc 1 (X+1) := by
    intro d hh
    have hh0 : 0 < n+1 := by omega
    have hv := Nat.dvd_of_mem_divisors hh
    exact Finset.mem_Icc.mpr
      ⟨Nat.pos_of_dvd_of_pos hv hh0,
        (Nat.le_of_dvd hh0 hv).trans (by have := (Finset.mem_Icc.mp hn).2; omega)⟩
  calc
    _ = ∑ n ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 (X+1),
        if d ∈ (n+1).divisors then b n*conj (w d) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      unfold divisorObservation
      rw [map_sum, Finset.mul_sum]
      have he : (Finset.Icc 1 (X+1)).filter (fun d => d ∈ (n+1).divisors) =
          (n+1).divisors := by
        ext d
        simp only [Finset.mem_filter]
        exact ⟨fun hh => hh.2, fun hh => ⟨hd n hn hh,hh⟩⟩
      rw [← Finset.sum_filter, he]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      simp only [rightKernel, Finset.mul_sum, mul_ite, mul_zero]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> ring

/-- BOTH signed Gamma cross orientations collapse together. This is
real-linear in the free weights and keeps each literal endpoint. -/
theorem mixed_eq_joined_kernels (X : ℕ) (w b : ℕ → ℂ) :
    mixed X b (divisorObservation w) =
      (∑ d ∈ Finset.Icc 1 X, w d*linearKernel X d b)+
      ∑ d ∈ Finset.Icc 1 (X+1), conj (w d)*rightKernel X d b := by
  unfold mixed
  rw [Finset.sum_add_distrib, linear_cross_eq_kernel, right_cross_eq_kernel]

/-- Power-mode diagnostic row AFTER height matching. It is not being
identified with an actual arithmetic cutoff expansion. -/
def matchedRow (v : ℂ) (beta : ℝ) (n : ℕ) : ℂ :=
  v*((n : ℝ)^(beta-1) : ℝ)

/-- Dyadic-shell quadratic keeps the actual successor, not `n` twice. -/
def shellResponse (v : ℂ) (beta : ℝ) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc (X+1) (2*X),
    matchedRow v beta n*conj (matchedRow v beta (n+1))

/-- Exact pointwise pole/density removal does not cancel the diagnostic
matched source. This identity allows ANY density/reference row. -/
theorem density_removed_shell (b : ℕ → ℂ) (v : ℂ) (beta : ℝ) (X : ℕ) :
    (∑ n ∈ Finset.Icc (X+1) (2*X),
      ((b n+matchedRow v beta n)-b n)*
        conj ((b (n+1)+matchedRow v beta (n+1))-b (n+1))) =
      shellResponse v beta X := by
  simp only [add_sub_cancel_left, shellResponse]

/-- The diagnostic quadratic is a nonnegative real weight, irrespective
of the phase of the original nonzero residue. -/
theorem matchedRow_product_re (v : ℂ) (beta : ℝ) (n : ℕ) :
    (matchedRow v beta n*conj (matchedRow v beta (n+1))).re =
      ‖v‖^2*(n : ℝ)^(beta-1)*((n+1 : ℕ) : ℝ)^(beta-1) := by
  unfold matchedRow
  rw [map_mul, Complex.conj_ofReal]
  have he : v*((n : ℝ)^(beta-1) : ℝ)*
      (conj v*(((n+1 : ℕ) : ℝ)^(beta-1) : ℝ)) =
      (v*conj v)*((n : ℝ)^(beta-1) : ℝ)*(((n+1 : ℕ) : ℝ)^(beta-1) : ℝ) := by ring
  rw [he, Complex.mul_conj]
  simp only [Complex.normSq_eq_norm_sq, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-- Uniform positive source-scale lower bound on every dyadic shell.
This elementary smooth-row response survives the full integer endpoints;
it is not an independent signed estimate for actual primes. -/
theorem shell_source_lower (v : ℂ) {beta : ℝ} (hb : beta ≤ 1)
    {X : ℕ} (hX : 0 < X) :
    ‖v‖^2*3^(2*beta-2) ≤
      (X : ℝ)^(-(2*beta-1))*(shellResponse v beta X).re := by
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  have hz : beta-1 ≤ 0 := by linarith
  have hh : ‖v‖^2*((3 : ℝ)*(X : ℝ))^(2*beta-2)*(X : ℝ) ≤
      (shellResponse v beta X).re := by
    rw [shellResponse, Complex.re_sum]
    calc
      _ = ∑ n ∈ Finset.Icc (X+1) (2*X),
          ‖v‖^2*((3 : ℝ)*(X : ℝ))^(2*beta-2) := by
        rw [Finset.sum_const, Nat.card_Icc]
        have hc : 2*X+1-(X+1) = X := by omega
        rw [hc]
        simp only [nsmul_eq_mul]
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp hn
        have ha : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
        have hb0 : 0 < ((n+1 : ℕ) : ℝ) := by positivity
        have han : (n : ℝ) ≤ 3*(X : ℝ) := by exact_mod_cast (show n ≤ 3*X by omega)
        have hbn : ((n+1 : ℕ) : ℝ) ≤ 3*(X : ℝ) := by
          exact_mod_cast (show n+1 ≤ 3*X by omega)
        have hra := Real.rpow_le_rpow_of_nonpos ha han hz
        have hrb := Real.rpow_le_rpow_of_nonpos hb0 hbn hz
        rw [matchedRow_product_re, show 2*beta-2 = (beta-1)+(beta-1) by ring,
          Real.rpow_add (by positivity)]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul hra hrb (by positivity) (by positivity)) (sq_nonneg _)
  calc
    _ = (X : ℝ)^(-(2*beta-1))*
        (‖v‖^2*((3 : ℝ)*(X : ℝ))^(2*beta-2)*(X : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) hx.le]
      have he : (X : ℝ)^(-(2*beta-1))*(X : ℝ)^(2*beta-2)*(X : ℝ) = 1 := by
        rw [← Real.rpow_add hx]
        have hh : -(2*beta-1)+(2*beta-2) = -1 := by ring
        rw [hh, Real.rpow_neg_one]
        exact inv_mul_cancel₀ hx.ne'
      calc
        _ = ‖v‖^2*3^(2*beta-2)*1 := by ring
        _ = ‖v‖^2*3^(2*beta-2)*
          ((X : ℝ)^(-(2*beta-1))*(X : ℝ)^(2*beta-2)*(X : ℝ)) := by rw [he]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hx.le _)

/-- The actual meromorphic matched residue is nonzero even with
multiplicity, so its diagnostic successor square is genuinely visible. -/
theorem matched_zero_shell_positive (rho : NontrivialZetaZero)
    {X : ℕ} (hX : 0 < X) :
    0 < (X : ℝ)^(-(2*rho.1.re-1))*
      (shellResponse (-(analyticZetaZeroMultiplicity rho : ℂ)*
        riemannZeta (rho.1.re : ℂ)) rho.1.re X).re := by
  have hv := commutator_source_ne_zero rho
  have hh := shell_source_lower
    (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ))
    (NontrivialZetaZero.re_lt_one rho).le hX
  have hp : 0 < ‖-(analyticZetaZeroMultiplicity rho : ℂ)*
      riemannZeta (rho.1.re : ℂ)‖^2*3^(2*rho.1.re-2) := by
    exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hv)) (Real.rpow_pos_of_pos (by norm_num) _)
  exact hp.trans_le hh

/-- Even the nonlinear smooth-row source is realized on literal finite
integer divisor incidence. This array is NOT actual positive Mangoldt
data, and does NOT satisfy the complete actual Gamma observations. -/
theorem shell_realized_by_finite_incidence (v : ℂ) (beta : ℝ) (X : ℕ) :
    ∃ w : ℕ → ℂ, (∀ n ∉ Finset.Icc 1 (2*X+1), w n = 0) ∧
      (∑ n ∈ Finset.Icc (X+1) (2*X),
        divisorObservation w n*conj (divisorObservation w (n+1))) =
          shellResponse v beta X := by
  obtain ⟨w,hw,he⟩ := exists_finite_array_with_rows (2*X+1) (matchedRow v beta)
  refine ⟨w,hw,?_⟩
  unfold shellResponse
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp hn
  rw [he n (Finset.mem_Icc.mpr ⟨by omega,by omega⟩),
    he (n+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)]

end
end RiemannGaussian.ArithmeticOperatorSuccessorSourceAudit
