/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryMellinJet
import Mathlib.NumberTheory.Chebyshev

/-!
# Collapse audit of the pole/diagonal-cancelled carry statistic

All rows and modulations are joined before estimating. The exact result
is one test function applied to the literal twisted von Mangoldt measure.
The row-to-denominator identity also holds for arbitrary weights. Thus
this identity alone is not an independent bound for actual primes.
-/

namespace RiemannGaussian.SuzukiCarryCollapseAudit
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryCorrelation SuzukiCarryGram SuzukiCarryGramSource SuzukiCarryFejer
open SuzukiCarryPoleCenter SuzukiCarryPhaseCode SuzukiCarryMellinLimit SuzukiCarryMellinRate
open scoped BigOperators Topology ComplexConjugate

/-- The unchanged pole/diagonal-cancelled kernel in one denominator. -/
def kernel (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) (d : ℕ) : ℂ :=
  familyKernel (Finset.range (H+2*H)) (coefficient H H)
    Finset.univ (code H theta y) theta d

/-- Complete row expression for arbitrary arithmetic weights on a common support.
Its von Mangoldt specialization retains every prime power and the height phase. -/
def weightedRows (X : ℕ) (S : Finset ℕ) (alpha : ℕ → ℂ)
    {ι : Type*} (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ)
    (w : ℕ → ℂ) : ℂ :=
  ∑ j ∈ J, lambda j * ∑ N ∈ S, ∑ M ∈ S,
    modulate alpha (theta j) N*conj (modulate alpha (theta j) M)*
      ∑ d ∈ Finset.Icc 1 X, ((incidence N d*incidence M d : ℝ) : ℂ)*w d

/-- Carry algebra imposes the same joined identity for every denominator weight.
No primality, multiplicativity, positivity or PNT hypothesis enters. -/
theorem weightedRows_eq_joined (X : ℕ) (S : Finset ℕ) (alpha : ℕ → ℂ)
    {ι : Type*} (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ)
    (w : ℕ → ℂ) :
    weightedRows X S alpha J lambda theta w =
      ∑ d ∈ Finset.Icc 1 X, w d*familyKernel S alpha J lambda theta d := by
  classical
  unfold weightedRows
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun _ _ =>
    Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)))
  apply Eq.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [familyKernel_eq_lag, Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N _
  apply Finset.sum_congr rfl
  intro M _
  simp only [lagFactor, Finset.mul_sum, Finset.sum_mul, modulate_mul_conj]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact delta-weight test: universal arithmetic annihilation is equivalent
to a zero kernel, rather than following from its pole Mellin zero. -/
theorem weightedRows_vanish_forall_iff (X : ℕ) (S : Finset ℕ) (alpha : ℕ → ℂ)
    {ι : Type*} (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ) :
    (∀ w : ℕ → ℂ, weightedRows X S alpha J lambda theta w = 0) ↔
      ∀ d ∈ Finset.Icc 1 X, familyKernel S alpha J lambda theta d = 0 := by
  classical
  constructor
  · intro h d hd
    have he := h (fun n => if n = d then 1 else 0)
    simpa [weightedRows_eq_joined, hd] using he
  · intro h w
    rw [weightedRows_eq_joined]
    exact Finset.sum_eq_zero (fun d hd => by rw [h d hd, mul_zero])

/-- Endpoint-gcd observations are also linear tests of arbitrary weights. -/
def weightedDivisors (w : ℕ → ℂ) (a : ℕ) : ℂ := ∑ d ∈ a.divisors, w d

/-- The genuine untwisted integer factorization identity is retained.
The arbitrary-weight collapse does not claim this identity for other measures. -/
theorem weightedDivisors_mangoldt (a : ℕ) :
    weightedDivisors (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) a =
      (Real.log a : ℂ) := by
  simp only [weightedDivisors, ← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum]

/-- At nonzero height the corresponding observation is the original
unpaid twisted divisor polynomial, including all proper prime powers. -/
theorem weightedDivisors_twisted (y : ℝ) (a : ℕ) :
    weightedDivisors (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) a =
      divisorPhase (primePhase y) a := rfl

private theorem common_divisor_weight {X a b : ℕ} (ha : 0 < a) (haX : a ≤ X)
    (w : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 X, ((divisorIndicator a d*divisorIndicator b d : ℝ) : ℂ)*w d) =
      weightedDivisors w (Nat.gcd a b) := by
  classical
  have hg : Nat.gcd a b ≠ 0 := (Nat.gcd_pos_of_pos_left b ha).ne'
  have he : (Finset.Icc 1 X).filter (fun d => d ∣ a ∧ d ∣ b) = (Nat.gcd a b).divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨_, hd⟩
      exact ⟨hd, hg⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 ha, (Nat.le_of_dvd ha hd.1).trans haX⟩, hd⟩
  have hterm (d : ℕ) : ((divisorIndicator a d*divisorIndicator b d : ℝ) : ℂ)*w d =
      if d ∣ a ∧ d ∣ b then w d else 0 := by
    by_cases hda : d ∣ a <;> by_cases hdb : d ∣ b <;> simp [divisorIndicator, hda, hdb]
  simp_rw [hterm]
  rw [← Finset.sum_filter, he]
  rfl

/-- The complete endpoint-gcd identity imposes no extra condition on w:
it is the same linear denominator test for every possible arithmetic measure. -/
theorem weightedGram_eq_gcd {X N M : ℕ} (hN : 2*(N+1) ≤ X) (w : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 X, ((incidence N d*incidence M d : ℝ) : ℂ)*w d) =
      ∑ i : Fin 3, ∑ j : Fin 3, ((endpointSign i*endpointSign j : ℝ) : ℂ)*
        weightedDivisors w (Nat.gcd (endpoint N i) (endpoint M j)) := by
  classical
  have hpos (i : Fin 3) : 0 < endpoint N i := by unfold endpoint; split_ifs <;> omega
  have hbound (i : Fin 3) : endpoint N i ≤ X := by unfold endpoint; split_ifs <;> omega
  simp_rw [incidence_eq_endpoint_sum, Finset.sum_mul, Finset.mul_sum,
    Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← common_divisor_weight (hpos i) (hbound i) w, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  push_cast
  ring

/-- No active correlated denominator is deleted. The former common support
is shortened only using the already proved exact single-incidence cancellation. -/
theorem codedStatistic_eq_denominator_sum (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) :
    codedStatistic H theta y = ∑ d ∈ Finset.Icc 1 (H+2*H),
      (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*kernel H theta y d := by
  classical
  rw [codedStatistic, familyQuadratic_eq_joined]
  let B := H+2*H
  have hb : B ≤ 2*((Finset.range B).sup id+1) := by
    by_cases hB : B = 0
    · simp [hB]
    have hh : B-1 ∈ Finset.range B := Finset.mem_range.mpr (by omega)
    have he : B-1 ≤ (Finset.range B).sup id := Finset.le_sup (f := id) hh
    omega
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hb)
  intro d hd hnot
  have hlarge : B < d := by
    have hpos := (Finset.mem_Icc.mp hd).1
    simp only [Finset.mem_Icc] at hnot
    omega
  rw [kernel, codedKernel_outer_eq_zero hlarge theta y]
  simp

/-- The continuous diagnostic kernel agrees exactly at every integer denominator. -/
theorem kernel_eq_realKernel {d : ℕ} (hd : 0 < d) (H : ℕ)
    (theta : Fin 3 → ℝ) (y : ℝ) :
    kernel H theta y d = codedRealKernel H theta y (Real.log d) := by
  simp only [kernel, familyKernel, codedRealKernel, realMass_log hd]

/-- The desired arithmetic estimate is exactly a twisted Chebyshev test estimate.
This equivalence is a reduction, not a proof of either bound. -/
theorem source_bound_iff_denominator_bound (H : ℕ) (theta : Fin 3 → ℝ)
    (y beta epsilon : ℝ) :
    ‖codedStatistic H theta y‖ ≤ epsilon*Real.exp ((1+beta)*Real.log H) ↔
      ‖∑ d ∈ Finset.Icc 1 (H+2*H),
        (ArithmeticFunction.vonMangoldt d : ℂ)*
          Complex.exp (-(I*y)*(Real.log d : ℂ))*kernel H theta y d‖ ≤
            epsilon*Real.exp ((1+beta)*Real.log H) := by
  rw [codedStatistic_eq_denominator_sum]
  rfl

/-- The full complex test, with the phase inside every global difference. -/
def test (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) (d : ℕ) : ℂ :=
  primePhase y d*kernel H theta y d

private theorem mangoldt_prefix (n : ℕ) :
    (∑ d ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt d : ℂ)) =
      (Chebyshev.psi (n : ℝ) : ℂ) := by
  classical
  rw [Chebyshev.psi, Nat.floor_natCast, Complex.ofReal_sum]
  symm
  apply Finset.sum_subset (by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    exact Finset.mem_range.mpr (by omega))
  intro d hd hnot
  have he : d = 0 := by
    simp only [Finset.mem_range] at hd
    simp only [Finset.mem_Ioc] at hnot
    omega
  subst d
  simp

/-- Exact global Chebyshev collapse, not a rowwise SBP allowance.
The outer boundary is exactly zero by diagonal/single-incidence cancellation.
All phase, integer-kernel jumps and prime powers stay in the signed expression. -/
theorem codedStatistic_eq_chebyshev_test (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) :
    codedStatistic H theta y =
      -(∑ n ∈ Finset.range (H+2*H+1),
        (Chebyshev.psi (n : ℝ) : ℂ)*(test H theta y (n+1)-test H theta y n)) := by
  classical
  let X := H+2*H+1
  have hx : H+2*H < X := by dsimp [X]; omega
  have hz : test H theta y X = 0 := by
    simp only [test, kernel, codedKernel_outer_eq_zero hx, mul_zero]
  have hsum : codedStatistic H theta y =
      ∑ d ∈ Finset.range (X+1), (ArithmeticFunction.vonMangoldt d : ℂ)*test H theta y d := by
    rw [codedStatistic_eq_denominator_sum]
    simp only [test, ← mul_assoc]
    apply Finset.sum_subset (by
      intro d hd
      have hh := (Finset.mem_Icc.mp hd).2
      exact Finset.mem_range.mpr (by dsimp [X]; omega))
    intro d hd hnot
    by_cases hzero : d = 0
    · subst d; simp
    have hlarge : H+2*H < d := by simp only [Finset.mem_Icc] at hnot; omega
    simp [kernel, codedKernel_outer_eq_zero hlarge]
  have h := Finset.sum_range_by_parts (test H theta y)
    (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) (X+1)
  simp only [smul_eq_mul, Nat.add_sub_cancel, mangoldt_prefix, hz, zero_mul, zero_sub] at h
  rw [hsum]
  calc
    _ = ∑ d ∈ Finset.range (X+1), test H theta y d*(ArithmeticFunction.vonMangoldt d : ℂ) := by
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := h
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      ring

/-- The signed continuum kernel after the native H^p normalization. -/
def continuumKernel (p : ℂ) (tau x : ℝ) : ℂ :=
  ∑ j : Fin 3, canonical (fun j : Fin 3 => continuumResponse p ((j : ℕ)*tau)) j*
    (‖profile ((j : ℕ)*tau) x‖^2 : ℂ)

/-- Exact Mellin symbol of the all-row/all-modulation continuum kernel. -/
theorem integral_continuumKernel {s : ℂ} (hs : 0 < s.re) (p : ℂ) (tau : ℝ) :
    (∫ t : ℝ, Complex.exp (s*t)*continuumKernel p tau (Real.exp t)) =
      -continuumDet p s tau := by
  unfold continuumKernel
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · simp_rw [show ∀ j : Fin 3,
        (fun t : ℝ => Complex.exp (s*t)*
          (canonical (fun j : Fin 3 => continuumResponse p ((j : ℕ)*tau)) j*
            (‖profile ((j : ℕ)*tau) (Real.exp t)‖^2 : ℂ))) =
        (fun t : ℝ => canonical (fun j : Fin 3 => continuumResponse p ((j : ℕ)*tau)) j*
          (Complex.exp (s*t)*(‖profile ((j : ℕ)*tau) (Real.exp t)‖^2 : ℂ))) by
            intro j; funext t; ring]
    simp_rw [integral_const_mul]
    simp [continuumResponse, continuumDet, sourceDet, Matrix.det_fin_three,
      canonical, Fin.sum_univ_three]
    ring
  · intro j _
    convert! (integrable_continuumResponse hs ((j : ℕ)*tau)).const_mul
      (canonical (fun j : Fin 3 => continuumResponse p ((j : ℕ)*tau)) j) using 1
    ext t
    simp only [Complex.ofReal_pow]
    ring

/-- The continuum density/pole symbol vanishes exactly. -/
theorem continuum_pole_symbol_eq_zero (p : ℂ) (tau : ℝ) :
    continuumDet p p tau = 0 := by
  simp only [continuumDet, sourceDet_eq_contrasts]
  ring

/-- The native exact signed Mellin response has the same continuum symbol.
The complex phase from H^(-p) is retained, not replaced by its norm. -/
theorem tendsto_normalized_codedResponse {s : ℂ} (hs : 0 < s.re)
    (y tau : ℝ) :
    Tendsto (fun H : ℕ =>
      Complex.exp (-(poleExponent y+s)*(Real.log H : ℂ))*
        codedResponse H (fun j : Fin 3 => (j : ℕ)*tau/(H : ℝ)) y s)
      atTop (𝓝 (-continuumDet (poleExponent y) s tau)) := by
  have hp : 0 < (poleExponent y).re := by rw [poleExponent_re]; norm_num
  have h := (tendsto_normalized_nativeDet hp hs tau).neg
  apply h.congr'
  filter_upwards with H
  rw [codedResponse_eq_neg_det]
  simp only [nativeDet, mul_neg]

end
end RiemannGaussian.SuzukiCarryCollapseAudit
