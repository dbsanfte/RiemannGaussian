/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryPoleCenter
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Same-amplitude phase codes for the literal carry quadratic

The diagonal is removed before any arithmetic estimate. The density mode
is removed by a second, independent linear constraint. Every prime power
and the complex height phase remain inside the off-diagonal carry sum.
The source determinant is exact; its cofinal lower bound is not assumed.
-/

namespace RiemannGaussian.SuzukiCarryPhaseCode
noncomputable section
open Complex MeasureTheory Set
open SuzukiCarryCorrelation SuzukiCarryGram SuzukiCarryGramSource SuzukiCarryFejer
open SuzukiCarryPoleCenter
open scoped BigOperators ComplexConjugate

/-- Unit modulation, using the literal integer carry location. -/
def modulation (theta : ℝ) (N : ℕ) : ℂ := Complex.exp (I*theta*(N : ℂ))

/-- Copies have identical coefficient norms. -/
def modulate (alpha : ℕ → ℂ) (theta : ℝ) (N : ℕ) : ℂ :=
  alpha N*modulation theta N

/-- Signed modulation coefficient at a signed integer lag. -/
def lagFactor {ι : Type*} (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ)
    (h : ℤ) : ℂ := ∑ j ∈ J, lambda j*Complex.exp (I*theta j*(h : ℂ))

/-- Same finite coefficient support, with no new physical cutoff. -/
def familyQuadratic {ι : Type*} (S : Finset ℕ) (alpha : ℕ → ℂ)
    (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ) (phase : ℕ → ℂ) : ℂ :=
  ∑ j ∈ J, lambda j*fullQuadratic S (modulate alpha (theta j)) phase

/-- The joined, generally complex kernel. It is not a positive allowance. -/
def familyKernel {ι : Type*} (S : Finset ℕ) (alpha : ℕ → ℂ)
    (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ) (d : ℕ) : ℂ :=
  ∑ j ∈ J, lambda j*(packetMass S (modulate alpha (theta j)) d : ℂ)

theorem norm_modulation (theta : ℝ) (N : ℕ) : ‖modulation theta N‖ = 1 := by
  simp [modulation, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem norm_modulate (alpha : ℕ → ℂ) (theta : ℝ) (N : ℕ) :
    ‖modulate alpha theta N‖ = ‖alpha N‖ := by
  rw [modulate, norm_mul, norm_modulation, mul_one]

theorem modulation_mul_conj (theta : ℝ) (N M : ℕ) :
    modulation theta N*conj (modulation theta M) =
      Complex.exp (I*theta*((N : ℤ)-M : ℤ)) := by
  simp only [modulation, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, Complex.conj_natCast]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem modulate_mul_conj (alpha : ℕ → ℂ) (theta : ℝ) (N M : ℕ) :
    modulate alpha theta N*conj (modulate alpha theta M) =
      alpha N*conj (alpha M)*Complex.exp (I*theta*((N : ℤ)-M : ℤ)) := by
  simp only [modulate, map_mul]
  rw [show alpha N*modulation theta N*(conj (alpha M)*conj (modulation theta M)) =
    alpha N*conj (alpha M)*(modulation theta N*conj (modulation theta M)) by ring,
    modulation_mul_conj]

theorem lagFactor_zero {ι : Type*} (J : Finset ι) (lambda : ι → ℂ)
    (theta : ι → ℝ) : lagFactor J lambda theta 0 = ∑ j ∈ J, lambda j := by
  simp [lagFactor]

/-- Exact signed lag expansion before norms, with all matrix entries kept. -/
theorem familyQuadratic_eq_lag {ι : Type*} (S : Finset ℕ) (alpha : ℕ → ℂ)
    (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ) (phase : ℕ → ℂ) :
    familyQuadratic S alpha J lambda theta phase =
      ∑ N ∈ S, ∑ M ∈ S, alpha N*conj (alpha M)*
        lagFactor J lambda theta ((N : ℤ)-M)*fullGram N M phase := by
  classical
  unfold familyQuadratic fullQuadratic lagFactor
  simp_rw [Finset.mul_sum, modulate_mul_conj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every diagonal coefficient is exactly zero, independent of primes. -/
theorem familyQuadratic_eq_offDiagonal {ι : Type*} (S : Finset ℕ) (alpha : ℕ → ℂ)
    (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ) (phase : ℕ → ℂ)
    (hl : ∑ j ∈ J, lambda j = 0) :
    familyQuadratic S alpha J lambda theta phase =
      ∑ N ∈ S, ∑ M ∈ S.filter (fun M => M ≠ N), alpha N*conj (alpha M)*
        lagFactor J lambda theta ((N : ℤ)-M)*fullGram N M phase := by
  classical
  rw [familyQuadratic_eq_lag]
  apply Finset.sum_congr rfl
  intro N _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro M _
  by_cases hm : M = N
  · subst M
    simp [lagFactor_zero, hl]
  · simp [hm]

/-- The unchanged literal prime-power sum, after joining all modulations. -/
theorem familyQuadratic_eq_joined {ι : Type*} (S : Finset ℕ) (alpha : ℕ → ℂ)
    (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ) (phase : ℕ → ℂ) :
    familyQuadratic S alpha J lambda theta phase =
      ∑ d ∈ Finset.Icc 1 (2*(S.sup id+1)),
        (ArithmeticFunction.vonMangoldt d : ℂ)*phase d*
          familyKernel S alpha J lambda theta d := by
  classical
  unfold familyQuadratic familyKernel
  simp_rw [fullQuadratic_eq_joined, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem kernel_atom (S : Finset ℕ) (alpha : ℕ → ℂ) (d : ℕ) :
    (packetMass S alpha d : ℂ) = ∑ N ∈ S, ∑ M ∈ S,
      alpha N*conj (alpha M)*((incidence N d*incidence M d : ℝ) : ℂ) := by
  classical
  rw [packetMass, ← Complex.mul_conj, packet]
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro N _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  push_cast
  ring

/-- The kernel also retains the lag coefficient before multiplication by Lambda. -/
theorem familyKernel_eq_lag {ι : Type*} (S : Finset ℕ) (alpha : ℕ → ℂ)
    (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ) (d : ℕ) :
    familyKernel S alpha J lambda theta d = ∑ N ∈ S, ∑ M ∈ S,
      alpha N*conj (alpha M)*lagFactor J lambda theta ((N : ℤ)-M)*
        ((incidence N d*incidence M d : ℝ) : ℂ) := by
  classical
  unfold familyKernel lagFactor
  simp_rw [kernel_atom, Finset.mul_sum, modulate_mul_conj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A denominator with no off-diagonal incidence is killed exactly, not
paid by its positive norm. Includes every single-incidence denominator. -/
theorem familyKernel_eq_zero_of_no_cross {ι : Type*} (S : Finset ℕ)
    (alpha : ℕ → ℂ) (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ) (d : ℕ)
    (hl : ∑ j ∈ J, lambda j = 0)
    (hc : ∀ N ∈ S, ∀ M ∈ S, M ≠ N → incidence N d*incidence M d = 0) :
    familyKernel S alpha J lambda theta d = 0 := by
  classical
  rw [familyKernel_eq_lag]
  apply Finset.sum_eq_zero
  intro N hN
  apply Finset.sum_eq_zero
  intro M hM
  by_cases hm : M = N
  · subst M
    simp [lagFactor_zero, hl]
  · rw [hc N hN M hM hm]
    simp

/-- In a finite initial interval and above its length, a denominator can
meet only its unique positive carry spike. -/
theorem incidence_range_no_cross {B N M d : ℕ} (hN : N < B) (hM : M < B)
    (hd : B < d) (hne : M ≠ N) : incidence N d*incidence M d = 0 := by
  have hdd : 2 ≤ d := by omega
  rw [incidence_two_spikes hdd, incidence_two_spikes hdd,
    Nat.mod_eq_of_lt (by omega : N < d), Nat.mod_eq_of_lt (by omega : M < d)]
  have hn : N ≠ d-1 := by omega
  have hm : M ≠ d-1 := by omega
  simp only [if_neg hn, if_neg hm, sub_zero]
  by_cases hp : N = (d-1)/2
  · have hq : M ≠ (d-1)/2 := by omega
    simp [hq]
  · simp [hp]

/-- The entire single-incidence outer sector is exactly zero. -/
theorem familyKernel_range_eq_zero {ι : Type*} {B d : ℕ} (hd : B < d)
    (alpha : ℕ → ℂ) (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ)
    (hl : ∑ j ∈ J, lambda j = 0) :
    familyKernel (Finset.range B) alpha J lambda theta d = 0 := by
  apply familyKernel_eq_zero_of_no_cross _ _ _ _ _ _ hl
  intro N hN M hM hne
  exact incidence_range_no_cross (Finset.mem_range.mp hN) (Finset.mem_range.mp hM) hd hne

set_option maxHeartbeats 1000000 in
/-- Signed lag support for arbitrary row order; zero lag is excluded. -/
theorem incidence_offDiagonal_eq_zero {N M d : ℕ} (hne : N ≠ M)
    (hd : 2*((N : ℤ)-M).natAbs+1 < d) : incidence N d*incidence M d = 0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · have habs : ((N : ℤ)-M).natAbs = M-N := by omega
    rw [habs] at hd
    have he : M = N+(M-N) := by omega
    rw [he]
    exact incidence_lag_product_eq_zero (N := N) (H := M-N) (by omega) hd
  · have habs : ((N : ℤ)-M).natAbs = N-M := by omega
    rw [habs] at hd
    have he : N = M+(N-M) := by omega
    rw [he, mul_comm]
    exact incidence_lag_product_eq_zero (N := M) (H := N-M) (by omega) hd

/-- Every genuinely surviving joined term has a correlated denominator. -/
theorem surviving_incidence_le_lag {N M d : ℕ} (hne : N ≠ M)
    (hc : incidence N d*incidence M d ≠ 0) : d ≤ 2*((N : ℤ)-M).natAbs+1 := by
  by_contra h
  exact hc (incidence_offDiagonal_eq_zero hne (by omega))

/-- Full off-diagonal entries use exactly the lag-supported denominator
range. The nine-term gcd identity remains available for every entry. -/
theorem fullGram_offDiagonal_eq_short_sum {N M : ℕ} (hne : N ≠ M)
    (phase : ℕ → ℂ) :
    fullGram N M phase = ∑ d ∈ Finset.Icc 1 (2*((N : ℤ)-M).natAbs+1),
      ((incidence N d*incidence M d : ℝ) : ℂ)*
        (ArithmeticFunction.vonMangoldt d : ℂ)*phase d := by
  unfold fullGram correlation
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega))
  intro d hdX hdLag
  have hd : 2*((N : ℤ)-M).natAbs+1 < d := by
    have := (Finset.mem_Icc.mp hdX).1
    simp only [Finset.mem_Icc] at hdLag
    omega
  rw [incidence_offDiagonal_eq_zero hne hd]
  simp

/-- Exact prime-power expansion confined to correlated off-diagonal rows. -/
theorem familyQuadratic_eq_correlated {ι : Type*} (S : Finset ℕ) (alpha : ℕ → ℂ)
    (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ) (phase : ℕ → ℂ)
    (hl : ∑ j ∈ J, lambda j = 0) :
    familyQuadratic S alpha J lambda theta phase =
      ∑ N ∈ S, ∑ M ∈ S.filter (fun M => M ≠ N),
        alpha N*conj (alpha M)*lagFactor J lambda theta ((N : ℤ)-M)*
          (∑ d ∈ Finset.Icc 1 (2*((N : ℤ)-M).natAbs+1),
            ((incidence N d*incidence M d : ℝ) : ℂ)*
              (ArithmeticFunction.vonMangoldt d : ℂ)*phase d) := by
  classical
  rw [familyQuadratic_eq_offDiagonal S alpha J lambda theta phase hl]
  apply Finset.sum_congr rfl
  intro N _
  apply Finset.sum_congr rfl
  intro M hM
  rw [fullGram_offDiagonal_eq_short_sum (Finset.mem_filter.mp hM).2.symm]

/-- Explicit fibers preserve the signed lag rather than taking its norm. -/
def lagRows (S : Finset ℕ) (h : ℤ) : Finset (ℕ × ℕ) :=
  (S.product S).filter (fun row => (row.1 : ℤ)-row.2 = h)

/-- Only lags actually present in the coefficient support are introduced. -/
def lags (S : Finset ℕ) : Finset ℤ :=
  (S.product S).image (fun row => (row.1 : ℤ)-row.2)

/-- The entire family is a signed sum over lag fibers, including both
orientations and every original endpoint/gcd observation. -/
theorem familyQuadratic_eq_lag_fibers {ι : Type*} (S : Finset ℕ) (alpha : ℕ → ℂ)
    (J : Finset ι) (lambda : ι → ℂ) (theta : ι → ℝ) (phase : ℕ → ℂ) :
    familyQuadratic S alpha J lambda theta phase =
      ∑ h ∈ lags S, lagFactor J lambda theta h*
        ∑ row ∈ lagRows S h,
          alpha row.1*conj (alpha row.2)*fullGram row.1 row.2 phase := by
  classical
  rw [familyQuadratic_eq_lag]
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := S.product S) (t := lags S)
    (g := fun row : ℕ × ℕ => (row.1 : ℤ)-row.2)
    (fun row hrow => Finset.mem_image_of_mem _ hrow)
    (fun row => alpha row.1*conj (alpha row.2)*
      lagFactor J lambda theta ((row.1 : ℤ)-row.2)*fullGram row.1 row.2 phase)
  have hp := Finset.sum_product' S S (fun N M => alpha N*conj (alpha M)*
    lagFactor J lambda theta ((N : ℤ)-M)*fullGram N M phase)
  calc
    _ = ∑ row ∈ S.product S, alpha row.1*conj (alpha row.2)*
        lagFactor J lambda theta ((row.1 : ℤ)-row.2)*fullGram row.1 row.2 phase := hp.symm
    _ = _ := hf.symm
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro h _
  unfold lagRows
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row hrow
  have he := (Finset.mem_filter.mp hrow).2
  rw [he]
  ring

/-- Three copies of exactly the same finite Fejer amplitude vector. -/
def Cmod (H : ℕ) (theta : ℝ) (s : ℂ) : ℂ :=
  mellin (Finset.range (H+2*H)) (modulate (coefficient H H) theta) s

/-- The requested rational slow phases; the coefficient norms do not change. -/
def slowPhase (H : ℕ) (j : Fin 3) : ℝ := (j : ℕ)/(H : ℝ)

/-- Canonical cyclic coefficient vector, with its determinant sign retained. -/
def canonical (c : Fin 3 → ℂ) : Fin 3 → ℂ := ![c 1-c 2, c 2-c 0, c 0-c 1]

theorem sum_canonical (c : Fin 3 → ℂ) : ∑ j : Fin 3, canonical c j = 0 := by
  simp [Fin.sum_univ_three, canonical]

theorem canonical_pole (c : Fin 3 → ℂ) : ∑ j : Fin 3, canonical c j*c j = 0 := by
  simp [Fin.sum_univ_three, canonical]
  ring

/-- Determinant with rows `1, pole response, matched response`. -/
def sourceDet (c b : Fin 3 → ℂ) : ℂ := Matrix.det !![1, 1, 1;
  c 0, c 1, c 2; b 0, b 1, b 2]

/-- The stated cyclic vector is minus the cofactors of the last row. -/
theorem canonical_response (c b : Fin 3 → ℂ) :
    ∑ j : Fin 3, canonical c j*b j = -sourceDet c b := by
  simp [Fin.sum_univ_three, canonical, sourceDet, Matrix.det_fin_three]
  ring

/-- Exact response of the specified matched power component. -/
theorem canonical_matched_response (c b : Fin 3 → ℂ) (m : ℕ) :
    ∑ j : Fin 3, canonical c j*(-(m : ℂ)*b j) = (m : ℂ)*sourceDet c b := by
  rw [show (∑ j : Fin 3, canonical c j*(-(m : ℂ)*b j)) =
    -(m : ℂ)*(∑ j : Fin 3, canonical c j*b j) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring,
    canonical_response]
  ring

/-- The complete literal pole responses fix the coefficients; no limiting
profile is substituted into the arithmetic statistic. -/
def code (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) : Fin 3 → ℂ :=
  canonical (fun j => Cmod H (theta j) (poleExponent y))

/-- Unnormalized phase-coded prime-power statistic. Divide by H when
comparing its expected native H^(1+beta) response with H^beta. -/
def codedStatistic (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) : ℂ :=
  familyQuadratic (Finset.range (H+2*H)) (coefficient H H)
    Finset.univ (code H theta y) theta (primePhase y)

/-- Exact response to a specified twisted power component. -/
def codedResponse (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) (s : ℂ) : ℂ :=
  ∑ j : Fin 3, code H theta y j*Cmod H (theta j) s

/-- The same finite coefficient packet in the log-denominator variable. -/
def codedRealKernel (H : ℕ) (theta : Fin 3 → ℝ) (y t : ℝ) : ℂ :=
  ∑ j : Fin 3, code H theta y j*
    (realMass (Finset.range (H+2*H)) (modulate (coefficient H H) (theta j)) t : ℂ)

theorem code_sum_eq_zero (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) :
    ∑ j : Fin 3, code H theta y j = 0 := sum_canonical _

/-- For the Fejer family, every literal denominator above 3H disappears. -/
theorem codedKernel_outer_eq_zero {H d : ℕ} (hd : H+2*H < d)
    (theta : Fin 3 → ℝ) (y : ℝ) :
    familyKernel (Finset.range (H+2*H)) (coefficient H H)
      Finset.univ (code H theta y) theta d = 0 :=
  familyKernel_range_eq_zero hd _ _ _ _ (code_sum_eq_zero H theta y)

/-- Both cancellations hold at every finite H, before arithmetic bounds. -/
theorem codedResponse_pole_eq_zero (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) :
    codedResponse H theta y (poleExponent y) = 0 := canonical_pole _

/-- Every ordinary prime and proper power stays in the signed correlated
sector. This is an equality, not a smallness assertion for that sector. -/
theorem codedStatistic_eq_correlated (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) :
    codedStatistic H theta y =
      ∑ N ∈ Finset.range (H+2*H),
        ∑ M ∈ (Finset.range (H+2*H)).filter (fun M => M ≠ N),
          coefficient H H N*conj (coefficient H H M)*
            lagFactor Finset.univ (code H theta y) theta ((N : ℤ)-M)*
              (∑ d ∈ Finset.Icc 1 (2*((N : ℤ)-M).natAbs+1),
                ((incidence N d*incidence M d : ℝ) : ℂ)*
                  (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) :=
  familyQuadratic_eq_correlated _ _ _ _ _ _ (code_sum_eq_zero H theta y)

/-- The same remainder in literal endpoint-gcd coordinates. -/
theorem codedStatistic_eq_offDiagonal_gcd (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) :
    codedStatistic H theta y =
      ∑ N ∈ Finset.range (H+2*H),
        ∑ M ∈ (Finset.range (H+2*H)).filter (fun M => M ≠ N),
          coefficient H H N*conj (coefficient H H M)*
            lagFactor Finset.univ (code H theta y) theta ((N : ℤ)-M)*
              (∑ i : Fin 3, ∑ j : Fin 3,
                ((endpointSign i*endpointSign j : ℝ) : ℂ)*
                  divisorPhase (primePhase y) (Nat.gcd (endpoint N i) (endpoint M j))) := by
  rw [codedStatistic, familyQuadratic_eq_offDiagonal _ _ _ _ _ _
    (code_sum_eq_zero H theta y)]
  simp_rw [fullGram_eq_gcd_sum]

/-- Genuine integrability is proved before interchanging the three responses. -/
theorem integral_codedRealKernel {H : ℕ} (theta : Fin 3 → ℝ) (y : ℝ)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ, Complex.exp (s*t)*codedRealKernel H theta y t) =
      codedResponse H theta y s := by
  unfold codedRealKernel codedResponse Cmod SuzukiCarryPoleCenter.mellin
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [show (fun t : ℝ => Complex.exp (s*t)*(code H theta y j*
      (realMass (Finset.range (H+2*H)) (modulate (coefficient H H) (theta j)) t : ℂ))) =
      (fun t : ℝ => code H theta y j*(Complex.exp (s*t)*
        (realMass (Finset.range (H+2*H)) (modulate (coefficient H H) (theta j)) t : ℂ))) by
          funext t; ring, integral_const_mul]
  · intro j _
    have hi := integrable_mellin (alpha := modulate (coefficient H H) (theta j))
      hs (fun N (hN : N ∈ Finset.range (H+2*H)) =>
        le_of_lt (Finset.mem_range.mp hN))
    convert hi.const_mul (code H theta y j) using 1
    ext t
    ring

/-- The actual continuous pole mode, not only an algebraic placeholder,
has exactly zero response against the joined finite kernel. -/
theorem integral_coded_pole_eq_zero (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) :
    (∫ t : ℝ, Complex.exp (poleExponent y*t)*codedRealKernel H theta y t) = 0 := by
  rw [integral_codedRealKernel theta y (by rw [poleExponent_re]; norm_num),
    codedResponse_pole_eq_zero]

/-- The exact complex determinant controls the specified matched source. -/
theorem codedResponse_eq_neg_det (H : ℕ) (theta : Fin 3 → ℝ) (y : ℝ) (s : ℂ) :
    codedResponse H theta y s = -sourceDet
      (fun j => Cmod H (theta j) (poleExponent y)) (fun j => Cmod H (theta j) s) :=
  canonical_response _ _

/-- All components and phase factors are joined before the power response
is extracted. It is not an actual-prime one-zero asymptotic. -/
theorem integral_coded_matched_response {H : ℕ} (theta : Fin 3 → ℝ)
    {beta : ℝ} (hb : 0 < beta) (y : ℝ) (m : ℕ) :
    (∫ t : ℝ, -(m : ℂ)*Complex.exp (((beta : ℂ)+I*y)*t)*
      Complex.exp (-(I*y)*t)*codedRealKernel H theta y t) =
        (m : ℂ)*sourceDet (fun j => Cmod H (theta j) (poleExponent y))
          (fun j => Cmod H (theta j) (beta : ℂ)) := by
  rw [show (fun t : ℝ => -(m : ℂ)*Complex.exp (((beta : ℂ)+I*y)*t)*
      Complex.exp (-(I*y)*t)*codedRealKernel H theta y t) =
      (fun t : ℝ => -(m : ℂ)*(Complex.exp ((beta : ℂ)*t)*
        codedRealKernel H theta y t)) by
          funext t
          rw [show -(m : ℂ)*Complex.exp (((beta : ℂ)+I*y)*t)*
            Complex.exp (-(I*y)*t)*codedRealKernel H theta y t =
              -(m : ℂ)*(Complex.exp (((beta : ℂ)+I*y)*t)*
                Complex.exp (-(I*y)*t))*codedRealKernel H theta y t by ring,
            ← Complex.exp_add,
            show (((beta : ℂ)+I*y)*t)+(-(I*y)*t) = (beta : ℂ)*t by ring]
          ring, integral_const_mul,
    integral_codedRealKernel theta y (by simpa using hb), codedResponse_eq_neg_det]
  ring

theorem conj_modulation (theta : ℝ) (N : ℕ) :
    conj (modulation theta N) = modulation (-theta) N := by
  simp only [modulation, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, Complex.conj_natCast]
  congr 1
  push_cast
  ring

/-- Real amplitudes give identical squared kernels at opposite modulations. -/
theorem realMass_modulate_neg (S : Finset ℕ) (alpha : ℕ → ℂ)
    (ha : ∀ N, conj (alpha N) = alpha N) (theta t : ℝ) :
    realMass S (modulate alpha (-theta)) t = realMass S (modulate alpha theta) t := by
  have he : realPacket S (modulate alpha (-theta)) t =
      conj (realPacket S (modulate alpha theta) t) := by
    simp only [realPacket, modulate, map_sum, map_mul, Complex.conj_ofReal,
      ha, conj_modulation]
  rw [realMass, realMass, he, Complex.norm_conj]

private theorem conj_coefficient (A H N : ℕ) :
    conj (coefficient A H N) = coefficient A H N := by
  unfold coefficient
  simp only [map_mul, map_inv₀, Complex.conj_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

/-- The symmetric three-code proposal loses the source exactly. -/
theorem Cmod_neg (H : ℕ) (theta : ℝ) (s : ℂ) :
    Cmod H (-theta) s = Cmod H theta s := by
  unfold Cmod SuzukiCarryPoleCenter.mellin
  simp_rw [realMass_modulate_neg _ _ (conj_coefficient H H)]

/-- A regression no-go valid for every finite length and complex exponent. -/
theorem symmetric_sourceDet_eq_zero (H : ℕ) (theta : ℝ) (p s : ℂ) :
    sourceDet (fun j : Fin 3 => Cmod H (![0,theta,-theta] j) p)
      (fun j : Fin 3 => Cmod H (![0,theta,-theta] j) s) = 0 := by
  simp [sourceDet, Matrix.det_fin_three, Cmod_neg]

/-- Only two pole contrasts and two matched contrasts enter the gate. -/
theorem sourceDet_eq_contrasts (c b : Fin 3 → ℂ) :
    sourceDet c b = (c 1-c 0)*(b 2-b 0)-(c 2-c 0)*(b 1-b 0) := by
  simp [sourceDet, Matrix.det_fin_three]
  ring

/-- Exact characterization of source loss; the response vectors become
affine-collinear. No uniform source lower bound follows just from coding. -/
theorem sourceDet_eq_zero_iff (c b : Fin 3 → ℂ) :
    sourceDet c b = 0 ↔ (c 1-c 0)*(b 2-b 0) = (c 2-c 0)*(b 1-b 0) := by
  rw [sourceDet_eq_contrasts, sub_eq_zero]

/-- A finite Mellin-response gap is sufficient for a quantitative source
bound. The analytic response hypotheses remain explicit and unproved. -/
theorem sourceDet_norm_lower_of_gap (c : Fin 3 → ℂ) (b : Fin 3 → ℝ)
    {epsilon : ℝ}
    (he : epsilon ≤ (c 1-c 0).re*(b 2-b 0)-(c 2-c 0).re*(b 1-b 0)) :
    epsilon ≤ ‖sourceDet c (fun j => (b j : ℂ))‖ := by
  have hr : (sourceDet c (fun j => (b j : ℂ))).re =
      (c 1-c 0).re*(b 2-b 0)-(c 2-c 0).re*(b 1-b 0) := by
    rw [sourceDet_eq_contrasts]
    simp [Complex.mul_re]
  rw [← hr] at he
  exact he.trans (Complex.re_le_norm _)

theorem modulation_pi (N : ℕ) : modulation Real.pi N = (-1 : ℂ)^N := by
  rw [modulation, show I*(Real.pi : ℂ)*(N : ℂ) = (N : ℂ)*((Real.pi : ℂ)*I) by ring,
    Complex.exp_nat_mul, Complex.exp_pi_mul_I]

private theorem incidence_two_eq_sign (N : ℕ) : (incidence N 2 : ℂ) = (-1 : ℂ)^N := by
  rw [incidence_two_spikes (by norm_num : 2 ≤ 2)]
  by_cases hn : N%2 = 0
  · have he := (Nat.even_iff.mpr hn).neg_one_pow (α := ℂ)
    simp [hn, he]
  · have ho := (Nat.odd_iff.mpr (by omega : N%2 = 1)).neg_one_pow (α := ℂ)
    simp [show N%2 = 1 by omega, ho]

/-- A fixed modulation can resonate with a literal small denominator.
Thus the old Fejer low-denominator payment cannot simply be reused. -/
theorem packet_pi_two (S : Finset ℕ) (alpha : ℕ → ℂ) :
    packet S (modulate alpha Real.pi) 2 = ∑ N ∈ S, alpha N := by
  unfold packet modulate
  apply Finset.sum_congr rfl
  intro N _
  rw [modulation_pi, incidence_two_eq_sign,
    mul_assoc, ← pow_add, show N+N = 2*N by omega, pow_mul]
  simp

/-- The finite triangular vector has exact total amplitude H. -/
theorem sum_coefficient (A H : ℕ) :
    (∑ N ∈ Finset.range (A+2*H), coefficient A H N) = (H : ℂ) := by
  classical
  by_cases hH : H = 0
  · simp [hH, coefficient]
  have hrow (t : ℕ) (ht : t ∈ Finset.range H) :
      (∑ N ∈ Finset.range (A+2*H),
        if A+t ≤ N ∧ N < A+t+H then (1 : ℂ) else 0) = H := by
    have hfilter : (Finset.range (A+2*H)).filter (fun N => A+t ≤ N ∧ N < A+t+H) =
        Finset.Ico (A+t) (A+t+H) := by
      ext N
      have := Finset.mem_range.mp ht
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [← Finset.sum_filter, hfilter]
    simp
  unfold coefficient
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl hrow]
  simp [hH]

/-- A concrete cofinal alias obstruction: the pi-modulated packet has
quadratic mass H^2 at d=2, rather than the old vanishing period remainder. -/
theorem packetMass_pi_two (A H : ℕ) :
    packetMass (Finset.range (A+2*H)) (modulate (coefficient A H) Real.pi) 2 =
      (H : ℝ)^2 := by
  rw [packetMass, packet_pi_two, sum_coefficient]
  simp [Complex.normSq_eq_norm_sq]

end
end RiemannGaussian.SuzukiCarryPhaseCode
