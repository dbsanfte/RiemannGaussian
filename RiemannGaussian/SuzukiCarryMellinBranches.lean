/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryMellinJet
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Exact polynomial branches of the carry Mellin jets

The common knot grid is `12/n`: it contains every tent knot `2a/b`
for `a=1,2,3`. Coincident knots retain their literal value. The branch
formulas are finite rational polynomials, not fitted Mellin samples.
-/

namespace RiemannGaussian.SuzukiCarryMellinBranches
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryMellinLimit SuzukiCarryMellinRate SuzukiCarryMellinJet
open scoped BigOperators Topology

/-- Finite alternating power prefix, with the original incidence sign. -/
def powerPrefix (j K : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, (-1 : ℝ)^k*(((k+1 : ℕ) : ℝ)*x/2)^j

/-- The literal tent moment on the common knot cell indexed by n. -/
def branchMoment (j n : ℕ) (x : ℝ) : ℝ :=
  2*powerPrefix (j+1) (n/3) x-powerPrefix (j+1) (n/6) x-
    powerPrefix (j+1) (n/2) x+powerPrefix j (n/6) x+
    3*powerPrefix j (n/2) x-4*powerPrefix j (n/3) x

/-- Exact quadratic coefficient density on a common-grid branch. -/
def branchB (n : ℕ) (x : ℝ) : ℝ :=
  branchMoment 1 n x^2-branchMoment 0 n x*branchMoment 2 n x

/-- Exact quartic coefficient density on a common-grid branch. -/
def branchC (n : ℕ) (x : ℝ) : ℝ :=
  branchMoment 2 n x^2/4+branchMoment 0 n x*branchMoment 4 n x/12-
    branchMoment 1 n x*branchMoment 3 n x/3

private theorem tent_prefix (v : ℝ) :
    tent v = (if v ≤ 2 then v-1 else 0)-(if v ≤ 1 then v-1 else 0)+
      (if v ≤ 3 then 3-v else 0)-(if v ≤ 2 then 3-v else 0) := by
  by_cases h1 : v ≤ 1
  · have h2 : v ≤ 2 := by linarith
    have h3 : v ≤ 3 := by linarith
    simp [h1, h2, h3, tent_eq_zero_of_le h1]
  by_cases h2 : v ≤ 2
  · have h3 : v ≤ 3 := by linarith
    rw [tent_eq_left (by linarith) h2]
    simp [h1, h2, h3]
  by_cases h3 : v ≤ 3
  · rw [tent_eq_right (by linarith) h3]
    simp [h1, h2, h3]
  · simp [h1, h2, h3, tent_eq_zero_of_ge (by linarith : 3 ≤ v)]

private theorem prefix_range {K A : ℕ} (hAK : A ≤ K) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range K, if k < A then f k else 0) =
      ∑ k ∈ Finset.range A, f k := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The moment is an exact combination of three alternating polynomial prefixes. -/
theorem moment_eq_prefixes (j : ℕ) {x : ℝ} (hx : 0 < x) :
    moment j x =
      2*powerPrefix (j+1) ⌊4/x⌋₊ x-powerPrefix (j+1) ⌊2/x⌋₊ x-
        powerPrefix (j+1) ⌊6/x⌋₊ x+powerPrefix j ⌊2/x⌋₊ x+
        3*powerPrefix j ⌊6/x⌋₊ x-4*powerPrefix j ⌊4/x⌋₊ x := by
  have hfloor (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
      (((k+1 : ℕ) : ℝ)*x/2 ≤ a) ↔ k < ⌊2*a/x⌋₊ := by
    rw [show k < ⌊2*a/x⌋₊ ↔ k+1 ≤ ⌊2*a/x⌋₊ by omega,
      Nat.le_floor_iff (by positivity : 0 ≤ 2*a/x)]
    rw [le_div_iff₀ hx]
    constructor <;> intro h <;> linarith
  have hlim (a : ℝ) (ha : 0 ≤ a) (ha3 : a ≤ 3) : ⌊2*a/x⌋₊ ≤ jumpCount x := by
    apply (Nat.floor_mono (by gcongr; linarith : 2*a/x ≤ 6/x)).trans
    exact Nat.floor_le_ceil _
  have hterm (k : ℕ) :
      (-1 : ℝ)^k*tent (((k+1 : ℕ) : ℝ)*x/2)*(((k+1 : ℕ) : ℝ)*x/2)^j =
        2*(if k < ⌊4/x⌋₊ then (-1 : ℝ)^k*(((k+1 : ℕ) : ℝ)*x/2)^(j+1) else 0)-
        (if k < ⌊2/x⌋₊ then (-1 : ℝ)^k*(((k+1 : ℕ) : ℝ)*x/2)^(j+1) else 0)-
        (if k < ⌊6/x⌋₊ then (-1 : ℝ)^k*(((k+1 : ℕ) : ℝ)*x/2)^(j+1) else 0)+
        (if k < ⌊2/x⌋₊ then (-1 : ℝ)^k*(((k+1 : ℕ) : ℝ)*x/2)^j else 0)+
        3*(if k < ⌊6/x⌋₊ then (-1 : ℝ)^k*(((k+1 : ℕ) : ℝ)*x/2)^j else 0)-
        4*(if k < ⌊4/x⌋₊ then (-1 : ℝ)^k*(((k+1 : ℕ) : ℝ)*x/2)^j else 0) := by
    rw [tent_prefix]
    simp only [hfloor 1 (by norm_num), hfloor 2 (by norm_num),
      hfloor 3 (by norm_num)]
    norm_num only [mul_one, show (2 : ℝ)*2 = 4 by norm_num,
      show (2 : ℝ)*3 = 6 by norm_num]
    split_ifs <;> (try simp only [pow_succ]) <;> ring
  unfold moment
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ⌊2/x⌋₊ ≤ jumpCount x := by simpa using hlim 1 (by norm_num) (by norm_num)
  have h2 : ⌊4/x⌋₊ ≤ jumpCount x := by convert! hlim 2 (by norm_num) (by norm_num) using 1; norm_num
  have h3 : ⌊6/x⌋₊ ≤ jumpCount x := by convert! hlim 3 (by norm_num) (by norm_num) using 1; norm_num
  rw [prefix_range h2, prefix_range h1, prefix_range h3,
    prefix_range h1, prefix_range h3, prefix_range h2]
  rfl

/-- Every common-grid cell gives a finite rational polynomial, including its upper knot. -/
theorem moment_eq_branch (j : ℕ) {x : ℝ} (hx : 0 < x) :
    moment j x = branchMoment j ⌊12/x⌋₊ x := by
  rw [moment_eq_prefixes j hx]
  unfold branchMoment
  have he (d : ℕ) (hd : 0 < d) : ⌊12/x/(d : ℝ)⌋₊ = ⌊12/x⌋₊/d :=
    Nat.floor_div_natCast _ _
  rw [show 4/x = 12/x/(3 : ℕ) by ring,
    show 2/x = 12/x/(6 : ℕ) by ring,
    show 6/x = 12/x/(2 : ℕ) by ring,
    he 3 (by norm_num), he 6 (by norm_num), he 2 (by norm_num)]

theorem quadraticDensity_eq_branch {x : ℝ} (hx : 0 < x) :
    quadraticDensity x = branchB ⌊12/x⌋₊ x := by
  simp only [quadraticDensity, branchB, moment_eq_branch _ hx]

theorem quarticDensity_eq_branch {x : ℝ} (hx : 0 < x) :
    quarticDensity x = branchC ⌊12/x⌋₊ x := by
  simp only [quarticDensity, branchC, moment_eq_branch _ hx]

/-- Polynomial version of a finite alternating prefix. -/
def prefixPolynomial (j K : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range K, Polynomial.C ((-1 : ℝ)^k)*
    (Polynomial.C (((k+1 : ℕ) : ℝ)/2)*Polynomial.X)^j

/-- Rational polynomial of the j-th moment on the n-th knot branch. -/
def momentPolynomial (j n : ℕ) : Polynomial ℝ :=
  Polynomial.C 2*prefixPolynomial (j+1) (n/3)-prefixPolynomial (j+1) (n/6)-
    prefixPolynomial (j+1) (n/2)+prefixPolynomial j (n/6)+
    Polynomial.C 3*prefixPolynomial j (n/2)-Polynomial.C 4*prefixPolynomial j (n/3)

/-- Polynomial of the exact quadratic coefficient density. -/
def bPolynomial (n : ℕ) : Polynomial ℝ :=
  momentPolynomial 1 n^2-momentPolynomial 0 n*momentPolynomial 2 n

/-- Polynomial of the exact quartic coefficient density. -/
def cPolynomial (n : ℕ) : Polynomial ℝ :=
  Polynomial.C (1/4)*momentPolynomial 2 n^2+
    Polynomial.C (1/12)*momentPolynomial 0 n*momentPolynomial 4 n-
    Polynomial.C (1/3)*momentPolynomial 1 n*momentPolynomial 3 n

theorem eval_prefixPolynomial (j K : ℕ) (x : ℝ) :
    (prefixPolynomial j K).eval x = powerPrefix j K x := by
  simp only [prefixPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, powerPrefix]
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  ring

theorem eval_momentPolynomial (j n : ℕ) (x : ℝ) :
    (momentPolynomial j n).eval x = branchMoment j n x := by
  simp [momentPolynomial, branchMoment, eval_prefixPolynomial]

theorem eval_bPolynomial (n : ℕ) (x : ℝ) :
    (bPolynomial n).eval x = branchB n x := by
  simp [bPolynomial, branchB, eval_momentPolynomial]

theorem eval_cPolynomial (n : ℕ) (x : ℝ) :
    (cPolynomial n).eval x = branchC n x := by
  simp only [cPolynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, eval_momentPolynomial,
    branchC]
  ring

/-- Upper cell edge. Each cell is open below and closed above. -/
def edge (n : ℕ) : ℝ := 12/(n+1 : ℕ)

/-- Logarithmic common-grid cell with its literal upper endpoint included. -/
def logCell (n : ℕ) : Set ℝ := Ioc (Real.log (edge (n+1))) (Real.log (edge n))

theorem edge_pos (n : ℕ) : 0 < edge n := by unfold edge; positivity

theorem edge_strictAnti : StrictAnti edge := by
  intro n m hnm
  unfold edge
  apply div_lt_div_of_pos_left (by norm_num) (by positivity)
  exact_mod_cast (show n+1 < m+1 by omega)

private theorem floor_eq_of_mem_cell {n : ℕ} {t : ℝ} (ht : t ∈ logCell n) :
    ⌊12/Real.exp t⌋₊ = n+1 := by
  have hx := Real.exp_pos t
  have hlo : edge (n+1) < Real.exp t :=
    (Real.log_lt_iff_lt_exp (edge_pos _)).mp ht.1
  have hhi : Real.exp t ≤ edge n :=
    (Real.le_log_iff_exp_le (edge_pos _)).mp ht.2
  apply Nat.floor_eq_iff (by positivity : 0 ≤ 12/Real.exp t) |>.mpr
  constructor
  · rw [le_div_iff₀ hx]
    have he := (le_div_iff₀ (show (0 : ℝ) < (n+1 : ℕ) by positivity)).mp hhi
    simpa only [mul_comm] using he
  · rw [div_lt_iff₀ hx]
    have he := (div_lt_iff₀ (show (0 : ℝ) < (n+1+1 : ℕ) by positivity)).mp hlo
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using he

/-- Elementary Mellin integral of any polynomial branch. -/
def polynomialCell (P : Polynomial ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ P.support, (P.coeff j : ℂ)*
    (Complex.exp ((s+j)*(Real.log (edge n) : ℂ))-
      Complex.exp ((s+j)*(Real.log (edge (n+1)) : ℂ)))/(s+j)

private theorem exponential_monomial (s : ℂ) (j : ℕ) (t : ℝ) :
    Complex.exp (s*t)*((Real.exp t)^j : ℂ) = Complex.exp ((s+j)*t) := by
  rw [Complex.ofReal_exp, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

theorem integral_polynomial_cell (P : Polynomial ℝ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ t in logCell n, Complex.exp (s*t)*((P.eval (Real.exp t) : ℝ) : ℂ)) =
      polynomialCell P s n := by
  have hab : Real.log (edge (n+1)) ≤ Real.log (edge n) :=
    (Real.log_le_log (edge_pos _) (edge_strictAnti (by omega)).le)
  rw [logCell, ← intervalIntegral.integral_of_le hab]
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    have hne : s+(j : ℂ) ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hr
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      linarith
    rw [show (fun t : ℝ => Complex.exp (s*t)*((P.coeff j : ℂ)*(Real.exp t : ℂ)^j)) =
      (fun t : ℝ => (P.coeff j : ℂ)*Complex.exp ((s+j)*t)) by
        funext t; rw [← exponential_monomial]; push_cast; ring,
      intervalIntegral.integral_const_mul, integral_exp_mul_complex hne]
    ring
  · intro j _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem integral_B_cell {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ t in logCell n, Complex.exp (s*t)*(quadraticDensity (Real.exp t) : ℂ)) =
      polynomialCell (bPolynomial (n+1)) s n := by
  rw [← integral_polynomial_cell _ hs]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [quadraticDensity_eq_branch (Real.exp_pos t), floor_eq_of_mem_cell ht,
    eval_bPolynomial]

theorem integral_C_cell {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ t in logCell n, Complex.exp (s*t)*(quarticDensity (Real.exp t) : ℂ)) =
      polynomialCell (cPolynomial (n+1)) s n := by
  rw [← integral_polynomial_cell _ hs]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [quarticDensity_eq_branch (Real.exp_pos t), floor_eq_of_mem_cell ht,
    eval_cPolynomial]

theorem logCells_disjoint : Pairwise (fun n m : ℕ => Disjoint (logCell n) (logCell m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro t hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · have he : edge m ≤ edge (n+1) :=
      edge_strictAnti.antitone (by omega)
    have hl := Real.log_le_log (edge_pos _) he
    have hh := hm.2.trans hl
    exact (not_lt_of_ge hh) hn.1
  · have he : edge n ≤ edge (m+1) :=
      edge_strictAnti.antitone (by omega)
    have hl := Real.log_le_log (edge_pos _) he
    have hh := hn.2.trans hl
    exact (not_lt_of_ge hh) hm.1

theorem union_logCells : (⋃ n : ℕ, logCell n) = Iic (Real.log 12) := by
  ext t
  constructor
  · intro ht
    rcases mem_iUnion.mp ht with ⟨n, hn⟩
    have he : edge n ≤ edge 0 := edge_strictAnti.antitone (by omega)
    have hh := hn.2.trans (Real.log_le_log (edge_pos _) he)
    simpa [edge] using hh
  · intro ht
    have hx := Real.exp_pos t
    have h12 : Real.exp t ≤ 12 :=
      (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 12)).mp ht
    let K := ⌊12/Real.exp t⌋₊
    have hK : 1 ≤ K := Nat.le_floor ((le_div_iff₀ hx).mpr (by simpa using h12))
    have hlo : (K : ℝ) ≤ 12/Real.exp t := Nat.floor_le (by positivity)
    have hhi : 12/Real.exp t < K+1 := Nat.lt_floor_add_one _
    apply mem_iUnion.mpr
    refine ⟨K-1, ?_⟩
    change Real.log (edge (K-1+1)) < t ∧ t ≤ Real.log (edge (K-1))
    rw [Nat.sub_add_cancel hK]
    constructor
    · apply (Real.log_lt_iff_lt_exp (edge_pos _)).mpr
      unfold edge
      rw [div_lt_iff₀ (show (0 : ℝ) < (K+1 : ℕ) by positivity)]
      have he := (div_lt_iff₀ hx).mp hhi
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using he
    · apply (Real.le_log_iff_exp_le (edge_pos _)).mpr
      unfold edge
      rw [Nat.sub_add_cancel hK, le_div_iff₀ (show (0 : ℝ) < K by exact_mod_cast hK)]
      have he := (le_div_iff₀ hx).mp hlo
      simpa only [mul_comm] using he

/-- Explicit convergent series for the quadratic coefficient, with no Hurwitz
identification or floating boundary evaluation assumed. -/
theorem hasSum_B_cells {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => polynomialCell (bPolynomial (n+1)) s n) (B s) := by
  have h := hasSum_integral_iUnion (f := fun t : ℝ =>
    Complex.exp (s*t)*(quadraticDensity (Real.exp t) : ℂ))
    (fun _ => measurableSet_Ioc) logCells_disjoint (integrable_B hs).integrableOn
  change HasSum (fun n : ℕ => ∫ t in logCell n,
    Complex.exp (s*t)*(quadraticDensity (Real.exp t) : ℂ))
    (∫ t in ⋃ n : ℕ, logCell n,
      Complex.exp (s*t)*(quadraticDensity (Real.exp t) : ℂ)) at h
  rw [union_logCells] at h
  have he : (∫ t in Iic (Real.log 12),
      Complex.exp (s*t)*(quadraticDensity (Real.exp t) : ℂ)) = B s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hx : 6 ≤ Real.exp t := by
      have hh := (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 12)).mp
        (lt_of_not_ge ht)
      linarith
    simp [quadraticDensity, moment_zero_above _ hx]
  rw [he] at h
  exact h.congr (fun N => Finset.sum_congr rfl (fun n _ => integral_B_cell hs n))

/-- Explicit convergent series for the quartic coefficient. -/
theorem hasSum_C_cells {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => polynomialCell (cPolynomial (n+1)) s n) (C s) := by
  have h := hasSum_integral_iUnion (f := fun t : ℝ =>
    Complex.exp (s*t)*(quarticDensity (Real.exp t) : ℂ))
    (fun _ => measurableSet_Ioc) logCells_disjoint (integrable_C hs).integrableOn
  change HasSum (fun n : ℕ => ∫ t in logCell n,
    Complex.exp (s*t)*(quarticDensity (Real.exp t) : ℂ))
    (∫ t in ⋃ n : ℕ, logCell n,
      Complex.exp (s*t)*(quarticDensity (Real.exp t) : ℂ)) at h
  rw [union_logCells] at h
  have he : (∫ t in Iic (Real.log 12),
      Complex.exp (s*t)*(quarticDensity (Real.exp t) : ℂ)) = C s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hx : 6 ≤ Real.exp t := by
      have hh := (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 12)).mp
        (lt_of_not_ge ht)
      linarith
    simp [quarticDensity, moment_zero_above _ hx]
  rw [he] at h
  exact h.congr (fun N => Finset.sum_congr rfl (fun n _ => integral_C_cell hs n))

/-- Finite-polynomial/exponential definition of the exact exceptional equation. -/
def explicitB (s : ℂ) : ℂ := ∑' n : ℕ, polynomialCell (bPolynomial (n+1)) s n

/-- Elementary polynomial/exponential series for the exact quartic coefficient. -/
def explicitC (s : ℂ) : ℂ := ∑' n : ℕ, polynomialCell (cPolynomial (n+1)) s n

theorem explicitB_eq {s : ℂ} (hs : 0 < s.re) : explicitB s = B s :=
  (hasSum_B_cells hs).tsum_eq

theorem explicitC_eq {s : ℂ} (hs : 0 < s.re) : explicitC s = C s :=
  (hasSum_C_cells hs).tsum_eq

/-- Exact, explicit series equation for loss of the fourth-order source.
This does not assert that its campaign solution set is empty. -/
theorem wedge_eq_zero_iff_explicit {p s : ℂ} (hp : 0 < p.re) (hs : 0 < s.re) :
    B p*C s-C p*B s = 0 ↔ explicitB p*explicitC s = explicitC p*explicitB s := by
  rw [explicitB_eq hp, explicitB_eq hs, explicitC_eq hp, explicitC_eq hs, sub_eq_zero]

private theorem integral_sub_prefix_cells {f : ℝ → ℂ} (hf : Integrable f)
    (hz : ∀ t, Real.log 12 < t → f t = 0) (N : ℕ) :
    (∫ t, f t)-(∑ n ∈ Finset.range N, ∫ t in logCell n, f t) =
      ∫ t in Iic (Real.log (edge N)), f t := by
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have he : ¬ t ≤ Real.log 12 := by simpa [edge] using ht
      exact hz t (lt_of_not_ge he)
  | succ N ih =>
      rw [Finset.sum_range_succ, show
        (∫ t, f t)-((∑ n ∈ Finset.range N, ∫ t in logCell n, f t)+
          ∫ t in logCell N, f t) =
        ((∫ t, f t)-(∑ n ∈ Finset.range N, ∫ t in logCell n, f t))-
          ∫ t in logCell N, f t by ring, ih]
      have hh := intervalIntegral.integral_Iic_sub_Iic
        (a := Real.log (edge (N+1))) (b := Real.log (edge N))
        hf.integrableOn hf.integrableOn
      have he : Real.log (edge (N+1)) ≤ Real.log (edge N) :=
        (Real.log_le_log (edge_pos _) (edge_strictAnti (by omega)).le)
      rw [intervalIntegral.integral_of_le he] at hh
      change _-_ = ∫ t in logCell N, f t at hh
      rw [← hh]
      ring

private theorem density_tail_bound {s : ℂ} (hs : 0 < s.re) (g : ℝ → ℝ)
    {D : ℝ} (_hD : 0 ≤ D) (hb : ∀ x, 0 < x → |g x| ≤ D) (N : ℕ) :
    ‖∫ t in Iic (Real.log (edge N)), Complex.exp (s*t)*(g (Real.exp t) : ℂ)‖ ≤
      D*Real.exp (s.re*Real.log (edge N))/s.re := by
  have hi := (integrableOn_exp_mul_Iic hs (Real.log (edge N))).const_mul D
  apply (norm_integral_le_of_norm_le hi ?_).trans_eq
    (by rw [integral_const_mul, integral_exp_mul_Iic hs]; ring)
  filter_upwards with t
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hr : (s*(t : ℂ)).re = s.re*t := by simp [Complex.mul_re]
  rw [hr]
  exact (mul_le_mul_of_nonneg_left (hb _ (Real.exp_pos t)) (Real.exp_pos _).le).trans_eq
    (by ring)

/-- Explicit certified truncation error for the elementary quadratic series. -/
theorem B_prefix_error {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖B s-∑ n ∈ Finset.range N, polynomialCell (bPolynomial (n+1)) s n‖ ≤
      279*Real.exp (s.re*Real.log (edge N))/s.re := by
  have he := integral_sub_prefix_cells (integrable_B hs) (fun t ht => by
    have hx : 6 ≤ Real.exp t := by
      have h := (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 12)).mp ht
      linarith
    simp [quadraticDensity, moment_zero_above _ hx]) N
  simp only [integral_B_cell hs] at he
  rw [B, he]
  exact density_tail_bound hs quadraticDensity (by norm_num)
    (fun _ hx => quadraticDensity_bound hx) N

/-- Explicit certified truncation error for the elementary quartic series. -/
theorem C_prefix_error {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖C s-∑ n ∈ Finset.range N, polynomialCell (cPolynomial (n+1)) s n‖ ≤
      1296*Real.exp (s.re*Real.log (edge N))/s.re := by
  have he := integral_sub_prefix_cells (integrable_C hs) (fun t ht => by
    have hx : 6 ≤ Real.exp t := by
      have h := (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 12)).mp ht
      linarith
    simp [quarticDensity, moment_zero_above _ hx]) N
  simp only [integral_C_cell hs] at he
  rw [C, he]
  exact density_tail_bound hs quarticDensity (by norm_num)
    (fun _ hx => quarticDensity_bound hx) N

/-- The exact exceptional equation for a campaign candidate. It involves
only the elementary branch series; emptiness has not been proved. -/
def exceptional (beta y : ℝ) : Prop :=
  explicitB (SuzukiCarryPoleCenter.poleExponent y)*explicitC (beta : ℂ) =
    explicitC (SuzukiCarryPoleCenter.poleExponent y)*explicitB (beta : ℂ)

theorem exceptional_iff_wedge_zero {beta : ℝ} (hb : 0 < beta) (y : ℝ) :
    exceptional beta y ↔
      B (SuzukiCarryPoleCenter.poleExponent y)*C (beta : ℂ)-
        C (SuzukiCarryPoleCenter.poleExponent y)*B (beta : ℂ) = 0 := by
  exact (wedge_eq_zero_iff_explicit
    (by rw [SuzukiCarryPoleCenter.poleExponent_re]; norm_num) (by simpa using hb)).symm

/-- Every nonexceptional candidate has a fixed positive asymmetric code
with an actual cofinal native source bound. No exposure or arithmetic
prime-sum estimate is assumed or concluded. -/
theorem exists_fixed_code_of_not_exceptional {beta : ℝ} (hb : 0 < beta)
    {y : ℝ} (h : ¬ exceptional beta y) :
    ∃ tau : ℝ, 0 < tau ∧ continuumDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖continuumDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖/2)*
          Real.exp ((1+beta)*Real.log H) ≤
            ‖nativeDet H (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖ := by
  have hw := mt (exceptional_iff_wedge_zero hb y).mpr h
  simpa only [SuzukiCarryPoleCenter.poleExponent_re, Complex.ofReal_re] using
    exists_fixed_code_of_wedge
      (by rw [SuzukiCarryPoleCenter.poleExponent_re]; norm_num) (by simpa using hb) hw

end
end RiemannGaussian.SuzukiCarryMellinBranches
