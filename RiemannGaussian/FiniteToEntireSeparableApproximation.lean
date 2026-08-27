import RiemannGaussian.FiniteToEntireRealApproximation
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Separable finite approximants with an exact homotopy root

This file closes the separability gap left by exact affine root pinning.  For
a positive homotopy parameter and a prescribed upper-half-plane root, it
constructs an explicit separable quadratic in the kernel of
`A ↦ (A + i * eta * A').eval z`.  A vanishing cubic-kernel perturbation first
raises every finite model above degree two.

For a polynomial of degree above two, its Wronskian with the quadratic kernel
is nonzero.  Every parameter at which the resulting pencil can fail to be
separable is then forced by a root of that Wronskian, producing a literal
finite bad-parameter set in Lean.  Choosing positive parameters tending to
zero outside those finite sets gives separable real polynomials which retain
the exact prescribed homotopy root and the original locally uniform limit.

The final theorem specializes this construction to the explicit real Taylor
approximants of spectral xi.  No root-selection or simplicity assumption on
xi is used.
-/

open Filter Polynomial Set
open scoped ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- An explicit monic real quadratic in the kernel of finite homotopy
evaluation at `z`. -/
def finiteERootKernelQuadratic (eta : ℝ) (z : ℂ) : ℝ[X] :=
  (X - C z.re) ^ 2 + C (z.im * (z.im + 2 * eta))

/-- The quadratic homotopy kernel is monic of degree two. -/
theorem finiteERootKernelQuadratic_isMonicOfDegree (eta : ℝ) (z : ℂ) :
    (finiteERootKernelQuadratic eta z).IsMonicOfDegree 2 := by
  have hdegree :
      (C (z.im * (z.im + 2 * eta)) : ℝ[X]).degree <
        ((X - C z.re) ^ 2 : ℝ[X]).degree := by
    calc
      (C (z.im * (z.im + 2 * eta)) : ℝ[X]).degree ≤ 0 := degree_C_le
      _ < 2 := by norm_num
      _ = ((X - C z.re) ^ 2 : ℝ[X]).degree := by simp
  refine ⟨?_, ?_⟩
  · rw [finiteERootKernelQuadratic,
      natDegree_add_eq_left_of_degree_lt hdegree]
    simp
  · rw [finiteERootKernelQuadratic]
    exact Monic.add_of_left ((monic_X_sub_C z.re).pow 2) hdegree

/-- The quadratic homotopy kernel is monic. -/
theorem finiteERootKernelQuadratic_monic (eta : ℝ) (z : ℂ) :
    (finiteERootKernelQuadratic eta z).Monic := by
  exact (finiteERootKernelQuadratic_isMonicOfDegree eta z).monic

/-- The quadratic homotopy kernel has degree two. -/
@[simp] theorem finiteERootKernelQuadratic_natDegree (eta : ℝ) (z : ℂ) :
    (finiteERootKernelQuadratic eta z).natDegree = 2 := by
  exact (finiteERootKernelQuadratic_isMonicOfDegree eta z).natDegree_eq

/-- Exact derivative of the quadratic homotopy kernel. -/
@[simp] theorem finiteERootKernelQuadratic_derivative (eta : ℝ) (z : ℂ) :
    (finiteERootKernelQuadratic eta z).derivative =
      C 2 * (X - C z.re) := by
  simp [finiteERootKernelQuadratic, derivative_pow]

/-- The quadratic kernel leaves `z` as an exact root of its finite
homotopy. -/
theorem finiteERootKernelQuadratic_isRoot (eta : ℝ) (z : ℂ) :
    (finiteEPolynomial (finiteERootKernelQuadratic eta z) eta).eval z = 0 := by
  have hqeval :
      (finiteERootKernelQuadratic eta z).eval₂ Complex.ofRealHom z =
        (z - (z.re : ℂ)) ^ 2 +
          (z.im * (z.im + 2 * eta) : ℝ) := by
    rw [finiteERootKernelQuadratic, eval₂_add, eval₂_pow]
    simp
  have hdeval :
      (finiteERootKernelQuadratic eta z).derivative.eval₂
        Complex.ofRealHom z = 2 * (z - (z.re : ℂ)) := by
    rw [finiteERootKernelQuadratic_derivative]
    simp
  rw [finiteEPolynomial_eval]
  rw [hqeval, hdeval]
  have hzdecomp : z - (z.re : ℂ) = Complex.I * (z.im : ℂ) := by
    apply Complex.ext <;> simp
  rw [hzdecomp]
  simp only [mul_pow, Complex.I_sq, neg_one_mul]
  rw [← Complex.ofReal_pow]
  apply Complex.ext
  · simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  · simp [pow_two, Complex.mul_re, Complex.mul_im]

/-- For positive `eta` and an upper-half-plane point `z`, the quadratic
homotopy kernel is separable. -/
theorem finiteERootKernelQuadratic_separable
    {eta : ℝ} (heta : 0 < eta) {z : ℂ} (hz : 0 < z.im) :
    (finiteERootKernelQuadratic eta z).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := ℝ) ℂ _ _).2
  intro a
  by_cases hd : aeval a (finiteERootKernelQuadratic eta z).derivative = 0
  · left
    have ha : a = (z.re : ℂ) := by
      simp only [finiteERootKernelQuadratic_derivative, map_mul, aeval_C,
        aeval_sub, aeval_X] at hd
      rcases mul_eq_zero.mp hd with htwo | hsub
      · norm_num at htwo
      · exact sub_eq_zero.mp hsub
    rw [ha]
    simp [finiteERootKernelQuadratic]
    constructor
    · exact_mod_cast hz.ne'
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
  · exact Or.inr hd

/-- A monic cubic obtained by root-pinning `X ^ 3`. -/
def finiteERootKernelCubic (eta : ℝ) (z : ℂ) : ℝ[X] :=
  finiteERootPinnedPolynomial (X ^ 3) eta z

/-- The cubic kernel retains `z` as an exact finite homotopy root whenever
the affine pinning denominator is nonzero. -/
theorem finiteERootKernelCubic_isRoot
    (eta : ℝ) {z : ℂ} (hz : z.im + eta ≠ 0) :
    (finiteEPolynomial (finiteERootKernelCubic eta z) eta).eval z = 0 := by
  exact finiteERootPinnedPolynomial_isRoot (X ^ 3) eta hz

/-- The cubic homotopy kernel is monic of degree three. -/
theorem finiteERootKernelCubic_isMonicOfDegree (eta : ℝ) (z : ℂ) :
    (finiteERootKernelCubic eta z).IsMonicOfDegree 3 := by
  rw [finiteERootKernelCubic, finiteERootPinnedPolynomial]
  rw [add_assoc]
  apply (isMonicOfDegree_X_pow ℝ 3).add_right
  apply (natDegree_add_le _ _).trans_lt
  apply lt_of_le_of_lt (b := 1)
  · apply max_le
    · simp
    · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  · omega

/-- The cubic homotopy kernel is monic. -/
theorem finiteERootKernelCubic_monic (eta : ℝ) (z : ℂ) :
    (finiteERootKernelCubic eta z).Monic := by
  exact (finiteERootKernelCubic_isMonicOfDegree eta z).monic

/-- The cubic homotopy kernel has degree three. -/
@[simp] theorem finiteERootKernelCubic_natDegree (eta : ℝ) (z : ℂ) :
    (finiteERootKernelCubic eta z).natDegree = 3 := by
  exact (finiteERootKernelCubic_isMonicOfDegree eta z).natDegree_eq

/-- Raise a low-degree pinned polynomial to degree three by a nonzero amount
of the cubic kernel; leave higher-degree polynomials unchanged. -/
def finiteERootDegreeLift
    (A : ℝ[X]) (eta : ℝ) (z : ℂ) (r : ℝ) : ℝ[X] :=
  if A.natDegree ≤ 2 then
    A + C r * finiteERootKernelCubic eta z
  else A

/-- Finite homotopy evaluation is additive in the real base polynomial. -/
theorem finiteEPolynomial_eval_add (A B : ℝ[X]) (eta : ℝ) (z : ℂ) :
    (finiteEPolynomial (A + B) eta).eval z =
      (finiteEPolynomial A eta).eval z +
        (finiteEPolynomial B eta).eval z := by
  simp [finiteEPolynomial, smul_eq_C_mul]
  ring

/-- Finite homotopy evaluation commutes with real scalar multiplication of
the base polynomial. -/
theorem finiteEPolynomial_eval_C_mul
    (r : ℝ) (A : ℝ[X]) (eta : ℝ) (z : ℂ) :
    (finiteEPolynomial (C r * A) eta).eval z =
      (r : ℂ) * (finiteEPolynomial A eta).eval z := by
  simp [finiteEPolynomial, smul_eq_C_mul]
  ring

/-- Degree lifting preserves an existing exact finite homotopy root. -/
theorem finiteERootDegreeLift_isRoot
    {A : ℝ[X]} {eta : ℝ} {z : ℂ}
    (hA : (finiteEPolynomial A eta).eval z = 0)
    (hz : z.im + eta ≠ 0) (r : ℝ) :
    (finiteEPolynomial (finiteERootDegreeLift A eta z r) eta).eval z = 0 := by
  rw [finiteERootDegreeLift]
  split_ifs
  · rw [finiteEPolynomial_eval_add, finiteEPolynomial_eval_C_mul,
      hA, finiteERootKernelCubic_isRoot eta hz]
    ring
  · exact hA

/-- A nonzero degree-lifting coefficient makes every output degree strictly
larger than two. -/
theorem finiteERootDegreeLift_natDegree_gt_two
    {A : ℝ[X]} (eta : ℝ) (z : ℂ) {r : ℝ} (hr : r ≠ 0) :
    2 < (finiteERootDegreeLift A eta z r).natDegree := by
  rw [finiteERootDegreeLift]
  split_ifs with hdeg
  · have hscaled :
        (C r * finiteERootKernelCubic eta z).natDegree = 3 := by
      rw [natDegree_C_mul hr, finiteERootKernelCubic_natDegree]
    rw [natDegree_add_eq_right_of_natDegree_lt]
    · omega
    · rw [hscaled]
      omega
  · omega

/-- Evaluation formula for the conditional degree lift. -/
@[simp] theorem finiteERootDegreeLift_map_eval
    (A : ℝ[X]) (eta : ℝ) (z : ℂ) (r : ℝ) (w : ℂ) :
    ((finiteERootDegreeLift A eta z r).map Complex.ofRealHom).eval w =
      (A.map Complex.ofRealHom).eval w +
        ((if A.natDegree ≤ 2 then r else 0 : ℝ) : ℂ) *
          ((finiteERootKernelCubic eta z).map Complex.ofRealHom).eval w := by
  rw [finiteERootDegreeLift]
  split_ifs <;> simp

/-- Degree lifting by coefficients tending to zero preserves a locally
uniform limit. -/
theorem finiteERootDegreeLift_tendstoLocallyUniformlyOn
    {ι : Type*} {φ : Filter ι} (A : ι → ℝ[X]) {f : ℂ → ℂ}
    (eta : ℝ) (z : ℂ) (r : ι → ℝ)
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w) f φ Set.univ)
    (hr : Tendsto r φ (nhds 0)) :
    TendstoLocallyUniformlyOn
      (fun n w ↦
        ((finiteERootDegreeLift (A n) eta z (r n)).map
          Complex.ofRealHom).eval w)
      f φ Set.univ := by
  let s : ι → ℝ := fun n ↦ if (A n).natDegree ≤ 2 then r n else 0
  have hs : Tendsto s φ (nhds 0) := by
    exact hr.if' tendsto_const_nhds
  have hsConst :=
    (hs.ofReal.tendstoUniformlyOn_const (Set.univ : Set ℂ)).tendstoLocallyUniformlyOn
  let q : ℂ → ℂ := fun w ↦
    ((finiteERootKernelCubic eta z).map Complex.ofRealHom).eval w
  have hq : TendstoLocallyUniformlyOn
      (fun _ : ι ↦ q) q φ (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_const_index q
  have hprod := hsConst.mul₀ hq continuousOn_const
    ((finiteERootKernelCubic eta z).map
      Complex.ofRealHom).continuous_aeval.continuousOn
  refine ((hA.add hprod).congr
    (G := fun n w ↦
      ((finiteERootDegreeLift (A n) eta z (r n)).map
        Complex.ofRealHom).eval w) ?_).congr_right ?_
  · intro n w _
    simp only [Pi.add_apply, Pi.mul_apply]
    simpa only [s, q] using
      (finiteERootDegreeLift_map_eval (A n) eta z (r n) w).symm
  · intro w _
    simp

/-- A polynomial of degree strictly above two has nonzero Wronskian with the
quadratic pinned kernel. -/
theorem wronskian_finiteERootKernelQuadratic_ne_zero
    {A : ℝ[X]} (hA : 2 < A.natDegree) (eta : ℝ) (z : ℂ) :
    Polynomial.wronskian A (finiteERootKernelQuadratic eta z) ≠ 0 := by
  intro hw
  rw [Polynomial.wronskian, sub_eq_zero] at hw
  have hlc := congrArg Polynomial.leadingCoeff hw
  simp only [leadingCoeff_mul, leadingCoeff_derivative,
    finiteERootKernelQuadratic_natDegree] at hlc
  rw [(finiteERootKernelQuadratic_monic eta z).leadingCoeff] at hlc
  norm_num at hlc
  have hA0 : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hA
    omega
  rcases hlc with hdegree | hzero
  · have : A.natDegree = 2 := by exact_mod_cast hdegree.symm
    omega
  · exact hA0 hzero

/-- The complex parameter forced by a common zero of a polynomial pencil
and its derivative. -/
def polynomialPencilBadParameter
    (A Q : ℝ[X]) (a : ℂ) : ℂ :=
  if aeval a Q = 0 then
    -aeval a A.derivative / aeval a Q.derivative
  else
    -aeval a A / aeval a Q

/-- A finite candidate set containing every parameter at which `A + t Q`
can fail to be separable, provided the Wronskian is nonzero. -/
def polynomialPencilBadParameterFinset
    (A Q : ℝ[X]) : Finset ℂ :=
  (((Polynomial.wronskian A Q).map Complex.ofRealHom).roots.toFinset).image
    (polynomialPencilBadParameter A Q)

/-- Every real parameter which makes a pencil nonseparable belongs to the
explicit finite bad-parameter set. -/
theorem mem_polynomialPencilBadParameterFinset_of_not_separable
    {A Q : ℝ[X]} (hQ : Q.Separable)
    (hW : Polynomial.wronskian A Q ≠ 0) {t : ℝ}
    (ht : ¬(A + C t * Q).Separable) :
    (t : ℂ) ∈ polynomialPencilBadParameterFinset A Q := by
  rw [separable_def] at ht
  have hcriterion :=
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
      (k := ℝ) ℂ (A + C t * Q) (A + C t * Q).derivative
  rw [hcriterion] at ht
  push Not at ht
  obtain ⟨a, hpa, hpda⟩ := ht
  have hpa' :
      aeval a A + (t : ℂ) * aeval a Q = 0 := by
    simpa using hpa
  have hpda' :
      aeval a A.derivative + (t : ℂ) * aeval a Q.derivative = 0 := by
    simpa [derivative_mul] using hpda
  have hWaReal : aeval a (Polynomial.wronskian A Q) = 0 := by
    simp only [Polynomial.wronskian, map_sub, map_mul]
    linear_combination (aeval a Q.derivative) * hpa' -
      (aeval a Q) * hpda'
  have hWa :
      ((Polynomial.wronskian A Q).map Complex.ofRealHom).eval a = 0 := by
    have hofRealHom : Complex.ofRealHom = algebraMap ℝ ℂ := by
      ext x
      rfl
    rw [eval_map, hofRealHom, ← aeval_def]
    exact hWaReal
  have hWmap :
      (Polynomial.wronskian A Q).map Complex.ofRealHom ≠ 0 :=
    Polynomial.map_ne_zero hW
  have haRoot :
      a ∈ ((Polynomial.wronskian A Q).map Complex.ofRealHom).roots :=
    (Polynomial.mem_roots hWmap).mpr hWa
  rw [polynomialPencilBadParameterFinset, Finset.mem_image]
  refine ⟨a, Multiset.mem_toFinset.mpr haRoot, ?_⟩
  rw [polynomialPencilBadParameter]
  by_cases hQa : aeval a Q = 0
  · rw [if_pos hQa]
    have hQda : aeval a Q.derivative ≠ 0 :=
      hQ.aeval_derivative_ne_zero hQa
    apply (div_eq_iff hQda).2
    linear_combination -hpda'
  · rw [if_neg hQa]
    apply (div_eq_iff hQa).2
    linear_combination -hpa'

/-- Avoiding the finite bad-parameter set guarantees that the pencil member
is separable. -/
theorem polynomialPencil_separable_of_parameter_not_mem
    {A Q : ℝ[X]} (hQ : Q.Separable)
    (hW : Polynomial.wronskian A Q ≠ 0) {t : ℝ}
    (ht : (t : ℂ) ∉ polynomialPencilBadParameterFinset A Q) :
    (A + C t * Q).Separable := by
  by_contra hsep
  exact ht (mem_polynomialPencilBadParameterFinset_of_not_separable
    hQ hW hsep)

/-- A pinned polynomial of degree above two has arbitrarily small nonzero
real perturbations in the quadratic kernel which are separable and retain
the exact homotopy root. -/
theorem exists_separable_finiteERootKernelQuadratic_perturbation
    {A : ℝ[X]} {eta : ℝ} (heta : 0 < eta) {z : ℂ} (hz : 0 < z.im)
    (hAdegree : 2 < A.natDegree)
    (hAroot : (finiteEPolynomial A eta).eval z = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧
      (A + C t * finiteERootKernelQuadratic eta z).Separable ∧
      (finiteEPolynomial
        (A + C t * finiteERootKernelQuadratic eta z) eta).eval z = 0 := by
  let Q := finiteERootKernelQuadratic eta z
  let bad : Set ℝ :=
    (fun t : ℝ ↦ (t : ℂ)) ⁻¹'
      (polynomialPencilBadParameterFinset A Q : Set ℂ)
  have hbad : bad.Finite := by
    apply Set.Finite.preimage
      (f := fun t : ℝ ↦ (t : ℂ)) Complex.ofReal_injective.injOn
    exact (polynomialPencilBadParameterFinset A Q).finite_toSet
  obtain ⟨t, ht, htbad⟩ :=
    (Set.Ioo_infinite hε).exists_notMem_finite hbad
  have htfinset :
      (t : ℂ) ∉ polynomialPencilBadParameterFinset A Q := by
    exact htbad
  have hQsep : Q.Separable :=
    finiteERootKernelQuadratic_separable heta hz
  have hW : Polynomial.wronskian A Q ≠ 0 :=
    wronskian_finiteERootKernelQuadratic_ne_zero hAdegree eta z
  refine ⟨t, ht.1, ht.2,
    polynomialPencil_separable_of_parameter_not_mem hQsep hW htfinset, ?_⟩
  rw [finiteEPolynomial_eval_add, finiteEPolynomial_eval_C_mul,
    hAroot, finiteERootKernelQuadratic_isRoot]
  ring

/-- Adding a fixed polynomial with a scalar coefficient tending to zero
preserves locally uniform convergence. -/
theorem add_C_mul_fixedPolynomial_tendstoLocallyUniformlyOn
    {ι : Type*} {φ : Filter ι} (A : ι → ℝ[X]) {f : ℂ → ℂ}
    (Q : ℝ[X]) (t : ι → ℝ)
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w) f φ Set.univ)
    (ht : Tendsto t φ (nhds 0)) :
    TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n + C (t n) * Q).map Complex.ofRealHom).eval w)
      f φ Set.univ := by
  have htConst :=
    (ht.ofReal.tendstoUniformlyOn_const (Set.univ : Set ℂ)).tendstoLocallyUniformlyOn
  let q : ℂ → ℂ := fun w ↦ (Q.map Complex.ofRealHom).eval w
  have hq : TendstoLocallyUniformlyOn
      (fun _ : ι ↦ q) q φ (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_const_index q
  have hprod := htConst.mul₀ hq continuousOn_const
    (Q.map Complex.ofRealHom).continuous_aeval.continuousOn
  refine ((hA.add hprod).congr
    (G := fun n w ↦
      ((A n + C (t n) * Q).map Complex.ofRealHom).eval w) ?_).congr_right ?_
  · intro n w _
    simp only [Pi.add_apply, Pi.mul_apply]
    simp [q]
  · intro w _
    simp

/-- Complete constrained separability bridge. A locally uniform sequence of
real polynomials whose finite homotopies all contain the same upper root can
be replaced by a locally uniform sequence of separable real polynomials with
that same exact root in every finite homotopy. -/
theorem exists_separable_finiteERoot_polynomial_sequence
    (A : ℕ → ℝ[X]) {f : ℂ → ℂ} {eta : ℝ} (heta : 0 < eta)
    {z : ℂ} (hz : 0 < z.im)
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      f atTop Set.univ)
    (hroot : ∀ n, (finiteEPolynomial (A n) eta).eval z = 0) :
    ∃ B : ℕ → ℝ[X],
      TendstoLocallyUniformlyOn
        (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
        f atTop Set.univ ∧
      ∀ n, (B n).Separable ∧
        (finiteEPolynomial (B n) eta).eval z = 0 := by
  have hzeta : z.im + eta ≠ 0 := by linarith
  let r : ℕ → ℝ := fun n ↦ 1 / ((n + 1 : ℕ) : ℝ)
  let D : ℕ → ℝ[X] := fun n ↦
    finiteERootDegreeLift (A n) eta z (r n)
  have hr : Tendsto r atTop (nhds 0) := by
    simpa only [r, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have hrpos (n : ℕ) : 0 < r n := by
    dsimp only [r]
    positivity
  have hDlimit : TendstoLocallyUniformlyOn
      (fun n w ↦ ((D n).map Complex.ofRealHom).eval w)
      f atTop Set.univ := by
    exact finiteERootDegreeLift_tendstoLocallyUniformlyOn
      A eta z r hA hr
  have hDdegree (n : ℕ) : 2 < (D n).natDegree := by
    exact finiteERootDegreeLift_natDegree_gt_two eta z (ne_of_gt (hrpos n))
  have hDroot (n : ℕ) : (finiteEPolynomial (D n) eta).eval z = 0 := by
    exact finiteERootDegreeLift_isRoot (hroot n) hzeta (r n)
  have hexists (n : ℕ) :
      ∃ t : ℝ, 0 < t ∧ t < r n ∧
        (D n + C t * finiteERootKernelQuadratic eta z).Separable ∧
        (finiteEPolynomial
          (D n + C t * finiteERootKernelQuadratic eta z) eta).eval z = 0 :=
    exists_separable_finiteERootKernelQuadratic_perturbation
      heta hz (hDdegree n) (hDroot n) (hrpos n)
  choose t htpos htbound htsep htroot using hexists
  let B : ℕ → ℝ[X] := fun n ↦
    D n + C (t n) * finiteERootKernelQuadratic eta z
  have ht : Tendsto t atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun n ↦ (htpos n).le
    · exact fun n ↦ (htbound n).le
    · exact hr
  refine ⟨B, ?_, ?_⟩
  · exact add_C_mul_fixedPolynomial_tendstoLocallyUniformlyOn
      D (finiteERootKernelQuadratic eta z) t hDlimit ht
  · intro n
    exact ⟨htsep n, htroot n⟩

/-- Spectral-xi specialization: every upper root of the limiting positive
homotopy is retained exactly by a locally uniform sequence of separable real
polynomials. -/
theorem exists_separable_riemannXiSpectral_finiteERoot_polynomial_sequence
    {eta : ℝ} (heta : 0 < eta) {z : ℂ} (hz : 0 < z.im)
    (hroot : analyticEValue riemannXiSpectral eta z = 0) :
    ∃ B : ℕ → ℝ[X],
      TendstoLocallyUniformlyOn
        (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
        riemannXiSpectral atTop Set.univ ∧
      ∀ n, (B n).Separable ∧
        (finiteEPolynomial (B n) eta).eval z = 0 := by
  let A : ℕ → ℝ[X] := fun n ↦
    finiteERootPinnedPolynomial
      (riemannXiSpectralRealTaylorPolynomial n) eta z
  have hzeta : z.im + eta ≠ 0 := by linarith
  have hspec :=
    riemannXiSpectralRealTaylorPinnedPolynomial_spec eta hroot hzeta
  exact exists_separable_finiteERoot_polynomial_sequence
    A heta hz hspec.1 hspec.2

end

end RiemannGaussian
