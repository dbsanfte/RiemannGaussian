import RiemannGaussian.FiniteHardyCauchyBasis
import Mathlib.Algebra.Polynomial.PartialFractions

/-!
# Confluent Cauchy coordinates for repeated finite roots

For a monic complex polynomial `P`, this file indexes every distinct root
`a` by `Fin (P.rootMultiplicity a)`.  The index `j` represents the rational
kernel with pole order `P.rootMultiplicity a - j`, whose numerator is the
exact monic quotient of `P` by that power of `X - a`.

Lean proves that these multiplicity-indexed quotient coordinates are linearly
independent by the uniqueness theorem for polynomial partial fractions.  Their
index type has cardinality `natDegree P`, so they form a basis of the complete
algebraic model space.  This is the algebraic input for the repeated-root
Hardy construction; realizing the higher-order kernels in boundary `L²` is a
separate analytic step.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

/-- A distinct root together with one index for each occurrence counted by
its root multiplicity. -/
abbrev finiteConfluentRootIndex (P : ℂ[X]) :=
  Σ a : ↑P.roots.toFinset, Fin (P.rootMultiplicity (a : ℂ))

/-- Pole order attached to a confluent root index.  As the local index runs
from `0` to `m - 1`, this runs from `m` down to `1`. -/
def finiteConfluentPoleOrder {P : ℂ[X]}
    (i : finiteConfluentRootIndex P) : ℕ :=
  P.rootMultiplicity (i.1 : ℂ) - i.2.1

theorem finiteConfluentPoleOrder_pos {P : ℂ[X]}
    (i : finiteConfluentRootIndex P) :
    0 < finiteConfluentPoleOrder i := by
  exact Nat.sub_pos_of_lt i.2.2

/-- The numerator coordinate whose rational value is the higher-order kernel
`(z - a)⁻ʳ`, with `r = finiteConfluentPoleOrder i`. -/
def finiteModelConfluentCauchyCoordinate
    (P : ℂ[X]) (hP : P ≠ 0) (i : finiteConfluentRootIndex P) :
    finiteModelSpace P :=
  ⟨P /ₘ (X - C (i.1 : ℂ)) ^ finiteConfluentPoleOrder i, by
    change P /ₘ (X - C (i.1 : ℂ)) ^ finiteConfluentPoleOrder i ∈
      Polynomial.degreeLT ℂ P.natDegree
    rw [Polynomial.mem_degreeLT, ← degree_eq_natDegree hP]
    apply degree_divByMonic_lt _ _ hP
    rw [degree_pow, degree_X_sub_C]
    simpa using finiteConfluentPoleOrder_pos i⟩

/-- Counting every distinct root by its root multiplicity recovers the full
degree over `ℂ`, including when roots repeat. -/
theorem finiteConfluentRootIndex_card (P : ℂ[X]) :
    Fintype.card (finiteConfluentRootIndex P) = P.natDegree := by
  change Fintype.card
      (Σ a : ↑P.roots.toFinset, Fin (P.rootMultiplicity (a : ℂ))) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← IsAlgClosed.card_roots_eq_natDegree (p := P)]
  simp_rw [← count_roots]
  rw [Finset.univ_eq_attach]
  exact (Finset.sum_attach P.roots.toFinset
    (fun a ↦ P.roots.count a)).trans
      (Multiset.toFinset_sum_count_eq P.roots)

/-- A monic complex polynomial is the product of its distinct linear root
factors raised to their exact root multiplicities. -/
theorem monic_eq_prod_rootMultiplicity
    {P : ℂ[X]} (hP : P.Monic) :
    P = ∏ a ∈ P.roots.toFinset,
      (X - C a) ^ P.rootMultiplicity a := by
  calc
    P = (P.roots.map fun a ↦ X - C a).prod :=
      (IsAlgClosed.splits P).eq_prod_roots_of_monic hP
    _ = ∏ a ∈ P.roots.toFinset,
        (X - C a) ^ P.rootMultiplicity a :=
      prod_multiset_root_eq_finset_root

/-- Subtype-indexed form of the exact multiplicity factorization. -/
theorem monic_eq_fintype_prod_rootMultiplicity
    {P : ℂ[X]} (hP : P.Monic) :
    P = ∏ a : ↑P.roots.toFinset,
      (X - C (a : ℂ)) ^ P.rootMultiplicity (a : ℂ) := by
  calc
    P = ∏ a ∈ P.roots.toFinset,
        (X - C a) ^ P.rootMultiplicity a :=
      monic_eq_prod_rootMultiplicity hP
    _ = ∏ a ∈ P.roots.toFinset.attach,
        (X - C (a : ℂ)) ^ P.rootMultiplicity (a : ℂ) :=
      (Finset.prod_attach P.roots.toFinset _).symm
    _ = ∏ a : ↑P.roots.toFinset,
        (X - C (a : ℂ)) ^ P.rootMultiplicity (a : ℂ) := by
      rw [Finset.attach_eq_univ]

/-- The monic quotient is exactly the term appearing in the formal
partial-fraction decomposition: the local factor to power `j`, times every
other root factor with full multiplicity. -/
theorem finiteModelConfluentCauchyCoordinate_eq_fintype_prod_erase
    {P : ℂ[X]} (hP : P.Monic) (i : finiteConfluentRootIndex P) :
    ((finiteModelConfluentCauchyCoordinate P hP.ne_zero i :
      finiteModelSpace P) : ℂ[X]) =
      (X - C (i.1 : ℂ)) ^ i.2.1 *
        ∏ a ∈ (Finset.univ.erase i.1),
          (X - C (a : ℂ)) ^ P.rootMultiplicity (a : ℂ) := by
  let g := X - C (i.1 : ℂ)
  let Q := ∏ a ∈ (Finset.univ.erase i.1),
    (X - C (a : ℂ)) ^ P.rootMultiplicity (a : ℂ)
  have hfactor : P = g ^ P.rootMultiplicity (i.1 : ℂ) * Q := by
    calc
      P = ∏ a : ↑P.roots.toFinset,
          (X - C (a : ℂ)) ^ P.rootMultiplicity (a : ℂ) :=
        monic_eq_fintype_prod_rootMultiplicity hP
      _ = g ^ P.rootMultiplicity (i.1 : ℂ) * Q :=
        (Finset.mul_prod_erase Finset.univ
          (fun a : ↑P.roots.toFinset ↦
            (X - C (a : ℂ)) ^ P.rootMultiplicity (a : ℂ))
          (Finset.mem_univ i.1)).symm
  have hsplit :
      finiteConfluentPoleOrder i + i.2.1 =
        P.rootMultiplicity (i.1 : ℂ) :=
    Nat.sub_add_cancel (Nat.le_of_lt i.2.2)
  change P /ₘ g ^ finiteConfluentPoleOrder i = g ^ i.2.1 * Q
  calc
    P /ₘ g ^ finiteConfluentPoleOrder i =
        (g ^ P.rootMultiplicity (i.1 : ℂ) * Q) /ₘ
          g ^ finiteConfluentPoleOrder i :=
      congrArg (fun R ↦ R /ₘ g ^ finiteConfluentPoleOrder i) hfactor
    _ = (g ^ (finiteConfluentPoleOrder i + i.2.1) * Q) /ₘ
        g ^ finiteConfluentPoleOrder i := by rw [hsplit]
    _ = (g ^ finiteConfluentPoleOrder i * (g ^ i.2.1 * Q)) /ₘ
        g ^ finiteConfluentPoleOrder i := by rw [pow_add, mul_assoc]
    _ = g ^ i.2.1 * Q := mul_divByMonic_cancel_left _
      ((monic_X_sub_C (i.1 : ℂ)).pow (finiteConfluentPoleOrder i))

/-- The full multiplicity-indexed quotient family is linearly independent.
This invokes the checked uniqueness theorem for partial fractions with
pairwise-coprime linear denominators. -/
theorem finiteModelConfluentCauchyCoordinate_linearIndependent
    {P : ℂ[X]} (hP : P.Monic) :
    LinearIndependent ℂ
      (fun i : finiteConfluentRootIndex P ↦
        finiteModelConfluentCauchyCoordinate P hP.ne_zero i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum i
  have hsumPolynomial :
      ∑ i, c i •
        (((finiteModelConfluentCauchyCoordinate P hP.ne_zero i :
          finiteModelSpace P) : ℂ[X])) = 0 := by
    simpa only [map_sum, map_smul, map_zero,
      Submodule.subtype_apply] using
      congrArg (finiteModelSpace P).subtype hsum
  rw [Fintype.sum_sigma] at hsumPolynomial
  simp only [smul_eq_C_mul] at hsumPolynomial
  simp_rw [finiteModelConfluentCauchyCoordinate_eq_fintype_prod_erase hP]
    at hsumPolynomial
  let I := ↑P.roots.toFinset
  let g : I → ℂ[X] := fun a ↦ X - C (a : ℂ)
  let n : I → ℕ := fun a ↦ P.rootMultiplicity (a : ℂ)
  let r₁ : (a : I) → Fin (n a) → ℂ[X] :=
    fun a j ↦ C (c ⟨a, j⟩)
  let r₂ : (a : I) → Fin (n a) → ℂ[X] := fun _ _ ↦ 0
  have hg : ∀ a ∈ (Finset.univ : Finset I), (g a).Monic := by
    intro a _
    exact monic_X_sub_C (a : ℂ)
  have hgg : Set.Pairwise (↑(Finset.univ : Finset I))
      fun a b ↦ IsCoprime (g a) (g b) := by
    intro a _ b _ hab
    exact pairwise_coprime_X_sub_C
      (s := fun a : I ↦ (a : ℂ)) Subtype.val_injective hab
  have hr₁ : ∀ a ∈ (Finset.univ : Finset I), ∀ j,
      (r₁ a j).degree < (g a).degree := by
    intro a _ j
    rw [show (g a).degree = 1 by simp [g, degree_X_sub_C]]
    exact (degree_C_le).trans_lt (by norm_num)
  have hr₂ : ∀ a ∈ (Finset.univ : Finset I), ∀ j,
      (r₂ a j).degree < (g a).degree := by
    intro a _ j
    simp [r₂, g, degree_X_sub_C]
  have hrepresentation :
      (0 : ℂ[X]) * ∏ a ∈ (Finset.univ : Finset I), (g a) ^ n a +
          ∑ a ∈ (Finset.univ : Finset I), ∑ j,
            r₁ a j * (g a) ^ j.1 *
              ∏ b ∈ (Finset.univ.erase a), (g b) ^ n b =
        (0 : ℂ[X]) * ∏ a ∈ (Finset.univ : Finset I), (g a) ^ n a +
          ∑ a ∈ (Finset.univ : Finset I), ∑ j,
            r₂ a j * (g a) ^ j.1 *
              ∏ b ∈ (Finset.univ.erase a), (g b) ^ n b := by
    simpa [I, g, n, r₁, r₂, mul_assoc] using hsumPolynomial
  have hunique := quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique
    hg hgg hr₁ hr₂ hrepresentation
  have hcoefficient := congrFun
    (hunique.2 i.1 (Finset.mem_univ i.1)) i.2
  simpa [I, n, r₁, r₂] using
    congrArg (Polynomial.eval 0) hcoefficient

/-- Multiplying a confluent coordinate by its exact pole denominator
reconstructs the monic polynomial. -/
theorem pow_mul_finiteModelConfluentCauchyCoordinate
    {P : ℂ[X]} (hP : P.Monic) (i : finiteConfluentRootIndex P) :
    (X - C (i.1 : ℂ)) ^ finiteConfluentPoleOrder i *
        (((finiteModelConfluentCauchyCoordinate P hP.ne_zero i :
          finiteModelSpace P) : ℂ[X])) = P := by
  let g := X - C (i.1 : ℂ)
  let Q := ∏ a ∈ (Finset.univ.erase i.1),
    (X - C (a : ℂ)) ^ P.rootMultiplicity (a : ℂ)
  have hfactor : P = g ^ P.rootMultiplicity (i.1 : ℂ) * Q := by
    calc
      P = ∏ a : ↑P.roots.toFinset,
          (X - C (a : ℂ)) ^ P.rootMultiplicity (a : ℂ) :=
        monic_eq_fintype_prod_rootMultiplicity hP
      _ = g ^ P.rootMultiplicity (i.1 : ℂ) * Q :=
        (Finset.mul_prod_erase Finset.univ
          (fun a : ↑P.roots.toFinset ↦
            (X - C (a : ℂ)) ^ P.rootMultiplicity (a : ℂ))
          (Finset.mem_univ i.1)).symm
  have hsplit :
      finiteConfluentPoleOrder i + i.2.1 =
        P.rootMultiplicity (i.1 : ℂ) :=
    Nat.sub_add_cancel (Nat.le_of_lt i.2.2)
  rw [finiteModelConfluentCauchyCoordinate_eq_fintype_prod_erase hP]
  change g ^ finiteConfluentPoleOrder i * (g ^ i.2.1 * Q) = P
  rw [← mul_assoc, ← pow_add, hsplit, ← hfactor]

/-- Away from the denominator zeros, a confluent coordinate evaluates to the
literal inverse power kernel. -/
theorem finiteModelValue_confluentCauchyCoordinate
    {P : ℂ[X]} (hP : P.Monic) (i : finiteConfluentRootIndex P)
    {z : ℂ} (hz : P.eval z ≠ 0) :
    finiteModelValue P
        (finiteModelConfluentCauchyCoordinate P hP.ne_zero i) z =
      ((z - (i.1 : ℂ)) ^ finiteConfluentPoleOrder i)⁻¹ := by
  have hrec := congrArg (Polynomial.eval z)
    (pow_mul_finiteModelConfluentCauchyCoordinate hP i)
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hrec
  unfold finiteModelValue
  have hden : (z - (i.1 : ℂ)) ^ finiteConfluentPoleOrder i ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hrec
    exact hz hrec.symm
  apply (div_eq_iff hz).2
  rw [← hrec, ← mul_assoc, inv_mul_cancel₀ hden, one_mul]

/-- The multiplicity-aware confluent quotient basis of the algebraic finite
model. -/
noncomputable def finiteModelConfluentCauchyBasis
    (P : ℂ[X]) (hP : P.Monic) :
    Module.Basis (finiteConfluentRootIndex P) ℂ (finiteModelSpace P) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun i ↦ finiteModelConfluentCauchyCoordinate P hP.ne_zero i)
    (finiteModelConfluentCauchyCoordinate_linearIndependent hP)
    (by rw [finiteConfluentRootIndex_card, finiteModelSpace_finrank])

@[simp] theorem finiteModelConfluentCauchyBasis_apply
    (P : ℂ[X]) (hP : P.Monic) (i : finiteConfluentRootIndex P) :
    finiteModelConfluentCauchyBasis P hP i =
      finiteModelConfluentCauchyCoordinate P hP.ne_zero i := by
  exact congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank'
      (fun i ↦ finiteModelConfluentCauchyCoordinate P hP.ne_zero i)
      (finiteModelConfluentCauchyCoordinate_linearIndependent hP)
      (by rw [finiteConfluentRootIndex_card, finiteModelSpace_finrank])) i

/-- Coefficientwise conjugation preserves monicity. -/
theorem conjugatePolynomial_monic_of_monic
    {P : ℂ[X]} (hP : P.Monic) :
    (conjugatePolynomial P).Monic := by
  exact hP.map (starRingEnd ℂ)

/-- The multiplicity-aware algebraic basis for the actual finite negative
model denominator.  This exists without a separability hypothesis. -/
noncomputable def finiteNegativeConfluentModelBasis
    (A : ℝ[X]) (tau : ℝ) :
    Module.Basis
      (finiteConfluentRootIndex
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)))) ℂ
      (finiteNegativeModelSpace A tau) :=
  finiteModelConfluentCauchyBasis _
    (conjugatePolynomial_monic_of_monic
      (upperRootFactor_monic (finiteEPolynomial A tau)))

end

end RiemannGaussian
