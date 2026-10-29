import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.LiftRing

namespace OAI.Algorithms

/-!
# Exact table interpolation over a commutative ring

The usual Lagrange construction works whenever the differences of distinct
nodes are units. In particular it does not require a field, and preserves
table values in the whole coefficient ring, not only in a residue field.
-/

noncomputable section

open scoped BigOperators

namespace SubexponentialSAT.TableInterpolation

variable {R : Type*} [CommRing R]
variable {ι : Type*}

/-- The exact denominator hypothesis for Lagrange interpolation. -/
def UnitDifferences (v : ι → R) : Prop :=
  ∀ i j, i ≠ j → IsUnit (v i - v j)

/-- Ring homomorphisms preserve the denominator hypothesis. -/
theorem UnitDifferences.map {S : Type*} [CommRing S]
    {v : ι → R} (hu : UnitDifferences v) (φ : R →+* S) :
    UnitDifferences (fun i => φ (v i)) := by
  intro i j hij
  simpa only [map_sub] using (hu i j hij).map φ

variable [DecidableEq ι]

/-- The inverse of a node difference; its value on the diagonal is unused. -/
def invDiff (v : ι → R) (hu : UnitDifferences v) (i j : ι) : R :=
  if hij : i ≠ j then ↑((hu i j hij).unit⁻¹) else 0

theorem invDiff_mul (v : ι → R) (hu : UnitDifferences v)
    {i j : ι} (hij : i ≠ j) :
    invDiff v hu i j * (v i - v j) = 1 := by
  simp only [invDiff, dite_eq_left hij]
  exact (hu i j hij).val_inv_mul

/-- Ring-valued version of the mathlib Lagrange basis divisor. -/
def basisDivisor (v : ι → R) (hu : UnitDifferences v) (i j : ι) : Polynomial R :=
  Polynomial.C (invDiff v hu i j) *
    (Polynomial.X - Polynomial.C (v j))

@[simp]
theorem eval_basisDivisor_right (v : ι → R) (hu : UnitDifferences v) (i j : ι) :
    (basisDivisor v hu i j).eval (v j) = 0 := by
  simp [basisDivisor]

theorem eval_basisDivisor_left (v : ι → R) (hu : UnitDifferences v)
    {i j : ι} (hij : i ≠ j) :
    (basisDivisor v hu i j).eval (v i) = 1 := by
  simpa [basisDivisor] using invDiff_mul v hu hij

theorem natDegree_basisDivisor_le (v : ι → R) (hu : UnitDifferences v) (i j : ι) :
    (basisDivisor v hu i j).natDegree ≤ 1 := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (by simpa using (Polynomial.natDegree_X_le (R := R)))

variable [Fintype ι]

/-- Lagrange basis for the finite node family. -/
def basis (v : ι → R) (hu : UnitDifferences v) (i : ι) : Polynomial R :=
  ∏ j ∈ Finset.univ.erase i, basisDivisor v hu i j

@[simp]
theorem eval_basis_self (v : ι → R) (hu : UnitDifferences v) (i : ι) :
    (basis v hu i).eval (v i) = 1 := by
  rw [basis, Polynomial.eval_prod]
  apply Finset.prod_eq_one
  intro j hj
  exact eval_basisDivisor_left v hu (Finset.ne_of_mem_erase hj).symm

theorem eval_basis_of_ne (v : ι → R) (hu : UnitDifferences v)
    {i j : ι} (hij : i ≠ j) :
    (basis v hu i).eval (v j) = 0 := by
  rw [basis, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (by simp [hij.symm]) (eval_basisDivisor_right v hu i j)

theorem eval_basis (v : ι → R) (hu : UnitDifferences v) (i j : ι) :
    (basis v hu i).eval (v j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, eval_basis_of_ne v hu hij]

theorem natDegree_basis_le (v : ι → R) (hu : UnitDifferences v) (i : ι) :
    (basis v hu i).natDegree ≤ Fintype.card ι - 1 := by
  calc
    (basis v hu i).natDegree ≤
        ∑ j ∈ Finset.univ.erase i, (basisDivisor v hu i j).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 :=
      Finset.sum_le_sum fun j _hj => natDegree_basisDivisor_le v hu i j
    _ = Fintype.card ι - 1 := by simp

/-- The exact interpolant of a finite table in the coefficient ring. -/
def interpolate (v : ι → R) (hu : UnitDifferences v) (r : ι → R) : Polynomial R :=
  ∑ i, Polynomial.C (r i) * basis v hu i

@[simp]
theorem eval_interpolate (v : ι → R) (hu : UnitDifferences v) (r : ι → R) (j : ι) :
    (interpolate v hu r).eval (v j) = r j := by
  simp [interpolate, Polynomial.eval_finsetSum, eval_basis]

theorem natDegree_interpolate_le (v : ι → R) (hu : UnitDifferences v) (r : ι → R) :
    (interpolate v hu r).natDegree ≤ Fintype.card ι - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _hi
  exact (Polynomial.natDegree_C_mul_le _ _).trans (natDegree_basis_le v hu i)

theorem exists_interpolant (v : ι → R) (hu : UnitDifferences v) (r : ι → R) :
    ∃ f : Polynomial R, f.natDegree ≤ Fintype.card ι - 1 ∧
      ∀ j, f.eval (v j) = r j :=
  ⟨interpolate v hu r, natDegree_interpolate_le v hu r, eval_interpolate v hu r⟩

variable {σ : Type*}

/-- A Lagrange basis polynomial in one selected multivariate coordinate. -/
def mvBasis (v : ι → R) (hu : UnitDifferences v) (s : σ) (i : ι) :
    MvPolynomial σ R :=
  ∏ j ∈ Finset.univ.erase i,
    MvPolynomial.C (invDiff v hu i j) *
      (MvPolynomial.X s - MvPolynomial.C (v j))

theorem eval_mvBasis (v : ι → R) (hu : UnitDifferences v)
    (s : σ) (i : ι) (x : σ → R) :
    MvPolynomial.eval x (mvBasis v hu s i) = (basis v hu i).eval (x s) := by
  simp [mvBasis, basis, basisDivisor, Polynomial.eval_prod]

variable [DecidableEq σ]

theorem degreeOf_X_le (t s : σ) :
    (MvPolynomial.X s : MvPolynomial σ R).degreeOf t ≤ if t = s then 1 else 0 := by
  classical
  calc
    (MvPolynomial.X s : MvPolynomial σ R).degreeOf t =
        (MvPolynomial.X s : MvPolynomial σ R).degrees.count t := by
      rw [MvPolynomial.degreeOf_def]
    _ ≤ ({s} : Multiset σ).count t :=
      Multiset.count_le_of_le t (MvPolynomial.degrees_X' s)
    _ = if t = s then 1 else 0 := Multiset.count_singleton t s

theorem degreeOf_mvBasis_le (v : ι → R) (hu : UnitDifferences v)
    (s t : σ) (i : ι) :
    (mvBasis v hu s i).degreeOf t ≤ if t = s then Fintype.card ι - 1 else 0 := by
  unfold mvBasis
  calc
    (∏ j ∈ Finset.univ.erase i,
        MvPolynomial.C (invDiff v hu i j) *
          (MvPolynomial.X s - MvPolynomial.C (v j))).degreeOf t
        ≤ ∑ j ∈ Finset.univ.erase i,
          (MvPolynomial.C (invDiff v hu i j) *
            (MvPolynomial.X s - MvPolynomial.C (v j))).degreeOf t :=
      MvPolynomial.degreeOf_prod_le _ _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase i, if t = s then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _hj
      refine (MvPolynomial.degreeOf_C_mul_le _ _ _).trans ?_
      refine (MvPolynomial.degreeOf_sub_le _ _ _).trans ?_
      simp only [MvPolynomial.degreeOf_C, Nat.max_zero]
      exact degreeOf_X_le t s
    _ = if t = s then Fintype.card ι - 1 else 0 := by
      by_cases h : t = s <;> simp [h]

variable [Fintype σ]

/-- The tensor product basis attached to a grid point. -/
def gridBasis (v : ι → R) (hu : UnitDifferences v) (a : σ → ι) :
    MvPolynomial σ R :=
  ∏ s, mvBasis v hu s (a s)

omit [DecidableEq σ] in
theorem eval_gridBasis (v : ι → R) (hu : UnitDifferences v) (a b : σ → ι) :
    MvPolynomial.eval (fun s => v (b s)) (gridBasis v hu a) =
      if a = b then 1 else 0 := by
  classical
  unfold gridBasis
  rw [MvPolynomial.eval_prod]
  by_cases hab : a = b
  · subst b
    simp [eval_mvBasis]
  · rw [ite_eq_right hab]
    have h : ∃ s, a s ≠ b s := Function.ne_iff.mp hab
    obtain ⟨s, hs⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp [eval_mvBasis, eval_basis, hs]

theorem degreeOf_gridBasis_le (v : ι → R) (hu : UnitDifferences v)
    (a : σ → ι) (t : σ) :
    (gridBasis v hu a).degreeOf t ≤ Fintype.card ι - 1 := by
  unfold gridBasis
  calc
    (∏ s, mvBasis v hu s (a s)).degreeOf t
        ≤ ∑ s, (mvBasis v hu s (a s)).degreeOf t :=
      MvPolynomial.degreeOf_prod_le _ _ _
    _ ≤ ∑ s : σ, if t = s then Fintype.card ι - 1 else 0 :=
      Finset.sum_le_sum fun s _hs => degreeOf_mvBasis_le v hu s t (a s)
    _ = Fintype.card ι - 1 := by simp

/-- Tensor-product interpolation of a finite grid table. -/
def mvInterpolate (v : ι → R) (hu : UnitDifferences v) (f : (σ → ι) → R) :
    MvPolynomial σ R :=
  ∑ a, MvPolynomial.C (f a) * gridBasis v hu a

@[simp]
theorem eval_mvInterpolate (v : ι → R) (hu : UnitDifferences v)
    (f : (σ → ι) → R) (a : σ → ι) :
    MvPolynomial.eval (fun s => v (a s)) (mvInterpolate v hu f) = f a := by
  classical
  simp [mvInterpolate, eval_gridBasis]

theorem degreeOf_mvInterpolate_le (v : ι → R) (hu : UnitDifferences v)
    (f : (σ → ι) → R) (s : σ) :
    (mvInterpolate v hu f).degreeOf s ≤ Fintype.card ι - 1 := by
  unfold mvInterpolate
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans ?_
  apply Finset.sup_le
  intro a _ha
  exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
    (degreeOf_gridBasis_le v hu a s)

theorem exists_mvInterpolant (v : ι → R) (hu : UnitDifferences v)
    (f : (σ → ι) → R) :
    ∃ F : MvPolynomial σ R,
      (∀ s, F.degreeOf s ≤ Fintype.card ι - 1) ∧
      ∀ a, MvPolynomial.eval (fun s => v (a s)) F = f a :=
  ⟨mvInterpolate v hu f, degreeOf_mvInterpolate_le v hu f, eval_mvInterpolate v hu f⟩

/-- Specialization to literal integer representatives; agreement is in R itself. -/
theorem exists_integerLabelInterpolant (p : ℕ)
    (hu : UnitDifferences (fun i : Fin p => (i.val : R)))
    (f : (σ → Fin p) → R) :
    ∃ F : MvPolynomial σ R,
      (∀ s, F.degreeOf s ≤ p - 1) ∧
      ∀ a, MvPolynomial.eval (fun s => ((a s).val : R)) F = f a := by
  simpa using exists_mvInterpolant (fun i : Fin p => (i.val : R)) hu f

/-- Positive integers below p remain units modulo every power of the prime p. -/
theorem isUnit_natCast_primePower {p a : ℕ} (μ : ℕ) (hp : p.Prime)
    (ha0 : 0 < a) (ha : a < p) :
    IsUnit (a : ZMod (p ^ μ)) := by
  apply (ZMod.isUnit_iff_coprime a (p ^ μ)).2
  exact hp.coprime_pow_of_not_dvd (Nat.not_dvd_of_pos_of_lt ha0 ha)

/-- Distinct integer representatives have unit differences modulo a prime power. -/
theorem unitDifferences_zmod_integerLabels (p μ : ℕ) (hp : p.Prime) :
    UnitDifferences (fun i : Fin p => (i.val : ZMod (p ^ μ))) := by
  have step : ∀ a b : Fin p, b.val < a.val →
      IsUnit ((a.val : ZMod (p ^ μ)) - (b.val : ZMod (p ^ μ))) := by
    intro a b hab
    rw [← Nat.cast_sub hab.le]
    exact isUnit_natCast_primePower μ hp (Nat.sub_pos_of_lt hab)
      ((Nat.sub_le a.val b.val).trans_lt a.isLt)
  intro i j hij
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h | h
  · exact IsUnit.sub_iff.mpr (step j i h)
  · exact step i j h

/-- The specified integer labels have unit differences in the lifted ring Lambda. -/
theorem unitDifferences_lambda_integerLabels (p μ : ℕ) (hp : p.Prime)
    (F : Polynomial (SubexponentialSAT.LiftRing.Base p μ)) :
    UnitDifferences
      (fun i : Fin p => (i.val : SubexponentialSAT.LiftRing.Lambda p μ F)) := by
  have h := (unitDifferences_zmod_integerLabels p μ hp).map (SubexponentialSAT.LiftRing.of F)
  simpa only [map_natCast] using h

/-- Every table has an exact polynomial representation over the actual lifted ring. -/
theorem exists_lambda_tableInterpolant (p μ : ℕ) (hp : p.Prime)
    (F : Polynomial (SubexponentialSAT.LiftRing.Base p μ))
    (f : (σ → Fin p) → SubexponentialSAT.LiftRing.Lambda p μ F) :
    ∃ P : MvPolynomial σ (SubexponentialSAT.LiftRing.Lambda p μ F),
      (∀ s, P.degreeOf s ≤ p - 1) ∧
      ∀ a, MvPolynomial.eval (fun s =>
        ((a s).val : SubexponentialSAT.LiftRing.Lambda p μ F)) P = f a :=
  exists_integerLabelInterpolant p (unitDifferences_lambda_integerLabels p μ hp F) f

end SubexponentialSAT.TableInterpolation

end

end OAI.Algorithms
