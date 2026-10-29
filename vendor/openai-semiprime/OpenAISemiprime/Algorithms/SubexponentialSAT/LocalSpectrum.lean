import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# The four-state involution in the interpolation layout

This file constructs the operator rather than assuming a spectral decomposition.
The only characteristic hypothesis on the field is that `2 ≠ 0`.
-/

namespace SubexponentialSAT.LocalSpectrum

abbrev PairState := Bool × Bool

/-- The local permutation swaps `00` and `11`, fixing `01` and `10`. -/
def swapPair (x : PairState) : PairState := (!x.2, !x.1)

@[simp] theorem swapPair_involutive (x : PairState) :
    swapPair (swapPair x) = x := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> rfl

def localPairPerm : Equiv.Perm PairState where
  toFun := swapPair
  invFun := swapPair
  left_inv := swapPair_involutive
  right_inv := swapPair_involutive

section Field

variable (K : Type*) [Field K]

/-- Pullback by the actual four-state permutation. -/
def localMap : Module.End K (PairState → K) where
  toFun f x := f (swapPair x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem localMap_apply (f : PairState → K) (x : PairState) :
    localMap K f x = f (swapPair x) := rfl

@[simp] theorem localMap_involutive (f : PairState → K) :
    localMap K (localMap K f) = f := by
  ext x
  simp

theorem localMap_sq : (localMap K) * (localMap K) = 1 := by
  apply LinearMap.ext
  intro f
  exact localMap_involutive K f

/-- Coordinates in the explicit eigenbasis, with the negative vector indexed by `11`. -/
def eigenCoordinates (f : PairState → K) : PairState → K
  | (false, false) => (f (false, false) + f (true, true)) / 2
  | (false, true) => f (false, true)
  | (true, false) => f (true, false)
  | (true, true) => (f (false, false) - f (true, true)) / 2

/-- Reconstruction from eigenbasis coordinates. -/
def fromEigenCoordinates (c : PairState → K) : PairState → K
  | (false, false) => c (false, false) + c (true, true)
  | (false, true) => c (false, true)
  | (true, false) => c (true, false)
  | (true, true) => c (false, false) - c (true, true)

def eigenCoordinateEquiv (h2 : (2 : K) ≠ 0) :
    (PairState → K) ≃ₗ[K] (PairState → K) where
  toFun := eigenCoordinates K
  invFun := fromEigenCoordinates K
  left_inv f := by
    ext ⟨a, b⟩
    cases a <;> cases b <;> simp only [eigenCoordinates, fromEigenCoordinates]
    all_goals field_simp ; ring
  right_inv c := by
    ext ⟨a, b⟩
    cases a <;> cases b <;> simp only [eigenCoordinates, fromEigenCoordinates]
    all_goals field_simp ; ring
  map_add' f g := by
    ext ⟨a, b⟩
    cases a <;> cases b <;> simp only [eigenCoordinates, Pi.add_apply] <;> ring
  map_smul' c f := by
    ext ⟨a, b⟩
    cases a <;> cases b <;> simp only [eigenCoordinates, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply] <;> ring

/-- A genuine basis, not merely a list of candidate eigenvectors. -/
noncomputable def localEigenbasis (h2 : (2 : K) ≠ 0) :
    Module.Basis PairState K (PairState → K) :=
  Module.Basis.ofEquivFun (eigenCoordinateEquiv K h2)

theorem localEigenbasis_apply (h2 : (2 : K) ≠ 0) (i : PairState) :
    localEigenbasis K h2 i = fromEigenCoordinates K (Pi.single i 1) := by
  change Module.Basis.ofEquivFun (eigenCoordinateEquiv K h2) i = _
  rw [Module.Basis.coe_ofEquivFun]
  rfl

def localEigenvalue (i : PairState) : K :=
  if i = (true, true) then -1 else 1

theorem localEigenbasis_eigen (h2 : (2 : K) ≠ 0) (i : PairState) :
    localMap K (localEigenbasis K h2 i) =
      localEigenvalue K i • localEigenbasis K h2 i := by
  rw [localEigenbasis_apply]
  rcases i with ⟨a, b⟩
  ext ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [localMap, swapPair, localEigenvalue, fromEigenCoordinates ]

/-- The positive eigenspace of the actual operator. -/
def positiveSpace : Submodule K (PairState → K) := LinearMap.ker (localMap K - 1)

/-- The negative eigenspace of the actual operator. -/
def negativeSpace : Submodule K (PairState → K) := LinearMap.ker (localMap K + 1)

@[simp] theorem mem_positiveSpace (f : PairState → K) :
    f ∈ positiveSpace K ↔ localMap K f = f := by
  simp [positiveSpace, LinearMap.mem_ker, sub_eq_zero]

@[simp] theorem mem_negativeSpace (f : PairState → K) :
    f ∈ negativeSpace K ↔ localMap K f = -f := by
  simp [negativeSpace, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]

/-- The three coordinates of a positive eigenvector are its values on `00`, `01`, `10`. -/
def positiveCoordinateEquiv : positiveSpace K ≃ₗ[K] (Option Bool → K) where
  toFun f
    | none => f.1 (false, false)
    | some false => f.1 (false, true)
    | some true => f.1 (true, false)
  invFun c := ⟨fun x => match x with
      | (false, false) => c none
      | (false, true) => c (some false)
      | (true, false) => c (some true)
      | (true, true) => c none, by
    rw [mem_positiveSpace]
    ext ⟨a, b⟩
    cases a <;> cases b <;> rfl⟩
  left_inv f := by
    apply Subtype.ext
    have hf := congrFun ((mem_positiveSpace K f.1).mp f.2) (false, false)
    ext ⟨a, b⟩
    cases a <;> cases b <;> try rfl
    exact hf.symm
  right_inv c := by
    ext x
    rcases x with _ | b
    · rfl
    · cases b <;> rfl
  map_add' f g := by
    ext x
    rcases x with _ | b
    · rfl
    · cases b <;> rfl
  map_smul' c f := by
    ext x
    rcases x with _ | b
    · rfl
    · cases b <;> rfl

private theorem eq_zero_of_self_eq_neg (h2 : (2 : K) ≠ 0) {x : K}
    (h : x = -x) : x = 0 := by
  have hsum : x + x = 0 := by
    simpa using congrArg (fun y : K => y + x) h
  have hmul : (2 : K) * x = 0 := by simpa [two_mul] using hsum
  exact (mul_eq_zero.mp hmul).resolve_left h2

/-- A negative eigenvector is determined by its value on `00`. -/
def negativeCoordinateEquiv (h2 : (2 : K) ≠ 0) : negativeSpace K ≃ₗ[K] K where
  toFun f := f.1 (false, false)
  invFun c := ⟨fun x => match x with
      | (false, false) => c
      | (false, true) => 0
      | (true, false) => 0
      | (true, true) => -c, by
    rw [mem_negativeSpace]
    ext ⟨a, b⟩
    cases a <;> cases b <;> simp [localMap, swapPair]⟩
  left_inv f := by
    apply Subtype.ext
    have hf := (mem_negativeSpace K f.1).mp f.2
    have h00 := congrFun hf (false, false)
    have h01 := congrFun hf (false, true)
    have h10 := congrFun hf (true, false)
    ext ⟨a, b⟩
    cases a <;> cases b
    · rfl
    · exact (eq_zero_of_self_eq_neg K h2 h01).symm
    · exact (eq_zero_of_self_eq_neg K h2 h10).symm
    · exact h00.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_positiveSpace : Module.finrank K (positiveSpace K) = 3 := by
  rw [(positiveCoordinateEquiv K).finrank_eq, Module.finrank_pi]
  decide

theorem finrank_negativeSpace (h2 : (2 : K) ≠ 0) :
    Module.finrank K (negativeSpace K) = 1 := by
  rw [(negativeCoordinateEquiv K h2).finrank_eq, Module.finrank_self]

end Field

section Positions

variable {ι : Type*} [DecidableEq ι]

/-- Change the bit pair at just one position. -/
def swapAt (l : ι) (x : ι → PairState) : ι → PairState :=
  Function.update x l (swapPair (x l))

@[simp] theorem swapAt_same (l : ι) (x : ι → PairState) :
    swapAt l x l = swapPair (x l) := by simp [swapAt]

@[simp] theorem swapAt_other {l j : ι} (h : j ≠ l) (x : ι → PairState) :
    swapAt l x j = x j := by simp [swapAt, h]

@[simp] theorem swapAt_involutive (l : ι) (x : ι → PairState) :
    swapAt l (swapAt l x) = x := by
  funext j
  by_cases h : j = l
  · subst j; simp
  · simp [swapAt_other h]

theorem swapAt_commute (l m : ι) (x : ι → PairState) :
    swapAt l (swapAt m x) = swapAt m (swapAt l x) := by
  by_cases hlm : l = m
  · subst m; rfl
  funext j
  by_cases hjl : j = l
  · subst j; simp [swapAt_other hlm ]
  by_cases hjm : j = m
  · subst j; simp [ swapAt_other (Ne.symm hlm)]
  · simp [swapAt_other hjl, swapAt_other hjm]

variable (K : Type*) [Field K]

/-- The actual permutation operator on all assignments of the separate positions. -/
def positionMap (l : ι) : Module.End K ((ι → PairState) → K) where
  toFun f x := f (swapAt l x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem positionMap_apply (l : ι) (f : (ι → PairState) → K)
    (x : ι → PairState) : positionMap K l f x = f (swapAt l x) := rfl

theorem positionMap_commute (l m : ι) :
    Commute (positionMap K l) (positionMap K m) := by
  change positionMap K l * positionMap K m = positionMap K m * positionMap K l
  ext f x
  exact congrArg f (swapAt_commute m l x)

@[simp] theorem positionMap_sq (l : ι) : positionMap K l * positionMap K l = 1 := by
  ext f x
  exact congrArg f (swapAt_involutive l x)

end Positions

section ProductBasis

open scoped BigOperators

variable (K : Type*) [Field K]

/-- Matrix entries of the explicit four-vector basis. -/
def localKernel (x i : PairState) : K :=
  fromEigenCoordinates K (Pi.single i 1) x

/-- Entries of the inverse change of coordinates. -/
def localDualKernel (i x : PairState) : K :=
  eigenCoordinates K (Pi.single x 1) i

theorem localKernel_inverse (h2 : (2 : K) ≠ 0) (x y : PairState) :
    (∑ i, localKernel K x i * localDualKernel K i y) = if x = y then 1 else 0 := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [Fintype.sum_prod_type, localKernel, localDualKernel,
      fromEigenCoordinates, eigenCoordinates, Pi.single_apply] <;> field_simp <;> ring

theorem localDualKernel_inverse (h2 : (2 : K) ≠ 0) (i j : PairState) :
    (∑ x, localDualKernel K i x * localKernel K x j) = if i = j then 1 else 0 := by
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [Fintype.sum_prod_type, localKernel, localDualKernel,
      fromEigenCoordinates, eigenCoordinates, Pi.single_apply] <;> field_simp <;> ring

theorem localKernel_eigen (i x : PairState) :
    localKernel K (swapPair x) i = localEigenvalue K i * localKernel K x i := by
  rcases i with ⟨a, b⟩
  rcases x with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [localKernel, localEigenvalue, swapPair, fromEigenCoordinates ]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Tensoring kernels is the pointwise product of their local entries. -/
def productKernel (A : PairState → PairState → K)
    (x y : ι → PairState) : K := ∏ l, A (x l) (y l)

theorem productKernel_inverse (A B : PairState → PairState → K)
    (h : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (x y : ι → PairState) :
    (∑ z, productKernel K A x z * productKernel K B z y) =
      if x = y then 1 else 0 := by
  classical
  simp only [productKernel, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun l z => A (x l) z * B z (y l))]
  simp_rw [h]
  by_cases hxy : x = y
  · subst y
    simp
  · rw [ite_eq_right hxy]
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ l) (ite_eq_right hl)

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Actual linear action of a finite matrix represented by its entries. -/
def kernelMap (A : Ω → Ω → K) : Module.End K (Ω → K) where
  toFun f x := ∑ y, A x y * f y
  map_add' f g := by
    ext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext x
    simp [Finset.mul_sum, mul_left_comm ]

theorem kernelMap_inverse (A B : Ω → Ω → K)
    (h : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (f : Ω → K) : kernelMap K A (kernelMap K B f) = f := by
  classical
  funext x
  change (∑ y, A x y * ∑ z, B y z * f z) = f x
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, h]
  simp

/-- The global coordinate transformation and its inverse are explicit finite sums. -/
noncomputable def productCoordinateEquiv (h2 : (2 : K) ≠ 0) :
    ((ι → PairState) → K) ≃ₗ[K] ((ι → PairState) → K) where
  toFun := kernelMap K (productKernel K (localDualKernel K))
  invFun := kernelMap K (productKernel K (localKernel K))
  left_inv := kernelMap_inverse K _ _
    (productKernel_inverse K _ _ (localKernel_inverse K h2))
  right_inv := kernelMap_inverse K _ _
    (productKernel_inverse K _ _ (localDualKernel_inverse K h2))
  map_add' := (kernelMap K _).map_add
  map_smul' := (kernelMap K _).map_smul

/-- A genuine basis on all pair assignments, with one local eigenvector chosen per position. -/
noncomputable def productEigenbasis (h2 : (2 : K) ≠ 0) :
    Module.Basis (ι → PairState) K ((ι → PairState) → K) :=
  Module.Basis.ofEquivFun (productCoordinateEquiv K h2)

theorem productEigenbasis_apply (h2 : (2 : K) ≠ 0)
    (a x : ι → PairState) :
    productEigenbasis K h2 a x = ∏ l, localKernel K (x l) (a l) := by
  classical
  change Module.Basis.ofEquivFun (productCoordinateEquiv K h2) a x = _
  rw [Module.Basis.coe_ofEquivFun]
  simp [productCoordinateEquiv, kernelMap, productKernel, Pi.single_apply]

/-- The product basis simultaneously diagonalizes every separate-position permutation. -/
theorem productEigenbasis_eigen (h2 : (2 : K) ≠ 0) (a : ι → PairState) (l : ι) :
    positionMap K l (productEigenbasis K h2 a) =
      localEigenvalue K (a l) • productEigenbasis K h2 a := by
  classical
  funext x
  simp only [positionMap_apply, productEigenbasis_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∏ j, localKernel K (swapAt l x j) (a j)) =
        localKernel K (swapPair (x l)) (a l) *
          ∏ j ∈ Finset.univ.erase l, localKernel K (x j) (a j) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => localKernel K (swapAt l x j) (a j)) (Finset.mem_univ l)]
      rw [swapAt_same]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [swapAt_other (Finset.mem_erase.mp hj).1]
    _ = localEigenvalue K (a l) *
        (localKernel K (x l) (a l) *
          ∏ j ∈ Finset.univ.erase l, localKernel K (x j) (a j)) := by
      rw [localKernel_eigen, mul_assoc]
    _ = localEigenvalue K (a l) * ∏ j, localKernel K (x j) (a j) := by
      rw [Finset.mul_prod_erase Finset.univ
        (fun j => localKernel K (x j) (a j)) (Finset.mem_univ l)]

end ProductBasis

section Spectators

variable (K : Type*) [Field K]
variable {ι U : Type*} [Fintype ι] [DecidableEq ι]

/-- Add arbitrary unused coordinates by applying the proved product transform separately
on each spectator fiber. -/
noncomputable def spectatorCoordinateEquiv (h2 : (2 : K) ≠ 0) :
    (((ι → PairState) × U) → K) ≃ₗ[K] ((U × (ι → PairState)) → K) where
  toFun f p := productCoordinateEquiv K h2 (fun x => f (x, p.1)) p.2
  invFun c p := (productCoordinateEquiv K h2).symm (fun a => c (p.2, a)) p.1
  left_inv f := by
    funext ⟨x, u⟩
    exact congrFun ((productCoordinateEquiv K h2).symm_apply_apply (fun y => f (y, u))) x
  right_inv c := by
    funext ⟨u, a⟩
    exact congrFun ((productCoordinateEquiv K h2).apply_symm_apply (fun b => c (u, b))) a
  map_add' f g := by
    funext ⟨u, a⟩
    exact congrFun ((productCoordinateEquiv K h2).map_add
      (fun x => f (x, u)) (fun x => g (x, u))) a
  map_smul' c f := by
    funext ⟨u, a⟩
    exact congrFun ((productCoordinateEquiv K h2).map_smul c (fun x => f (x, u))) a

variable [Fintype U] [DecidableEq U]

/-- The full basis, including a separate coordinate vector for each unused-bit assignment. -/
noncomputable def spectatorEigenbasis (h2 : (2 : K) ≠ 0) :
    Module.Basis (U × (ι → PairState)) K ((((ι → PairState) × U) → K)) :=
  Module.Basis.ofEquivFun (spectatorCoordinateEquiv K h2)

theorem spectatorEigenbasis_apply (h2 : (2 : K) ≠ 0)
    (u : U) (a x : ι → PairState) (v : U) :
    spectatorEigenbasis K h2 (u, a) (x, v) =
      if v = u then productEigenbasis K h2 a x else 0 := by
  classical
  change Module.Basis.ofEquivFun (spectatorCoordinateEquiv K h2) (u, a) (x, v) = _
  rw [Module.Basis.coe_ofEquivFun]
  by_cases huv : v = u
  · subst v
    simp [spectatorCoordinateEquiv, productCoordinateEquiv, kernelMap,
      productEigenbasis_apply, productKernel, Pi.single_apply]
  · simp [spectatorCoordinateEquiv, productCoordinateEquiv, kernelMap, productKernel, huv ]

/-- The actual separate-position permutation leaves all spectator coordinates fixed. -/
def spectatorPositionMap (l : ι) : Module.End K ((((ι → PairState) × U) → K)) where
  toFun f p := f (swapAt l p.1, p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] [Fintype U] [DecidableEq U] in
theorem spectatorPositionMap_commute (l m : ι) :
    Commute (spectatorPositionMap K (U := U) l) (spectatorPositionMap K m) := by
  change spectatorPositionMap K l * spectatorPositionMap K m =
    spectatorPositionMap K m * spectatorPositionMap K l
  apply LinearMap.ext
  intro f
  funext p
  exact congrArg (fun x => f (x, p.2)) (swapAt_commute m l p.1)

omit [Fintype ι] [Fintype U] [DecidableEq U] in
@[simp] theorem spectatorPositionMap_sq (l : ι) :
    spectatorPositionMap K (U := U) l * spectatorPositionMap K l = 1 := by
  apply LinearMap.ext
  intro f
  funext p
  exact congrArg (fun x => f (x, p.2)) (swapAt_involutive l p.1)

theorem spectatorEigenbasis_eigen (h2 : (2 : K) ≠ 0) (u : U)
    (a : ι → PairState) (l : ι) :
    spectatorPositionMap K l (spectatorEigenbasis K h2 (u, a)) =
      localEigenvalue K (a l) • spectatorEigenbasis K h2 (u, a) := by
  funext ⟨x, v⟩
  change spectatorEigenbasis K h2 (u, a) (swapAt l x, v) =
    localEigenvalue K (a l) * spectatorEigenbasis K h2 (u, a) (x, v)
  rw [spectatorEigenbasis_apply, spectatorEigenbasis_apply]
  by_cases huv : v = u
  · simp only [huv, ite_true]
    exact congrFun (productEigenbasis_eigen K h2 a l) x
  · simp [huv]

end Spectators

end SubexponentialSAT.LocalSpectrum

end OAI.Algorithms
