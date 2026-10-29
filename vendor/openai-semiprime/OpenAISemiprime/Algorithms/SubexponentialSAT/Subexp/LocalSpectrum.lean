import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity

namespace OAI.Algorithms

/-!
# Spectrum of a swap of two finite ordered registers

The alphabet size is unrestricted relative to the characteristic.  The only
field assumption beyond `Field K` is `2 ≠ 0`.  Basis labels on or above the
diagonal are positive; labels strictly below the diagonal are negative.
-/

namespace SubexponentialSAT.Subexp.LocalSpectrum

open scoped BigOperators

abbrev Pair (α : Type*) := α × α

def swapPair {α : Type*} (x : Pair α) : Pair α := (x.2, x.1)

@[simp] theorem swapPair_involutive {α : Type*} (x : Pair α) :
    swapPair (swapPair x) = x := by cases x; rfl

def swapPerm (α : Type*) : Equiv.Perm (Pair α) where
  toFun := swapPair
  invFun := swapPair
  left_inv := swapPair_involutive
  right_inv := swapPair_involutive

variable (K : Type*) [Field K]
variable {α : Type*}

/-- The actual permutation operator on functions on two registers. -/
def swapMap : Module.End K (Pair α → K) where
  toFun f x := f (swapPair x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem swapMap_apply (f : Pair α → K) (x : Pair α) :
    swapMap K f x = f (swapPair x) := rfl

@[simp] theorem swapMap_involutive (f : Pair α → K) :
    swapMap K (swapMap K f) = f := by
  funext x
  simp

theorem swapMap_sq : swapMap K (α := α) * swapMap K = 1 := by
  apply LinearMap.ext
  exact swapMap_involutive K

variable [LinearOrder α]

/-- Diagonal entries are fixed; each unordered off-diagonal pair supplies a sum
coordinate and a difference coordinate. -/
def eigenCoordinates (f : Pair α → K) (x : Pair α) : K :=
  if x.1 = x.2 then f x else
  if x.1 < x.2 then (f x + f (swapPair x)) / 2
  else (f (swapPair x) - f x) / 2

def fromEigenCoordinates (c : Pair α → K) (x : Pair α) : K :=
  if x.1 = x.2 then c x else
  if x.1 < x.2 then c x + c (swapPair x)
  else c (swapPair x) - c x

def eigenCoordinateEquiv (h2 : (2 : K) ≠ 0) :
    (Pair α → K) ≃ₗ[K] (Pair α → K) where
  toFun := eigenCoordinates K
  invFun := fromEigenCoordinates K
  left_inv f := by
    funext ⟨a, b⟩
    rcases lt_trichotomy a b with hab | rfl | hba
    · simp only [eigenCoordinates, fromEigenCoordinates, swapPair,
        ne_of_lt hab, Ne.symm (ne_of_lt hab), ite_false, hab, ite_true,
        not_lt_of_ge (le_of_lt hab)]
      field_simp
      ring
    · simp [eigenCoordinates, fromEigenCoordinates]
    · simp only [eigenCoordinates, fromEigenCoordinates, swapPair,
        ne_of_lt hba, Ne.symm (ne_of_lt hba), ite_false, hba, ite_true,
        not_lt_of_ge (le_of_lt hba)]
      field_simp
      ring
  right_inv c := by
    funext ⟨a, b⟩
    rcases lt_trichotomy a b with hab | rfl | hba
    · simp only [eigenCoordinates, fromEigenCoordinates, swapPair,
        ne_of_lt hab, Ne.symm (ne_of_lt hab), ite_false, hab, ite_true,
        not_lt_of_ge (le_of_lt hab)]
      field_simp
      ring
    · simp [eigenCoordinates, fromEigenCoordinates]
    · simp only [eigenCoordinates, fromEigenCoordinates, swapPair,
        ne_of_lt hba, Ne.symm (ne_of_lt hba), ite_false, hba, ite_true,
        not_lt_of_ge (le_of_lt hba)]
      field_simp
      ring
  map_add' f g := by
    funext x
    simp only [eigenCoordinates, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c f := by
    funext x
    simp only [eigenCoordinates, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

def eigenvalue (i : Pair α) : K := if i.1 ≤ i.2 then 1 else -1

/-- Conjugating the actual swap gives a diagonal sign operator. -/
theorem eigenCoordinates_swap (f : Pair α → K) (i : Pair α) :
    eigenCoordinates K (swapMap K f) i = eigenvalue K i * eigenCoordinates K f i := by
  rcases i with ⟨a, b⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · simp [eigenCoordinates, eigenvalue, swapPair, ne_of_lt hab, hab, le_of_lt hab, swapMap]
    ring
  · simp [eigenCoordinates, eigenvalue, swapPair, swapMap]
  · simp [eigenCoordinates, eigenvalue, swapPair,
      Ne.symm (ne_of_lt hba), not_lt_of_ge (le_of_lt hba), not_le_of_gt hba,
      swapMap]
    ring

variable [Fintype α]

/-- The sum/difference construction is a genuine basis over every field with `2 ≠ 0`. -/
noncomputable def swapEigenbasis (h2 : (2 : K) ≠ 0) :
    Module.Basis (Pair α) K (Pair α → K) :=
  Module.Basis.ofEquivFun (eigenCoordinateEquiv K h2)

theorem swapEigenbasis_apply (h2 : (2 : K) ≠ 0) (i : Pair α) :
    swapEigenbasis K h2 i = fromEigenCoordinates K (Pi.single i 1) := by
  change Module.Basis.ofEquivFun (eigenCoordinateEquiv K h2) i = _
  rw [Module.Basis.coe_ofEquivFun]
  rfl

@[simp] theorem coordinates_basis (h2 : (2 : K) ≠ 0) (i : Pair α) :
    eigenCoordinateEquiv K h2 (swapEigenbasis K h2 i) = Pi.single i 1 := by
  rw [swapEigenbasis_apply]
  exact (eigenCoordinateEquiv K h2).apply_symm_apply (Pi.single i 1)

theorem swapEigenbasis_eigen (h2 : (2 : K) ≠ 0) (i : Pair α) :
    swapMap K (swapEigenbasis K h2 i) = eigenvalue K i • swapEigenbasis K h2 i := by
  apply (eigenCoordinateEquiv K h2).injective
  rw [map_smul]
  funext j
  change eigenCoordinates K (swapMap K (swapEigenbasis K h2 i)) j =
    eigenvalue K i * (eigenCoordinateEquiv K h2 (swapEigenbasis K h2 i)) j
  rw [eigenCoordinates_swap]
  change eigenvalue K j * (eigenCoordinateEquiv K h2 (swapEigenbasis K h2 i)) j = _
  rw [coordinates_basis]
  by_cases hij : i = j
  · subst j; rfl
  · simp [ hij]

def localKernel (x i : Pair α) : K :=
  fromEigenCoordinates K (Pi.single i 1) x

def localDualKernel (i x : Pair α) : K :=
  eigenCoordinates K (Pi.single x 1) i

/-- The matrix-entry formula for a finite linear map, used to verify both kernel inverses. -/
theorem linearMap_apply_eq_sum {β γ : Type*} [Fintype β] [DecidableEq β]
    (L : (β → K) →ₗ[K] (γ → K)) (f : β → K) (x : γ) :
    L f x = ∑ i, L (Pi.single i 1) x * f i := by
  have hf : (∑ i, f i • (Pi.single i (1 : K) : β → K)) = f := by
    funext j
    simp [Pi.single_apply]
  calc
    L f x = L (∑ i, f i • (Pi.single i (1 : K) : β → K)) x := by rw [hf]
    _ = ∑ i, L (Pi.single i 1) x * f i := by
      simp [map_sum, map_smul, mul_comm]

theorem localKernel_inverse (h2 : (2 : K) ≠ 0) (x y : Pair α) :
    (∑ i, localKernel K x i * localDualKernel K i y) = if x = y then 1 else 0 := by
  have h := linearMap_apply_eq_sum K (eigenCoordinateEquiv K h2).symm.toLinearMap
    (eigenCoordinateEquiv K h2 (Pi.single y 1)) x
  calc
    _ = (eigenCoordinateEquiv K h2).symm
        (eigenCoordinateEquiv K h2 (Pi.single y 1)) x := h.symm
    _ = (Pi.single y (1 : K) : Pair α → K) x :=
      congrFun ((eigenCoordinateEquiv K h2).symm_apply_apply (Pi.single y 1)) x
    _ = (if x = y then 1 else 0) := by simp [Pi.single_apply ]

theorem localDualKernel_inverse (h2 : (2 : K) ≠ 0) (i j : Pair α) :
    (∑ x, localDualKernel K i x * localKernel K x j) = if i = j then 1 else 0 := by
  have h := linearMap_apply_eq_sum K (eigenCoordinateEquiv K h2).toLinearMap
    ((eigenCoordinateEquiv K h2).symm (Pi.single j 1)) i
  calc
    _ = (eigenCoordinateEquiv K h2)
        ((eigenCoordinateEquiv K h2).symm (Pi.single j 1)) i := h.symm
    _ = (Pi.single j (1 : K) : Pair α → K) i :=
      congrFun ((eigenCoordinateEquiv K h2).apply_symm_apply (Pi.single j 1)) i
    _ = (if i = j then 1 else 0) := by simp [Pi.single_apply ]

theorem localKernel_eigen (h2 : (2 : K) ≠ 0) (i x : Pair α) :
    localKernel K (swapPair x) i = eigenvalue K i * localKernel K x i := by
  have h := congrFun (swapEigenbasis_eigen K h2 i) x
  simpa only [swapMap_apply, swapEigenbasis_apply, Pi.smul_apply, smul_eq_mul,
    localKernel] using h

/-- These are the eigenspaces of the actual permutation operator. -/
def positiveSpace : Submodule K (Pair α → K) := LinearMap.ker (swapMap K - 1)

def negativeSpace : Submodule K (Pair α → K) := LinearMap.ker (swapMap K + 1)

omit [LinearOrder α] [Fintype α] in
@[simp] theorem mem_positiveSpace (f : Pair α → K) :
    f ∈ positiveSpace K ↔ swapMap K f = f := by
  simp [positiveSpace, LinearMap.mem_ker, sub_eq_zero]

omit [LinearOrder α] [Fintype α] in
@[simp] theorem mem_negativeSpace (f : Pair α → K) :
    f ∈ negativeSpace K ↔ swapMap K f = -f := by
  simp [negativeSpace, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]

private theorem scalar_eq_zero_of_eq_neg (h2 : (2 : K) ≠ 0) {x : K}
    (h : x = -x) : x = 0 := by
  have hs : x + x = 0 := by simpa using congrArg (fun y : K => y + x) h
  have hm : (2 : K) * x = 0 := by simpa [two_mul] using hs
  exact (mul_eq_zero.mp hm).resolve_left h2

omit [Fintype α] in
theorem negative_coordinate_of_positive (h2 : (2 : K) ≠ 0)
    (f : Pair α → K) (hf : f ∈ positiveSpace K) (i : Pair α)
    (hi : ¬ i.1 ≤ i.2) : eigenCoordinates K f i = 0 := by
  have h := eigenCoordinates_swap K f i
  rw [(mem_positiveSpace K f).mp hf] at h
  simp only [eigenvalue, ite_eq_right hi, neg_one_mul] at h
  exact scalar_eq_zero_of_eq_neg K h2 h

omit [Fintype α] in
theorem positive_coordinate_of_negative (h2 : (2 : K) ≠ 0)
    (f : Pair α → K) (hf : f ∈ negativeSpace K) (i : Pair α)
    (hi : i.1 ≤ i.2) : eigenCoordinates K f i = 0 := by
  have h := eigenCoordinates_swap K f i
  rw [(mem_negativeSpace K f).mp hf] at h
  have hn : eigenCoordinates K (-f) i = -eigenCoordinates K f i :=
    congrFun ((eigenCoordinateEquiv K h2).map_neg f) i
  rw [hn] at h
  simp only [eigenvalue, ite_eq_left hi, one_mul] at h
  exact scalar_eq_zero_of_eq_neg K h2 h.symm

theorem positiveSpace_eq_span (h2 : (2 : K) ≠ 0) :
    positiveSpace K (α := α) = Submodule.span K
      (Set.range fun i : {i : Pair α // i.1 ≤ i.2} => swapEigenbasis K h2 i.1) := by
  apply le_antisymm
  · intro f hf
    rw [← (swapEigenbasis K h2).sum_repr f]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i.1 ≤ i.2
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    · have hz : (swapEigenbasis K h2).repr f i = 0 := by
        change eigenCoordinates K f i = 0
        exact negative_coordinate_of_positive K h2 f hf i hi
      simp [hz]
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (mem_positiveSpace K _).mpr
    simpa [eigenvalue, i.2] using swapEigenbasis_eigen K h2 i.1

theorem negativeSpace_eq_span (h2 : (2 : K) ≠ 0) :
    negativeSpace K (α := α) = Submodule.span K
      (Set.range fun i : {i : Pair α // i.2 < i.1} => swapEigenbasis K h2 i.1) := by
  apply le_antisymm
  · intro f hf
    rw [← (swapEigenbasis K h2).sum_repr f]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i.2 < i.1
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    · have hz : (swapEigenbasis K h2).repr f i = 0 := by
        change eigenCoordinates K f i = 0
        exact positive_coordinate_of_negative K h2 f hf i (not_lt.mp hi)
      simp [hz]
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (mem_negativeSpace K _).mpr
    simpa [eigenvalue, not_le_of_gt i.2] using swapEigenbasis_eigen K h2 i.1

theorem finrank_positiveSpace (h2 : (2 : K) ≠ 0) :
    Module.finrank K (positiveSpace K (α := α)) =
      Fintype.card {i : Pair α // i.1 ≤ i.2} := by
  rw [positiveSpace_eq_span K h2]
  exact finrank_span_eq_card
    ((swapEigenbasis K h2).linearIndependent.comp _ Subtype.val_injective)

theorem finrank_negativeSpace (h2 : (2 : K) ≠ 0) :
    Module.finrank K (negativeSpace K (α := α)) =
      Fintype.card {i : Pair α // i.2 < i.1} := by
  rw [negativeSpace_eq_span K h2]
  exact finrank_span_eq_card
    ((swapEigenbasis K h2).linearIndependent.comp _ Subtype.val_injective)

/-- The two actual eigenspaces form a direct sum of the full register space. -/
theorem spaces_isCompl (h2 : (2 : K) ≠ 0) :
    IsCompl (positiveSpace K (α := α)) (negativeSpace K) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro f hp hn
    have h : f = -f := ((mem_positiveSpace K f).mp hp).symm.trans
      ((mem_negativeSpace K f).mp hn)
    funext x
    exact scalar_eq_zero_of_eq_neg K h2 (congrFun h x)
  · apply codisjoint_iff_le_sup.mpr
    rw [← (swapEigenbasis K h2).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.1 ≤ i.2
    · apply (show positiveSpace K ≤ positiveSpace K ⊔ negativeSpace K from le_sup_left)
      apply (mem_positiveSpace K _).mpr
      simpa [eigenvalue, hi] using swapEigenbasis_eigen K h2 i
    · apply (show negativeSpace K ≤ positiveSpace K ⊔ negativeSpace K from le_sup_right)
      apply (mem_negativeSpace K _).mpr
      simpa [eigenvalue, hi] using swapEigenbasis_eigen K h2 i

theorem finrank_positiveSpace_fin (r : ℕ) (h2 : (2 : K) ≠ 0) :
    Module.finrank K (positiveSpace K (α := Fin r)) = r * (r + 1) / 2 := by
  rw [finrank_positiveSpace K h2]
  exact SubexponentialSAT.SubexpSwapMultiplicity.card_positive r

theorem finrank_negativeSpace_fin (r : ℕ) (h2 : (2 : K) ≠ 0) :
    Module.finrank K (negativeSpace K (α := Fin r)) = r * (r - 1) / 2 := by
  rw [finrank_negativeSpace K h2]
  exact SubexponentialSAT.SubexpSwapMultiplicity.card_negative r

end SubexponentialSAT.Subexp.LocalSpectrum

end OAI.Algorithms
