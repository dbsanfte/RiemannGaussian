import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.LocalSpectrum
import OpenAISemiprime.Algorithms.SubexponentialSAT.Subexp.LocalSpectrum
import OpenAISemiprime.Algorithms.SubexponentialSAT.MulticolorTypes
import OpenAISemiprime.Algorithms.SubexponentialSAT.Subexp.MatrixSupport
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity
import OpenAISemiprime.Algorithms.SubexponentialSAT.SpectralRank

namespace OAI.Algorithms

/-!
# Tensor eigenbases for the multicolor register swap

The finite change of basis is constructed from invertible local kernels. This
module then specializes it to the actual register swap and transports it to the
joint fiber of universal types; multiplicities count those actual basis labels.
-/

namespace SubexponentialSAT.Subexp.TensorSpectrum

open scoped BigOperators

section ProductKernel

variable (K : Type*) [Field K]
variable {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

/-- Pointwise tensor product of local change-of-basis entries. -/
def productKernel (A : β → β → K) (x y : ι → β) : K :=
  ∏ l, A (x l) (y l)

theorem productKernel_inverse (A B : β → β → K)
    (h : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (x y : ι → β) :
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

/-- Explicit mutually inverse finite tensor transforms. -/
noncomputable def productCoordinateEquiv (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0) :
    ((ι → β) → K) ≃ₗ[K] ((ι → β) → K) where
  toFun := SubexponentialSAT.LocalSpectrum.kernelMap K (productKernel K B)
  invFun := SubexponentialSAT.LocalSpectrum.kernelMap K (productKernel K A)
  left_inv := SubexponentialSAT.LocalSpectrum.kernelMap_inverse K _ _
    (productKernel_inverse K _ _ hAB)
  right_inv := SubexponentialSAT.LocalSpectrum.kernelMap_inverse K _ _
    (productKernel_inverse K _ _ hBA)
  map_add' := (SubexponentialSAT.LocalSpectrum.kernelMap K _).map_add
  map_smul' := (SubexponentialSAT.LocalSpectrum.kernelMap K _).map_smul

/-- A genuine basis of the full function space on assignments of local states. -/
noncomputable def productBasis (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0) :
    Module.Basis (ι → β) K ((ι → β) → K) :=
  Module.Basis.ofEquivFun (productCoordinateEquiv K A B hAB hBA)

theorem productBasis_apply (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0)
    (a x : ι → β) :
    productBasis K A B hAB hBA a x = ∏ l, A (x l) (a l) := by
  classical
  change Module.Basis.ofEquivFun (productCoordinateEquiv K A B hAB hBA) a x = _
  rw [Module.Basis.coe_ofEquivFun]
  simp [productCoordinateEquiv, SubexponentialSAT.LocalSpectrum.kernelMap,
    productKernel, Pi.single_apply]

/-- If the local kernel is an eigenkernel, the genuine product basis has the
same eigenvalue under a change at one position. -/
theorem productBasis_eigen (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0)
    (σ : β → β) (eigenvalue : β → K)
    (heigen : ∀ a x, A (σ x) a = eigenvalue a * A x a)
    (a x : ι → β) (l : ι) :
    productBasis K A B hAB hBA a (Function.update x l (σ (x l))) =
      eigenvalue (a l) * productBasis K A B hAB hBA a x := by
  classical
  simp only [productBasis_apply]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => A (Function.update x l (σ (x l)) j) (a j)) (Finset.mem_univ l)]
  rw [Function.update_self, heigen]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => A (x j) (a j)) (Finset.mem_univ l), mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

end ProductKernel

section Spectators

variable (K : Type*) [Field K]
variable {β ι U : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

/-- Apply the tensor change of basis independently on each spectator fiber. -/
noncomputable def spectatorCoordinateEquiv (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0) :
    (((ι → β) × U) → K) ≃ₗ[K] ((U × (ι → β)) → K) where
  toFun f p := productCoordinateEquiv K A B hAB hBA (fun x => f (x, p.1)) p.2
  invFun c p := (productCoordinateEquiv K A B hAB hBA).symm (fun a => c (p.2, a)) p.1
  left_inv f := by
    funext ⟨x, u⟩
    exact congrFun ((productCoordinateEquiv K A B hAB hBA).symm_apply_apply
      (fun y => f (y, u))) x
  right_inv c := by
    funext ⟨u, a⟩
    exact congrFun ((productCoordinateEquiv K A B hAB hBA).apply_symm_apply
      (fun b => c (u, b))) a
  map_add' f g := by
    funext ⟨u, a⟩
    exact congrFun ((productCoordinateEquiv K A B hAB hBA).map_add
      (fun x => f (x, u)) (fun x => g (x, u))) a
  map_smul' c f := by
    funext ⟨u, a⟩
    exact congrFun ((productCoordinateEquiv K A B hAB hBA).map_smul c
      (fun x => f (x, u))) a

variable [Fintype U] [DecidableEq U]

/-- Include a separate coordinate vector for every assignment of the untouched registers. -/
noncomputable def spectatorBasis (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0) :
    Module.Basis (U × (ι → β)) K ((((ι → β) × U) → K)) :=
  Module.Basis.ofEquivFun (spectatorCoordinateEquiv K A B hAB hBA)

theorem spectatorBasis_apply (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0)
    (u : U) (a x : ι → β) (v : U) :
    spectatorBasis K A B hAB hBA (u, a) (x, v) =
      if v = u then productBasis K A B hAB hBA a x else 0 := by
  classical
  change Module.Basis.ofEquivFun (spectatorCoordinateEquiv K A B hAB hBA) (u, a) (x, v) = _
  rw [Module.Basis.coe_ofEquivFun]
  by_cases huv : v = u
  · subst v
    simp [spectatorCoordinateEquiv, productCoordinateEquiv, SubexponentialSAT.LocalSpectrum.kernelMap,
      productBasis_apply, productKernel, Pi.single_apply]
  · simp [spectatorCoordinateEquiv, productCoordinateEquiv, SubexponentialSAT.LocalSpectrum.kernelMap, productKernel, huv ]

theorem spectatorBasis_eigen (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0)
    (σ : β → β) (eigenvalue : β → K)
    (heigen : ∀ a x, A (σ x) a = eigenvalue a * A x a)
    (u : U) (a x : ι → β) (v : U) (l : ι) :
    spectatorBasis K A B hAB hBA (u, a) (Function.update x l (σ (x l)), v) =
      eigenvalue (a l) * spectatorBasis K A B hAB hBA (u, a) (x, v) := by
  rw [spectatorBasis_apply, spectatorBasis_apply]
  by_cases huv : v = u
  · simp only [huv, ite_true]
    exact productBasis_eigen K A B hAB hBA σ eigenvalue heigen a x l
  · simp [huv]

end Spectators

section JointBasis

open SubexponentialSAT.MulticolorTypes

variable {r Q Δ : ℕ}

private theorem pairKernel_inverse (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (d : DecidableEq (Fin r × Fin r)) (x y : Fin r × Fin r) :
    (∑ z, LocalSpectrum.localKernel K x z * LocalSpectrum.localDualKernel K z y) =
      @ite K (x = y) (d x y) 1 0 := by
  by_cases hxy : x = y
  · simpa only [ite_eq_left hxy] using LocalSpectrum.localKernel_inverse K h2 x y
  · simpa only [ite_eq_right hxy] using LocalSpectrum.localKernel_inverse K h2 x y

private theorem pairDualKernel_inverse (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (d : DecidableEq (Fin r × Fin r)) (x y : Fin r × Fin r) :
    (∑ z, LocalSpectrum.localDualKernel K x z * LocalSpectrum.localKernel K z y) =
      @ite K (x = y) (d x y) 1 0 := by
  by_cases hxy : x = y
  · simpa only [ite_eq_left hxy] using LocalSpectrum.localDualKernel_inverse K h2 x y
  · simpa only [ite_eq_right hxy] using LocalSpectrum.localDualKernel_inverse K h2 x y

/-- Labels of the genuine joint eigenbasis. The spectator includes the
non-head color of the pinned slot and all unused slot words. -/
abbrev JointBasisIndex (t : Fin Q) (g : Fin r) (i : Fin Δ) :=
  Spectator (Q := Q) g i × (OtherPosition t → Fin r × Fin r)

noncomputable def jointEigenbasis (K : Type*) [Field K]
    (h2 : (2 : K) ≠ 0) (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Module.Basis (JointBasisIndex t g i) K (Joint t g i → K) :=
  (@spectatorBasis K inferInstance (Fin r × Fin r) (OtherPosition t)
    (Spectator (Q := Q) g i) inferInstance inferInstance inferInstance inferInstance
    inferInstance
    (LocalSpectrum.localKernel K (α := Fin r)) (LocalSpectrum.localDualKernel K (α := Fin r))
    (pairKernel_inverse K h2 inferInstance) (pairDualKernel_inverse K h2 inferInstance)).map
      (LinearEquiv.funCongrLeft K K (jointEquivPairs t g i))

@[simp] theorem jointEigenbasis_apply (K : Type*) [Field K]
    (h2 : (2 : K) ≠ 0) (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (a : JointBasisIndex t g i) (u : Joint t g i) :
    jointEigenbasis K h2 t g i a u =
      @spectatorBasis K inferInstance (Fin r × Fin r) (OtherPosition t)
        (Spectator (Q := Q) g i) inferInstance inferInstance inferInstance inferInstance
        inferInstance
        (LocalSpectrum.localKernel K (α := Fin r)) (LocalSpectrum.localDualKernel K (α := Fin r))
        (pairKernel_inverse K h2 inferInstance) (pairDualKernel_inverse K h2 inferInstance)
        a (jointEquivPairs t g i u) := rfl

/-- The actual register swap becomes a change of just one local pair under
the joint-fiber decomposition. -/
theorem jointEquivPairs_jointSwap (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (l : OtherPosition t) (u : Joint t g i) :
    jointEquivPairs t g i (MatrixSupport.jointSwap i t g l u) =
      (Function.update (jointEquivPairs t g i u).1 l
        (LocalSpectrum.swapPair ((jointEquivPairs t g i u).1 l)),
        (jointEquivPairs t g i u).2) := by
  apply Prod.ext
  · funext m
    by_cases h : m = l
    · subst m
      apply Prod.ext <;>
        simp [jointEquivPairs, MatrixSupport.jointSwap, MatrixSupport.swapPositions,
          LocalSpectrum.swapPair]
    · have hm : m.val ≠ l.val := fun hc => h (Subtype.ext hc)
      apply Prod.ext <;>
        simp [jointEquivPairs, MatrixSupport.jointSwap, MatrixSupport.swapPositions, h, hm]
  · apply Prod.ext
    · apply Subtype.ext
      simp [jointEquivPairs, MatrixSupport.jointSwap, MatrixSupport.swapPositions,
        Ne.symm l.property]
    · funext j m
      simp [jointEquivPairs, MatrixSupport.jointSwap, MatrixSupport.swapPositions, j.property]

theorem jointEigenbasis_swap_eigen (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (a : JointBasisIndex t g i)
    (l : OtherPosition t) (u : Joint t g i) :
    jointEigenbasis K h2 t g i a (MatrixSupport.jointSwap i t g l u) =
      LocalSpectrum.eigenvalue K (a.2 l) * jointEigenbasis K h2 t g i a u := by
  simp only [jointEigenbasis_apply, jointEquivPairs_jointSwap]
  exact @spectatorBasis_eigen K inferInstance (Fin r × Fin r) (OtherPosition t)
    (Spectator (Q := Q) g i) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance _ _
    (pairKernel_inverse K h2 inferInstance) (pairDualKernel_inverse K h2 inferInstance)
    LocalSpectrum.swapPair (LocalSpectrum.eigenvalue K) (LocalSpectrum.localKernel_eigen K h2)
    a.1 a.2 (jointEquivPairs t g i u).1 (jointEquivPairs t g i u).2 l

/-- Negative signs are indexed by the local labels strictly below the diagonal. -/
def negativePositions {t : Fin Q} {g : Fin r} {i : Fin Δ} (a : JointBasisIndex t g i) :
    Finset (Fin Q) :=
  (Finset.univ.filter fun l : OtherPosition t => (a.2 l).2 < (a.2 l).1).map
    ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_negativePositions {t : Fin Q} {g : Fin r} {i : Fin Δ}
    (a : JointBasisIndex t g i) (l : OtherPosition t) :
    l.val ∈ negativePositions a ↔ (a.2 l).2 < (a.2 l).1 := by
  simp only [negativePositions, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, hj, hjl⟩
    have h : j = l := Subtype.ext hjl
    simpa only [h] using hj
  · intro h
    exact ⟨l, h, rfl⟩

theorem negativePositions_subset {t : Fin Q} {g : Fin r} {i : Fin Δ}
    (a : JointBasisIndex t g i) : negativePositions a ⊆ MatrixSupport.activePositions t := by
  intro l hl
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hl
  simp [MatrixSupport.activePositions, j.property]

def jointWeight {t : Fin Q} {g : Fin r} {i : Fin Δ} (a : JointBasisIndex t g i) : ℕ :=
  SubexponentialSAT.SubexpSwapMultiplicity.swapWeight a.2

@[simp] theorem card_negativePositions {t : Fin Q} {g : Fin r} {i : Fin Δ}
    (a : JointBasisIndex t g i) : (negativePositions a).card = jointWeight a := by
  simp [negativePositions, jointWeight, SubexponentialSAT.SubexpSwapMultiplicity.swapWeight,
    SubexponentialSAT.SubexpSwapMultiplicity.weight, SubexponentialSAT.SubexpSwapMultiplicity.negativeSupport,
    SubexponentialSAT.SubexpSwapMultiplicity.negativePair]
  rfl

theorem jointWeight_le {t : Fin Q} {g : Fin r} {i : Fin Δ}
    (a : JointBasisIndex t g i) : jointWeight a ≤ Q - 1 := by
  simpa only [jointWeight, card_otherPosition] using
    SubexponentialSAT.SubexpSwapMultiplicity.weight_le SubexponentialSAT.SubexpSwapMultiplicity.negativePair a.2

def jointSign (K : Type*) [Field K] {t : Fin Q} {g : Fin r} {i : Fin Δ}
    (a : JointBasisIndex t g i) (l : Fin Q) : K :=
  if l ∈ negativePositions a then -1 else 1

@[simp] theorem jointSign_other (K : Type*) [Field K]
    {t : Fin Q} {g : Fin r} {i : Fin Δ} (a : JointBasisIndex t g i) (l : OtherPosition t) :
    jointSign K a l.val = LocalSpectrum.eigenvalue K (a.2 l) := by
  simp only [jointSign, mem_negativePositions, LocalSpectrum.eigenvalue, ← not_le, ite_not]

theorem jointEigenbasis_sign_eigen (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (a : JointBasisIndex t g i)
    (l : OtherPosition t) (u : Joint t g i) :
    jointEigenbasis K h2 t g i a (MatrixSupport.jointSwap i t g l u) =
      jointSign K a l.val * jointEigenbasis K h2 t g i a u := by
  rw [jointSign_other]
  exact jointEigenbasis_swap_eigen K h2 t g i a l u

end JointBasis

section Multiplicities

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSwapMultiplicity

variable {r Q Δ : ℕ}

/-- Integer multiplicity of all untouched registers, including the pinned slot color. -/
def spectatorCard (r Q Δ : ℕ) : ℕ := (r - 1) * r ^ (Q * (Δ - 1))

@[simp] theorem card_spectator (g : Fin r) (i : Fin Δ) :
    Fintype.card (Spectator (Q := Q) g i) = spectatorCard r Q Δ := by
  simp [Spectator, spectatorCard, ← pow_mul]

/-- Exact dimensions of the weight spaces of the actual tensor eigenbasis. -/
theorem card_jointWeight (t : Fin Q) (g : Fin r) (i : Fin Δ) (w : ℕ) :
    Fintype.card {a : JointBasisIndex t g i // jointWeight a = w} =
      spectatorCard r Q Δ * (Q - 1).choose w *
        positiveMultiplicity r ^ (Q - 1 - w) * negativeMultiplicity r ^ w := by
  change Fintype.card {x : Spectator (Q := Q) g i ×
      (OtherPosition t → Fin r × Fin r) // weight negativePair x.2 = w} = _
  simpa only [JointBasisIndex, jointWeight, swapWeight, card_otherPosition,
    card_spectator, card_not_negativePair, card_negativePair] using
    card_weight_with_unused_left (ι := OtherPosition t)
      (υ := Spectator (Q := Q) g i) negativePair w

/-- The integer tail, with both local eigenspace multiplicities retained. -/
def weightedTail (q a b A R : ℕ) : ℕ :=
  ∑ w ∈ Finset.range (q + 1),
    if w ∈ Finset.Ico A (A + R) then 0 else q.choose w * a ^ (q - w) * b ^ w

theorem card_bad_jointWeight (t : Fin Q) (g : Fin r) (i : Fin Δ) (A R : ℕ) :
    Fintype.card {a : JointBasisIndex t g i // jointWeight a ∉ Finset.Ico A (A + R)} =
      spectatorCard r Q Δ *
        weightedTail (Q - 1) (positiveMultiplicity r) (negativeMultiplicity r) A R := by
  rw [SubexponentialSAT.SpectralRank.card_bad_eq_sum_fibers jointWeight (Q - 1) jointWeight_le]
  simp_rw [card_jointWeight]
  rw [SubexponentialSAT.SpectralRank.sum_bad_fin_eq_range (Q - 1) (Finset.Ico A (A + R))
    (fun w => spectatorCard r Q Δ * (Q - 1).choose w *
      positiveMultiplicity r ^ (Q - 1 - w) * negativeMultiplicity r ^ w)]
  simp only [weightedTail, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs <;> simp [Nat.mul_assoc]

theorem localMultiplicity_sum (r : ℕ) :
    positiveMultiplicity r + negativeMultiplicity r = r * r := by
  have h : Fintype.card {x : Fin r × Fin r // ¬ negativePair x} +
      Fintype.card {x : Fin r × Fin r // negativePair x} = Fintype.card (Fin r × Fin r) := by
    rw [Fintype.card_subtype_compl]
    exact Nat.sub_add_cancel (Fintype.card_subtype_le _)
  simpa only [card_not_negativePair, card_negativePair, Fintype.card_prod,
    Fintype.card_fin] using h

/-- The total number of actual coordinates has the same spectator factor as
the weight-space count; hence the normalized weight distribution is binomial. -/
theorem card_joint_via_multiplicities (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Fintype.card (Joint t g i) = spectatorCard r Q Δ *
      (positiveMultiplicity r + negativeMultiplicity r) ^ (Q - 1) := by
  rw [SubexponentialSAT.MulticolorTypes.card_joint_via_pairs, localMultiplicity_sum]
  simp only [spectatorCard]
  ac_rfl

theorem card_jointWeight_eq_swapMultiplicity (t : Fin Q) (g : Fin r) (i : Fin Δ) (w : ℕ) :
    Fintype.card {a : JointBasisIndex t g i // jointWeight a = w} =
      spectatorCard r Q Δ * swapMultiplicity r (Q - 1) w := by
  rw [card_jointWeight]
  simp only [swapMultiplicity, Nat.mul_assoc]

theorem spectatorCard_pos (hr : 2 ≤ r) : 0 < spectatorCard r Q Δ := by
  have hr0 : 0 < r := lt_of_lt_of_le (by decide : 0 < 2) hr
  have hr1 : 1 < r := lt_of_lt_of_le (by decide : 1 < 2) hr
  exact Nat.mul_pos (Nat.sub_pos_of_lt hr1) (Nat.pow_pos hr0)

/-- The uniform probability of a weight among the actual joint eigenbasis labels. -/
def jointWeightProbability (t : Fin Q) (g : Fin r) (i : Fin Δ) (w : ℕ) : ℚ :=
  (Fintype.card {a : JointBasisIndex t g i // jointWeight a = w} : ℚ) /
    (Fintype.card (Joint t g i) : ℚ)

/-- Spectator coordinates cancel from the normalized, exact weight count. -/
theorem jointWeightProbability_eq_swapProbability (hr : 2 ≤ r)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (w : ℕ) :
    jointWeightProbability t g i w = swapProbability r (Q - 1) w := by
  have hs : (spectatorCard r Q Δ : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (spectatorCard_pos hr))
  rw [jointWeightProbability, card_jointWeight_eq_swapMultiplicity,
    card_joint_via_multiplicities, multiplicities_add]
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [mul_div_mul_left _ _ hs]
  rfl

/-- The actual basis weight law is Bin(Q-1,(r-1)/(2r)), counted with multiplicity.
This is an identity of rational probabilities, not a calculation in the field. -/
theorem jointWeightProbability_eq_binomial (hr : 2 ≤ r)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (w : ℕ) :
    jointWeightProbability t g i w =
      ((Q - 1).choose w : ℚ) * (((r : ℚ) - 1) / (2 * r)) ^ w *
        (1 - ((r : ℚ) - 1) / (2 * r)) ^ (Q - 1 - w) := by
  rw [jointWeightProbability_eq_swapProbability hr]
  exact swapProbability_Q_eq_binomial r Q w
    (lt_of_lt_of_le (by decide : 0 < 2) hr)

end Multiplicities

end SubexponentialSAT.Subexp.TensorSpectrum

end OAI.Algorithms
