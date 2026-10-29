import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.Types
import OpenAISemiprime.Algorithms.SubexponentialSAT.LocalSpectrum
import OpenAISemiprime.Algorithms.SubexponentialSAT.MatrixSupport
import OpenAISemiprime.Algorithms.SubexponentialSAT.BinomialMultiplicity
import OpenAISemiprime.Algorithms.SubexponentialSAT.LayoutParameters
import OpenAISemiprime.Algorithms.SubexponentialSAT.BinomialInterpolation

namespace OAI.Algorithms

/-!
# Rank defects of diagonal operators

The rank here is the dimension of the actual range of a linear map.  The main
bound is obtained by identifying that range with the span of precisely those
basis vectors on which the diagonal coefficient is nonzero.
-/

namespace SubexponentialSAT.SpectralRank

open Module Submodule
open scoped BigOperators

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A linear map's image is spanned by its values on any basis. -/
theorem range_eq_span_basis_images (b : Basis ι K V) (f : V →ₗ[K] V) :
    LinearMap.range f = Submodule.span K (Set.range fun i => f (b i)) := by
  calc
    LinearMap.range f = LinearMap.range (b.constr K (fun i => f (b i))) := by
      rw [b.constr_self]
    _ = _ := b.constr_range K

/-- For a diagonal operator, only the nonzero diagonal entries contribute to
the range; every corresponding basis vector does belong to that range. -/
theorem range_eq_span_nonzero (b : Basis ι K V) (f : V →ₗ[K] V) (μ : ι → K)
    (hdiag : ∀ i, f (b i) = μ i • b i) :
    LinearMap.range f =
      Submodule.span K (Set.range fun i : {i // μ i ≠ 0} => b i.1) := by
  rw [range_eq_span_basis_images b f]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    dsimp only
    by_cases hi : μ i = 0
    · rw [hdiag, hi, zero_smul]
      exact Submodule.zero_mem _
    · rw [hdiag]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi : μ i.1 • b i.1 ∈
        Submodule.span K (Set.range fun j => f (b j)) := by
      rw [← hdiag]
      exact Submodule.subset_span ⟨i.1, rfl⟩
    have hi' := Submodule.smul_mem
      (Submodule.span K (Set.range fun j => f (b j))) (μ i.1)⁻¹ hi
    rw [smul_smul, inv_mul_cancel₀ i.2, one_smul] at hi'
    exact hi'

/-- Exact finite rank, counted by basis indices with nonzero eigenvalue. -/
theorem finrank_range_eq_card_nonzero [Fintype ι]
    (b : Basis ι K V) (f : V →ₗ[K] V) (μ : ι → K)
    (hdiag : ∀ i, f (b i) = μ i • b i) :
    finrank K (LinearMap.range f) = Nat.card {i // μ i ≠ 0} := by
  classical
  rw [range_eq_span_nonzero b f μ hdiag, Nat.card_eq_fintype_card]
  exact finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)

/-- Exact rank of `id - M`: each eigenvalue different from one contributes
one basis index, with its full multiplicity. -/
theorem finrank_defect_eq_card [Fintype ι]
    (b : Basis ι K V) (M : V →ₗ[K] V) (μ : ι → K)
    (hdiag : ∀ i, M (b i) = μ i • b i) :
    finrank K (LinearMap.range (LinearMap.id - M)) = Nat.card {i // μ i ≠ 1} := by
  have hdiag' : ∀ i, (LinearMap.id - M : V →ₗ[K] V) (b i) = (1 - μ i) • b i := by
    intro i
    simp only [LinearMap.sub_apply, LinearMap.id_apply, hdiag, sub_smul, one_smul]
  rw [finrank_range_eq_card_nonzero b (LinearMap.id - M) (fun i => 1 - μ i) hdiag']
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
    not_congr (sub_eq_zero.trans eq_comm))

/-- A designated set of good indices need only have eigenvalue one. Extra
unit eigenvalues outside that set can reduce the rank further. -/
theorem finrank_defect_le_card_bad [Fintype ι]
    (b : Basis ι K V) (M : V →ₗ[K] V) (μ : ι → K)
    (good : ι → Prop) [DecidablePred good]
    (hdiag : ∀ i, M (b i) = μ i • b i)
    (hgood : ∀ i, good i → μ i = 1) :
    finrank K (LinearMap.range (LinearMap.id - M)) ≤ Fintype.card {i // ¬ good i} := by
  classical
  rw [finrank_defect_eq_card b M μ hdiag, Nat.card_eq_fintype_card]
  apply Fintype.card_le_of_injective
    (fun i : {i // μ i ≠ 1} => (⟨i.1, fun hi => i.2 (hgood i.1 hi)⟩ : {i // ¬ good i}))
  intro i j hij
  apply Subtype.ext
  exact congrArg (fun x : {i // ¬ good i} => x.1) hij

/-- Weight-indexed form of the rank estimate used in equation (5.5). -/
theorem rank_defect_le_weight_bad [Fintype ι]
    (b : Basis ι K V) (M : V →ₗ[K] V) (weight : ι → ℕ)
    (eigenvalue : ℕ → K) (good : Finset ℕ)
    (hdiag : ∀ i, M (b i) = eigenvalue (weight i) • b i)
    (hgood : ∀ w ∈ good, eigenvalue w = 1) :
    finrank K (LinearMap.range (LinearMap.id - M)) ≤
      Fintype.card {i // weight i ∉ good} :=
  finrank_defect_le_card_bad b M (fun i => eigenvalue (weight i))
    (fun i => weight i ∈ good) hdiag (fun i hi => hgood (weight i) hi)

/-- A natural-number tail estimate gives the corresponding multiplied rank
bound, without introducing division in the coefficient field. -/
theorem mul_rank_defect_le_of_weight_tail [Fintype ι]
    (b : Basis ι K V) (M : V →ₗ[K] V) (weight : ι → ℕ)
    (eigenvalue : ℕ → K) (good : Finset ℕ) (c N : ℕ)
    (hdiag : ∀ i, M (b i) = eigenvalue (weight i) • b i)
    (hgood : ∀ w ∈ good, eigenvalue w = 1)
    (htail : c * Fintype.card {i // weight i ∉ good} ≤ N) :
    c * finrank K (LinearMap.range (LinearMap.id - M)) ≤ N :=
  (Nat.mul_le_mul_left c
    (rank_defect_le_weight_bad b M weight eigenvalue good hdiag hgood)).trans htail

/-- Partition the bad basis indices according to their actual finite weight.
This is an explicit equivalence, so the later multiplicity sum counts each
basis vector exactly once. -/
def badWeightEquiv (weight : ι → ℕ) (n : ℕ) (hweight : ∀ i, weight i ≤ n)
    (good : Finset ℕ) :
    {i // weight i ∉ good} ≃
      (Σ w : {w : Fin (n + 1) // w.1 ∉ good}, {i // weight i = w.1.1}) where
  toFun i := ⟨⟨⟨weight i.1, Nat.lt_succ_of_le (hweight i.1)⟩, i.2⟩, ⟨i.1, rfl⟩⟩
  invFun x := ⟨x.2.1, by rw [x.2.2]; exact x.1.2⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨⟨w, hw⟩, hg⟩, ⟨i, hi⟩⟩
    dsimp only at hi
    subst w
    rfl

/-- Exact cardinality decomposition, before assuming a binomial law. -/
theorem card_bad_eq_sum_fibers [Fintype ι]
    (weight : ι → ℕ) (n : ℕ) (hweight : ∀ i, weight i ≤ n) (good : Finset ℕ) :
    Fintype.card {i // weight i ∉ good} =
      ∑ w : {w : Fin (n + 1) // w.1 ∉ good}, Fintype.card {i // weight i = w.1.1} := by
  rw [Fintype.card_congr (badWeightEquiv weight n hweight good), Fintype.card_sigma]

/-- Rewrite a sum over bad finite weights in the ordinary range-sum form. -/
theorem sum_bad_fin_eq_range (n : ℕ) (good : Finset ℕ) (f : ℕ → ℕ) :
    (∑ w : {w : Fin (n + 1) // w.1 ∉ good}, f w.1.1) =
      ∑ w ∈ Finset.range (n + 1), if w ∈ good then 0 else f w := by
  calc
    _ = ∑ w ∈ Finset.univ.filter (fun w : Fin (n + 1) => w.1 ∉ good), f w.1 := by
      exact (Finset.sum_subtype
        (p := fun w : Fin (n + 1) => w.1 ∉ good)
        (Finset.univ.filter fun w : Fin (n + 1) => w.1 ∉ good)
        (by intro w; simp) (fun w : Fin (n + 1) => f w.1)).symm
    _ = ∑ w : Fin (n + 1), if w.1 ∈ good then 0 else f w.1 := by
      simp only [Finset.sum_filter, ite_not]
    _ = _ := Fin.sum_univ_eq_sum_range (fun w => if w ∈ good then 0 else f w) (n + 1)

/-- Rank bounded by the exact sum of the dimensions of all bad weight fibers. -/
theorem rank_defect_le_sum_fibers [Fintype ι]
    (b : Basis ι K V) (M : V →ₗ[K] V) (weight : ι → ℕ)
    (eigenvalue : ℕ → K) (good : Finset ℕ) (n : ℕ)
    (hweight : ∀ i, weight i ≤ n)
    (hdiag : ∀ i, M (b i) = eigenvalue (weight i) • b i)
    (hgood : ∀ w ∈ good, eigenvalue w = 1) :
    finrank K (LinearMap.range (LinearMap.id - M)) ≤
      ∑ w : {w : Fin (n + 1) // w.1 ∉ good}, Fintype.card {i // weight i = w.1.1} := by
  rw [← card_bad_eq_sum_fibers weight n hweight good]
  exact rank_defect_le_weight_bad b M weight eigenvalue good hdiag hgood

/-- Conditional bridge to the manuscript's binomial multiplicities. The
independently checkable `hmult` hypothesis records the tensor-basis count;
the rank inequality itself is proved rather than assumed. -/
theorem rank_defect_le_binomial_tail [Fintype ι]
    (b : Basis ι K V) (M : V →ₗ[K] V) (weight : ι → ℕ)
    (eigenvalue : ℕ → K) (good : Finset ℕ) (n copies : ℕ)
    (hweight : ∀ i, weight i ≤ n)
    (hdiag : ∀ i, M (b i) = eigenvalue (weight i) • b i)
    (hgood : ∀ w ∈ good, eigenvalue w = 1)
    (hmult : ∀ w : Fin (n + 1), Fintype.card {i // weight i = w.1} =
      copies * n.choose w.1 * 3 ^ (n - w.1)) :
    finrank K (LinearMap.range (LinearMap.id - M)) ≤
      ∑ w : {w : Fin (n + 1) // w.1 ∉ good}, copies * n.choose w.1.1 * 3 ^ (n - w.1.1) := by
  simpa only [hmult] using
    rank_defect_le_sum_fibers b M weight eigenvalue good n hweight hdiag hgood

section JointBasis

open SubexponentialSAT.Types SubexponentialSAT.LocalSpectrum

variable {Q Δ : ℕ}

/-- Labels of the genuine joint-fiber eigenbasis: an unused-word assignment
and one local eigenvector label at each active position. -/
abbrev JointBasisIndex (t : Fin Q) (i : Fin Δ) :=
  (OtherSlot i → Word Q) × (OtherPosition t → PairState)

/-- Transport the explicitly constructed product eigenbasis to the actual
joint fiber of universal types. -/
noncomputable def jointEigenbasis (K : Type*) [Field K]
    (h2 : (2 : K) ≠ 0) (t : Fin Q) (g : Bool) (i : Fin Δ) :
    Basis (JointBasisIndex t i) K (Joint t g i → K) :=
  (spectatorEigenbasis K h2).map
    (LinearEquiv.funCongrLeft K K (jointEquivPairs t g i))

@[simp] theorem jointEigenbasis_apply (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Bool) (i : Fin Δ) (a : JointBasisIndex t i)
    (u : Joint t g i) :
    jointEigenbasis K h2 t g i a u =
      spectatorEigenbasis K h2 a (jointEquivPairs t g i u) := rfl

/-- The transported basis has the expected eigenvalue under the active
coordinate permutation. No diagonalization hypothesis is used here. -/
theorem jointEigenbasis_coordinate_eigen (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Bool) (i : Fin Δ) (a : JointBasisIndex t i)
    (l : OtherPosition t) (u : Joint t g i) :
    jointEigenbasis K h2 t g i a
        ((jointEquivPairs t g i).symm
          (swapAt l (jointEquivPairs t g i u).1, (jointEquivPairs t g i u).2)) =
      localEigenvalue K (a.2 l) * jointEigenbasis K h2 t g i a u := by
  rw [jointEigenbasis_apply, Equiv.apply_symm_apply, jointEigenbasis_apply]
  exact congrFun (spectatorEigenbasis_eigen K h2 a.1 a.2 l)
    (jointEquivPairs t g i u)

end JointBasis

section JointSpectrum

open SubexponentialSAT.Types SubexponentialSAT.LocalSpectrum SubexponentialSAT.MatrixSupport SubexponentialSAT.BinomialMultiplicity

variable {Q Δ : ℕ}

/-- The concrete universal-type bit swap agrees with the independent-coordinate
swap after decomposing the joint fiber. -/
theorem jointEquivPairs_jointSwap (t : Fin Q) (g : Bool) (i : Fin Δ)
    (l : OtherPosition t) (u : Joint t g i) :
    jointEquivPairs t g i (jointSwap i t g l u) =
      (swapAt l (jointEquivPairs t g i u).1, (jointEquivPairs t g i u).2) := by
  apply Prod.ext
  · funext m
    by_cases h : m = l
    · subst m
      apply Prod.ext <;>
        simp [jointEquivPairs, jointSwap, swapPositions, swapAt, swapPair]
    · have hm : m.val ≠ l.val := fun hc => h (Subtype.ext hc)
      apply Prod.ext <;>
        simp [jointEquivPairs, jointSwap, swapPositions, swapAt, h, hm]
  · funext j m
    simp [jointEquivPairs, jointSwap, swapPositions, j.property]

/-- The actual matrix-construction swap acts diagonally on the transported
joint basis. -/
theorem jointEigenbasis_swap_eigen (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Bool) (i : Fin Δ) (a : JointBasisIndex t i)
    (l : OtherPosition t) (u : Joint t g i) :
    jointEigenbasis K h2 t g i a (jointSwap i t g l u) =
      localEigenvalue K (a.2 l) * jointEigenbasis K h2 t g i a u := by
  have hu : jointSwap i t g l u =
      (jointEquivPairs t g i).symm
        (swapAt l (jointEquivPairs t g i u).1, (jointEquivPairs t g i u).2) := by
    apply (jointEquivPairs t g i).injective
    rw [Equiv.apply_symm_apply, jointEquivPairs_jointSwap]
  rw [hu]
  exact jointEigenbasis_coordinate_eigen h2 t g i a l u

/-- Active positions at which the local basis label is the negative eigenvector. -/
def negativePositions {t : Fin Q} {i : Fin Δ} (a : JointBasisIndex t i) :
    Finset (Fin Q) :=
  (Finset.univ.filter fun l : OtherPosition t => a.2 l = (true, true)).map
    ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_negativePositions {t : Fin Q} {i : Fin Δ}
    (a : JointBasisIndex t i) (l : OtherPosition t) :
    l.val ∈ negativePositions a ↔ a.2 l = (true, true) := by
  simp only [negativePositions, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, hj, hjl⟩
    have h : j = l := Subtype.ext hjl
    simpa only [h] using hj
  · intro h
    exact ⟨l, h, rfl⟩

theorem negativePositions_subset {t : Fin Q} {i : Fin Δ}
    (a : JointBasisIndex t i) : negativePositions a ⊆ activePositions t := by
  intro l hl
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hl
  simp [activePositions, j.property]

/-- Integer weight of a joint-basis index, unaffected by the spectator words. -/
def jointWeight {t : Fin Q} {i : Fin Δ} (a : JointBasisIndex t i) : ℕ :=
  pairWeight a.2

@[simp] theorem card_negativePositions {t : Fin Q} {i : Fin Δ}
    (a : JointBasisIndex t i) : (negativePositions a).card = jointWeight a := by
  simp [negativePositions, jointWeight, pairWeight, weight, negativeSupport]

theorem jointWeight_le {t : Fin Q} {i : Fin Δ} (a : JointBasisIndex t i) :
    jointWeight a ≤ Q - 1 := by
  simpa only [jointWeight, card_otherPosition] using pairWeight_le a.2

/-- Sign profile on all positions; its value at the pinned position is one. -/
def jointSign (K : Type*) [Field K] {t : Fin Q} {i : Fin Δ}
    (a : JointBasisIndex t i) (l : Fin Q) : K :=
  if l ∈ negativePositions a then -1 else 1

@[simp] theorem jointSign_other {t : Fin Q} {i : Fin Δ}
    (a : JointBasisIndex t i) (l : OtherPosition t) :
    jointSign K a l.val = localEigenvalue K (a.2 l) := by
  simp only [jointSign, mem_negativePositions, localEigenvalue]

theorem jointEigenbasis_sign_eigen (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Bool) (i : Fin Δ) (a : JointBasisIndex t i)
    (l : OtherPosition t) (u : Joint t g i) :
    jointEigenbasis K h2 t g i a (jointSwap i t g l u) =
      jointSign K a l.val * jointEigenbasis K h2 t g i a u := by
  rw [jointSign_other]
  exact jointEigenbasis_swap_eigen h2 t g i a l u

/-- Exact multiplicity on the actual joint eigenbasis, including all unused bits. -/
theorem card_jointWeight (t : Fin Q) (i : Fin Δ) (w : ℕ) :
    Fintype.card {a : JointBasisIndex t i // jointWeight a = w} =
      2 ^ (Q * (Δ - 1)) * (Q - 1).choose w * 3 ^ (Q - 1 - w) := by
  change Fintype.card
      {x : (OtherSlot i → Word Q) × (OtherPosition t → Bool × Bool) //
        pairWeight x.2 = w} = _
  rw [card_pair_weight_with_unused_left]
  simp only [card_otherPosition, card_otherSlotWords]

/-- Exact bad-weight cardinality for the concrete joint eigenbasis. -/
theorem card_bad_jointWeight (t : Fin Q) (i : Fin Δ) (A R : ℕ) :
    Fintype.card {a : JointBasisIndex t i // jointWeight a ∉ Finset.Ico A (A + R)} =
      2 ^ (Q * (Δ - 1)) * SubexponentialSAT.LayoutParameters.intervalTail (Q - 1) A R := by
  rw [card_bad_eq_sum_fibers jointWeight (Q - 1) jointWeight_le]
  simp_rw [card_jointWeight]
  rw [sum_bad_fin_eq_range (Q - 1) (Finset.Ico A (A + R))
    (fun w => 2 ^ (Q * (Δ - 1)) * (Q - 1).choose w * 3 ^ (Q - 1 - w))]
  simp only [SubexponentialSAT.LayoutParameters.intervalTail, SubexponentialSAT.LayoutParameters.binomialWeight,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs <;> simp [Nat.mul_assoc]

/-- For this concrete basis, the integer binomial tail gives the desired
relative rank bound. Only the operator's eigenaction remains to be supplied. -/
theorem joint_rank_defect_of_eigenaction (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Bool) (i : Fin Δ)
    (M : (Joint t g i → K) →ₗ[K] (Joint t g i → K))
    (eigenvalue : ℕ → K) (A R : ℕ)
    (hdiag : ∀ a, M (jointEigenbasis K h2 t g i a) =
      eigenvalue (jointWeight a) • jointEigenbasis K h2 t g i a)
    (hgood : ∀ w ∈ Finset.Ico A (A + R), eigenvalue w = 1)
    (htail : 8 * Δ * SubexponentialSAT.LayoutParameters.intervalTail (Q - 1) A R ≤ 4 ^ (Q - 1)) :
    8 * Δ * finrank K (LinearMap.range (LinearMap.id - M)) ≤
      Fintype.card (Joint t g i) := by
  have h := rank_defect_le_weight_bad (jointEigenbasis K h2 t g i) M
    jointWeight eigenvalue (Finset.Ico A (A + R)) hdiag hgood
  rw [card_bad_jointWeight] at h
  calc
    _ ≤ (8 * Δ) * (2 ^ (Q * (Δ - 1)) *
        SubexponentialSAT.LayoutParameters.intervalTail (Q - 1) A R) := Nat.mul_le_mul_left _ h
    _ = 2 ^ (Q * (Δ - 1)) *
        (8 * Δ * SubexponentialSAT.LayoutParameters.intervalTail (Q - 1) A R) := by ac_rfl
    _ ≤ 2 ^ (Q * (Δ - 1)) * 4 ^ (Q - 1) := Nat.mul_le_mul_left _ htail
    _ = Fintype.card (Joint t g i) := by rw [card_joint_via_pairs]; ac_rfl

end JointSpectrum

section MatrixRank

open SubexponentialSAT.Types SubexponentialSAT.MatrixSupport SubexponentialSAT.BinomialInterpolation

variable {Q Δ : ℕ}

/-- The weight-dependent scalar appearing in the spectrum of the matrix (5.4). -/
def coefficientEigenvalue (R : ℕ) (c : ℕ → K) (w : ℕ) : K :=
  (-1 : K) ^ w * ∑ j ∈ Finset.range R, c j * (w.choose j : K)

/-- Spectral action of the shared concrete matrix on the actual joint basis. -/
theorem jointMatrix_eigenbasis (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Bool) (i : Fin Δ) (R : ℕ) (c : ℕ → K)
    (a : JointBasisIndex t i) :
    (jointMatrix i t g R c).mulVecLin (jointEigenbasis K h2 t g i a) =
      coefficientEigenvalue R c (jointWeight a) • jointEigenbasis K h2 t g i a := by
  rw [Matrix.mulVecLin_apply]
  have heig := jointMatrix_eigenvector i t g R c (jointSign K a)
    (jointEigenbasis K h2 t g i a) (jointEigenbasis_sign_eigen h2 t g i a)
  have hvalue : matrixEigenvalue t R c (jointSign K a) =
      coefficientEigenvalue R c (jointWeight a) := by
    change matrixEigenvalue t R c
        (fun l => if l ∈ negativePositions a then -1 else 1) =
      (-1 : K) ^ jointWeight a *
        ∑ j ∈ Finset.range R, c j * (jointWeight a).choose j
    simpa only [card_negativePositions] using
      matrixEigenvalue_signIndicator h2 t R c (negativePositions a)
        (negativePositions_subset a)
  rw [hvalue] at heig
  exact heig

/-- Equation (5.5) for the actual matrix used by the support construction.
The coefficient interpolation and finite integer tail are the only numerical
hypotheses; the spectrum, multiplicities, and rank bound are all derived. -/
theorem jointMatrix_rank_bound (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Bool) (i : Fin Δ) (A R : ℕ) (c : ℕ → K)
    (hcoeff : ∀ w ∈ Finset.Ico A (A + R),
      (∑ j ∈ Finset.range R, c j * (w.choose j : K)) = (-1 : K) ^ w)
    (htail : 8 * Δ * SubexponentialSAT.LayoutParameters.intervalTail (Q - 1) A R ≤ 4 ^ (Q - 1)) :
    8 * Δ * finrank K
      (LinearMap.range (LinearMap.id - (jointMatrix i t g R c).mulVecLin)) ≤
        Fintype.card (Joint t g i) := by
  apply joint_rank_defect_of_eigenaction h2 t g i
    (jointMatrix i t g R c).mulVecLin (coefficientEigenvalue R c) A R
  · exact jointMatrix_eigenbasis h2 t g i R c
  · intro w hw
    rw [coefficientEigenvalue, hcoeff w hw, ← mul_pow]
    simp
  · exact htail

/-- The constructed parity-interpolation coefficients discharge the entire
spectral interpolation hypothesis of the concrete rank bound. -/
theorem jointMatrix_parity_rank_bound (h2 : (2 : K) ≠ 0)
    (t : Fin Q) (g : Bool) (i : Fin Δ) (A R : ℕ)
    (htail : 8 * Δ * SubexponentialSAT.LayoutParameters.intervalTail (Q - 1) A R ≤ 4 ^ (Q - 1)) :
    8 * Δ * finrank K
      (LinearMap.range (LinearMap.id -
        (jointMatrix i t g R (extendCoefficients (parityCoefficients (K := K) A R))).mulVecLin)) ≤
          Fintype.card (Joint t g i) := by
  apply jointMatrix_rank_bound h2 t g i A R
    (extendCoefficients (parityCoefficients (K := K) A R))
  · intro w hw
    exact sum_range_extend_parity_of_mem A R w
      (Finset.mem_Ico.mp hw).1 (Finset.mem_Ico.mp hw).2
  · exact htail

end MatrixRank

end SubexponentialSAT.SpectralRank

end OAI.Algorithms
