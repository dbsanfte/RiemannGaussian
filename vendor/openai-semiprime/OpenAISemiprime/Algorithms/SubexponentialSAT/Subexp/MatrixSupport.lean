import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.MulticolorTypes

namespace OAI.Algorithms

/-!
# Restricted support of the multicolor interpolation matrices

The multicolor register permutations and the products of (1 - J_l) / 2 are constructed
explicitly.  The support conclusion is derived from their sublist expansion.
-/

namespace SubexponentialSAT.Subexp.MatrixSupport

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ}

/-- Mismatches compare the column head against the row's selected slot. -/
def mismatches (i : Fin Δ) (u y : UniversalType r Q Δ) : Finset (Fin Q) :=
  Finset.univ.filter (fun l => y.head l ≠ u.slot i l)

@[simp] theorem mem_mismatches (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    l ∈ mismatches i u y ↔ y.head l ≠ u.slot i l := by
  simp [mismatches]

/-- Swap the head and selected slot register at each selected position. -/
def swapPositions (i : Fin Δ) (s : Finset (Fin Q)) (u : UniversalType r Q Δ) :
    UniversalType r Q Δ where
  head l := if l ∈ s then u.slot i l else u.head l
  slot j l := if j = i then
    if l ∈ s then u.head l else u.slot j l
    else u.slot j l

@[simp] theorem swapPositions_head (i : Fin Δ) (s : Finset (Fin Q))
    (u : UniversalType r Q Δ) (l : Fin Q) :
    (swapPositions i s u).head l = if l ∈ s then u.slot i l else u.head l := rfl

@[simp] theorem swapPositions_slot_same (i : Fin Δ) (s : Finset (Fin Q))
    (u : UniversalType r Q Δ) (l : Fin Q) :
    (swapPositions i s u).slot i l =
      if l ∈ s then u.head l else u.slot i l := by
  simp [swapPositions]

@[simp] theorem swapPositions_slot_other (i j : Fin Δ) (h : j ≠ i)
    (s : Finset (Fin Q)) (u : UniversalType r Q Δ) (l : Fin Q) :
    (swapPositions i s u).slot j l = u.slot j l := by
  simp [swapPositions, h]

theorem swapPositions_pair_of_mem (i : Fin Δ) (s : Finset (Fin Q))
    (u : UniversalType r Q Δ) {l : Fin Q} (hl : l ∈ s) :
    ((swapPositions i s u).head l, (swapPositions i s u).slot i l) =
      Prod.swap (u.head l, u.slot i l) := by
  simp [hl, Prod.swap]

@[simp] theorem swapPositions_empty (i : Fin Δ) (u : UniversalType r Q Δ) :
    swapPositions i ∅ u = u := by
  apply UniversalType.ext
  · funext l
    simp
  · funext j l
    simp [swapPositions]

theorem swapPositions_involutive (i : Fin Δ) (s : Finset (Fin Q))
    (u : UniversalType r Q Δ) :
    swapPositions i s (swapPositions i s u) = u := by
  apply UniversalType.ext
  · funext l
    by_cases hl : l ∈ s <;> simp [hl]
  · funext j l
    by_cases hj : j = i
    · subst j
      by_cases hl : l ∈ s <;> simp [hl]
    · simp [swapPositions_slot_other, hj]

theorem swapPositions_insert (i : Fin Δ) (s : Finset (Fin Q))
    (a : Fin Q) (ha : a ∉ s) (u : UniversalType r Q Δ) :
    swapPositions i (insert a s) u =
      swapPositions i s (swapPositions i {a} u) := by
  apply UniversalType.ext
  · funext l
    by_cases hla : l = a
    · subst l
      simp [ha]
    · by_cases hl : l ∈ s <;> simp [hl, hla]
  · funext j l
    by_cases hj : j = i
    · subst j
      by_cases hla : l = a
      · subst l
        simp [ha]
      · by_cases hl : l ∈ s <;> simp [hl, hla]
    · simp [swapPositions_slot_other, hj]

theorem swapPositions_commute (i : Fin Δ) (s b : Finset (Fin Q))
    (u : UniversalType r Q Δ) :
    swapPositions i s (swapPositions i b u) =
      swapPositions i b (swapPositions i s u) := by
  apply UniversalType.ext
  · funext l
    by_cases hs : l ∈ s <;> by_cases hr : l ∈ b <;> simp [hs, hr]
  · funext j l
    by_cases hj : j = i
    · subst j
      by_cases hs : l ∈ s <;> by_cases hr : l ∈ b <;> simp [hs, hr]
    · simp [swapPositions_slot_other, hj]

/-- Multiplying the full permutation by an omitted subset cancels those positions. -/
theorem swapPositions_sdiff (i : Fin Δ) (L B : Finset (Fin Q)) (hB : B ⊆ L)
    (u : UniversalType r Q Δ) :
    swapPositions i B (swapPositions i L u) = swapPositions i (L \ B) u := by
  apply UniversalType.ext
  · funext l
    by_cases hb : l ∈ B
    · simp [hb, hB hb]
    · by_cases hl : l ∈ L <;> simp [hb, hl]
  · funext j l
    by_cases hj : j = i
    · subst j
      by_cases hb : l ∈ B
      · simp [hb, hB hb]
      · by_cases hl : l ∈ L <;> simp [hb, hl]
    · simp [swapPositions_slot_other, hj]

/-- Ordered application of the position involutions. -/
def applySwaps (i : Fin Δ) : List (Fin Q) → UniversalType r Q Δ → UniversalType r Q Δ
  | [], u => u
  | a :: as, u => applySwaps i as (swapPositions i {a} u)

theorem applySwaps_eq_swapPositions (i : Fin Δ) (as : List (Fin Q))
    (ha : as.Nodup) (u : UniversalType r Q Δ) :
    applySwaps i as u = swapPositions i as.toFinset u := by
  induction as generalizing u with
  | nil => simp [applySwaps]
  | cons a as ih =>
    rw [List.nodup_cons] at ha
    simp only [applySwaps, List.toFinset_cons]
    rw [ih ha.2, swapPositions_insert]
    simpa using ha.1

theorem applySwaps_head_of_not_mem (i : Fin Δ) (as : List (Fin Q))
    (u : UniversalType r Q Δ) {l : Fin Q} (hl : l ∉ as) :
    (applySwaps i as u).head l = u.head l := by
  induction as generalizing u with
  | nil => rfl
  | cons a as ih =>
    simp only [List.mem_cons, not_or] at hl
    rw [applySwaps, ih _ hl.2]
    simp [hl.1]

/-- Any possible mismatches are in the omitted set, together with position t. -/
theorem mismatches_card_le (i : Fin Δ) (t : Fin Q) (A : Finset (Fin Q))
    (u y : UniversalType r Q Δ)
    (h : ∀ l, l ≠ t → l ∉ A → y.head l = u.slot i l) :
    (mismatches i u y).card ≤ A.card + 1 := by
  have hs : mismatches i u y ⊆ insert t A := by
    intro l hl
    by_cases hlt : l = t
    · simp [hlt]
    · have hlA : l ∈ A := by
        by_contra hn
        exact ((mem_mismatches i u y l).mp hl) (h l hlt hn)
      exact Finset.mem_insert_of_mem hlA
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le t A)

section Operators

variable {K : Type*} [Field K]

/-- The actual ordered product of Id - J_l, acting by pullback. -/
def differenceProduct (i : Fin Δ) :
    List (Fin Q) → (UniversalType r Q Δ → K) → UniversalType r Q Δ → K
  | [], f, u => f u
  | a :: as, f, u =>
      differenceProduct i as f u -
      differenceProduct i as f (swapPositions i {a} u)

/-- The product of the normalized projectors (Id - J_l) / 2. -/
def projectorProduct (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) : K :=
  (2 : K)⁻¹ ^ as.length * differenceProduct i as f u

/-- Full expansion: one term for each choice of the permutation part of a factor. -/
theorem differenceProduct_expansion (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    differenceProduct i as f u =
      (as.sublists'.map (fun bs =>
        (-1 : K) ^ bs.length * f (applySwaps i bs u))).sum := by
  induction as generalizing u with
  | nil => simp [differenceProduct, applySwaps]
  | cons a as ih =>
    simp only [differenceProduct, ih, List.sublists'_cons, List.map_append,
      List.sum_append, List.map_map, Function.comp_def, List.length_cons,
      applySwaps, pow_succ]
    simp only [mul_assoc, mul_comm (-1 : K) ]
    simp only [← mul_assoc]
    rw [List.sum_map_mul_right]
    ring

/-- The normalized expansion is valid even when some coefficients cancel. -/
theorem projectorProduct_expansion (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    projectorProduct i as f u =
      (2 : K)⁻¹ ^ as.length *
        (as.sublists'.map (fun bs =>
          (-1 : K) ^ bs.length * f (applySwaps i bs u))).sum := by
  rw [projectorProduct, differenceProduct_expansion]

/-- The full permutation at t acts at every other position. -/
def activePositions (t : Fin Q) : Finset (Fin Q) := Finset.univ.erase t

/-- A column basis vector, in function coordinates. -/
def delta (y : UniversalType r Q Δ) (x : UniversalType r Q Δ) : K :=
  if x = y then 1 else 0

/-- Elementary symmetric sum of degree j in the actual normalized projectors. -/
noncomputable def elementaryProjector (i : Fin Δ) (t : Fin Q) (j : ℕ)
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) : K :=
  ∑ A ∈ (activePositions t).powersetCard j,
    projectorProduct i A.toList f u

/-- Equation (3.5), evaluated on the column basis vector indexed by y.
The outer full permutation is pullback by swapPositions.
-/
noncomputable def matrixEntry (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K)
    (u y : UniversalType r Q Δ) : K :=
  ∑ j ∈ Finset.range R,
    c j * elementaryProjector i t j (delta y) (swapPositions i (activePositions t) u)

/-- Every subword of omitted flips leaves all other positions equal to the original slot. -/
theorem applySwaps_mismatches_card_le (i : Fin Δ) (t : Fin Q)
    (as : List (Fin Q)) (u : UniversalType r Q Δ) :
    (mismatches i u (applySwaps i as (swapPositions i (activePositions t) u))).card ≤
      as.toFinset.card + 1 := by
  apply mismatches_card_le i t as.toFinset
  intro l hlt hl
  rw [applySwaps_head_of_not_mem i as _ (by simpa using hl)]
  simp [activePositions, hlt]

theorem delta_applySwaps_eq_zero (i : Fin Δ) (t : Fin Q) (A : Finset (Fin Q))
    (as : List (Fin Q)) (has : as.Sublist A.toList) (u y : UniversalType r Q Δ)
    (hbad : A.card + 1 < (mismatches i u y).card) :
    (delta y (applySwaps i as (swapPositions i (activePositions t) u)) : K) = 0 := by
  unfold delta
  split_ifs with heq
  · have hbound := applySwaps_mismatches_card_le i t as u
    rw [heq] at hbound
    have hsub : as.toFinset ⊆ A := by
      intro l hl
      have hm : l ∈ as := by simpa using hl
      have hm' : l ∈ A.toList := has.subset hm
      simpa using hm'
    have hc := Finset.card_le_card hsub
    omega
  · rfl

/-- Each elementary projector term has restricted support after the full permutation. -/
theorem projectorProduct_delta_eq_zero (i : Fin Δ) (t : Fin Q)
    (A : Finset (Fin Q)) (u y : UniversalType r Q Δ)
    (hbad : A.card + 1 < (mismatches i u y).card) :
    projectorProduct i A.toList (delta y)
      (swapPositions i (activePositions t) u) = (0 : K) := by
  rw [projectorProduct_expansion]
  suffices hsum :
      (A.toList.sublists'.map (fun bs =>
        (-1 : K) ^ bs.length *
          delta y (applySwaps i bs (swapPositions i (activePositions t) u)))).sum = 0 by
    rw [hsum, mul_zero]
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨bs, hbs, rfl⟩ := List.mem_map.mp ha
  have hsub := List.mem_sublists'.mp hbs
  rw [delta_applySwaps_eq_zero i t A bs hsub u y hbad, mul_zero]

/-- The restricted-support conclusion for the actual matrix formula, with no
assumption on the coefficients or on whether expansion terms cancel. -/
theorem matrixEntry_support (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K)
    (u y : UniversalType r Q Δ) (hne : matrixEntry i t R c u y ≠ 0) :
    (mismatches i u y).card ≤ R := by
  by_contra h
  have hbad : R < (mismatches i u y).card := by omega
  apply hne
  unfold matrixEntry
  apply Finset.sum_eq_zero
  intro j hj
  have hjR : j < R := Finset.mem_range.mp hj
  have he : elementaryProjector i t j (delta y)
      (swapPositions i (activePositions t) u) = (0 : K) := by
    unfold elementaryProjector
    apply Finset.sum_eq_zero
    intro A hA
    have hcard : A.card = j := (Finset.mem_powersetCard.mp hA).2
    apply projectorProduct_delta_eq_zero i t A u y
    omega
  rw [he, mul_zero]

/-- The matrix on the joint fiber used by the universal-block construction. -/
noncomputable def jointMatrix (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (R : ℕ) (c : ℕ → K) :
    Matrix (Joint t g i) (Joint t g i) K :=
  fun u y => matrixEntry i t R c u.val y.val

theorem jointMatrix_support (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (R : ℕ) (c : ℕ → K) (u y : Joint t g i)
    (hne : jointMatrix i t g R c u y ≠ 0) :
    (mismatches i u.val y.val).card ≤ R :=
  matrixEntry_support i t R c u.val y.val hne

/-- The permutation operator associated with any set of positions. -/
def permutationLinear (i : Fin Δ) (s : Finset (Fin Q)) :
    Module.End K (UniversalType r Q Δ → K) where
  toFun f u := f (swapPositions i s u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem permutationLinear_apply (i : Fin Δ) (s : Finset (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    permutationLinear i s f u = f (swapPositions i s u) := rfl

theorem permutationLinear_sq (i : Fin Δ) (s : Finset (Fin Q)) :
    (permutationLinear (r := r) (K := K) i s) * permutationLinear i s = 1 := by
  apply LinearMap.ext
  intro f
  funext u
  exact congrArg f (swapPositions_involutive i s u)

theorem permutationLinear_commute (i : Fin Δ) (s b : Finset (Fin Q)) :
    Commute (permutationLinear (r := r) (K := K) i s) (permutationLinear i b) := by
  change permutationLinear i s * permutationLinear i b =
    permutationLinear i b * permutationLinear i s
  apply LinearMap.ext
  intro f
  funext u
  exact congrArg f (swapPositions_commute i b s u)

/-- Linear-map presentation of the ordered product of Id - J. -/
def differenceLinear (i : Fin Δ) :
    List (Fin Q) → Module.End K (UniversalType r Q Δ → K)
  | [] => 1
  | a :: as => (1 - permutationLinear i {a}) * differenceLinear i as

@[simp] theorem differenceLinear_apply (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    differenceLinear i as f u = differenceProduct i as f u := by
  induction as generalizing u with
  | nil => rfl
  | cons a as ih =>
    change differenceLinear i as f u -
      differenceLinear i as f (swapPositions i {a} u) = _
    rw [ih, ih]
    rfl

/-- A linear map for a product of normalized projectors. -/
def projectorLinear (i : Fin Δ) (as : List (Fin Q)) :
    Module.End K (UniversalType r Q Δ → K) :=
  (2 : K)⁻¹ ^ as.length • differenceLinear i as

@[simp] theorem projectorLinear_apply (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    projectorLinear i as f u = projectorProduct i as f u := by
  simp [projectorLinear, projectorProduct]

/-- The endomorphism in (3.5), before restriction to the joint fiber. -/
noncomputable def matrixLinear (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K) :
    Module.End K (UniversalType r Q Δ → K) :=
  permutationLinear i (activePositions t) *
    ∑ j ∈ Finset.range R,
      c j • ∑ A ∈ (activePositions t).powersetCard j, projectorLinear i A.toList

@[simp] theorem matrixLinear_apply (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K)
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    matrixLinear i t R c f u =
      ∑ j ∈ Finset.range R,
        c j * elementaryProjector i t j f (swapPositions i (activePositions t) u) := by
  simp [matrixLinear, elementaryProjector, Module.End.mul_apply]

theorem matrixEntry_eq_matrixLinear (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K)
    (u y : UniversalType r Q Δ) :
    matrixEntry i t R c u y = matrixLinear i t R c (delta y) u := by
  simp [matrixEntry]

/-- Extend a vector on the joint fiber by zero, using its coordinate basis. -/
noncomputable def extendJoint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (f : Joint t g i → K) : UniversalType r Q Δ → K :=
  ∑ y : Joint t g i, f y • delta y.val

@[simp] theorem extendJoint_on_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (f : Joint t g i → K) (u : Joint t g i) :
    extendJoint i t g f u.val = f u := by
  classical
  simp [extendJoint, delta, Subtype.val_inj]

theorem extendJoint_off_joint (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (f : Joint t g i → K) (u : UniversalType r Q Δ)
    (hu : u ∉ joint t g i) :
    extendJoint i t g f u = 0 := by
  classical
  simp only [extendJoint, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro y hy
  have hne : u ≠ y.val := by
    intro heq
    apply hu
    rw [heq]
    exact y.property
  simp [delta, hne]

/-- Matrix-vector multiplication is exactly the concrete projector action.
This supplies the bridge needed for a spectral proof of the rank bound.
-/
theorem jointMatrix_mulVec (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (R : ℕ) (c : ℕ → K) (f : Joint t g i → K) (u : Joint t g i) :
    (jointMatrix i t g R c).mulVec f u =
      matrixLinear i t R c (extendJoint i t g f) u.val := by
  classical
  simp only [Matrix.mulVec, dotProduct, jointMatrix, matrixEntry_eq_matrixLinear,
    extendJoint, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y hy
  exact mul_comm _ _

theorem swapPositions_mem_joint_iff (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (s : Finset (Fin Q)) (ht : t ∉ s) (u : UniversalType r Q Δ) :
    swapPositions i s u ∈ joint t g i ↔ u ∈ joint t g i := by
  simp [ht]

/-- The actual position involution restricted to the joint fiber. -/
def jointSwap (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (l : OtherPosition t) (u : Joint t g i) : Joint t g i :=
  ⟨swapPositions i {l.val} u.val,
    (swapPositions_mem_joint_iff i t g {l.val}
      (by simpa using Ne.symm l.property) u.val).mpr u.property⟩

@[simp] theorem jointSwap_val (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (l : OtherPosition t) (u : Joint t g i) :
    (jointSwap i t g l u).val = swapPositions i {l.val} u.val := rfl

/-- A simultaneous eigenvector on the fiber extends to one on the full type space. -/
theorem extendJoint_swap_eigen (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (f : Joint t g i → K) (sign : Fin Q → K)
    (heig : ∀ l : OtherPosition t, ∀ u : Joint t g i,
      f (jointSwap i t g l u) = sign l.val * f u)
    (l : OtherPosition t) (u : UniversalType r Q Δ) :
    extendJoint i t g f (swapPositions i {l.val} u) =
      sign l.val * extendJoint i t g f u := by
  classical
  by_cases hu : u ∈ joint t g i
  · let u' : Joint t g i := ⟨u, hu⟩
    change extendJoint i t g f (jointSwap i t g l u').val =
      sign l.val * extendJoint i t g f u'.val
    rw [extendJoint_on_joint i t g f (jointSwap i t g l u'),
      extendJoint_on_joint i t g f u']
    exact heig l u'
  · have hs : swapPositions i {l.val} u ∉ joint t g i :=
      fun h => hu ((swapPositions_mem_joint_iff i t g {l.val}
        (by simpa using Ne.symm l.property) u).mp h)
    rw [extendJoint_off_joint i t g f _ hs, extendJoint_off_joint i t g f _ hu]
    simp

theorem projectorProduct_cons (i : Fin Δ) (a : Fin Q) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    projectorProduct i (a :: as) f u =
      (projectorProduct i as f u -
        projectorProduct i as f (swapPositions i {a} u)) / 2 := by
  simp only [projectorProduct, List.length_cons, differenceProduct,
    pow_succ, div_eq_mul_inv]
  ring

/-- The scaled product definition is precisely the product of normalized factors. -/
theorem projectorLinear_cons (i : Fin Δ) (a : Fin Q) (as : List (Fin Q)) :
    projectorLinear (r := r) (K := K) i (a :: as) =
      ((2 : K)⁻¹ • (1 - permutationLinear i {a})) * projectorLinear i as := by
  apply LinearMap.ext
  intro f
  funext u
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, Pi.smul_apply, Pi.sub_apply, permutationLinear_apply,
    projectorLinear_apply, smul_eq_mul]
  rw [projectorProduct_cons, div_eq_mul_inv, mul_comm]

/-- One normalized local factor, for the executable elementary-symmetric recurrence. -/
def positionProjector (i : Fin Δ) (l : Fin Q) :
    Module.End K (UniversalType r Q Δ → K) :=
  (2 : K)⁻¹ • (1 - permutationLinear i {l})

theorem positionProjector_commute (i : Fin Δ) (a b : Fin Q) :
    Commute (positionProjector (r := r) (K := K) i a) (positionProjector i b) := by
  have h := permutationLinear_commute (r := r) (K := K) i {a} {b}
  have h0 : Commute (1 - permutationLinear (r := r) (K := K) i {a})
      (1 - permutationLinear i {b}) :=
    (Commute.one_right _).sub_right ((Commute.one_left _).sub_left h)
  exact (h0.smul_left ((2 : K)⁻¹)).smul_right ((2 : K)⁻¹)

theorem projectorLinear_eq_list_prod (i : Fin Δ) (as : List (Fin Q)) :
    projectorLinear (r := r) (K := K) i as =
      (as.map (positionProjector i)).prod := by
  induction as with
  | nil =>
    apply LinearMap.ext
    intro f
    funext u
    simp [projectorLinear, differenceLinear]
  | cons a as ih =>
    rw [projectorLinear_cons, List.map_cons, List.prod_cons, ih]
    rfl

/-- Eigenaction of an ordered product of the normalized projectors. -/
theorem projectorProduct_eigen (i : Fin Δ) (as : List (Fin Q))
    (sign : Fin Q → K) (f : UniversalType r Q Δ → K)
    (heig : ∀ l ∈ as, ∀ u, f (swapPositions i {l} u) = sign l * f u)
    (u : UniversalType r Q Δ) :
    projectorProduct i as f u =
      (as.map (fun l => (1 - sign l) / 2)).prod * f u := by
  induction as generalizing u with
  | nil => simp [projectorProduct, differenceProduct]
  | cons a as ih =>
    have htail : ∀ l ∈ as, ∀ u, f (swapPositions i {l} u) = sign l * f u :=
      fun l hl => heig l (List.mem_cons_of_mem a hl)
    rw [projectorProduct_cons, ih htail, ih htail, heig a (by simp)]
    simp only [List.map_cons, List.prod_cons]
    ring

theorem applySwaps_eigen (i : Fin Δ) (as : List (Fin Q))
    (sign : Fin Q → K) (f : UniversalType r Q Δ → K)
    (heig : ∀ l ∈ as, ∀ u, f (swapPositions i {l} u) = sign l * f u)
    (u : UniversalType r Q Δ) :
    f (applySwaps i as u) = (as.map sign).prod * f u := by
  induction as generalizing u with
  | nil => simp [applySwaps]
  | cons a as ih =>
    have htail : ∀ l ∈ as, ∀ u, f (swapPositions i {l} u) = sign l * f u :=
      fun l hl => heig l (List.mem_cons_of_mem a hl)
    rw [applySwaps, ih htail, heig a (by simp)]
    simp only [List.map_cons, List.prod_cons]
    ring

theorem swapPositions_eigen (i : Fin Δ) (s : Finset (Fin Q))
    (sign : Fin Q → K) (f : UniversalType r Q Δ → K)
    (heig : ∀ l ∈ s, ∀ u, f (swapPositions i {l} u) = sign l * f u)
    (u : UniversalType r Q Δ) :
    f (swapPositions i s u) = (∏ l ∈ s, sign l) * f u := by
  have hp := applySwaps_eq_swapPositions i s.toList s.nodup_toList u
  simp only [Finset.toList_toFinset] at hp
  rw [← hp]
  have heig' : ∀ l ∈ s.toList, ∀ u, f (swapPositions i {l} u) = sign l * f u :=
    fun l hl => heig l (by simpa using hl)
  rw [applySwaps_eigen i s.toList sign f heig']
  rw [← List.prod_toFinset sign s.nodup_toList, Finset.toList_toFinset]

theorem elementaryProjector_eigen (i : Fin Δ) (t : Fin Q) (j : ℕ)
    (sign : Fin Q → K) (f : UniversalType r Q Δ → K)
    (heig : ∀ l ∈ activePositions t, ∀ u, f (swapPositions i {l} u) = sign l * f u)
    (u : UniversalType r Q Δ) :
    elementaryProjector i t j f u =
      (∑ A ∈ (activePositions t).powersetCard j,
        ∏ l ∈ A, (1 - sign l) / 2) * f u := by
  unfold elementaryProjector
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A hA
  have hsub := (Finset.mem_powersetCard.mp hA).1
  have heig' : ∀ l ∈ A.toList, ∀ u, f (swapPositions i {l} u) = sign l * f u :=
    fun l hl => heig l (hsub (by simpa using hl))
  rw [projectorProduct_eigen i A.toList sign f heig']
  rw [← List.prod_toFinset (fun l => (1 - sign l) / 2) A.nodup_toList,
    Finset.toList_toFinset]

/-- Eigenvalue obtained by multiplying the position eigenvalues and evaluating
the elementary symmetric polynomial on (1 - sign) / 2. -/
noncomputable def matrixEigenvalue (t : Fin Q) (R : ℕ)
    (c : ℕ → K) (sign : Fin Q → K) : K :=
  (∏ l ∈ activePositions t, sign l) *
    ∑ j ∈ Finset.range R, c j *
      ∑ A ∈ (activePositions t).powersetCard j, ∏ l ∈ A, (1 - sign l) / 2

/-- Simultaneous position eigenvectors are eigenvectors of the constructed map. -/
theorem matrixLinear_eigen (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K)
    (sign : Fin Q → K) (f : UniversalType r Q Δ → K)
    (heig : ∀ l ∈ activePositions t, ∀ u, f (swapPositions i {l} u) = sign l * f u)
    (u : UniversalType r Q Δ) :
    matrixLinear i t R c f u =
      ((∏ l ∈ activePositions t, sign l) *
        ∑ j ∈ Finset.range R, c j *
          ∑ A ∈ (activePositions t).powersetCard j, ∏ l ∈ A, (1 - sign l) / 2) * f u := by
  rw [matrixLinear_apply]
  simp_rw [elementaryProjector_eigen i t _ sign f heig,
    swapPositions_eigen i (activePositions t) sign f heig]
  let P : K := ∏ l ∈ activePositions t, sign l
  let E : ℕ → K := fun j =>
    ∑ A ∈ (activePositions t).powersetCard j, ∏ l ∈ A, (1 - sign l) / 2
  change (∑ j ∈ Finset.range R, c j * (E j * (P * f u))) =
    (P * (∑ j ∈ Finset.range R, c j * E j)) * f u
  calc
    _ = (∑ j ∈ Finset.range R, c j * E j) * (P * f u) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by ring

/-- Concrete matrix eigenaction on the joint fiber.  No eigenvalue or
support conclusion is assumed; only the individual position actions are given. -/
theorem jointMatrix_eigen (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (R : ℕ) (c : ℕ → K) (sign : Fin Q → K) (f : Joint t g i → K)
    (heig : ∀ l : OtherPosition t, ∀ u : Joint t g i,
      f (jointSwap i t g l u) = sign l.val * f u)
    (u : Joint t g i) :
    (jointMatrix i t g R c).mulVec f u =
      ((∏ l ∈ activePositions t, sign l) *
        ∑ j ∈ Finset.range R, c j *
          ∑ A ∈ (activePositions t).powersetCard j, ∏ l ∈ A, (1 - sign l) / 2) * f u := by
  rw [jointMatrix_mulVec]
  have heig' : ∀ l ∈ activePositions t, ∀ v,
      extendJoint i t g f (swapPositions i {l} v) = sign l * extendJoint i t g f v := by
    intro l hl v
    have hlt : l ≠ t := (Finset.mem_erase.mp hl).1
    exact extendJoint_swap_eigen i t g f sign heig ⟨l, hlt⟩ v
  rw [matrixLinear_eigen i t R c sign (extendJoint i t g f) heig',
    extendJoint_on_joint]

theorem jointMatrix_eigenvector (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (R : ℕ) (c : ℕ → K) (sign : Fin Q → K) (f : Joint t g i → K)
    (heig : ∀ l : OtherPosition t, ∀ u : Joint t g i,
      f (jointSwap i t g l u) = sign l.val * f u) :
    (jointMatrix i t g R c).mulVec f = matrixEigenvalue t R c sign • f := by
  funext u
  exact jointMatrix_eigen i t g R c sign f heig u

/-- The distinguished position is always a mismatch on this joint fiber. -/
theorem joint_mismatch_at_t (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (u y : Joint t g i) : t ∈ mismatches i u.val y.val := by
  rw [mem_mismatches, y.property.1]
  exact Ne.symm u.property.2

end Operators

end SubexponentialSAT.Subexp.MatrixSupport

end OAI.Algorithms
