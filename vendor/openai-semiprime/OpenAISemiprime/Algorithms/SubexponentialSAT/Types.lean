import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Universal types

A universal type records a head word and one word per incidence slot.  The
head selects the side of the coordinate, whereas a slot records a factor color.
This file proves the sizes of the type universe and the one- and two-bit fibers
using explicit equivalences.
-/

namespace SubexponentialSAT.Types

/-- A binary word indexed by interpolation positions. -/
abbrev Word (Q : ℕ) := Fin Q → Bool

/-- One head word and `Δ` slot words. No relation is imposed between their bits. -/
structure UniversalType (Q Δ : ℕ) where
  head : Word Q
  slot : Fin Δ → Word Q
  deriving DecidableEq

variable {Q Δ : ℕ}

@[ext] theorem UniversalType.ext {u v : UniversalType Q Δ}
    (hhead : u.head = v.head) (hslot : u.slot = v.slot) : u = v := by
  cases u
  cases v
  cases hhead
  cases hslot
  rfl

/-- Explicit presentation as a Cartesian product of independent word spaces. -/
def equivProd (Q Δ : ℕ) :
    UniversalType Q Δ ≃ Word Q × (Fin Δ → Word Q) where
  toFun u := (u.head, u.slot)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (UniversalType Q Δ) :=
  Fintype.ofEquiv (Word Q × (Fin Δ → Word Q)) (equivProd Q Δ).symm

/-- The size `N` of the complete universal block. -/
def blockSize (Q Δ : ℕ) : ℕ := 2 ^ (Q * (Δ + 1))

@[simp] theorem card_word (Q : ℕ) : Fintype.card (Word Q) = 2 ^ Q := by
  simp [Word ]

@[simp] theorem card_universalType (Q Δ : ℕ) :
    Fintype.card (UniversalType Q Δ) = 2 ^ (Q * (Δ + 1)) := by
  rw [Fintype.card_congr (equivProd Q Δ)]
  simp [Fintype.card_prod, ← pow_mul, Nat.mul_add,
    pow_add, Nat.mul_comm]

/-- Head side at a fixed interpolation point. -/
def side (t : Fin Q) (g : Bool) : Set (UniversalType Q Δ) :=
  {u | u.head t = g}

/-- Joint head-and-slot fiber, denoted `J(t,g,i)` in the exposition. -/
def joint (t : Fin Q) (g : Bool) (i : Fin Δ) : Set (UniversalType Q Δ) :=
  {u | u.head t = g ∧ u.slot i t = g}

abbrev Side (t : Fin Q) (g : Bool) := {u : UniversalType Q Δ // u ∈ side t g}
abbrev Joint (t : Fin Q) (g : Bool) (i : Fin Δ) :=
  {u : UniversalType Q Δ // u ∈ joint t g i}

instance (t : Fin Q) (g : Bool) : DecidablePred (side (Δ := Δ) t g) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

instance (t : Fin Q) (g : Bool) (i : Fin Δ) : DecidablePred (joint t g i) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

instance (t : Fin Q) (g : Bool) : Fintype (Side (Δ := Δ) t g) := by
  change Fintype {u : UniversalType Q Δ // u.head t = g}
  infer_instance

instance (t : Fin Q) (g : Bool) (i : Fin Δ) : Fintype (Joint t g i) := by
  change Fintype {u : UniversalType Q Δ // u.head t = g ∧ u.slot i t = g}
  infer_instance

@[simp] theorem mem_side (u : UniversalType Q Δ) (t : Fin Q) (g : Bool) :
    u ∈ side t g ↔ u.head t = g := Iff.rfl

@[simp] theorem mem_joint (u : UniversalType Q Δ) (t : Fin Q) (g : Bool)
    (i : Fin Δ) : u ∈ joint t g i ↔ u.head t = g ∧ u.slot i t = g := Iff.rfl

theorem joint_subset_side (t : Fin Q) (g : Bool) (i : Fin Δ) :
    joint t g i ⊆ side t g := fun _ h => h.1

theorem side_disjoint (t : Fin Q) :
    Disjoint (side (Δ := Δ) t false) (side t true) := by
  apply Set.disjoint_left.mpr
  intro u hfalse htrue
  have h : false = true := hfalse.symm.trans htrue
  cases h

theorem side_union (t : Fin Q) :
    side (Δ := Δ) t false ∪ side t true = Set.univ := by
  apply Set.eq_univ_of_forall
  intro u
  change u.head t = false ∨ u.head t = true
  cases h : u.head t <;> simp []

/-- Replace just one head bit. -/
def pinHead (u : UniversalType Q Δ) (t : Fin Q) (g : Bool) : UniversalType Q Δ :=
  {u with head := Function.update u.head t g}

/-- Replace just one bit of one slot. -/
def pinSlot (u : UniversalType Q Δ) (i : Fin Δ) (t : Fin Q) (g : Bool) :
    UniversalType Q Δ :=
  {u with slot := Function.update u.slot i (Function.update (u.slot i) t g)}

@[simp] theorem pinHead_head (u : UniversalType Q Δ) (t : Fin Q) (g : Bool) :
    (pinHead u t g).head = Function.update u.head t g := rfl

@[simp] theorem pinHead_slot (u : UniversalType Q Δ) (t : Fin Q) (g : Bool) :
    (pinHead u t g).slot = u.slot := rfl

@[simp] theorem pinSlot_head (u : UniversalType Q Δ) (i : Fin Δ) (t : Fin Q)
    (g : Bool) : (pinSlot u i t g).head = u.head := rfl

@[simp] theorem pinSlot_slot (u : UniversalType Q Δ) (i : Fin Δ) (t : Fin Q)
    (g : Bool) : (pinSlot u i t g).slot =
      Function.update u.slot i (Function.update (u.slot i) t g) := rfl

@[simp] theorem pinHead_pinHead (u : UniversalType Q Δ) (t : Fin Q) (g h : Bool) :
    pinHead (pinHead u t g) t h = pinHead u t h := by
  cases u
  simp [pinHead]

@[simp] theorem pinHead_self (u : UniversalType Q Δ) (t : Fin Q) :
    pinHead u t (u.head t) = u := by
  cases u
  simp [pinHead, Function.update_eq_self]

@[simp] theorem pinSlot_pinSlot (u : UniversalType Q Δ) (i : Fin Δ) (t : Fin Q)
    (g h : Bool) : pinSlot (pinSlot u i t g) i t h = pinSlot u i t h := by
  cases u
  simp [pinSlot]

@[simp] theorem pinSlot_self (u : UniversalType Q Δ) (i : Fin Δ) (t : Fin Q) :
    pinSlot u i t (u.slot i t) = u := by
  cases u
  simp [pinSlot, Function.update_eq_self]

/-- Removing the chosen head bit leaves exactly one free Boolean bit. -/
def fullSideEquiv (t : Fin Q) (g : Bool) :
    UniversalType Q Δ ≃ Bool × Side (Δ := Δ) t g where
  toFun u := (u.head t, ⟨pinHead u t g, by simp [side]⟩)
  invFun z := pinHead z.2.val t z.1
  left_inv u := by simp
  right_inv z := by
    rcases z with ⟨b, u⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change pinHead (pinHead u.val t b) t g = u.val
      rw [pinHead_pinHead]
      have hg : g = u.val.head t := u.property.symm
      exact (congrArg (pinHead u.val t) hg).trans (pinHead_self u.val t)

/-- Within a head side, removing the selected slot bit leaves one free bit. -/
def sideJointEquiv (t : Fin Q) (g : Bool) (i : Fin Δ) :
    Side (Δ := Δ) t g ≃ Bool × Joint t g i where
  toFun u := (u.val.slot i t, ⟨pinSlot u.val i t g, by
    change (pinSlot u.val i t g).head t = g ∧ (pinSlot u.val i t g).slot i t = g
    constructor
    · exact u.property
    · simp⟩)
  invFun z := ⟨pinSlot z.2.val i t z.1, z.2.property.1⟩
  left_inv u := by
    apply Subtype.ext
    simp
  right_inv z := by
    rcases z with ⟨b, u⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change pinSlot (pinSlot u.val i t b) i t g = u.val
      rw [pinSlot_pinSlot]
      have hg : g = u.val.slot i t := u.property.2.symm
      exact (congrArg (pinSlot u.val i t) hg).trans (pinSlot_self u.val i t)

/-- The two pinned bits are independent, giving two free Boolean factors. -/
def fullJointEquiv (t : Fin Q) (g : Bool) (i : Fin Δ) :
    UniversalType Q Δ ≃ Bool × (Bool × Joint t g i) :=
  (fullSideEquiv t g).trans (Equiv.prodCongr (Equiv.refl Bool) (sideJointEquiv t g i))

theorem card_full_eq_two_mul_side (t : Fin Q) (g : Bool) :
    Fintype.card (UniversalType Q Δ) = 2 * Fintype.card (Side (Δ := Δ) t g) := by
  simpa only [Fintype.card_prod, Fintype.card_bool] using
    Fintype.card_congr (fullSideEquiv (Δ := Δ) t g)

theorem card_side_eq_two_mul_joint (t : Fin Q) (g : Bool) (i : Fin Δ) :
    Fintype.card (Side (Δ := Δ) t g) = 2 * Fintype.card (Joint t g i) := by
  simpa only [Fintype.card_prod, Fintype.card_bool] using
    Fintype.card_congr (sideJointEquiv t g i)

theorem card_full_eq_four_mul_joint (t : Fin Q) (g : Bool) (i : Fin Δ) :
    Fintype.card (UniversalType Q Δ) = 4 * Fintype.card (Joint t g i) := by
  rw [card_full_eq_two_mul_side t g, card_side_eq_two_mul_joint t g i,
    ← Nat.mul_assoc]

/-- Each head side contains exactly half the universal types. -/
theorem card_side (t : Fin Q) (g : Bool) :
    Fintype.card (Side (Δ := Δ) t g) = blockSize Q Δ / 2 := by
  have h := card_full_eq_two_mul_side (Δ := Δ) t g
  rw [card_universalType] at h
  rw [blockSize, h]
  simp

/-- A fixed head and a fixed slot color occupy exactly one quarter of the types. -/
theorem card_joint (t : Fin Q) (g : Bool) (i : Fin Δ) :
    Fintype.card (Joint t g i) = blockSize Q Δ / 4 := by
  have h := card_full_eq_four_mul_joint t g i
  rw [card_universalType] at h
  rw [blockSize, h]
  simp

/-- All interpolation positions except the one fixed by a joint fiber. -/
abbrev OtherPosition (t : Fin Q) := {l : Fin Q // l ≠ t}

/-- The slots not used in the active head--slot pair. -/
abbrev OtherSlot (i : Fin Δ) := {j : Fin Δ // j ≠ i}

@[simp] theorem card_otherPosition (t : Fin Q) :
    Fintype.card (OtherPosition t) = Q - 1 := by
  change Fintype.card {l : Fin Q // ¬l = t} = Q - 1
  rw [Fintype.card_subtype_compl]
  simp

@[simp] theorem card_otherSlot (i : Fin Δ) :
    Fintype.card (OtherSlot i) = Δ - 1 := by
  change Fintype.card {j : Fin Δ // ¬j = i} = Δ - 1
  rw [Fintype.card_subtype_compl]
  simp

@[simp] theorem card_otherSlotWords (i : Fin Δ) :
    Fintype.card (OtherSlot i → Word Q) = 2 ^ (Q * (Δ - 1)) := by
  simp [ ← pow_mul]

/-- A joint fiber is a product of independently free head--slot pairs at the
other positions, together with the completely untouched other slot words.
The two Boolean coordinates at the fixed position are restored as `g`. -/
def jointEquivPairs (t : Fin Q) (g : Bool) (i : Fin Δ) :
    Joint t g i ≃ (OtherPosition t → Bool × Bool) × (OtherSlot i → Word Q) where
  toFun u := ((fun l => (u.val.head l.val, u.val.slot i l.val)),
    fun j => u.val.slot j.val)
  invFun z := ⟨{
    head := fun l => if h : l = t then g else (z.1 ⟨l, h⟩).1
    slot := fun j => if hj : j = i then
      fun l => if h : l = t then g else (z.1 ⟨l, h⟩).2
      else z.2 ⟨j, hj⟩
    }, by simp [joint]⟩
  left_inv u := by
    apply Subtype.ext
    apply UniversalType.ext
    · funext l
      by_cases hl : l = t
      · subst l
        simpa using u.property.1.symm
      · simp [hl]
    · funext j l
      by_cases hj : j = i
      · subst j
        by_cases hl : l = t
        · subst l
          simpa using u.property.2.symm
        · simp [hl]
      · simp [hj]
  right_inv z := by
    apply Prod.ext
    · funext l
      apply Prod.ext <;> simp [l.property]
    · funext j l
      simp [j.property]

@[simp] theorem jointEquivPairs_head (t : Fin Q) (g : Bool) (i : Fin Δ)
    (u : Joint t g i) (l : OtherPosition t) :
    ((jointEquivPairs t g i u).1 l).1 = u.val.head l.val := rfl

@[simp] theorem jointEquivPairs_slot (t : Fin Q) (g : Bool) (i : Fin Δ)
    (u : Joint t g i) (l : OtherPosition t) :
    ((jointEquivPairs t g i u).1 l).2 = u.val.slot i l.val := rfl

@[simp] theorem jointEquivPairs_otherSlot (t : Fin Q) (g : Bool) (i : Fin Δ)
    (u : Joint t g i) (j : OtherSlot i) :
    (jointEquivPairs t g i u).2 j = u.val.slot j.val := rfl

@[simp] theorem jointEquivPairs_symm_head (t : Fin Q) (g : Bool) (i : Fin Δ)
    (z : (OtherPosition t → Bool × Bool) × (OtherSlot i → Word Q))
    (l : OtherPosition t) :
    ((jointEquivPairs t g i).symm z).val.head l.val = (z.1 l).1 := by
  simp [jointEquivPairs, l.property]

@[simp] theorem jointEquivPairs_symm_slot (t : Fin Q) (g : Bool) (i : Fin Δ)
    (z : (OtherPosition t → Bool × Bool) × (OtherSlot i → Word Q))
    (l : OtherPosition t) :
    ((jointEquivPairs t g i).symm z).val.slot i l.val = (z.1 l).2 := by
  simp [jointEquivPairs, l.property]

@[simp] theorem jointEquivPairs_symm_otherSlot (t : Fin Q) (g : Bool) (i : Fin Δ)
    (z : (OtherPosition t → Bool × Bool) × (OtherSlot i → Word Q))
    (j : OtherSlot i) :
    ((jointEquivPairs t g i).symm z).val.slot j.val = z.2 j := by
  simp [jointEquivPairs, j.property]

/-- The tensor-factor cardinality form used in spectral multiplicity counts. -/
theorem card_joint_via_pairs (t : Fin Q) (g : Bool) (i : Fin Δ) :
    Fintype.card (Joint t g i) = 4 ^ (Q - 1) * 2 ^ (Q * (Δ - 1)) := by
  rw [Fintype.card_congr (jointEquivPairs t g i)]
  simp [Fintype.card_prod, ← pow_mul]

end SubexponentialSAT.Types

end OAI.Algorithms
