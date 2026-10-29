import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SlotAssignment

namespace OAI.Algorithms

/-!
# Multicolor universal types and consistent incidence slots

The number `r` of colors is an explicit natural parameter throughout. No
finiteness instance or cardinality identity treats it as a fixed constant.
The joint fiber uses a head color different from the selected slot color,
as required by Sections 3.1 and 3.4 of the subexponential construction.
-/

namespace SubexponentialSAT.MulticolorTypes

abbrev Word (r Q : ℕ) := Fin Q → Fin r

structure UniversalType (r Q Δ : ℕ) where
  head : Word r Q
  slot : Fin Δ → Word r Q
  deriving DecidableEq

variable {r Q Δ : ℕ}

@[ext] theorem UniversalType.ext {u v : UniversalType r Q Δ}
    (hhead : u.head = v.head) (hslot : u.slot = v.slot) : u = v := by
  cases u
  cases v
  cases hhead
  cases hslot
  rfl

def equivProd (r Q Δ : ℕ) :
    UniversalType r Q Δ ≃ Word r Q × (Fin Δ → Word r Q) where
  toFun u := (u.head, u.slot)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (UniversalType r Q Δ) :=
  Fintype.ofEquiv (Word r Q × (Fin Δ → Word r Q)) (equivProd r Q Δ).symm

def blockSize (r Q Δ : ℕ) : ℕ := r ^ (Q * (Δ + 1))

@[simp] theorem card_word (r Q : ℕ) : Fintype.card (Word r Q) = r ^ Q := by
  simp [Word ]

@[simp] theorem card_universalType (r Q Δ : ℕ) :
    Fintype.card (UniversalType r Q Δ) = r ^ (Q * (Δ + 1)) := by
  rw [Fintype.card_congr (equivProd r Q Δ)]
  simp [Fintype.card_prod, ← pow_mul, Nat.mul_add,
    pow_add, Nat.mul_comm]

/-- The cardinality form independent of the chosen `Fintype` instance. -/
@[simp] theorem natCard_universalType (r Q Δ : ℕ) :
    Nat.card (UniversalType r Q Δ) = r ^ (Q * (Δ + 1)) := by
  rw [Nat.card_eq_fintype_card, card_universalType]

theorem natCard_universalType_eq_blockSize (r Q Δ : ℕ) :
    Nat.card (UniversalType r Q Δ) = blockSize r Q Δ :=
  natCard_universalType r Q Δ

/-- Cast form used by the rational deviation and block-threshold inequalities. -/
@[simp] theorem card_universalType_rat (r Q Δ : ℕ) :
    (Fintype.card (UniversalType r Q Δ) : ℚ) = (r : ℚ) ^ (Q * (Δ + 1)) := by
  rw [card_universalType, Nat.cast_pow]

@[simp] theorem natCard_universalType_rat (r Q Δ : ℕ) :
    (Nat.card (UniversalType r Q Δ) : ℚ) = (r : ℚ) ^ (Q * (Δ + 1)) := by
  rw [natCard_universalType, Nat.cast_pow]

@[simp] theorem blockSize_rat (r Q Δ : ℕ) :
    (blockSize r Q Δ : ℚ) = (r : ℚ) ^ (Q * (Δ + 1)) := by
  rw [blockSize, Nat.cast_pow]

def side (t : Fin Q) (g : Fin r) : Set (UniversalType r Q Δ) :=
  {u | u.head t = g}

def joint (t : Fin Q) (g : Fin r) (i : Fin Δ) : Set (UniversalType r Q Δ) :=
  {u | u.head t = g ∧ u.slot i t ≠ g}

abbrev Side (t : Fin Q) (g : Fin r) :=
  {u : UniversalType r Q Δ // u ∈ side t g}
abbrev Joint (t : Fin Q) (g : Fin r) (i : Fin Δ) :=
  {u : UniversalType r Q Δ // u ∈ joint t g i}

instance (t : Fin Q) (g : Fin r) : DecidablePred (side (Δ := Δ) t g) :=
  fun _ => inferInstanceAs (Decidable (_ = _))
instance (t : Fin Q) (g : Fin r) (i : Fin Δ) : DecidablePred (joint t g i) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

instance decidableMemSide (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r) :
    Decidable (u ∈ side t g) :=
  inferInstanceAs (Decidable (u.head t = g))
instance decidableMemJoint (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r)
    (i : Fin Δ) : Decidable (u ∈ joint t g i) :=
  inferInstanceAs (Decidable (u.head t = g ∧ u.slot i t ≠ g))

instance (t : Fin Q) (g : Fin r) : Fintype (Side (Δ := Δ) t g) :=
  inferInstanceAs (Fintype {u : UniversalType r Q Δ // u.head t = g})
instance (t : Fin Q) (g : Fin r) (i : Fin Δ) : Fintype (Joint t g i) :=
  inferInstanceAs (Fintype {u : UniversalType r Q Δ // u.head t = g ∧ u.slot i t ≠ g})

@[simp] theorem mem_side (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r) :
    u ∈ side t g ↔ u.head t = g := Iff.rfl
@[simp] theorem mem_joint (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r)
    (i : Fin Δ) : u ∈ joint t g i ↔ u.head t = g ∧ u.slot i t ≠ g := Iff.rfl

theorem joint_subset_side (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    joint t g i ⊆ side t g := fun _ h => h.1

theorem side_disjoint (t : Fin Q) {g h : Fin r} (hne : g ≠ h) :
    Disjoint (side (Δ := Δ) t g) (side t h) := by
  rw [Set.disjoint_left]
  intro u hu hv
  exact hne (hu.symm.trans hv)

def pinHead (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r) : UniversalType r Q Δ :=
  {u with head := Function.update u.head t g}

def pinSlot (u : UniversalType r Q Δ) (i : Fin Δ) (t : Fin Q) (g : Fin r) :
    UniversalType r Q Δ :=
  {u with slot := Function.update u.slot i (Function.update (u.slot i) t g)}

@[simp] theorem pinHead_head (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r) :
    (pinHead u t g).head = Function.update u.head t g := rfl
@[simp] theorem pinHead_slot (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r) :
    (pinHead u t g).slot = u.slot := rfl
@[simp] theorem pinSlot_head (u : UniversalType r Q Δ) (i : Fin Δ) (t : Fin Q)
    (g : Fin r) : (pinSlot u i t g).head = u.head := rfl
@[simp] theorem pinSlot_slot (u : UniversalType r Q Δ) (i : Fin Δ) (t : Fin Q)
    (g : Fin r) : (pinSlot u i t g).slot =
      Function.update u.slot i (Function.update (u.slot i) t g) := rfl

@[simp] theorem pinHead_pinHead (u : UniversalType r Q Δ) (t : Fin Q) (g h : Fin r) :
    pinHead (pinHead u t g) t h = pinHead u t h := by
  cases u
  simp [pinHead]
@[simp] theorem pinHead_self (u : UniversalType r Q Δ) (t : Fin Q) :
    pinHead u t (u.head t) = u := by
  cases u
  simp [pinHead, Function.update_eq_self]
@[simp] theorem pinSlot_pinSlot (u : UniversalType r Q Δ) (i : Fin Δ) (t : Fin Q)
    (g h : Fin r) : pinSlot (pinSlot u i t g) i t h = pinSlot u i t h := by
  cases u
  simp [pinSlot]
@[simp] theorem pinSlot_self (u : UniversalType r Q Δ) (i : Fin Δ) (t : Fin Q) :
    pinSlot u i t (u.slot i t) = u := by
  cases u
  simp [pinSlot, Function.update_eq_self]

def fullSideEquiv (t : Fin Q) (g : Fin r) :
    UniversalType r Q Δ ≃ Fin r × Side (Δ := Δ) t g where
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

theorem card_full_eq_mul_side (t : Fin Q) (g : Fin r) :
    Fintype.card (UniversalType r Q Δ) = r * Fintype.card (Side (Δ := Δ) t g) := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    Fintype.card_congr (fullSideEquiv (Δ := Δ) t g)

theorem card_side (t : Fin Q) (g : Fin r) :
    Fintype.card (Side (Δ := Δ) t g) = blockSize r Q Δ / r := by
  have h := card_full_eq_mul_side (Δ := Δ) t g
  rw [card_universalType] at h
  rw [blockSize, h, Nat.mul_div_cancel_left _ (Nat.zero_lt_of_lt g.isLt)]

theorem card_joint_le_side (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Fintype.card (Joint t g i) ≤ Fintype.card (Side (Δ := Δ) t g) :=
  Fintype.card_le_of_injective (fun u : Joint t g i => (⟨u.val, u.property.1⟩ : Side t g))
    (fun _ _ h => Subtype.ext (congrArg (fun z : Side (Δ := Δ) t g => z.val) h))

abbrev OtherPosition (t : Fin Q) := {l : Fin Q // l ≠ t}
abbrev OtherSlot (i : Fin Δ) := {j : Fin Δ // j ≠ i}
abbrev OtherColor (g : Fin r) := {c : Fin r // c ≠ g}

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
@[simp] theorem card_otherColor (g : Fin r) :
    Fintype.card (OtherColor g) = r - 1 := by
  change Fintype.card {c : Fin r // ¬c = g} = r - 1
  rw [Fintype.card_subtype_compl]
  simp
@[simp] theorem card_otherSlotWords (i : Fin Δ) :
    Fintype.card (OtherSlot i → Word r Q) = r ^ (Q * (Δ - 1)) := by
  simp [ ← pow_mul]

/-- Coordinates not changed by the swaps at positions other than `t`. -/
abbrev Spectator (g : Fin r) (i : Fin Δ) :=
  OtherColor g × (OtherSlot i → Word r Q)

/-- A joint fiber is the product of free head--slot pairs at all other
positions and the untouched slot color at `t` and all other slot words. -/
def jointEquivPairs (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Joint t g i ≃ (OtherPosition t → Fin r × Fin r) × Spectator (Q := Q) g i where
  toFun u := ((fun l => (u.val.head l.val, u.val.slot i l.val)),
    (⟨u.val.slot i t, u.property.2⟩, fun j => u.val.slot j.val))
  invFun z := ⟨{
    head := fun l => if h : l = t then g else (z.1 ⟨l, h⟩).1
    slot := fun j => if hj : j = i then
      fun l => if h : l = t then z.2.1.val else (z.1 ⟨l, h⟩).2
      else z.2.2 ⟨j, hj⟩
    }, by simpa [joint] using z.2.1.property⟩
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
          simp
        · simp [hl]
      · simp [hj]
  right_inv z := by
    apply Prod.ext
    · funext l
      apply Prod.ext <;> simp [l.property]
    · apply Prod.ext
      · apply Subtype.ext
        simp
      · funext j l
        simp [j.property]

@[simp] theorem jointEquivPairs_head (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (u : Joint t g i) (l : OtherPosition t) :
    ((jointEquivPairs t g i u).1 l).1 = u.val.head l.val := rfl
@[simp] theorem jointEquivPairs_slot (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (u : Joint t g i) (l : OtherPosition t) :
    ((jointEquivPairs t g i u).1 l).2 = u.val.slot i l.val := rfl
@[simp] theorem jointEquivPairs_color (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (u : Joint t g i) : (jointEquivPairs t g i u).2.1.val = u.val.slot i t := rfl
@[simp] theorem jointEquivPairs_otherSlot (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (u : Joint t g i) (j : OtherSlot i) :
    (jointEquivPairs t g i u).2.2 j = u.val.slot j.val := rfl

@[simp] theorem jointEquivPairs_symm_head (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (z : (OtherPosition t → Fin r × Fin r) × Spectator (Q := Q) g i)
    (l : OtherPosition t) :
    ((jointEquivPairs t g i).symm z).val.head l.val = (z.1 l).1 := by
  simp [jointEquivPairs, l.property]
@[simp] theorem jointEquivPairs_symm_slot (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (z : (OtherPosition t → Fin r × Fin r) × Spectator (Q := Q) g i)
    (l : OtherPosition t) :
    ((jointEquivPairs t g i).symm z).val.slot i l.val = (z.1 l).2 := by
  simp [jointEquivPairs, l.property]
@[simp] theorem jointEquivPairs_symm_otherSlot (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (z : (OtherPosition t → Fin r × Fin r) × Spectator (Q := Q) g i)
    (j : OtherSlot i) :
    ((jointEquivPairs t g i).symm z).val.slot j.val = z.2.2 j := by
  simp [jointEquivPairs, j.property]

theorem card_joint_via_pairs (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Fintype.card (Joint t g i) =
      (r * r) ^ (Q - 1) * ((r - 1) * r ^ (Q * (Δ - 1))) := by
  rw [Fintype.card_congr (jointEquivPairs t g i)]
  simp [Spectator, Fintype.card_prod, ← pow_mul]

/-- Auxiliary fiber with both selected colors pinned to `g`. -/
abbrev ExactJoint (t : Fin Q) (g : Fin r) (i : Fin Δ) :=
  {u : UniversalType r Q Δ // u.head t = g ∧ u.slot i t = g}

def sideExactJointEquiv (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Side (Δ := Δ) t g ≃ Fin r × ExactJoint t g i where
  toFun u := (u.val.slot i t, ⟨pinSlot u.val i t g, by
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
      exact (congrArg (pinSlot u.val i t) u.property.2.symm).trans
        (pinSlot_self u.val i t)

def fullExactJointEquiv (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    UniversalType r Q Δ ≃ Fin r × (Fin r × ExactJoint t g i) :=
  (fullSideEquiv t g).trans
    (Equiv.prodCongr (Equiv.refl (Fin r)) (sideExactJointEquiv t g i))

/-- A mismatch joint has `r-1` possible selected slot colors, all with the
same remaining free coordinates as the auxiliary pinned fiber. -/
def jointExactJointEquiv (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Joint t g i ≃ OtherColor g × ExactJoint t g i where
  toFun u := (⟨u.val.slot i t, u.property.2⟩, ⟨pinSlot u.val i t g, by
    constructor
    · exact u.property.1
    · simp⟩)
  invFun z := ⟨pinSlot z.2.val i t z.1.val, by
    change (pinSlot z.2.val i t z.1.val).head t = g ∧
      (pinSlot z.2.val i t z.1.val).slot i t ≠ g
    constructor
    · exact z.2.property.1
    · simpa using z.1.property⟩
  left_inv u := by
    apply Subtype.ext
    simp
  right_inv z := by
    rcases z with ⟨b, u⟩
    apply Prod.ext
    · apply Subtype.ext
      simp
    · apply Subtype.ext
      change pinSlot (pinSlot u.val i t b.val) i t g = u.val
      rw [pinSlot_pinSlot]
      exact (congrArg (pinSlot u.val i t) u.property.2.symm).trans
        (pinSlot_self u.val i t)

theorem card_full_eq_sq_mul_exactJoint (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Fintype.card (UniversalType r Q Δ) = (r * r) * Fintype.card (ExactJoint t g i) := by
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc] using
    Fintype.card_congr (fullExactJointEquiv t g i)

theorem card_exactJoint (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Fintype.card (ExactJoint t g i) = blockSize r Q Δ / (r * r) := by
  have h := card_full_eq_sq_mul_exactJoint t g i
  rw [card_universalType] at h
  have hr : 0 < r := Nat.zero_lt_of_lt g.isLt
  rw [blockSize, h, Nat.mul_div_cancel_left _ (Nat.mul_pos hr hr)]

/-- The mismatch joint occupies exactly `(r-1)/r²` of the block. -/
theorem card_joint (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Fintype.card (Joint t g i) = (r - 1) * (blockSize r Q Δ / (r * r)) := by
  rw [Fintype.card_congr (jointExactJointEquiv t g i), Fintype.card_prod,
    card_otherColor, card_exactJoint]

/-- Division-free form of the exact joint-size identity. -/
theorem card_joint_mul_sq (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    (r * r) * Fintype.card (Joint t g i) = (r - 1) * blockSize r Q Δ := by
  rw [Fintype.card_congr (jointExactJointEquiv t g i), Fintype.card_prod,
    card_otherColor]
  have h := card_full_eq_sq_mul_exactJoint t g i
  rw [card_universalType] at h
  rw [blockSize, h]
  ac_rfl

section SlotWords

open SubexponentialSAT.Factor SubexponentialSAT.SlotAssignment

variable {V E : Type*} [DecidableEq V] [Fintype E]
    (P : Pattern V E) (slots : SlotMap P Δ)

/-- The color-independent slot embeddings of `SlotAssignment` are reused. -/
def typeFromWords (sigma : E → Word r Q) (head : V → Word r Q)
    (padding : V → Fin Δ → Word r Q) (v : V) : UniversalType r Q Δ where
  head := head v
  slot := fillSlots (slots v) (fun e => sigma e.val) (padding v)

@[simp] theorem typeFromWords_head (sigma : E → Word r Q) (head : V → Word r Q)
    (padding : V → Fin Δ → Word r Q) (v : V) :
    (typeFromWords P slots sigma head padding v).head = head v := rfl
@[simp] theorem typeFromWords_incidence (sigma : E → Word r Q) (head : V → Word r Q)
    (padding : V → Fin Δ → Word r Q) (v : V) (e : Incident P v) :
    (typeFromWords P slots sigma head padding v).slot (slots v e) = sigma e.val :=
  fillSlots_used (slots v) _ _ e
@[simp] theorem typeFromWords_unused (sigma : E → Word r Q) (head : V → Word r Q)
    (padding : V → Fin Δ → Word r Q) (v : V) (i : Fin Δ)
    (h : ¬ ∃ e, slots v e = i) :
    (typeFromWords P slots sigma head padding v).slot i = padding v i :=
  fillSlots_unused (slots v) _ _ i h

theorem factor_word_consistent (sigma : E → Word r Q) (head : V → Word r Q)
    (padding : V → Fin Δ → Word r Q) (e : E) (v w : V)
    (hv : v ∈ P.scope e) (hw : w ∈ P.scope e) :
    (typeFromWords P slots sigma head padding v).slot (slots v ⟨e, hv⟩) =
      (typeFromWords P slots sigma head padding w).slot (slots w ⟨e, hw⟩) := by
  simp

theorem typeFromWords_congr (sigma tau : E → Word r Q) (head head' : V → Word r Q)
    (padding padding' : V → Fin Δ → Word r Q) (v : V)
    (hsigma : ∀ e : Incident P v, sigma e.val = tau e.val)
    (hhead : head v = head' v)
    (hpadding : ∀ i : Unused (slots v), padding v i.val = padding' v i.val) :
    typeFromWords P slots sigma head padding v =
      typeFromWords P slots tau head' padding' v := by
  apply UniversalType.ext hhead
  change slotWordsEquiv (slots v) (Word r Q) _ = slotWordsEquiv (slots v) (Word r Q) _
  congr 1
  exact Prod.ext (funext hsigma) (funext hpadding)

end SlotWords

open SubexponentialSAT.SlotAssignment in
/-- The exact local product correspondence remains valid for growing `r`. -/
def localTypeEquiv {A : Type*} [Fintype A] (s : A ↪ Fin Δ) (r Q : ℕ) :
    (Word r Q × ((A → Word r Q) × (Unused s → Word r Q))) ≃ UniversalType r Q Δ :=
  (Equiv.prodCongr (Equiv.refl (Word r Q)) (slotWordsEquiv s (Word r Q))).trans
    (equivProd r Q Δ).symm

@[simp] theorem localTypeEquiv_head {A : Type*} [Fintype A] (s : A ↪ Fin Δ)
    (head : Word r Q) (f : A → Word r Q)
    (padding : SubexponentialSAT.SlotAssignment.Unused s → Word r Q) :
    (localTypeEquiv s r Q (head, (f, padding))).head = head := rfl

@[simp] theorem localTypeEquiv_used {A : Type*} [Fintype A] (s : A ↪ Fin Δ)
    (head : Word r Q) (f : A → Word r Q)
    (padding : SubexponentialSAT.SlotAssignment.Unused s → Word r Q) (a : A) :
    (localTypeEquiv s r Q (head, (f, padding))).slot (s a) = f a :=
  SubexponentialSAT.SlotAssignment.slotWordsEquiv_used s f padding a

@[simp] theorem localTypeEquiv_unused {A : Type*} [Fintype A] (s : A ↪ Fin Δ)
    (head : Word r Q) (f : A → Word r Q)
    (padding : SubexponentialSAT.SlotAssignment.Unused s → Word r Q)
    (i : SubexponentialSAT.SlotAssignment.Unused s) :
    (localTypeEquiv s r Q (head, (f, padding))).slot i.val = padding i :=
  SubexponentialSAT.SlotAssignment.slotWordsEquiv_unused s f padding i

end SubexponentialSAT.MulticolorTypes

end OAI.Algorithms
