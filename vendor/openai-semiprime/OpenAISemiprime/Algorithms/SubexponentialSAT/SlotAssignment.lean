import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.Incidence
import OpenAISemiprime.Algorithms.SubexponentialSAT.Types

namespace OAI.Algorithms

/-!
# Incidence slots and globally consistent factor words

Section 5.4 assigns each coordinate's incident factors to different slots.
The same factor word is then used at every incidence of that factor.  The
slot numbers themselves need not agree at different coordinates.

The ordered constructor and the slot-filling operations are computable.  An
additional constructor for arbitrary finite factor types chooses an enumeration.
No running-time bound or probabilistic independence assertion is hidden here.
-/

namespace SubexponentialSAT.SlotAssignment

open SubexponentialSAT.Factor SubexponentialSAT.Types

variable {V E : Type*} [DecidableEq V]

/-- The actual factors incident to one coordinate. -/
abbrev Incident (P : Pattern V E) (v : V) := {e : E // v ∈ P.scope e}

/-- An injective slot assignment separately at each coordinate. -/
abbrev SlotMap (P : Pattern V E) (Δ : ℕ) :=
  (v : V) → Incident P v ↪ Fin Δ

@[simp] theorem card_incident [Fintype E] (P : Pattern V E) (v : V) :
    Fintype.card (Incident P v) =
      (Finset.univ.filter fun e => v ∈ P.scope e).card := by
  exact Fintype.card_subtype _

/-- The incidence bound supplies exactly the cardinal inequality needed for slots. -/
theorem card_incident_le [Fintype E] (P : Pattern V E) {k Δ : ℕ}
    (hP : P.Bounded k Δ) (v : V) : Fintype.card (Incident P v) ≤ Δ := by
  rw [card_incident]
  exact hP.incidence_le v

/-- A finite slot assignment, using a chosen enumeration for each incident set. -/
noncomputable def slotsOfCardLE [Fintype E] (P : Pattern V E) {Δ : ℕ}
    (h : ∀ v, Fintype.card (Incident P v) ≤ Δ) : SlotMap P Δ :=
  fun v => (Fintype.equivFin (Incident P v)).toEmbedding.trans (Fin.castLEEmb (h v))

/-- Slot assignments exist for every bounded factor pattern. -/
noncomputable def slotsOfBounded [Fintype E] (P : Pattern V E) {k Δ : ℕ}
    (hP : P.Bounded k Δ) : SlotMap P Δ :=
  slotsOfCardLE P (card_incident_le P hP)

/-- For ordered factor indices, sort the incident factors and use their ranks.
This constructor makes the fixed local ordering in the exposition explicit. -/
def orderedSlotsOfCardLE [Fintype E] [LinearOrder E] (P : Pattern V E) {Δ : ℕ}
    (h : ∀ v, Fintype.card (Incident P v) ≤ Δ) : SlotMap P Δ :=
  fun v => (Fintype.orderIsoFinOfCardEq (Incident P v) rfl).symm.toEquiv.toEmbedding.trans
    (Fin.castLEEmb (h v))

/-- Computable slot assignment for a bounded pattern with ordered factor indices. -/
def orderedSlotsOfBounded [Fintype E] [LinearOrder E] (P : Pattern V E) {k Δ : ℕ}
    (hP : P.Bounded k Δ) : SlotMap P Δ :=
  orderedSlotsOfCardLE P (card_incident_le P hP)

theorem slot_eq_iff (P : Pattern V E) {Δ : ℕ} (slots : SlotMap P Δ)
    (v : V) (e f : Incident P v) : slots v e = slots v f ↔ e = f :=
  (slots v).injective.eq_iff

section FiniteSlotFilling

variable {A W : Type*} [Fintype A] {Δ : ℕ}

/-- Slots not used by the given embedding. -/
abbrev Unused (s : A ↪ Fin Δ) := {i : Fin Δ // ¬ ∃ a, s a = i}

private theorem unique_preimage (s : A ↪ Fin Δ) (i : Fin Δ)
    (h : ∃ a, s a = i) : ∃! a, a ∈ (Finset.univ : Finset A) ∧ s a = i := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ⟨Finset.mem_univ a, ha⟩, ?_⟩
  intro b hb
  exact s.injective (hb.2.trans ha.symm)

/-- Search the finite incident set for the unique factor assigned to a used slot. -/
def preimage (s : A ↪ Fin Δ) (i : Fin Δ) (h : ∃ a, s a = i) : A :=
  Finset.choose (fun a => s a = i) Finset.univ (unique_preimage s i h)

@[simp] theorem preimage_spec (s : A ↪ Fin Δ) (i : Fin Δ) (h : ∃ a, s a = i) :
    s (preimage s i h) = i :=
  Finset.choose_property (fun a => s a = i) Finset.univ (unique_preimage s i h)

@[simp] theorem preimage_at (s : A ↪ Fin Δ) (a : A) (h : ∃ b, s b = s a) :
    preimage s (s a) h = a :=
  s.injective (preimage_spec s (s a) h)

/-- Every slot is uniquely either an incident-factor slot or an unused slot. -/
def slotIndexEquiv (s : A ↪ Fin Δ) : A ⊕ Unused s ≃ Fin Δ where
  toFun := Sum.elim s Subtype.val
  invFun i := if h : ∃ a, s a = i then Sum.inl (preimage s i h) else Sum.inr ⟨i, h⟩
  left_inv x := by
    cases x with
    | inl a => simp
    | inr i => simp [i.property]
  right_inv i := by
    by_cases h : ∃ a, s a = i
    · simp [h]
    · simp [h]

@[simp] theorem slotIndexEquiv_inl (s : A ↪ Fin Δ) (a : A) :
    slotIndexEquiv s (Sum.inl a) = s a := rfl

@[simp] theorem slotIndexEquiv_inr (s : A ↪ Fin Δ) (i : Unused s) :
    slotIndexEquiv s (Sum.inr i) = i.val := rfl

/-- Incident words and independently specified unused words are exactly all slot words. -/
def slotWordsEquiv (s : A ↪ Fin Δ) (W : Type*) :
    ((A → W) × (Unused s → W)) ≃ (Fin Δ → W) :=
  (Equiv.sumArrowEquivProdArrow A (Unused s) W).symm.trans
    (Equiv.arrowCongr (slotIndexEquiv s) (Equiv.refl W))

@[simp] theorem slotWordsEquiv_used (s : A ↪ Fin Δ) (f : A → W)
    (padding : Unused s → W) (a : A) :
    slotWordsEquiv s W (f, padding) (s a) = f a := by
  change Sum.elim f padding ((slotIndexEquiv s).symm (s a)) = f a
  rw [← slotIndexEquiv_inl s a, Equiv.symm_apply_apply]
  rfl

@[simp] theorem slotWordsEquiv_unused (s : A ↪ Fin Δ) (f : A → W)
    (padding : Unused s → W) (i : Unused s) :
    slotWordsEquiv s W (f, padding) i.val = padding i := by
  change Sum.elim f padding ((slotIndexEquiv s).symm i.val) = padding i
  rw [← slotIndexEquiv_inr s i, Equiv.symm_apply_apply]
  rfl

/-- A convenient extension allowing padding values for all slots; used-slot
padding is ignored. -/
def fillSlots (s : A ↪ Fin Δ) (f : A → W) (padding : Fin Δ → W) : Fin Δ → W :=
  slotWordsEquiv s W (f, fun i => padding i.val)

@[simp] theorem fillSlots_used (s : A ↪ Fin Δ) (f : A → W)
    (padding : Fin Δ → W) (a : A) : fillSlots s f padding (s a) = f a :=
  slotWordsEquiv_used s f _ a

@[simp] theorem fillSlots_unused (s : A ↪ Fin Δ) (f : A → W)
    (padding : Fin Δ → W) (i : Fin Δ) (h : ¬ ∃ a, s a = i) :
    fillSlots s f padding i = padding i :=
  slotWordsEquiv_unused s f _ ⟨i, h⟩

/-- The local seed correspondence has exactly the expected finite size. -/
theorem card_incident_add_unused (s : A ↪ Fin Δ) :
    Fintype.card A + Fintype.card (Unused s) = Δ := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr (slotIndexEquiv s)

/-- Adding the independent head word gives precisely one universal type.
This finite equivalence is the local combinatorial input to uniformity proofs. -/
def localTypeEquiv (s : A ↪ Fin Δ) (Q : ℕ) :
    (Word Q × ((A → Word Q) × (Unused s → Word Q))) ≃ UniversalType Q Δ :=
  (Equiv.prodCongr (Equiv.refl (Word Q)) (slotWordsEquiv s (Word Q))).trans
    (SubexponentialSAT.Types.equivProd Q Δ).symm

@[simp] theorem localTypeEquiv_head (s : A ↪ Fin Δ) (Q : ℕ) (head : Word Q)
    (f : A → Word Q) (padding : Unused s → Word Q) :
    (localTypeEquiv s Q (head, (f, padding))).head = head := rfl

@[simp] theorem localTypeEquiv_used (s : A ↪ Fin Δ) (Q : ℕ) (head : Word Q)
    (f : A → Word Q) (padding : Unused s → Word Q) (a : A) :
    (localTypeEquiv s Q (head, (f, padding))).slot (s a) = f a :=
  slotWordsEquiv_used s f padding a

@[simp] theorem localTypeEquiv_unused (s : A ↪ Fin Δ) (Q : ℕ) (head : Word Q)
    (f : A → Word Q) (padding : Unused s → Word Q) (i : Unused s) :
    (localTypeEquiv s Q (head, (f, padding))).slot i.val = padding i :=
  slotWordsEquiv_unused s f padding i

end FiniteSlotFilling

section GlobalWords

variable [Fintype E] (P : Pattern V E) {Q Δ : ℕ} (slots : SlotMap P Δ)

/-- Create a coordinate type from one global word per factor and free local data. -/
def typeFromWords (sigma : E → Word Q) (head : V → Word Q)
    (padding : V → Fin Δ → Word Q) (v : V) : UniversalType Q Δ where
  head := head v
  slot := fillSlots (slots v) (fun e => sigma e.val) (padding v)

@[simp] theorem typeFromWords_head (sigma : E → Word Q) (head : V → Word Q)
    (padding : V → Fin Δ → Word Q) (v : V) :
    (typeFromWords P slots sigma head padding v).head = head v := rfl

/-- All incidences of a factor read that same factor's global word. -/
@[simp] theorem typeFromWords_incidence (sigma : E → Word Q) (head : V → Word Q)
    (padding : V → Fin Δ → Word Q) (v : V) (e : Incident P v) :
    (typeFromWords P slots sigma head padding v).slot (slots v e) = sigma e.val :=
  fillSlots_used (slots v) _ _ e

@[simp] theorem typeFromWords_unused (sigma : E → Word Q) (head : V → Word Q)
    (padding : V → Fin Δ → Word Q) (v : V) (i : Fin Δ)
    (h : ¬ ∃ e, slots v e = i) :
    (typeFromWords P slots sigma head padding v).slot i = padding v i :=
  fillSlots_unused (slots v) _ _ i h

/-- The local slot numbers may differ at two incidences; their full words agree. -/
theorem factor_word_consistent (sigma : E → Word Q) (head : V → Word Q)
    (padding : V → Fin Δ → Word Q) (e : E) (v w : V)
    (hv : v ∈ P.scope e) (hw : w ∈ P.scope e) :
    (typeFromWords P slots sigma head padding v).slot (slots v ⟨e, hv⟩) =
      (typeFromWords P slots sigma head padding w).slot (slots w ⟨e, hw⟩) := by
  simp

/-- Dependence on the global word assignment is confined to incident factors. -/
theorem typeFromWords_congr (sigma tau : E → Word Q) (head head' : V → Word Q)
    (padding padding' : V → Fin Δ → Word Q) (v : V)
    (hsigma : ∀ e : Incident P v, sigma e.val = tau e.val)
    (hhead : head v = head' v)
    (hpadding : ∀ i : Unused (slots v), padding v i.val = padding' v i.val) :
    typeFromWords P slots sigma head padding v =
      typeFromWords P slots tau head' padding' v := by
  apply UniversalType.ext hhead
  change slotWordsEquiv (slots v) (Word Q) _ = slotWordsEquiv (slots v) (Word Q) _
  congr 1
  exact Prod.ext (funext hsigma) (funext hpadding)

end GlobalWords

end SubexponentialSAT.SlotAssignment

end OAI.Algorithms
