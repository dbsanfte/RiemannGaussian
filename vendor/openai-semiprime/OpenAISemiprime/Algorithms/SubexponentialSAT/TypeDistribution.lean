import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SlotAssignment
import OpenAISemiprime.Algorithms.SubexponentialSAT.Variance
import OpenAISemiprime.Algorithms.SubexponentialSAT.ConditionalExpectation

namespace OAI.Algorithms

/-!
# Uniform words induce uniform local types

The outcome space consists of all assignments of words to distinct factor,
head, and padding indices. Local read maps are injective. Read maps at
distinct coordinates sharing no factor have disjoint ranges. Finite product
counting then supplies the actual marginals and pair moments needed by
SubexponentialSAT.Variance; these probabilistic properties are conclusions, not hypotheses.
-/

namespace SubexponentialSAT.TypeDistribution

open scoped BigOperators
open SubexponentialSAT.Types SubexponentialSAT.SlotAssignment SubexponentialSAT.Variance

section FiniteMeans

variable {A B I J W : Type*}

theorem mean_equiv [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℚ) :
    mean uniformWeight (fun a => f (e a)) = mean uniformWeight f := by
  rw [mean_uniformWeight, mean_uniformWeight, e.sum_comp, Fintype.card_congr e]

theorem mean_prod_fst [Fintype A] [Fintype B] [Nonempty B] (f : A → ℚ) :
    mean uniformWeight (fun p : A × B => f p.1) = mean uniformWeight f := by
  have hb : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mean_uniformWeight, mean_uniformWeight, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    Fintype.card_prod, Nat.cast_mul]
  rw [mul_comm (Fintype.card A : ℚ) (Fintype.card B : ℚ)]
  exact mul_div_mul_left _ _ hb

theorem mean_prod_mul [Fintype A] [Fintype B] (f : A → ℚ) (g : B → ℚ) :
    mean uniformWeight (fun p : A × B => f p.1 * g p.2) =
      mean uniformWeight f * mean uniformWeight g := by
  rw [mean_uniformWeight, mean_uniformWeight, mean_uniformWeight,
    Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, Fintype.card_prod, Nat.cast_mul]
  exact mul_div_mul_comm _ _ _ _

theorem mean_indicator [Fintype A] [DecidableEq A] (u : A) :
    mean uniformWeight (fun a : A => if a = u then (1 : ℚ) else 0) =
      1 / (Fintype.card A : ℚ) := by
  rw [mean_uniformWeight]
  simp

/-- Coordinates outside the image of an injective read map. -/
abbrev Unread (e : J ↪ I) := {i : I // i ∉ Set.range e}

/-- Split a global assignment into the read coordinates and all remaining ones. -/
noncomputable def splitReads (e : J ↪ I) (W : Type*) :
    (I → W) ≃ (J → W) × (Unread e → W) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun i => i ∈ Set.range e) (fun _ => W)).trans
    (Equiv.prodCongr
      (Equiv.arrowCongr (Equiv.ofInjective e e.injective).symm (Equiv.refl W))
      (Equiv.refl _))

@[simp] theorem splitReads_fst (e : J ↪ I) (ω : I → W) :
    (splitReads e W ω).1 = fun j => ω (e j) := rfl

/-- Restricting independent uniform coordinates along an injection is uniform. -/
theorem mean_restrict [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype W] [Nonempty W]
    (e : J ↪ I) (f : (J → W) → ℚ) :
    mean uniformWeight (fun ω : I → W => f (fun j => ω (e j))) =
      mean uniformWeight f := by
  classical
  calc
    _ = mean uniformWeight (fun p : (J → W) × (Unread e → W) => f p.1) :=
      mean_equiv (splitReads e W) _
    _ = _ := mean_prod_fst f

/-- Combine two disjoint injective sets of reads into a single injection. -/
def jointReads (e : A ↪ I) (f : B ↪ I) (h : ∀ a b, e a ≠ f b) : A ⊕ B ↪ I where
  toFun := Sum.elim e f
  inj' := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (e.injective hab)
      | inr b => exact (h a b hab).elim
    | inr a =>
      cases b with
      | inl b => exact (h b a hab.symm).elim
      | inr b => exact congrArg Sum.inr (f.injective hab)

/-- Functions of disjoint sets of independent uniform coordinates have
factorizing pair moments. -/
theorem mean_restrict_mul [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype W] [Nonempty W]
    (e : A ↪ I) (f : B ↪ I) (h : ∀ a b, e a ≠ f b)
    (F : (A → W) → ℚ) (G : (B → W) → ℚ) :
    mean uniformWeight (fun ω : I → W =>
      F (fun a => ω (e a)) * G (fun b => ω (f b))) =
      mean uniformWeight F * mean uniformWeight G := by
  calc
    _ = mean uniformWeight (fun ξ : A ⊕ B → W =>
        F (fun a => ξ (.inl a)) * G (fun b => ξ (.inr b))) :=
      mean_restrict (jointReads e f h) _
    _ = mean uniformWeight (fun p : (A → W) × (B → W) => F p.1 * G p.2) :=
      mean_equiv (Equiv.sumArrowEquivProdArrow A B W)
        (fun p : (A → W) × (B → W) => F p.1 * G p.2)
    _ = _ := mean_prod_mul F G

end FiniteMeans

section EnumeratedExpectations

variable {I W A B : Type*}

theorem mean_prod_nested [Fintype A] [Fintype B] (F : A × B → ℚ) :
    mean uniformWeight F =
      mean uniformWeight (fun a : A => mean uniformWeight (fun b : B => F (a, b))) := by
  simp only [mean_uniformWeight, Fintype.sum_prod_type, Fintype.card_prod,
    Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, Finset.sum_mul, mul_assoc]

/-- An explicit duplicate-free complete alphabet has the uniform finite mean. -/
theorem list_mean_eq_uniform [Fintype W] [DecidableEq W]
    (alphabet : List W) (hnodup : alphabet.Nodup) (hfull : ∀ w, w ∈ alphabet)
    (f : W → ℚ) :
    SubexponentialSAT.ConditionalExpectation.mean alphabet f = mean uniformWeight f := by
  have hset : alphabet.toFinset = (Finset.univ : Finset W) := by
    ext w
    simp [hfull w]
  rw [mean_uniformWeight]
  unfold SubexponentialSAT.ConditionalExpectation.mean
  rw [← List.sum_toFinset f hnodup, hset,
    ← List.toFinset_card_of_nodup hnodup, hset, Finset.card_univ]

/-- Swap an assignment coordinate with one fresh word. This is a permutation
of the full product outcome space, including the old coordinate value. -/
def resampleEquiv [DecidableEq I] (i : I) : ((I → W) × W) ≃ ((I → W) × W) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    apply Prod.ext
    · funext j
      by_cases h : j = i
      · subst j; simp
      · simp [Function.update_of_ne h]
    · simp
  right_inv p := by
    apply Prod.ext
    · funext j
      by_cases h : j = i
      · subst j; simp
      · simp [Function.update_of_ne h]
    · simp

/-- Resampling any single word preserves the uniform mean. -/
theorem mean_resample [Fintype I] [DecidableEq I] [Fintype W] [Nonempty W]
    (i : I) (f : (I → W) → ℚ) :
    mean uniformWeight (fun ω : I → W =>
      mean uniformWeight (fun w : W => f (Function.update ω i w))) =
      mean uniformWeight f := by
  calc
    _ = mean uniformWeight (fun p : (I → W) × W =>
        f (Function.update p.1 i p.2)) := (mean_prod_nested _).symm
    _ = mean uniformWeight (fun p : (I → W) × W => f p.1) :=
      mean_equiv (resampleEquiv i) (fun p : (I → W) × W => f p.1)
    _ = _ := mean_prod_fst f

/-- Bridge from a recursively enumerated word expectation to the uniform
finite mean. Completeness of the coordinate list suffices: repeated resampling
of a coordinate also preserves the uniform distribution. The recursion
equations are explicit hypotheses so this applies to independently implemented
finite evaluators without introducing a second algorithm definition. -/
theorem recursive_word_mean_eq_uniform
    [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W] [Nonempty W]
    (alphabet : List W) (hnodup : alphabet.Nodup) (hfull : ∀ w, w ∈ alphabet)
    (f : (I → W) → ℚ) (expect : List I → (I → W) → ℚ)
    (hzero : ∀ ω, expect [] ω = f ω)
    (hstep : ∀ i xs ω, expect (i :: xs) ω =
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => expect xs (Function.update ω i w)))
    (indices : List I) (hcover : ∀ i, i ∈ indices) (ω : I → W) :
    expect indices ω = mean uniformWeight f := by
  have hcongr : ∀ (xs : List I) (a b : I → W),
      (∀ i, i ∉ xs → a i = b i) → expect xs a = expect xs b := by
    intro xs
    induction xs with
    | nil =>
      intro a b h
      have hab : a = b := funext fun i => h i (by simp)
      rw [hab]
    | cons i xs ih =>
      intro a b h
      rw [hstep, hstep]
      apply congrArg (SubexponentialSAT.ConditionalExpectation.mean alphabet)
      funext w
      apply ih
      intro j hj
      by_cases hji : j = i
      · subst j; simp
      · simp only [Function.update_of_ne hji]
        exact h j (by simp [hji, hj])
  have havg (xs : List I) : mean uniformWeight (expect xs) = mean uniformWeight f := by
    induction xs with
    | nil =>
      apply congrArg (mean uniformWeight)
      funext a
      exact hzero a
    | cons i xs ih =>
      calc
        _ = mean uniformWeight (fun a : I → W =>
            mean uniformWeight (fun w : W => expect xs (Function.update a i w))) := by
          apply congrArg (mean uniformWeight)
          funext a
          rw [hstep, list_mean_eq_uniform alphabet hnodup hfull]
        _ = mean uniformWeight (expect xs) := mean_resample i (expect xs)
        _ = _ := ih
  have hc : expect indices = (fun _ : I → W => expect indices ω) := by
    funext a
    apply hcongr
    intro i hi
    exact (hi (hcover i)).elim
  calc
    expect indices ω = mean uniformWeight (fun _ : I → W => expect indices ω) :=
      (mean_const uniformWeight uniformWeight_sum _).symm
    _ = mean uniformWeight (expect indices) := congrArg (mean uniformWeight) hc.symm
    _ = _ := havg indices

end EnumeratedExpectations

section TypeCollisions

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq U]

theorem sum_fiberCount (τ : V → U) :
    (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ)) =
      (Fintype.card V : ℚ) := by
  have hc (u : U) :
      ((Finset.univ.filter fun v => τ v = u).card : ℚ) =
        ∑ v : V, if τ v = u then (1 : ℚ) else 0 := by simp
  simp_rw [hc]
  rw [Finset.sum_comm]
  simp

/-- Squared fiber counts count ordered pairs in the same fiber. -/
theorem sum_fiberCount_sq (τ : V → U) :
    (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ) ^ 2) =
      ∑ v : V, ∑ w : V, if τ v = τ w then (1 : ℚ) else 0 := by
  have hc (u : U) :
      ((Finset.univ.filter fun v => τ v = u).card : ℚ) =
        ∑ v : V, if τ v = u then (1 : ℚ) else 0 := by simp
  calc
    _ = ∑ u : U, ∑ v : V, ∑ w : V,
        (if τ v = u then (1 : ℚ) else 0) * (if τ w = u then (1 : ℚ) else 0) := by
      simp_rw [hc, pow_two, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ v : V, ∑ w : V, ∑ u : U,
        (if τ v = u then (1 : ℚ) else 0) * (if τ w = u then (1 : ℚ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      simp [ eq_comm]

/-- The global squared-deviation potential is a sum of local pair-collision
indicators minus a constant. This is the efficient-evaluation interface. -/
theorem squared_deviation_eq_collisions [Nonempty U] (τ : V → U) :
    (∑ u : U, (((Finset.univ.filter fun v => τ v = u).card : ℚ) -
      (Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2) =
      (∑ v : V, ∑ w : V, if τ v = τ w then (1 : ℚ) else 0) -
        (Fintype.card V : ℚ) ^ 2 / (Fintype.card U : ℚ) := by
  have hN : (Fintype.card U : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hexpand :
      (∑ u : U, (((Finset.univ.filter fun v => τ v = u).card : ℚ) -
        (Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2) =
      (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ) ^ 2) -
        2 * ((Fintype.card V : ℚ) / (Fintype.card U : ℚ)) *
          (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ)) +
        (Fintype.card U : ℚ) *
          ((Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2 := by
    calc
      _ = ∑ u : U,
          (((Finset.univ.filter fun v => τ v = u).card : ℚ) ^ 2 -
          (2 * ((Fintype.card V : ℚ) / (Fintype.card U : ℚ))) *
            ((Finset.univ.filter fun v => τ v = u).card : ℚ) +
          ((Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hexpand, sum_fiberCount_sq, sum_fiberCount]
  field_simp
  ring

end TypeCollisions

section GlobalAssignments

open SubexponentialSAT.Factor

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable (P : Pattern V E) {Q Δ : ℕ} (slots : SlotMap P Δ)

/-- Each factor, head, and padding slot has a distinct independent word. -/
abbrev SeedIndex (V E : Type*) (Δ : ℕ) := E ⊕ (V ⊕ (V × Fin Δ))

/-- A complete assignment of all independent random words. -/
abbrev Assignment (V E : Type*) (Q Δ : ℕ) := SeedIndex V E Δ → Word Q

/-- A head position and one position for every slot. -/
abbrev LocalCoord (Δ : ℕ) := Unit ⊕ Fin Δ

/-- The same local positions, distinguishing used and unused slots. -/
abbrev LocalParts (v : V) :=
  Unit ⊕ (Incident P v ⊕ Unused (slots v))

def rawRead (v : V) : LocalParts P slots v → SeedIndex V E Δ
  | .inl _ => .inr (.inl v)
  | .inr (.inl e) => .inl e.val
  | .inr (.inr i) => .inr (.inr (v, i.val))

omit [DecidableEq E] [Fintype E] in
theorem rawRead_injective (v : V) : Function.Injective (rawRead P slots v) := by
  intro a b h
  rcases a with ⟨⟩ | (e | i) <;> rcases b with ⟨⟩ | (f | j)
  all_goals simp_all [rawRead, Subtype.ext_iff]

def localCoordEquiv (v : V) : LocalCoord Δ ≃ LocalParts P slots v :=
  Equiv.sumCongr (Equiv.refl Unit) (slotIndexEquiv (slots v)).symm

/-- Every local type coordinate reads a different underlying word. -/
def reads (v : V) : LocalCoord Δ ↪ SeedIndex V E Δ :=
  (localCoordEquiv P slots v).toEmbedding.trans
    ⟨rawRead P slots v, rawRead_injective P slots v⟩

omit [DecidableEq E] in
@[simp] theorem reads_head (v : V) :
    reads P slots v (.inl ()) = .inr (.inl v) := rfl

omit [DecidableEq E] in
@[simp] theorem reads_used (v : V) (e : Incident P v) :
    reads P slots v (.inr (slots v e)) = .inl e.val := by
  change rawRead P slots v (.inr ((slotIndexEquiv (slots v)).symm (slots v e))) = _
  rw [← slotIndexEquiv_inl (slots v) e, Equiv.symm_apply_apply]
  rfl

omit [DecidableEq E] in
@[simp] theorem reads_unused (v : V) (i : Unused (slots v)) :
    reads P slots v (.inr i.val) = .inr (.inr (v, i.val)) := by
  change rawRead P slots v (.inr ((slotIndexEquiv (slots v)).symm i.val)) = _
  rw [← slotIndexEquiv_inr (slots v) i, Equiv.symm_apply_apply]
  rfl

/-- Functions on the local read positions are precisely universal types. -/
def wordTypeEquiv (Q Δ : ℕ) : (LocalCoord Δ → Word Q) ≃ UniversalType Q Δ where
  toFun f := ⟨f (.inl ()), fun i => f (.inr i)⟩
  invFun u := Sum.elim (fun _ => u.head) u.slot
  left_inv f := by
    funext a
    rcases a with ⟨⟩ | i <;> rfl
  right_inv u := by cases u; rfl

/-- Types induced by one full assignment of independent words. -/
def assignmentType (ω : Assignment V E Q Δ) (v : V) : UniversalType Q Δ :=
  wordTypeEquiv Q Δ (fun a => ω (reads P slots v a))

omit [DecidableEq E] in
/-- This read-map presentation is the actual slot assignment of Section 5.4. -/
theorem assignmentType_eq_typeFromWords (ω : Assignment V E Q Δ) (v : V) :
    assignmentType P slots ω v =
      typeFromWords P slots
        (fun e => ω (.inl e)) (fun v => ω (.inr (.inl v)))
        (fun v i => ω (.inr (.inr (v, i)))) v := by
  apply UniversalType.ext
  · rfl
  · funext i
    by_cases h : ∃ e, slots v e = i
    · obtain ⟨e, rfl⟩ := h
      change ω (reads P slots v (.inr (slots v e))) = _
      rw [reads_used, typeFromWords_incidence]
    · change ω (reads P slots v (.inr i)) = _
      rw [reads_unused P slots v ⟨i, h⟩, typeFromWords_unused P slots _ _ _ v i h]

omit [DecidableEq E] [Fintype E] in
/-- Distinct chunks without a common factor have disjoint raw read indices. -/
theorem rawRead_ne {v w : V} (hvw : v ≠ w)
    (hshare : ∀ e, v ∈ P.scope e → w ∉ P.scope e)
    (a : LocalParts P slots v) (b : LocalParts P slots w) :
    rawRead P slots v a ≠ rawRead P slots w b := by
  intro h
  rcases a with ⟨⟩ | (e | i) <;> rcases b with ⟨⟩ | (f | j)
  all_goals simp [rawRead] at h
  · exact hvw h
  · exact hshare e.val e.property (h.symm ▸ f.property)
  · exact hvw h.1

omit [DecidableEq E] in
theorem reads_ne {v w : V} (hvw : v ≠ w)
    (hshare : ∀ e, v ∈ P.scope e → w ∉ P.scope e)
    (a b : LocalCoord Δ) : reads P slots v a ≠ reads P slots w b :=
  rawRead_ne P slots hvw hshare (localCoordEquiv P slots v a)
    (localCoordEquiv P slots w b)

/-- The exact finite set of source words read by one coordinate. -/
def readSupport (v : V) : Finset (SeedIndex V E Δ) :=
  Finset.univ.image (reads P slots v)

theorem readSupport_card (v : V) : (readSupport P slots v).card = Δ + 1 := by
  rw [readSupport, Finset.card_image_of_injective _ (reads P slots v).injective]
  simp [LocalCoord, Nat.add_comm]

theorem assignmentType_congr (ω ω' : Assignment V E Q Δ) (v : V)
    (h : ∀ i ∈ readSupport P slots v, ω i = ω' i) :
    assignmentType P slots ω v = assignmentType P slots ω' v := by
  unfold assignmentType
  congr 1
  funext a
  exact h _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)

/-- Shared factors are counted only once in the union of two read supports. -/
def pairSupport (v w : V) : Finset (SeedIndex V E Δ) :=
  readSupport P slots v ∪ readSupport P slots w

theorem pairSupport_card_le (v w : V) :
    (pairSupport P slots v w).card ≤ 2 * (Δ + 1) := by
  calc
    _ ≤ (readSupport P slots v).card + (readSupport P slots w).card :=
      Finset.card_union_le _ _
    _ = _ := by rw [readSupport_card, readSupport_card]; omega

/-- Rational indicator that two coordinate types coincide. -/
def pairCollision (ω : Assignment V E Q Δ) (v w : V) : ℚ :=
  if assignmentType P slots ω v = assignmentType P slots ω w then 1 else 0

theorem pairCollision_congr (ω ω' : Assignment V E Q Δ) (v w : V)
    (h : ∀ i ∈ pairSupport P slots v w, ω i = ω' i) :
    pairCollision P slots ω v w = pairCollision P slots ω' v w := by
  have hv := assignmentType_congr P slots ω ω' v
    (fun i hi => h i (Finset.mem_union_left _ hi))
  have hw := assignmentType_congr P slots ω ω' w
    (fun i hi => h i (Finset.mem_union_right _ hi))
  simp only [pairCollision, hv, hw]

variable [Fintype V]

omit [DecidableEq E] in
/-- The exact potential used for derandomization is a sum of local pair terms. -/
theorem assignment_deviation_eq_collisions (ω : Assignment V E Q Δ) :
    (∑ u : UniversalType Q Δ,
      ((typeCount (assignmentType P slots) u ω : ℚ) -
        (Fintype.card V : ℚ) / (Fintype.card (UniversalType Q Δ) : ℚ)) ^ 2) =
      (∑ v : V, ∑ w : V, pairCollision P slots ω v w) -
        (Fintype.card V : ℚ) ^ 2 / (Fintype.card (UniversalType Q Δ) : ℚ) := by
  let _ : Nonempty (UniversalType Q Δ) :=
    ⟨⟨fun _ => false, fun _ _ => false⟩⟩
  exact squared_deviation_eq_collisions (assignmentType P slots ω)

/-- The full law of a coordinate type is uniform, derived from its read injection. -/
theorem mean_assignmentType (v : V) (F : UniversalType Q Δ → ℚ) :
    mean uniformWeight (fun ω : Assignment V E Q Δ => F (assignmentType P slots ω v)) =
      mean uniformWeight F := by
  calc
    _ = mean uniformWeight
        (fun ξ : LocalCoord Δ → Word Q => F (wordTypeEquiv Q Δ ξ)) :=
      mean_restrict (reads P slots v) _
    _ = _ := mean_equiv (wordTypeEquiv Q Δ) F

/-- Types at distinct coordinates sharing no factor have factorizing moments. -/
theorem mean_assignmentType_mul {v w : V} (hvw : v ≠ w)
    (hshare : ∀ e, v ∈ P.scope e → w ∉ P.scope e)
    (F G : UniversalType Q Δ → ℚ) :
    mean uniformWeight (fun ω : Assignment V E Q Δ =>
      F (assignmentType P slots ω v) * G (assignmentType P slots ω w)) =
      mean uniformWeight F * mean uniformWeight G := by
  calc
    _ = mean uniformWeight (fun ξ : LocalCoord Δ → Word Q => F (wordTypeEquiv Q Δ ξ)) *
        mean uniformWeight (fun ξ : LocalCoord Δ → Word Q => G (wordTypeEquiv Q Δ ξ)) :=
      mean_restrict_mul (reads P slots v) (reads P slots w)
        (reads_ne P slots hvw hshare) _ _
    _ = _ := by rw [mean_equiv, mean_equiv]

/-- The single-coordinate indicator moment required by the variance theorem. -/
theorem assignmentType_marginal (u : UniversalType Q Δ) (v : V) :
    mean uniformWeight
      (fun ω : Assignment V E Q Δ => typeIndicator (assignmentType P slots) u ω v) =
        1 / (Fintype.card (UniversalType Q Δ) : ℚ) := by
  exact (mean_assignmentType P slots v
    (fun a => if a = u then (1 : ℚ) else 0)).trans (mean_indicator u)

/-- The independent pair moment required by the variance theorem.
Adjacent chunks need not satisfy this conclusion and are not assumed to. -/
theorem assignmentType_independent (u : UniversalType Q Δ) {v w : V} (hvw : v ≠ w)
    (hshare : ∀ e, v ∈ P.scope e → w ∉ P.scope e) :
    mean uniformWeight (fun ω : Assignment V E Q Δ =>
      typeIndicator (assignmentType P slots) u ω v *
        typeIndicator (assignmentType P slots) u ω w) =
      (1 / (Fintype.card (UniversalType Q Δ) : ℚ)) *
        (1 / (Fintype.card (UniversalType Q Δ) : ℚ)) := by
  calc
    _ = mean uniformWeight (fun a => if a = u then (1 : ℚ) else 0) *
        mean uniformWeight (fun a => if a = u then (1 : ℚ) else 0) :=
      mean_assignmentType_mul P slots hvw hshare _ _
    _ = _ := by rw [mean_indicator]

/-- Expected squared type-count deviation for the actual independent word
assignment, with the manuscript's conservative dependency-degree bound. -/
theorem mean_squared_deviation_le {k : ℕ} (hP : P.Bounded k Δ) :
    mean uniformWeight (fun ω : Assignment V E Q Δ =>
      ∑ u : UniversalType Q Δ,
        ((typeCount (assignmentType P slots) u ω : ℚ) -
          (Fintype.card V : ℚ) / (Fintype.card (UniversalType Q Δ) : ℚ)) ^ 2) ≤
      (Fintype.card (UniversalType Q Δ) : ℚ) *
        (1 + (Δ * k : ℕ)) * (Fintype.card V : ℚ) := by
  apply sum_typeCount_variances_le uniformWeight uniformWeight_nonneg uniformWeight_sum
    (assignmentType P slots) (assignmentType_marginal P slots)
    (SubexponentialSAT.Incidence.dependencyNeighbors P.scope) (Δ * k)
  · intro v
    exact (SubexponentialSAT.Incidence.bounded_card_dependencyNeighbors_le P v k Δ hP).trans
      (Nat.mul_le_mul_left Δ (Nat.sub_le k 1))
  · intro u v w hvw hn
    apply assignmentType_independent P slots u hvw
    intro e hv hw
    apply hn
    exact (SubexponentialSAT.Incidence.mem_dependencyNeighbors P.scope v w).mpr
      ⟨Ne.symm hvw, e, hv, hw⟩

/-- A concrete global word assignment satisfying (5.8) exists.
This uses the finite averaging theorem; the sequential computable minimizer
is supplied separately in ConditionalExpectation. -/
theorem exists_assignment_deviation_le {k : ℕ} (hP : P.Bounded k Δ) :
    ∃ ω : Assignment V E Q Δ,
      (∑ u : UniversalType Q Δ,
        ((typeCount (assignmentType P slots) u ω : ℚ) -
          (Fintype.card V : ℚ) / (Fintype.card (UniversalType Q Δ) : ℚ)) ^ 2) ≤
        (Fintype.card (UniversalType Q Δ) : ℚ) *
          (1 + (Δ * k : ℕ)) * (Fintype.card V : ℚ) := by
  apply SubexponentialSAT.ConditionalExpectation.exists_le_of_uniform_mean_le
  rw [← mean_uniformWeight]
  exact mean_squared_deviation_le P slots hP

/-- Direct layout interface: one global word per factor and a consistent
coordinate type assignment, with the full squared-deviation guarantee. -/
theorem exists_consistent_types_deviation_le {k : ℕ} (hP : P.Bounded k Δ) :
    ∃ (sigma : E → Word Q) (τ : V → UniversalType Q Δ),
      (∀ (v : V) (e : Incident P v), (τ v).slot (slots v e) = sigma e.val) ∧
      (∑ u : UniversalType Q Δ,
        (((Finset.univ.filter fun v => τ v = u).card : ℚ) -
          (Fintype.card V : ℚ) / (Fintype.card (UniversalType Q Δ) : ℚ)) ^ 2) ≤
        (Fintype.card (UniversalType Q Δ) : ℚ) *
          (1 + (Δ * k : ℕ)) * (Fintype.card V : ℚ) := by
  obtain ⟨ω, hω⟩ := exists_assignment_deviation_le (Q := Q) P slots hP
  refine ⟨fun e => ω (.inl e), assignmentType P slots ω, ?_, hω⟩
  intro v e
  rw [assignmentType_eq_typeFromWords, typeFromWords_incidence]

end GlobalAssignments

end SubexponentialSAT.TypeDistribution

end OAI.Algorithms
