/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterPacketHeight

/-!
# Explicit partial separated-fibre accumulators

Finite local-localSets sets and label-localSets sets are expanded into actual loop
records. Inactive groups have one dummy Boolean choice, not a multiplicity.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace RiemannGaussian.SemiprimeFibreAccumulatorHeight
open scoped BigOperators
open Polynomial
open SemiprimeCounterCompose SemiprimeCounterPacketHeight SemiprimeCounterSeparation
open SemiprimeCounterNative SemiprimeStreamingTensor SemiprimeJetArrayHeight
attribute [local instance] Classical.propDecidable

variable {G Y : Type*} [Fintype G] [DecidableEq G] {L : G → Type*}

/-- Actual localSets choices, with a sole dummy assignment for inactive groups. -/
def options (groups : Finset G) (localSets : (g : G) → Finset (L g → Bool))
    (g : G) : Finset (L g → Bool) :=
  if g ∈ groups then localSets g else {fun _ => false}

/-- The actual gated local factor in the product-of-localSets-sums expansion. -/
def leaf (groups : Finset G) (gate : (g : G) → (L g → Bool) → Prop)
    (value : (g : G) → (L g → Bool) → Polynomial ℚ)
    (g : G) (a : L g → Bool) : Polynomial ℚ :=
  if g ∈ groups then if gate g a then value g a else 0 else 1

/-- Exact expansion of a partial product of partial local sums. -/
theorem partial_product_expansion (groups : Finset G)
    (localSets : (g : G) → Finset (L g → Bool))
    (gate : (g : G) → (L g → Bool) → Prop)
    (value : (g : G) → (L g → Bool) → Polynomial ℚ) :
    (∏ g ∈ groups, ∑ a ∈ localSets g, if gate g a then value g a else 0) =
      ∑ a ∈ Fintype.piFinset (options groups localSets), ∏ g, leaf groups gate value g (a g) := by
  have hlocal (g : G) :
      (∑ a ∈ options groups localSets g, leaf groups gate value g a) =
      if g ∈ groups then ∑ a ∈ localSets g, if gate g a then value g a else 0 else 1 := by
    by_cases hg : g ∈ groups <;> simp [options, leaf, hg]
  rw [← Finset.prod_univ_sum]
  simp_rw [hlocal]
  simp only [← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Literal zero-or-one weight of all selected local gates. -/
def gateWeight (groups : Finset G) (gate : (g : G) → (L g → Bool) → Prop)
    (a : (g : G) → L g → Bool) : ℤ :=
  if ∀ g ∈ groups, gate g (a g) then 1 else 0

/-- Gating is factored as a literal 0/1 scalar before any sum cancellation. -/
theorem product_leaf (groups : Finset G)
    (gate : (g : G) → (L g → Bool) → Prop)
    (value : (g : G) → (L g → Bool) → Polynomial ℚ)
    (a : (g : G) → L g → Bool) :
    (∏ g, leaf groups gate value g (a g)) =
      C (gateWeight groups gate a : ℚ) * ∏ g ∈ groups, value g (a g) := by
  have hprod : (∏ g, leaf groups gate value g (a g)) =
      ∏ g ∈ groups, if gate g (a g) then value g (a g) else 0 := by
    simp only [leaf]
    exact (Finset.prod_filter (fun g => g ∈ groups)
      (fun g => if gate g (a g) then value g (a g) else 0)).symm.trans (by simp)
  rw [hprod]
  by_cases h : ∀ g ∈ groups, gate g (a g)
  · simp only [gateWeight, ite_eq_left h, Int.cast_one, C_1, one_mul]
    apply Finset.prod_congr rfl
    intro g hg
    rw [ite_eq_left (h g hg)]
  · simp only [gateWeight, ite_eq_right h, Int.cast_zero, C_0, zero_mul]
    push Not at h
    obtain ⟨g, hg, hgate⟩ := h
    exact Finset.prod_eq_zero hg (by simp only [ite_eq_right hgate])

/-- Explicit prefix records: each label paired with its actual finite local choices. -/
def records (labels : Finset Y) (groups : Finset G)
    (localSets : Y → (g : G) → Finset (L g → Bool)) :
    Finset ((_y : Y) × ((g : G) → L g → Bool)) :=
  labels.sigma (fun y => Fintype.piFinset (options groups (localSets y)))

/-- A prefix record family never exceeds labels times all Boolean assignments. -/
theorem records_card_le [∀ g, Fintype (L g)] (labels : Finset Y) (groups : Finset G)
    (localSets : Y → (g : G) → Finset (L g → Bool)) :
    (records labels groups localSets).card ≤ labels.card * Fintype.card ((g : G) → L g → Bool) := by
  rw [records, Finset.card_sigma]
  calc
    _ ≤ ∑ _y ∈ labels, Fintype.card ((g : G) → L g → Bool) :=
      Finset.sum_le_sum (fun _ _ => Finset.card_le_univ _)
    _ = _ := by simp

/-- Full signed label-localSets expansion, with every selected local-localSets choice. -/
theorem accumulator_expansion (labels : Finset Y) (groups : Finset G)
    (localSets : Y → (g : G) → Finset (L g → Bool))
    (gate : Y → (g : G) → (L g → Bool) → Prop)
    (value : Y → (g : G) → (L g → Bool) → Polynomial ℚ) (weight : Y → ℤ) :
    (∑ y ∈ labels, C (weight y : ℚ) *
      ∏ g ∈ groups, ∑ a ∈ localSets y g, if gate y g a then value y g a else 0) =
      ∑ rec ∈ records labels groups localSets,
        C ((weight rec.1 * gateWeight groups (gate rec.1) rec.2 : ℤ) : ℚ) *
          ∏ g ∈ groups, value rec.1 g (rec.2 g) := by
  simp_rw [partial_product_expansion, product_leaf]
  simp only [records, Finset.sum_sigma, Finset.mul_sum, Int.cast_mul, C_mul, mul_assoc]

/-- A selected product of fibre products is precisely the selected-factor product. -/
theorem prod_selected_fibres {E C : Type*} [Fintype E] [CommMonoid C]
    (assigned : E → G) (groups : Finset G) (f : E → C) :
    (∏ g ∈ groups, ∏ e ∈ Finset.univ.filter (fun e => assigned e=g), f e) =
      ∏ e ∈ Finset.univ.filter (fun e => assigned e ∈ groups), f e := by
  classical
  have h := Fintype.prod_fiberwise assigned (fun e => if assigned e ∈ groups then f e else 1)
  have hi (g : G) :
      (∏ e : {e // assigned e=g}, if assigned e.val ∈ groups then f e.val else 1) =
      if g ∈ groups then ∏ e ∈ Finset.univ.filter (fun e => assigned e=g), f e else 1 := by
    have hr : ∀ e : {e // assigned e=g},
        (if assigned e.val ∈ groups then f e.val else 1) = (if g ∈ groups then f e.val else 1) := by
      intro e
      rw [e.property]
    simp_rw [hr]
    by_cases hg : g ∈ groups
    · simp only [ite_eq_left hg]
      exact (Finset.prod_subtype (p := fun e => assigned e=g)
        (Finset.univ.filter (fun e => assigned e=g)) (by intro e; simp) f).symm
    · simp only [ite_eq_right hg, Finset.prod_const_one]
  simp_rw [hi] at h
  simpa only [← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] using h

section Native
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

/-- Actual full Boolean representative/update used by one group scan. -/
def state (arity : E → ℕ) (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ)
    (t : ℚ) (d : NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (label : (g : d.Group) → d.Summary g) (g : d.Group) (a : d.Local g → Bool) :
    (g : d.Group) → d.Local g → Bool := Function.update (d.representative label) g a

/-- Actual corrected local group value at its recorded representative/update. -/
def nativeValue (arity : E → ℕ) (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (label : (g : d.Group) → d.Summary g) (U : Finset V) (g : d.Group) (a : d.Local g → Bool) : Polynomial ℚ :=
  groupValue arity (fun e b => (Tentry e b : ℚ)) d.assigned
    (groupedRows arity (fun e i v => (rows e i v).eval t) d)
    (nativeCorrection arity rows t R U) g (state arity rows t d label g a)

/-- Factor-dependent Boolean bases retain each group's actual recorded update. -/
def nativeBase (arity : E → ℕ) (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ)
    (t : ℚ) (d : NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (label : (g : d.Group) → d.Summary g) (a : (g : d.Group) → d.Local g → Bool) (e : E) : Finset V :=
  (splitAssignment d.grouping).symm (state arity rows t d label (d.assigned e) (a (d.assigned e)))

/-- The actual partial group product is a masked native factor product with
independent recorded bases; no measurement or row-span cancellation is used. -/
theorem native_product_eq [DecidableEq E] (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t)) (groups : Finset d.Group)
    (label : (g : d.Group) → d.Summary g) (U : Finset V) (a : (g : d.Group) → d.Local g → Bool) :
    (∏ g ∈ groups, nativeValue arity Tentry rows t R d label U g (a g)) =
      nativeTerm arity (fun e b => if d.assigned e ∈ groups then Tentry e b else 1)
        rows t R (nativeBase arity rows t d label a) U := by
  let f := fun e => evaluate (arity e) (fun b => C (Tentry e b : ℚ))
    (fun i => correctedPort (rows e i) t R (nativeBase arity rows t d label a e) U)
  have hg (g : d.Group) : nativeValue arity Tentry rows t R d label U g (a g) =
      ∏ e ∈ Finset.univ.filter (fun e => d.assigned e=g), f e := by
    let x := (splitAssignment d.grouping).symm (state arity rows t d label g (a g))
    have h := groupValue_corrected_product arity Tentry rows t R d g x U
    simp only [x, Equiv.apply_symm_apply] at h
    rw [nativeValue, h]
    apply Finset.prod_congr rfl
    intro e he
    have heq := (Finset.mem_filter.mp he).2
    dsimp only [f, nativeBase]
    rw [heq]
  simp_rw [hg]
  rw [prod_selected_fibres]
  have hmask := masked_nativeTerm (Finset.univ.filter (fun e => d.assigned e ∈ groups))
    arity Tentry rows t R (nativeBase arity rows t d label a) U
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, f] using hmask.symm

/-- The literal measurement/forced-coordinate gate of the counter's local scan. -/
def nativeGate (arity : E → ℕ) (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ)
    (t : ℚ) (d : NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (label : (g : d.Group) → d.Summary g) (S : Finset V) (g : d.Group) (a : d.Local g → Bool) : Prop :=
  d.measurement g a=label g ∧ localForced arity (fun e i v => (rows e i v).eval t) d S g a

/-- Actual signed label-prefix/product-of-local-prefix-sums expression. -/
def nativeAccumulator (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (labels : Finset Y) (groups : Finset d.Group)
    (localSets : Y → (g : d.Group) → Finset (d.Local g → Bool))
    (label : Y → (g : d.Group) → d.Summary g) (forced correction : Y → Finset V) (weight : Y → ℤ) : Polynomial ℚ :=
  ∑ y ∈ labels, C (weight y : ℚ) * ∏ g ∈ groups, ∑ a ∈ localSets y g,
    if nativeGate arity rows t d (label y) (forced y) g a then
      nativeValue arity Tentry rows t R d (label y) (correction y) g a else 0

omit [Fintype E] in
/-- Prefix records use no more than 2^n Boolean choices for each label. -/
theorem native_records_card (arity : E → ℕ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (labels : Finset Y) (groups : Finset d.Group)
    (localSets : Y → (g : d.Group) → Finset (d.Local g → Bool)) :
    (records labels groups localSets).card ≤ labels.card * 2^Fintype.card V := by
  have hc : Fintype.card ((g : d.Group) → d.Local g → Bool) = 2^Fintype.card V := by
    calc
      _ = Fintype.card (Finset V) := (Fintype.card_congr (splitAssignment d.grouping)).symm
      _ = _ := by simp
  simpa only [hc] using records_card_le labels groups localSets

/-- The actual partial accumulator expands to 0/1-gated selected native terms. -/
theorem nativeAccumulator_expansion [DecidableEq E] (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (d : NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (labels : Finset Y) (groups : Finset d.Group)
    (localSets : Y → (g : d.Group) → Finset (d.Local g → Bool))
    (label : Y → (g : d.Group) → d.Summary g) (forced correction : Y → Finset V) (weight : Y → ℤ) :
    nativeAccumulator arity Tentry rows t R d labels groups localSets label forced correction weight =
      ∑ rec ∈ records labels groups localSets,
        C ((weight rec.1*gateWeight groups
          (nativeGate arity rows t d (label rec.1) (forced rec.1)) rec.2 : ℤ) : ℚ) *
        nativeTerm arity (fun e b => if d.assigned e ∈ groups then Tentry e b else 1)
          rows t R (nativeBase arity rows t d (label rec.1) rec.2) (correction rec.1) := by
  unfold nativeAccumulator
  rw [accumulator_expansion]
  simp_rw [native_product_eq]

/-- Actual partial summary/fibre accumulators have one original-incidence
power denominator, with every label and local-prefix record counted. -/
theorem built_accumulator_representation [DecidableEq E] (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    {r Q : ℕ} (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T J : ℕ) (hJ : 1 ≤ J)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hentry : ∀ e a, |Tentry e a| ≤ 1) (t : ℤ) (ht : |t| ≤ (T : ℤ))
    (d : NodeCertificate arity (fun e i v => ((builtRows arity owner en ε R) e i v).eval (t : ℚ)))
    (labels : Finset Y) (groups : Finset d.Group)
    (localSets : Y → (g : d.Group) → Finset (d.Local g → Bool))
    (label : Y → (g : d.Group) → d.Summary g) (forced correction : Y → Finset V)
    (weight : Y → ℤ) (hw : ∀ y ∈ labels, |weight y| ≤ 1) (k : ℕ) (hk : k < J) :
    Representation ((nativeAccumulator arity Tentry (builtRows arity owner en ε R) (t : ℚ) R d
      labels groups localSets label forced correction weight).coeff k)
      ((SemiprimeSourceRowHeight.rowDenominator Q R)^(∑ e, arity e))
      (labels.card*2^Fintype.card V*termBound (V := V) arity
        (SemiprimeSourceRowHeight.rowDenominator Q R) R (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) T J) := by
  rw [nativeAccumulator_expansion]
  have hmask : ∀ e b, |(if d.assigned e ∈ groups then Tentry e b else 1 : ℤ)| ≤ 1 := by
    intro e b
    split_ifs
    · exact hentry e b
    · norm_num
  have hweight : ∀ rec ∈ records labels groups localSets,
      |weight rec.1*gateWeight groups
        (nativeGate arity (builtRows arity owner en ε R) (t : ℚ) d (label rec.1) (forced rec.1)) rec.2| ≤ 1 := by
    intro rec hr
    have hy := (Finset.mem_sigma.mp hr).1
    have hg : |gateWeight groups
        (nativeGate arity (builtRows arity owner en ε R) (t : ℚ) d (label rec.1) (forced rec.1)) rec.2| ≤ 1 := by
      unfold gateWeight
      split_ifs <;> norm_num
    rw [abs_mul]
    exact (mul_le_mul (hw rec.1 hy) hg (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have h := built_signed_terms_representation (records labels groups localSets) arity
    (fun e b => if d.assigned e ∈ groups then Tentry e b else 1) owner en ε R B T J hJ
    howner hQ hAQ hmask t ht
    (fun rec => nativeBase arity (builtRows arity owner en ε R) (t : ℚ) d (label rec.1) rec.2)
    (fun rec => correction rec.1)
    (fun rec => weight rec.1*gateWeight groups
      (nativeGate arity (builtRows arity owner en ε R) (t : ℚ) d (label rec.1) (forced rec.1)) rec.2)
    hweight k hk
  apply representation_mono h
  exact Nat.mul_le_mul_right _ (native_records_card arity (builtRows arity owner en ε R) (t : ℚ) d labels groups localSets)

/-- Different label records may stop at different group/local prefixes. This
includes all completed records and the currently unfinished nested-loop record. -/
theorem built_varying_accumulator_representation [DecidableEq E] (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    {r Q : ℕ} (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T J : ℕ) (hJ : 1 ≤ J)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hentry : ∀ e a, |Tentry e a| ≤ 1) (t : ℤ) (ht : |t| ≤ (T : ℤ))
    (d : NodeCertificate arity (fun e i v => ((builtRows arity owner en ε R) e i v).eval (t : ℚ)))
    (labels : Finset Y) (groups : Y → Finset d.Group)
    (localSets : Y → (g : d.Group) → Finset (d.Local g → Bool))
    (label : Y → (g : d.Group) → d.Summary g) (forced correction : Y → Finset V)
    (weight : Y → ℤ) (hw : ∀ y ∈ labels, |weight y| ≤ 1) (k : ℕ) (hk : k < J) :
    Representation ((∑ y ∈ labels, C (weight y : ℚ) * ∏ g ∈ groups y, ∑ a ∈ localSets y g,
      if nativeGate arity (builtRows arity owner en ε R) (t : ℚ) d (label y) (forced y) g a then
        nativeValue arity Tentry (builtRows arity owner en ε R) (t : ℚ) R d (label y) (correction y) g a else 0).coeff k)
      ((SemiprimeSourceRowHeight.rowDenominator Q R)^(∑ e, arity e))
      (labels.card*2^Fintype.card V*termBound (V := V) arity
        (SemiprimeSourceRowHeight.rowDenominator Q R) R (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) T J) := by
  rw [Polynomial.finsetSum_coeff]
  have h := representation_sum labels
    (fun y => (C (weight y : ℚ) * ∏ g ∈ groups y, ∑ a ∈ localSets y g,
      if nativeGate arity (builtRows arity owner en ε R) (t : ℚ) d (label y) (forced y) g a then
        nativeValue arity Tentry (builtRows arity owner en ε R) (t : ℚ) R d (label y) (correction y) g a else 0).coeff k)
    ((SemiprimeSourceRowHeight.rowDenominator Q R)^(∑ e, arity e))
    (2^Fintype.card V*termBound (V := V) arity (SemiprimeSourceRowHeight.rowDenominator Q R) R
      (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) T J) (by
        intro y hy
        have hh := built_accumulator_representation arity Tentry owner en ε R B T J hJ howner hQ hAQ
          hentry t ht d {y} (groups y) localSets label forced correction weight (by
            intro z hz
            have he : z=y := Finset.mem_singleton.mp hz
            subst z
            exact hw y hy) k hk
        simpa only [nativeAccumulator, Finset.sum_singleton, Finset.card_singleton, one_mul] using hh)
  convert h using 1
  ring

/-- Record-dependent constant-one factor masks also cover unfinished local
factor products without changing the original scopes or incidence denominator. -/
theorem built_recordwise_accumulator_representation [DecidableEq E] (arity : E → ℕ)
    (Tentry : Y → (e : E) → (Fin (arity e) → Bool) → ℤ)
    {r Q : ℕ} (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T J : ℕ) (hJ : 1 ≤ J)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (t : ℤ) (ht : |t| ≤ (T : ℤ))
    (d : NodeCertificate arity (fun e i v => ((builtRows arity owner en ε R) e i v).eval (t : ℚ)))
    (labels : Finset Y) (hentry : ∀ y ∈ labels, ∀ e a, |Tentry y e a| ≤ 1)
    (groups : Y → Finset d.Group)
    (localSets : Y → (g : d.Group) → Finset (d.Local g → Bool))
    (label : Y → (g : d.Group) → d.Summary g) (forced correction : Y → Finset V)
    (weight : Y → ℤ) (hw : ∀ y ∈ labels, |weight y| ≤ 1) (k : ℕ) (hk : k < J) :
    Representation ((∑ y ∈ labels, C (weight y : ℚ) * ∏ g ∈ groups y, ∑ a ∈ localSets y g,
      if nativeGate arity (builtRows arity owner en ε R) (t : ℚ) d (label y) (forced y) g a then
        nativeValue arity (Tentry y) (builtRows arity owner en ε R) (t : ℚ) R d (label y) (correction y) g a else 0).coeff k)
      ((SemiprimeSourceRowHeight.rowDenominator Q R)^(∑ e, arity e))
      (labels.card*2^Fintype.card V*termBound (V := V) arity
        (SemiprimeSourceRowHeight.rowDenominator Q R) R (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) T J) := by
  rw [Polynomial.finsetSum_coeff]
  have h := representation_sum labels
    (fun y => (C (weight y : ℚ) * ∏ g ∈ groups y, ∑ a ∈ localSets y g,
      if nativeGate arity (builtRows arity owner en ε R) (t : ℚ) d (label y) (forced y) g a then
        nativeValue arity (Tentry y) (builtRows arity owner en ε R) (t : ℚ) R d (label y) (correction y) g a else 0).coeff k)
    ((SemiprimeSourceRowHeight.rowDenominator Q R)^(∑ e, arity e))
    (2^Fintype.card V*termBound (V := V) arity (SemiprimeSourceRowHeight.rowDenominator Q R) R
      (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) T J) (by
        intro y hy
        have hh := built_accumulator_representation arity (Tentry y) owner en ε R B T J hJ howner hQ hAQ
          (hentry y hy) t ht d {y} (groups y) localSets label forced correction weight (by
            intro z hz
            have he : z=y := Finset.mem_singleton.mp hz
            subst z
            exact hw y hy) k hk
        simpa only [nativeAccumulator, Finset.sum_singleton, Finset.card_singleton, one_mul] using hh)
  convert h using 1
  ring

end Native

end RiemannGaussian.SemiprimeFibreAccumulatorHeight

#print axioms RiemannGaussian.SemiprimeFibreAccumulatorHeight.built_accumulator_representation
#print axioms RiemannGaussian.SemiprimeFibreAccumulatorHeight.built_varying_accumulator_representation

#print axioms RiemannGaussian.SemiprimeFibreAccumulatorHeight.built_recordwise_accumulator_representation
