/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFiniteEnumerations
import RiemannGaussian.SemiprimeConstructedCounter

/-!
# Constructed counters on explicit source enumerations

Every source list is a supplied concrete enumeration, and indexed-network
instances below use the compiled finite-list constructors. No equality to
classical defaultEnumerations is assumed or required. Row interpolation,
selected certificates and scalar counter execution retain their stated scope.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace RiemannGaussian.SemiprimeEnumeratedCounter
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open SemiprimeSourceLayout SemiprimeSourceLayoutHeight SemiprimeLayoutSelection
open SemiprimeCounterCompose SemiprimeCounterSearch SemiprimeCountRecovery SemiprimeHermiteRecovery
open SemiprimeConstructedCounter
attribute [local instance] Classical.propDecidable
variable {A E : Type} [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E]
variable {arity : E → ℕ} {coordinate : (e : E) → Fin (arity e) → A}

/-- Concrete finite inputs consumed by this particular source constructor. -/
abbrev EnumerationData (p : Parameters arity coordinate) :=
  SemiprimeSourceLayout.Enumerations (Incidence arity) A E p.r p.Q

/-- Actual source layout, constructed on the network's dependent port indices. -/
def layout (p : Parameters arity coordinate) (en : EnumerationData p) :
    Layout.Data (O := ℚ) (G := Fin p.r)
      (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst p.Q p.R :=
  builtLayout (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst
    en p.epsilon p.R

/-- Every selected original integer constraint retains the native height bound. -/
theorem layout_height (p : Parameters arity coordinate) (en : EnumerationData p) (t : Fin p.Q) (g : Fin p.r)
    (j : Fin ((layout p en).rowCount t g)) (v : {v : A // (layout p en).head t v = g}) :
    |(layout p en).constraints t g j v| ≤ (height p : ℤ) := by
  exact builtLayout_constraints_abs_le _ _ _ _ _ _ p.occurrences (by have := p.nodes; omega)
    (Nat.le_trans (Nat.le_add_right _ _) (OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart_end_le
      p.groups p.degree p.size)) t g j v

/-- The bounded selected-row certificate at an actual source node. -/
def nodeDesign (p : Parameters arity coordinate) (en : EnumerationData p) (t : Fin p.Q) :
    NodeCertificate arity (nodeRows (layout p en) arity (fun e i => ⟨e, i⟩) t) :=
  nodeCertificate (layout p en) arity (fun e i => ⟨e, i⟩) (by intro e i; rfl) t
    (fun _ => height p) (layout_height p en t)

/-- The actual total rank of the constructed integer constraints. -/
def totalRank (p : Parameters arity coordinate) (en : EnumerationData p) (t : Fin p.Q) : ℕ :=
  ∑ g, LayoutRank.rowRank ((layout p en).constraints t g)

/-- The cardinality of the full finite tuple of stored summaries. -/
def summaryCount (p : Parameters arity coordinate) (en : EnumerationData p) (t : Fin p.Q) : ℕ :=
  Nat.card ((g : Fin p.r) → (nodeDesign p en t).Summary g)

theorem summary_count (p : Parameters arity coordinate) (en : EnumerationData p) (t : Fin p.Q) :
    summaryCount p en t = ∏ g,
      (2 * (Fintype.card {v : A // (layout p en).head t v = g} * height p) + 1) ^
        LayoutRank.rowRank ((layout p en).constraints t g) := by
  let : Fintype ((g : Fin p.r) → (nodeDesign p en t).Summary g) :=
    nodeCertificateTupleFinite (layout p en) arity (fun e i => ⟨e, i⟩)
      (by intro e i; rfl) t (fun _ => height p) (layout_height p en t)
  exact (Nat.card_eq_fintype_card).trans
    (nodeCertificate_summary_card (layout p en) arity (fun e i => ⟨e, i⟩)
      (by intro e i; rfl) t (fun _ => height p) (layout_height p en t))

/-- A common summary box with an exponent equal to the actual selected rank. -/
theorem summary_count_le (p : Parameters arity coordinate) (en : EnumerationData p) (t : Fin p.Q) :
    summaryCount p en t ≤ (2 * (Fintype.card A * height p) + 1) ^ totalRank p en t := by
  rw [summary_count]
  calc
    _ ≤ ∏ g : Fin p.r, (2 * (Fintype.card A * height p) + 1) ^
        LayoutRank.rowRank ((layout p en).constraints t g) := by
      apply Finset.prod_le_prod
      intro g _
      apply Nat.pow_le_pow_left
      have hc := Fintype.card_le_of_injective
        (fun v : {v : A // (layout p en).head t v = g} => v.val) Subtype.val_injective
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hc)) 1
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

/-- The rank budget is a theorem about these constructed rows, assuming only
the source's public incidence, load and spectral-width guards. -/
theorem totalRank_le (p : Parameters arity coordinate) (en : EnumerationData p) (a : ℕ)
    (h : PackingGuard (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst
      p.r p.Q p.epsilon p.B a)
    (hwidth : 32 * ((p.Q - 1 : ℕ) : ℝ) * Real.log (2 / (p.epsilon : ℝ)) ≤ (p.R : ℝ)^2)
    (t : Fin p.Q) :
    (totalRank p en t : ℚ) ≤ 2 * p.epsilon * Fintype.card (Incidence arity) := by
  simpa only [totalRank, Nat.cast_sum, layout] using
    builtLayout_total_rank (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst
      en p.epsilon p.R p.B a h p.groups p.nodes p.degree p.size hwidth t

/-- The same certificate at the Hermite counter's positive rational sample node. -/
def design (p : Parameters arity coordinate) (en : EnumerationData p) (t : samplePoints p.Q) :
    NodeCertificate arity (fun e i v => ((layout p en).row ⟨e, i⟩ v).eval t) := by
  have h := nodeDesign p en ((sampleEquiv p.Q).symm t)
  change NodeCertificate arity (fun e i v =>
    ((layout p en).row ⟨e, i⟩ v).eval ((layout p en).node ((sampleEquiv p.Q).symm t))) at h
  have hv : (layout p en).node ((sampleEquiv p.Q).symm t) = t.val :=
    sampleEquiv_symm_value p.Q t
  rw [hv] at h
  exact h

/-- The counter problem built solely from original tables, coordinates and parameters. -/
def problem (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (p : Parameters arity coordinate) (en : EnumerationData p) : Problem A E where
  arity := arity
  table := table
  coordinate := coordinate
  coverage := coverage
  rows := fun e i v => (layout p en).row ⟨e, i⟩ v
  Q := p.Q
  R := p.R
  Q_pos := by have := p.nodes; omega
  design := design p en
  row_degree := fun e i v => (layout p en).row_degree ⟨e, i⟩ v
  restoration := fun e i v => (layout p en).row_origin ⟨e, i⟩ v

/-- Exact prefix counts with no supplied layout, row span, measurement certificate,
or count-correctness premise. -/
theorem constructed_prefix_count
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (p : Parameters arity coordinate) (en : EnumerationData p)
    (fixed : List (A × Bool)) :
    prefixCount (problem table coverage p en) fixed =
      acceptedCount (restricted assignmentBit (originalPredicate arity table coordinate) fixed) :=
  prefixCount_eq_accepted (problem table coverage p en) fixed

/-- Search using the constructed exact counter returns bits of one common original
accepting assignment. This does not assert a primitive running-time bound. -/
theorem constructed_search_sound
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (p : Parameters arity coordinate) (en : EnumerationData p)
    (indices : List A) (values : List (A × Bool))
    (h : (counterSearch (problem table coverage p en) indices).values = some values) :
    values.map Prod.fst = indices ∧ ∃ x,
      originalPredicate arity table coordinate x = true ∧
      ∀ pair ∈ values, assignmentBit x pair.1 = pair.2 :=
  counterSearch_some_sound (problem table coverage p en) indices values h

/-- A failed constructed search exactly characterizes an empty original solution set. -/
theorem constructed_search_none
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (p : Parameters arity coordinate) (en : EnumerationData p)
    (indices : List A) :
    (counterSearch (problem table coverage p en) indices).values = none ↔
      ¬ ∃ x, originalPredicate arity table coordinate x = true :=
  counterSearch_none_iff (problem table coverage p en) indices

/-- Prefix recovery needs one initial constructed count and at most one per bit. -/
theorem constructed_search_queries
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (p : Parameters arity coordinate) (en : EnumerationData p)
    (indices : List A) :
    (counterSearch (problem table coverage p en) indices).queries ≤ indices.length + 1 :=
  counterSearch_queries_le (problem table coverage p en) indices


/-- The actual head labels are supplied by the compiled word-search data path. -/
theorem layout_head_computed (p : Parameters arity coordinate) (en : EnumerationData p)
    (t : Fin p.Q) (v : A) :
    (layout p en).head t v = SemiprimeFiniteEnumerations.searchWords
      (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst en p.epsilon (.inl v) t := by
  rw [SemiprimeFiniteEnumerations.searchWords_eq]
  rfl

/-- Actual computed bucket coverage on the same explicit enumeration inputs. -/
theorem computed_packing_coverage (p : Parameters arity coordinate) (en : EnumerationData p) (a : ℕ)
    (h : PackingGuard (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst
      p.r p.Q p.epsilon p.B a) :
    (1-p.epsilon)*(Fintype.card (Incidence arity) : ℚ) ≤
      ((SemiprimeFiniteEnumerations.searchPacking
        (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst en p.epsilon).blockCount : ℚ)*
        Fintype.card (OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType p.r p.Q 1) := by
  rw [SemiprimeFiniteEnumerations.searchPacking_eq]
  exact searchedPacking_coverage _ _ en p.epsilon p.B a h

/-- Fin-indexed original networks receive the fully compiled enumeration data. -/
def indexedEnumerationData {n m : ℕ} {arity : Fin m → ℕ}
    {coordinate : (e : Fin m) → Fin (arity e) → Fin n} (p : Parameters arity coordinate) : EnumerationData p :=
  SemiprimeFiniteEnumerations.indexed n m p.r p.Q arity

/-- Exact constructed indexed-network prefix count on its actual finite lists. -/
theorem indexed_prefix_count {n m : ℕ} {arity : Fin m → ℕ}
    {coordinate : (e : Fin m) → Fin (arity e) → Fin n}
    (table : (e : Fin m) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i=a) (p : Parameters arity coordinate)
    (fixed : List (Fin n × Bool)) :
    prefixCount (problem table coverage p (indexedEnumerationData p)) fixed =
      acceptedCount (restricted assignmentBit (originalPredicate arity table coordinate) fixed) :=
  constructed_prefix_count table coverage p (indexedEnumerationData p) fixed

end RiemannGaussian.SemiprimeEnumeratedCounter
#print axioms RiemannGaussian.SemiprimeEnumeratedCounter.indexed_prefix_count
#print axioms RiemannGaussian.SemiprimeEnumeratedCounter.totalRank_le
