/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceLayoutHeight
import RiemannGaussian.SemiprimeLayoutSelection
import RiemannGaussian.SemiprimeCounterSearch

/-!
# The exact counter with its layout certificates constructed from original ports

The input is the original Boolean network and public numerical parameters.
Words, complete blocks, pulled rows, bounded integer constraints, selected
rows and node certificates are constructed, rather than supplied as oracles.
This is a mathematical counter and search correctness theorem; primitive
execution of finite enumerations, row selection and arithmetic remains separate.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeConstructedCounter
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open RiemannGaussian.SemiprimeSourceLayout
open RiemannGaussian.SemiprimeSourceLayoutHeight
open RiemannGaussian.SemiprimeLayoutSelection
open RiemannGaussian.SemiprimeCounterCompose
open RiemannGaussian.SemiprimeCounterSearch
open RiemannGaussian.SemiprimeCountRecovery
open RiemannGaussian.SemiprimeHermiteRecovery
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A E : Type} [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E]

/-- Literal original port incidence type. -/
abbrev Incidence (arity : E → ℕ) := (e : E) × Fin (arity e)

/-- Public layout dimensions and a bound on original coordinate occurrences. -/
structure Parameters (arity : E → ℕ) (coordinate : (e : E) → Fin (arity e) → A) where
  /-- Number of heads. -/
  r : ℕ
  /-- Number of interpolation nodes. -/
  Q : ℕ
  /-- Replacement row degree. -/
  R : ℕ
  /-- Maximum original coordinate occurrence count. -/
  B : ℕ
  /-- Tolerance used by the actual word search. -/
  epsilon : ℚ
  /-- The universal swap alphabet has at least two heads. -/
  groups : 2 ≤ r
  /-- There are at least two interpolation nodes. -/
  nodes : 2 ≤ Q
  /-- The centered spectral interval has sufficient width. -/
  degree : 4 ≤ R
  /-- The centered interval lies in the node range. -/
  size : 4 * R ≤ Q
  /-- The bound concerns original ports, before constructing any rows. -/
  occurrences : ∀ a, (Finset.univ.filter
    (fun i : Incidence arity => coordinate i.1 i.2 = a)).card ≤ B

/-- The public group range supplies the nonempty word alphabet. -/
instance Parameters.groupsNonzero {arity : E → ℕ}
    {coordinate : (e : E) → Fin (arity e) → A} (p : Parameters arity coordinate) :
    NeZero p.r := ⟨by have := p.groups; omega⟩

/-- Sample nodes reindexed by their exact positive rational values. -/
def sampleEquiv (Q : ℕ) : Fin Q ≃ samplePoints Q :=
  Equiv.ofBijective (fun t => ⟨sampleNode Q t, Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩⟩)
    ⟨by
      intro a b h
      exact sampleNode_injective Q (congrArg Subtype.val h), by
      intro t
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp t.property
      exact ⟨i, Subtype.ext hi⟩⟩

theorem sampleEquiv_symm_value (Q : ℕ) (t : samplePoints Q) :
    sampleNode Q ((sampleEquiv Q).symm t) = t.val :=
  congrArg Subtype.val ((sampleEquiv Q).apply_symm_apply t)

variable {arity : E → ℕ} {coordinate : (e : E) → Fin (arity e) → A}

/-- Actual source layout, constructed on the network's dependent port indices. -/
def layout (p : Parameters arity coordinate) :
    Layout.Data (O := ℚ) (G := Fin p.r)
      (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst p.Q p.R :=
  builtLayout (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst
    defaultEnumerations p.epsilon p.R

/-- Literal coefficient bound after original-coordinate pullback. -/
def height (p : Parameters arity coordinate) : ℕ := p.B * 2 * (8 * p.Q) ^ (2 * p.R)

theorem layout_height (p : Parameters arity coordinate) (t : Fin p.Q) (g : Fin p.r)
    (j : Fin ((layout p).rowCount t g)) (v : {v : A // (layout p).head t v = g}) :
    |(layout p).constraints t g j v| ≤ (height p : ℤ) := by
  exact builtLayout_constraints_abs_le _ _ _ _ _ _ p.occurrences (by have := p.nodes; omega)
    (Nat.le_trans (Nat.le_add_right _ _) (OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart_end_le
      p.groups p.degree p.size)) t g j v

/-- The bounded selected-row certificate at an actual source node. -/
def nodeDesign (p : Parameters arity coordinate) (t : Fin p.Q) :
    NodeCertificate arity (nodeRows (layout p) arity (fun e i => ⟨e, i⟩) t) :=
  nodeCertificate (layout p) arity (fun e i => ⟨e, i⟩) (by intro e i; rfl) t
    (fun _ => height p) (layout_height p t)

/-- The actual total rank of the constructed integer constraints. -/
def totalRank (p : Parameters arity coordinate) (t : Fin p.Q) : ℕ :=
  ∑ g, LayoutRank.rowRank ((layout p).constraints t g)

/-- The cardinality of the full finite tuple of stored summaries. -/
def summaryCount (p : Parameters arity coordinate) (t : Fin p.Q) : ℕ :=
  Nat.card ((g : Fin p.r) → (nodeDesign p t).Summary g)

theorem summary_count (p : Parameters arity coordinate) (t : Fin p.Q) :
    summaryCount p t = ∏ g,
      (2 * (Fintype.card {v : A // (layout p).head t v = g} * height p) + 1) ^
        LayoutRank.rowRank ((layout p).constraints t g) := by
  let : Fintype ((g : Fin p.r) → (nodeDesign p t).Summary g) :=
    nodeCertificateTupleFinite (layout p) arity (fun e i => ⟨e, i⟩)
      (by intro e i; rfl) t (fun _ => height p) (layout_height p t)
  exact (Nat.card_eq_fintype_card).trans
    (nodeCertificate_summary_card (layout p) arity (fun e i => ⟨e, i⟩)
      (by intro e i; rfl) t (fun _ => height p) (layout_height p t))

/-- A common summary box with an exponent equal to the actual selected rank. -/
theorem summary_count_le (p : Parameters arity coordinate) (t : Fin p.Q) :
    summaryCount p t ≤ (2 * (Fintype.card A * height p) + 1) ^ totalRank p t := by
  rw [summary_count]
  calc
    _ ≤ ∏ g : Fin p.r, (2 * (Fintype.card A * height p) + 1) ^
        LayoutRank.rowRank ((layout p).constraints t g) := by
      apply Finset.prod_le_prod
      intro g _
      apply Nat.pow_le_pow_left
      have hc := Fintype.card_le_of_injective
        (fun v : {v : A // (layout p).head t v = g} => v.val) Subtype.val_injective
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hc)) 1
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

/-- The rank budget is a theorem about these constructed rows, assuming only
the source's public incidence, load and spectral-width guards. -/
theorem totalRank_le (p : Parameters arity coordinate) (a : ℕ)
    (h : PackingGuard (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst
      p.r p.Q p.epsilon p.B a)
    (hwidth : 32 * ((p.Q - 1 : ℕ) : ℝ) * Real.log (2 / (p.epsilon : ℝ)) ≤ (p.R : ℝ)^2)
    (t : Fin p.Q) :
    (totalRank p t : ℚ) ≤ 2 * p.epsilon * Fintype.card (Incidence arity) := by
  simpa only [totalRank, Nat.cast_sum, layout] using
    builtLayout_total_rank (fun i : Incidence arity => coordinate i.1 i.2) Sigma.fst
      defaultEnumerations p.epsilon p.R p.B a h p.groups p.nodes p.degree p.size hwidth t

/-- The same certificate at the Hermite counter's positive rational sample node. -/
def design (p : Parameters arity coordinate) (t : samplePoints p.Q) :
    NodeCertificate arity (fun e i v => ((layout p).row ⟨e, i⟩ v).eval t) := by
  have h := nodeDesign p ((sampleEquiv p.Q).symm t)
  change NodeCertificate arity (fun e i v =>
    ((layout p).row ⟨e, i⟩ v).eval ((layout p).node ((sampleEquiv p.Q).symm t))) at h
  have hv : (layout p).node ((sampleEquiv p.Q).symm t) = t.val :=
    sampleEquiv_symm_value p.Q t
  rw [hv] at h
  exact h

/-- The counter problem built solely from original tables, coordinates and parameters. -/
def problem (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (p : Parameters arity coordinate) : Problem A E where
  arity := arity
  table := table
  coordinate := coordinate
  coverage := coverage
  rows := fun e i v => (layout p).row ⟨e, i⟩ v
  Q := p.Q
  R := p.R
  Q_pos := by have := p.nodes; omega
  design := design p
  row_degree := fun e i v => (layout p).row_degree ⟨e, i⟩ v
  restoration := fun e i v => (layout p).row_origin ⟨e, i⟩ v

/-- Exact prefix counts with no supplied layout, row span, measurement certificate,
or count-correctness premise. -/
theorem constructed_prefix_count
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (p : Parameters arity coordinate)
    (fixed : List (A × Bool)) :
    prefixCount (problem table coverage p) fixed =
      acceptedCount (restricted assignmentBit (originalPredicate arity table coordinate) fixed) :=
  prefixCount_eq_accepted (problem table coverage p) fixed

/-- Search using the constructed exact counter returns bits of one common original
accepting assignment. This does not assert a primitive running-time bound. -/
theorem constructed_search_sound
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (p : Parameters arity coordinate)
    (indices : List A) (values : List (A × Bool))
    (h : (counterSearch (problem table coverage p) indices).values = some values) :
    values.map Prod.fst = indices ∧ ∃ x,
      originalPredicate arity table coordinate x = true ∧
      ∀ pair ∈ values, assignmentBit x pair.1 = pair.2 :=
  counterSearch_some_sound (problem table coverage p) indices values h

/-- A failed constructed search exactly characterizes an empty original solution set. -/
theorem constructed_search_none
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (p : Parameters arity coordinate)
    (indices : List A) :
    (counterSearch (problem table coverage p) indices).values = none ↔
      ¬ ∃ x, originalPredicate arity table coordinate x = true :=
  counterSearch_none_iff (problem table coverage p) indices

/-- Prefix recovery needs one initial constructed count and at most one per bit. -/
theorem constructed_search_queries
    (table : (e : E) → (Fin (arity e) → Bool) → Bool)
    (coverage : ∀ a, ∃ e i, coordinate e i = a) (p : Parameters arity coordinate)
    (indices : List A) :
    (counterSearch (problem table coverage p) indices).queries ≤ indices.length + 1 :=
  counterSearch_queries_le (problem table coverage p) indices

#print axioms constructed_prefix_count
#print axioms constructed_search_sound
end
end RiemannGaussian.SemiprimeConstructedCounter
