/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OpenAISemiprime

set_option autoImplicit false

/-!
# Actual generic incidence layout from the pinned source construction

The word search, complete bucket packing, universal swap rows, leftover identity
rows and original-variable pullback are constructed here. The quantitative
premises concern only dimensions, incidence fibres and numerical guards, not
layout existence, row locality or a counting oracle.
-/

namespace RiemannGaussian.SemiprimeSourceLayout
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V E : Type} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable {r Q R : ℕ} [NeZero r]

/-- Explicit duplicate-free finite data consumed by the actual word and bucket scans. -/
structure Enumerations (I V E : Type) (r Q : ℕ) where
  /-- Ordered original incidences. -/
  incidences : FiniteEnumeration I
  /-- Ordered universal incidence types. -/
  types : FiniteEnumeration (UniversalType r Q 1)
  /-- First candidate word. -/
  wordFirst : Word r Q
  /-- Remaining candidate words. -/
  wordTail : List (Word r Q)
  /-- No repeated candidate words. -/
  words_nodup : (wordFirst :: wordTail).Nodup
  /-- All candidate words are enumerated. -/
  words_complete : ∀ w, w ∈ wordFirst :: wordTail
  /-- Exact finite score-term list. -/
  terms : FiniteEnumeration (Packing.ScoreTerm I V Q)
  /-- Word labels for original variables and factors. -/
  indices : FiniteEnumeration (V ⊕ E)

/-- The literal list behind a finite enumeration; no search over layouts. -/
def enumerate (A : Type*) [Fintype A] : FiniteEnumeration A :=
  ⟨Finset.univ.toList, Finset.nodup_toList _, by intro a; simp⟩

/-- All lists needed by the constructor are obtained from the input finite
enumerations and the explicitly finite word/type alphabets. -/
def defaultEnumerations : Enumerations I V E r Q where
  incidences := enumerate I
  types := enumerate (UniversalType r Q 1)
  wordFirst := fun _ => 0
  wordTail := ((Finset.univ : Finset (Word r Q)).erase (fun _ => 0)).toList
  words_nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp, Finset.nodup_toList _⟩
  words_complete := by
    intro w
    by_cases h : w = (fun _ => (0 : Fin r)) <;> simp [h]
  terms := enumerate (Packing.ScoreTerm I V Q)
  indices := enumerate (V ⊕ E)

/-- The incidence-score scale, as used by the published computed packing. -/
def incidenceScale (ε : ℚ) : ℚ :=
  ε * (Fintype.card I : ℚ) / (Fintype.card (UniversalType r Q 1) : ℚ)

/-- The original-variable head-score scale. -/
def headScale : ℚ := (Fintype.card V : ℚ) / (2*(r : ℚ))

/-- Literal conditional-expectation word assignment on explicit enumerations. -/
def searchedWords (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) : Packing.WordAssignment V E r Q :=
  Packing.computedWords owner factor en.wordFirst en.wordTail en.terms.values en.indices.values
    (incidenceScale (I := I) (r := r) (Q := Q) ε) (headScale (V := V) (r := r))

/-- Actual complete bucket packing and its explicit finite scans. -/
def searchedPacking (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) : PackingData I (UniversalType r Q 1) :=
  Packing.computedPacking owner factor en.incidences en.types en.wordFirst en.wordTail
    en.terms.values en.indices.values
    (incidenceScale (I := I) (r := r) (Q := Q) ε) (headScale (V := V) (r := r))

/-- Positive integer interpolation nodes represented exactly over the rationals. -/
def sampleNode (Q : ℕ) (t : Fin Q) : ℚ := (t.val : ℚ)+1

theorem sampleNode_injective (Q : ℕ) : Function.Injective (sampleNode Q) := by
  intro a b hab
  apply Fin.ext
  exact_mod_cast (add_right_cancel hab : (a.val : ℚ) = b.val)

theorem sampleNode_ne_zero (Q : ℕ) (t : Fin Q) : sampleNode Q t ≠ 0 := by
  unfold sampleNode
  positivity

/-- The actual nonzero nodes and node differences are units in the rational field. -/
def sampleUnits (Q : ℕ) : SubexpRowInterpolation.NodeUnits (sampleNode Q) :=
  SubexpRowInterpolation.NodeUnits.ofField (sampleNode Q)
    (sampleNode_injective Q) (sampleNode_ne_zero Q)

/-- The swap construction's public power-of-two denominator, as a rational unit. -/
def denominatorUnit (R : ℕ) : ℚˣ :=
  Units.mk0 (LayoutNumerator.denominator R : ℚ) (by
    simp only [LayoutNumerator.denominator, Int.cast_pow, Int.cast_ofNat]
    positivity)

/-- Universal rows at the source's actual Q-1-centered spectral interval. -/
def universalLayout (r Q R : ℕ) :
    Layout.Data (O := ℚ) (G := Fin r) (id : UniversalType r Q 1 → UniversalType r Q 1)
      (id : UniversalType r Q 1 → UniversalType r Q 1) Q R :=
  LayoutUniversal.data (Subexp.TailInterval.intervalStart r Q R) R
    (denominatorUnit R) rfl (sampleUnits Q)

/-- Constructed original-variable layout: searched complete blocks, identity
leftovers, and the literal owner-fibre pullback. -/
def builtLayout (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R : ℕ) :
    Layout.Data (O := ℚ) (G := Fin r) owner factor Q R :=
  let pack := searchedPacking owner factor en ε
  let words := searchedWords owner factor en ε
  let C := universalLayout r Q R
  let B := LayoutBlocks.data C pack.completeBlocks factor
    (fun e => words (.inr e)) (by intro i t; rfl)
  LayoutHeadPullback.pullback owner factor (fun t v => words (.inl v) t) B
    (by intro t i; rfl)

omit [Fintype E] [NeZero r] in
theorem builtLayout_node (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R : ℕ) (t : Fin Q) :
    (builtLayout owner factor en ε R).node t = sampleNode Q t := rfl

omit [Fintype E] [NeZero r] in
theorem builtLayout_head (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R : ℕ) (t : Fin Q) (v : V) :
    (builtLayout owner factor en ε R).head t v = searchedWords owner factor en ε (.inl v) t := rfl

omit [Fintype E] [NeZero r] in
theorem builtLayout_restoration (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R : ℕ) (i : I) (v : V) :
    ((builtLayout owner factor en ε R).row i v).eval 0 = if v=owner i then 1 else 0 :=
  (builtLayout owner factor en ε R).row_origin i v

omit [Fintype E] [NeZero r] in
theorem builtLayout_degree (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R : ℕ) (i : I) (v : V) :
    ((builtLayout owner factor en ε R).row i v).natDegree ≤ R :=
  (builtLayout owner factor en ε R).row_degree i v

/-- Literal finite incidence and size premises of the generic searched packing. -/
structure PackingGuard (owner : I → V) (factor : I → E) (r Q : ℕ) (ε : ℚ) (B a : ℕ) : Prop where
  /-- Positive packing tolerance. -/
  epsilon_pos : 0 < ε
  /-- Bounded actual owner fibres. -/
  owner_bound : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B
  /-- Bounded actual factor scopes. -/
  factor_bound : ∀ e, (Finset.univ.filter (fun i => factor i = e)).card ≤ a
  /-- At least one actual incidence. -/
  incidence_pos : 0 < Fintype.card I
  /-- At least one actual variable. -/
  variable_pos : 0 < Fintype.card V
  /-- The stronger published packing load guard. -/
  load : 4*((B+a : ℕ) : ℚ)*(Fintype.card (UniversalType r Q 1) : ℚ)^2 ≤
    ε^2*(Fintype.card I : ℚ)
  /-- The stronger published head balance guard. -/
  heads : 16*(Q : ℚ)*(r : ℚ)^2 ≤ (Fintype.card V : ℚ)

theorem searchedPacking_coverage (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (B a : ℕ)
    (h : PackingGuard owner factor r Q ε B a) :
    (1-ε)*(Fintype.card I : ℚ) ≤
      ((searchedPacking owner factor en ε).blockCount : ℚ)*Fintype.card (UniversalType r Q 1) := by
  exact Packing.computedPacking_coverage owner factor en.incidences en.types
    en.wordFirst en.wordTail en.words_nodup en.words_complete
    en.terms.values en.terms.nodup en.terms.complete
    en.indices.values en.indices.nodup en.indices.complete
    ε h.epsilon_pos B a h.owner_bound h.factor_bound h.incidence_pos h.variable_pos h.load h.heads

theorem builtLayout_head_bound (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R B a : ℕ)
    (h : PackingGuard owner factor r Q ε B a) (t : Fin Q) (g : Fin r) :
    (Fintype.card {v : V // (builtLayout owner factor en ε R).head t v = g} : ℚ) ≤
      3*(Fintype.card V : ℚ)/(2*(r : ℚ)) := by
  have hp := Packing.correlated_packing owner factor en.wordFirst en.wordTail
    en.words_nodup en.words_complete en.terms.values en.terms.nodup en.terms.complete
    en.indices.values en.indices.nodup en.indices.complete
    ε h.epsilon_pos B a h.owner_bound h.factor_bound h.incidence_pos h.variable_pos h.load h.heads
  obtain ⟨b, pack, cover, heads⟩ := hp
  rw [Fintype.card_subtype]
  have heq : (Finset.univ.filter (fun v : V => (builtLayout owner factor en ε R).head t v = g)) =
      Packing.headSupport (searchedWords owner factor en ε) t g := by
    apply Finset.ext
    intro v
    rw [Finset.mem_filter, Packing.mem_headSupport]
    exact ⟨fun hv => hv.2, fun hv => ⟨Finset.mem_univ v, hv⟩⟩
  rw [heq]
  exact heads t g

/-- Quantitative rank of the actually constructed original-variable constraints.
Coverage, universal rows and locality are all obtained from the construction. -/
theorem builtLayout_total_rank (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R B a : ℕ)
    (h : PackingGuard owner factor r Q ε B a)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q)
    (hwidth : 32*((Q-1 : ℕ) : ℝ)*Real.log (2/(ε : ℝ)) ≤ (R : ℝ)^2) (t : Fin Q) :
    (∑ g : Fin r, (LayoutRank.rowRank ((builtLayout owner factor en ε R).constraints t g) : ℚ)) ≤
      2*ε*Fintype.card I := by
  exact LayoutRank.actual_pulled_blocks_total_rank_le
    (denominatorUnit R) rfl (sampleUnits Q)
    (searchedPacking owner factor en ε).completeBlocks factor
    (fun e => searchedWords owner factor en ε (.inr e)) (by intro i t; rfl)
    owner (fun t v => searchedWords owner factor en ε (.inl v) t) (by intro t i; rfl)
    t ε hr hQ hR hsize h.epsilon_pos hwidth
    (searchedPacking_coverage owner factor en ε B a h)

#print axioms builtLayout_restoration
#print axioms builtLayout_degree
#print axioms builtLayout_head_bound
#print axioms builtLayout_total_rank
end
end RiemannGaussian.SemiprimeSourceLayout
