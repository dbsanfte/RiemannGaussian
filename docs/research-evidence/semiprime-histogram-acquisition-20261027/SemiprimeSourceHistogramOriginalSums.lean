/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramGrouping
import RiemannGaussian.SemiprimeSourceIncidenceNamespaces
import RiemannGaussian.SemiprimeSourceIncidenceHistogram
import RiemannGaussian.SemiprimeSourceScoreCountsObjective

/-! # Original compiled score lanes as direct occurrence-pair sums
The quadratic original score list appears only in the specification being
simplified. The right sides use the original port, vertex and coordinate lists,
without assuming an acquired term list, histogram answer or source-count oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceHistogramOriginalSums
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open LocalExpectation MulticolorTypes
open SemiprimeMaterializedScoreEnvironment SemiprimeSourceScoreCountsPadding
open SemiprimeSourceScoreCountsObjective SemiprimeSourceHistogramGrouping

/-- Incidence contribution of an actual descriptor, including literal zero for heads. -/
def incidenceValue {r Q : ℕ} (alphabet : List (Word r Q))
    (remaining : List ℕ) (env : Environment r Q) : ScoreProgram Q→ℕ
  | .incidence a b c d => (paddedLocal alphabet (.incidence a b c d) remaining env).value
  | .head _ _ _ => 0

/-- Head contribution of an actual descriptor, including literal zero for incidences. -/
def headValue {r Q : ℕ} (alphabet : List (Word r Q))
    (remaining : List ℕ) (env : Environment r Q) : ScoreProgram Q→ℕ
  | .incidence _ _ _ _ => 0
  | .head q a b => (paddedLocal alphabet (.head q a b) remaining env).value

/-- The actual ordered recursive lane is its literal descriptor-list sum. -/
theorem evaluate_incidence {r Q : ℕ} (alphabet : List (Word r Q))
    (programs : List (ScoreProgram Q)) (remaining : List ℕ) (env : Environment r Q) :
    (evaluateCounts alphabet programs remaining env).value.incidence=
      (programs.map (incidenceValue alphabet remaining env)).sum := by
  induction programs with
  | nil => rfl
  | cons p ps ih => cases p <;> simp only [evaluateCounts,List.map_cons,List.sum_cons,
      incidenceValue,ih,Nat.zero_add]

/-- The actual ordered recursive head lane is its literal descriptor-list sum. -/
theorem evaluate_head {r Q : ℕ} (alphabet : List (Word r Q))
    (programs : List (ScoreProgram Q)) (remaining : List ℕ) (env : Environment r Q) :
    (evaluateCounts alphabet programs remaining env).value.head=
      (programs.map (headValue alphabet remaining env)).sum := by
  induction programs with
  | nil => rfl
  | cons p ps ih => cases p <;> simp only [evaluateCounts,List.map_cons,List.sum_cons,
      headValue,ih,Nat.zero_add]

/-- Ordered Cartesian-list aggregation retains duplicate occurrences in both inputs. -/
theorem sum_product {A B R : Type*} [AddCommMonoid R] (xs : List A) (ys : List B)
    (f : A×B→R) :
    ((xs.product ys).map f).sum=
      (xs.map (fun a => (ys.map (fun b => f (a,b))).sum)).sum := by
  simp only [List.product]
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_map,
      Function.comp_def,List.map_cons,List.sum_cons,ih]

variable {I V E : Type} [DecidableEq V] [DecidableEq E] {r Q : ℕ}

/-- Actual compiled original incidence lane, with no pairwise term-list premise. -/
theorem compiled_incidence_sum (owner : I→V) (factor : I→E) (indices : List (V⊕E))
    (ports : List I) (vertices : List V) (coordinates : List (Fin Q))
    (alphabet : List (Word r Q)) (remaining : List ℕ) (env : Environment r Q) :
    (evaluateCounts alphabet
      (SemiprimeMaterializedSourceWords.compileAll owner factor indices
        (SemiprimePaidFiniteEnumerations.scores ports vertices coordinates).value).value
      remaining env).value.incidence=
    pairs ports (fun i j => (paddedLocal alphabet
      (.incidence (indexCode indices (.inl (owner i))) (indexCode indices (.inr (factor i)))
        (indexCode indices (.inl (owner j))) (indexCode indices (.inr (factor j)))) remaining env).value) := by
  rw [evaluate_incidence,SemiprimeMaterializedSourceWords.compileAll_value,
    SemiprimePaidFiniteEnumerations.scores_value]
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,
    SemiprimeMaterializedSourceWords.descriptor,incidenceValue]
  simp only [List.map_const',List.sum_replicate,smul_zero,add_zero]
  exact sum_product (R:=ℕ) ports ports _

/-- Actual compiled original head lane, with the original coordinate/vertex order. -/
theorem compiled_head_sum (owner : I→V) (factor : I→E) (indices : List (V⊕E))
    (ports : List I) (vertices : List V) (coordinates : List (Fin Q))
    (alphabet : List (Word r Q)) (remaining : List ℕ) (env : Environment r Q) :
    (evaluateCounts alphabet
      (SemiprimeMaterializedSourceWords.compileAll owner factor indices
        (SemiprimePaidFiniteEnumerations.scores ports vertices coordinates).value).value
      remaining env).value.head=
    (coordinates.map (fun q => pairs vertices (fun v w => (paddedLocal alphabet
      (.head q (indexCode indices (.inl v)) (indexCode indices (.inl w))) remaining env).value))).sum := by
  rw [evaluate_head,SemiprimeMaterializedSourceWords.compileAll_value,
    SemiprimePaidFiniteEnumerations.scores_value]
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,
    SemiprimeMaterializedSourceWords.descriptor,headValue]
  simp only [List.map_const',List.sum_replicate,smul_zero,zero_add]
  rw [sum_product]
  congr 1
  apply List.map_congr_left
  intro q _
  exact sum_product (R:=ℕ) vertices vertices _


/-- Casting an actual ordered integer pair sum preserves both list multiplicities. -/
theorem cast_pairs {A : Type*} (xs : List A) (f : A→A→ℕ) :
    ((pairs xs f:ℕ):ℚ)=pairs xs (fun a b => (f a b:ℚ)) := by
  simp only [pairs,Nat.cast_list_sum,List.map_map,Function.comp_def]

/-- Derived sparse head formula: fixed-colour and free-variable-key buckets.
Every bucket is a literal sum over the original occurrence list. -/
def headHistogram {V : Type*} (vertices : List V) (key : V→ℕ)
    (r Q : ℕ) (q : Fin Q) (remaining : List ℕ) (env : Environment r Q) : ℚ :=
  let colour := fun k => denote env k q
  let fixed : V→ℚ := fun v => if key v∈remaining then 0 else 1
  let free : V→ℚ := fun v => if key v∈remaining then 1 else 0
  let A : ℚ := ((r^Q)^4:ℕ)
  let B : ℚ := (r^(4*Q-1):ℕ)
  A*(∑ c∈(vertices.map (fun v => colour (key v))).toFinset,
      (bucket (fun v => colour (key v)) vertices fixed c)^2)+
    B*(((vertices.map (fun _ => (1:ℚ))).sum)^2-((vertices.map fixed).sum)^2)+
    (A-B)*(∑ k∈(vertices.map key).toFinset,(bucket key vertices free k)^2)

/-- All-prefix original padded head-pair sum, with no histogram input or answer. -/
theorem head_pairs_histogram {V : Type*} (vertices : List V) (key : V→ℕ)
    (r Q : ℕ) (q : Fin Q) (remaining : List ℕ) (env : Environment r Q)
    (hn : remaining.Nodup) :
    ((pairs vertices (fun v w => (paddedLocal (SemiprimeFiniteEnumerations.words r Q).values
      (.head q (key v) (key w)) remaining env).value):ℕ):ℚ)=
      headHistogram vertices key r Q q remaining env := by
  rw [cast_pairs]
  have hpoint : (fun v w => ((paddedLocal (SemiprimeFiniteEnumerations.words r Q).values
      (.head q (key v) (key w)) remaining env).value:ℚ))=
      (fun v w => if key v=key w then (((r^Q)^4:ℕ):ℚ)
        else if key v∈remaining ∨ key w∈remaining then ((r^(4*Q-1):ℕ):ℚ)
        else if denote env (key v) q=denote env (key w) q then (((r^Q)^4:ℕ):ℚ) else 0) := by
    funext v w
    rw [SemiprimeSourceHeadCountFormula.head_padded_original r Q q (key v) (key w) remaining env hn]
    split_ifs <;> rfl
  rw [hpoint]
  exact head_prefix_grouping vertices key (fun k => denote env k q)
    (fun k => k∈remaining) (((r^Q)^4:ℕ):ℚ) ((r^(4*Q-1):ℕ):ℚ)

/-- The actual complete compiled head lane is acquired from vertex/coordinate
lists alone; no quadratic source-term list occurs on the histogram side. -/
theorem compiled_head_histogram (owner : I→V) (factor : I→E) (indices : List (V⊕E))
    (ports : List I) (vertices : List V) (coordinates : List (Fin Q))
    (remaining : List ℕ) (env : Environment r Q) (hn : remaining.Nodup) :
    (((evaluateCounts (SemiprimeFiniteEnumerations.words r Q).values
      (SemiprimeMaterializedSourceWords.compileAll owner factor indices
        (SemiprimePaidFiniteEnumerations.scores ports vertices coordinates).value).value
      remaining env).value.head:ℕ):ℚ)=
    (coordinates.map (fun q => headHistogram vertices
      (fun v => indexCode indices (.inl v)) r Q q remaining env)).sum := by
  rw [compiled_head_sum]
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro q _
  exact head_pairs_histogram vertices (fun v => indexCode indices (.inl v)) r Q q remaining env hn


/-- Complete original indices discharge every namespace condition; the actual
compiled incidence lane is exactly sixteen sparse occurrence histograms. -/
theorem compiled_incidence_histogram (owner : I→V) (factor : I→E)
    (indices : List (V⊕E)) (hc : ∀ z,z∈indices)
    (ports : List I) (vertices : List V) (coordinates : List (Fin Q))
    (hr : 0<r) (remaining : List ℕ) (env : Environment r Q) (hn : remaining.Nodup) :
    (((evaluateCounts (SemiprimeFiniteEnumerations.words r Q).values
      (SemiprimeMaterializedSourceWords.compileAll owner factor indices
        (SemiprimePaidFiniteEnumerations.scores ports vertices coordinates).value).value
      remaining env).value.incidence:ℕ):ℚ)=
    ((r^Q:ℕ):ℚ)^2*SemiprimeSourceIncidenceHistogram.histogramSum ((r^Q:ℕ):ℚ)
      ports remaining (denote env)
      (fun i => indexCode indices (.inl (owner i)))
      (fun i => indexCode indices (.inr (factor i))) := by
  rw [compiled_incidence_sum,cast_pairs]
  exact SemiprimeSourceIncidenceHistogram.original_incidence_pairs ports
    (fun i => indexCode indices (.inl (owner i)))
    (fun i => indexCode indices (.inr (factor i))) r Q hr remaining env hn
    (fun i _ j _ => SemiprimeSourceIncidenceNamespaces.indexCode_cross indices hc (owner i) (factor j))

end RiemannGaussian.SemiprimeSourceHistogramOriginalSums
