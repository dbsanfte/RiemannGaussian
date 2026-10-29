/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramOriginalSums
import RiemannGaussian.SemiprimeSourceHistogramMetadata

/-! # Original score lanes from actual sparse metadata acquisition
The original quadratic descriptor construction is confined to the specification.
The histogram side consumes only the new actually acquired ports, vertices,
coordinates and indices. No advised score list or histogram answer is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceHistogramAcquiredSums
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedScoreEnvironment SemiprimeSourceScoreCountsObjective
open SemiprimeSourceHistogramOriginalSums

/-- The old materialized score menu is exactly the menu from the new actual
primitive lists; this is a proof identity, not a runtime call to scores. -/
theorem original_terms (n F Q : ℕ) (arity : Fin F→ℕ) :
    (SemiprimeSourceWordIdMetadata.acquire n F Q arity).terms=
    (SemiprimePaidFiniteEnumerations.scores
      (SemiprimeSourceHistogramMetadata.acquire n F Q arity).incidences
      (SemiprimeSourceHistogramMetadata.acquire n F Q arity).vertices
      (SemiprimeSourceHistogramMetadata.acquire n F Q arity).coordinates).value := by
  rw [(SemiprimeSourceHistogramMetadata.original_fields n F Q arity).1]
  simp only [SemiprimeSourceHistogramMetadata.acquire,
    SemiprimeSourceWordIdMetadata.acquire,SemiprimeSourceHistogramMetadata.finFast_value,
    SemiprimePaidFiniteEnumerationLists.fin_value]

/-- Complete actual original incidence/head lanes from acquired sparse metadata,
for every original prefix and arbitrary original environment. -/
theorem acquired_original_lanes (n F r Q : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (hr : 0<r)
    (remaining : List ℕ) (env : Environment r Q) (hn : remaining.Nodup) :
    let old := SemiprimeSourceWordIdMetadata.acquire n F Q arity
    let data := SemiprimeSourceHistogramMetadata.acquire n F Q arity
    let counts := (evaluateCounts (SemiprimeFiniteEnumerations.words r Q).values
      (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst old.indices old.terms).value
      remaining env).value
    ((counts.incidence:ℕ):ℚ)=((r^Q:ℕ):ℚ)^2*
      SemiprimeSourceIncidenceHistogram.histogramSum ((r^Q:ℕ):ℚ) data.incidences
        remaining (denote env)
        (fun i => OAI.Algorithms.SubexponentialSAT.LocalExpectation.indexCode data.indices (.inl (owner i)))
        (fun i => OAI.Algorithms.SubexponentialSAT.LocalExpectation.indexCode data.indices (.inr i.1)) ∧
    ((counts.head:ℕ):ℚ)=(data.coordinates.map (fun q => headHistogram data.vertices
      (fun v => OAI.Algorithms.SubexponentialSAT.LocalExpectation.indexCode data.indices (.inl v))
      r Q q remaining env)).sum := by
  dsimp only
  simp only [original_terms,
    ← (SemiprimeSourceHistogramMetadata.original_fields n F Q arity).2]
  constructor
  · exact compiled_incidence_histogram owner Sigma.fst _
      (SemiprimeSourceHistogramMetadata.indices_certificate n F Q arity).2
      _ _ _ hr remaining env hn
  · exact compiled_head_histogram owner Sigma.fst _ _ _ _ remaining env hn

end RiemannGaussian.SemiprimeSourceHistogramAcquiredSums
