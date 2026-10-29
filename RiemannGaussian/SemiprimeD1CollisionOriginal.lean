/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1CollisionVariance
import RiemannGaussian.SemiprimeSourceHistogramQueryCorrectness

/-! # Original acquired incidence query at the two endpoints
The degree premises concern actual original port-fibre lengths. The histogram
query and its original padded count lane are already executed, not supplied.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1CollisionOriginal
open SemiprimeD1CollisionVariance SemiprimeSourceHistogramGrouping
open SemiprimeSourceHistogramQueryCorrectness

/-- Original acquired factor-major port list, including parallel occurrences. -/
def ports (n F Q : ℕ) (arity : Fin F→ℕ) :=
  (SemiprimeSourceHistogramMetadata.acquire n F Q arity).incidences

/-- Initial original count obeys the degree-derived D.3 collision budget. -/
theorem initial_incidence_le (n F r Q : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F Q arity,
      multiplicity (fun i => (owner i).val) (ports n F Q arity) (owner i).val≤Δ)
    (hf : ∀ i∈ports n F Q arity,
      multiplicity (fun i => n+i.1.val) (ports n F Q arity) (n+i.1.val)≤Δ) :
    ((originalCounts n F r Q arity owner [] (n+F)).incidence:ℚ)≤
      ((r^Q:ℕ):ℚ)^2*((ports n F Q arity).length:ℚ)^2+
        2*(ports n F Q arity).length*Δ*((r^Q:ℕ):ℚ)^4 := by
  have h := (SemiprimeSourceHistogramAcquiredSums.acquired_original_lanes n F r Q
    arity owner (NeZero.pos r) (List.range' 0 (n+F))
    (SemiprimeSourceHistogramHeadOriginal.originalEnv r Q []) (List.nodup_range')).1
  simp only [SemiprimeSourceHistogramPortKeys.indexCode_inl,
    SemiprimeSourceHistogramPortKeys.indexCode_inr] at h
  change ((originalCounts n F r Q arity owner [] (n+F)).incidence:ℚ)=_ at h
  rw [h]
  apply padded_initial_le (ports n F Q arity) (fun i => (owner i).val)
    (fun i => n+i.1.val) _ _ Δ _
  · exact_mod_cast (show 1≤r^Q from Nat.succ_le_of_lt (pow_pos (NeZero.pos r) Q))
  · intro i _
    have hv: (owner i).val<n := (owner i).isLt
    apply List.mem_range'.mpr
    refine ⟨(owner i).val,?_,by omega⟩
    omega
  · intro i _
    have he:i.1.val<F := i.1.isLt
    apply List.mem_range'.mpr
    refine ⟨n+i.1.val,?_,by omega⟩
    omega
  · exact ho
  · exact hf

/-- Terminal original padded count is exactly L⁴ times actual pair-label collisions. -/
theorem terminal_incidence (n F r Q : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool)) :
    ((originalCounts n F r Q arity owner fixed 0).incidence:ℚ)=
      ((r^Q:ℕ):ℚ)^4*pairs (ports n F Q arity) (fun i j =>
        if SemiprimeMaterializedScoreEnvironment.denote
            (SemiprimeSourceHistogramHeadOriginal.originalEnv r Q fixed) (owner i).val=
           SemiprimeMaterializedScoreEnvironment.denote
            (SemiprimeSourceHistogramHeadOriginal.originalEnv r Q fixed) (owner j).val ∧
           SemiprimeMaterializedScoreEnvironment.denote
            (SemiprimeSourceHistogramHeadOriginal.originalEnv r Q fixed) (n+i.1.val)=
           SemiprimeMaterializedScoreEnvironment.denote
            (SemiprimeSourceHistogramHeadOriginal.originalEnv r Q fixed) (n+j.1.val)
          then (1:ℚ) else 0) := by
  have h := (SemiprimeSourceHistogramAcquiredSums.acquired_original_lanes n F r Q
    arity owner (NeZero.pos r) (List.range' fixed.length 0)
    (SemiprimeSourceHistogramHeadOriginal.originalEnv r Q fixed) (List.nodup_range')).1
  simp only [SemiprimeSourceHistogramPortKeys.indexCode_inl,
    SemiprimeSourceHistogramPortKeys.indexCode_inr,List.range'_zero] at h
  change ((originalCounts n F r Q arity owner fixed 0).incidence:ℚ)=_ at h
  rw [h]
  exact histogram_terminal _ _ _ _ _

end RiemannGaussian.SemiprimeD1CollisionOriginal
