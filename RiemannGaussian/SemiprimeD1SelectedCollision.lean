/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1IncidenceSearch
import RiemannGaussian.SemiprimeD1CollisionOriginal

/-! # Collision guarantee for actual incidence-only acquired labels
All graph ports, degree hypotheses and selected labels are original data. There
is no supplied assignment, collision answer, desired objective or head penalty.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1SelectedCollision
open SemiprimeSourceHistogramGrouping
open SemiprimeD1CollisionOriginal SemiprimeD1CollisionVariance
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- Proof-side interpretation of the actual selected physical compact IDs. -/
def selectedLabel (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) : Word r a × Word r a :=
  let env := SemiprimeSourceHistogramHeadOriginal.originalEnv r a
    (SemiprimeD1IncidenceSearch.run n F r a arity owner).value
  (SemiprimeMaterializedScoreEnvironment.denote env (owner i).val,
    SemiprimeMaterializedScoreEnvironment.denote env (n+i.1.val))

/-- Literal ordered-port-pair collisions of the actual selected labels.
This mathematical specification is not executed by the sparse selector. -/
def collisionSum (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) : ℚ :=
  pairs (ports n F a arity) (fun i j => if selectedLabel n F r a arity owner i=
    selectedLabel n F r a arity owner j then (1:ℚ) else 0)

/-- Terminal count equals the exact collision sum of the acquired selector output. -/
theorem terminal_eq (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ((SemiprimeSourceHistogramQueryCorrectness.originalCounts n F r a arity owner
      (SemiprimeD1IncidenceSearch.run n F r a arity owner).value 0).incidence:ℚ)=
      ((r^a:ℕ):ℚ)^4*collisionSum n F r a arity owner := by
  simpa only [collisionSum,selectedLabel,Prod.mk.injEq] using
    terminal_incidence n F r a arity owner (SemiprimeD1IncidenceSearch.run n F r a arity owner).value

/-- Original D.3 collision budget for this actual deterministic selector.
Parallel incidences, diagonal ordered pairs and arbitrary degree distributions remain. -/
theorem selected_collision_le (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a arity,
      multiplicity (fun i => (owner i).val) (ports n F a arity) (owner i).val≤Δ)
    (hf : ∀ i∈ports n F a arity,
      multiplicity (fun i => n+i.1.val) (ports n F a arity) (n+i.1.val)≤Δ) :
    collisionSum n F r a arity owner≤
      ((ports n F a arity).length:ℚ)^2/((r^a:ℕ):ℚ)^2+
        2*(ports n F a arity).length*Δ := by
  have hs : ((SemiprimeSourceHistogramQueryCorrectness.originalCounts n F r a arity owner
      (SemiprimeD1IncidenceSearch.run n F r a arity owner).value 0).incidence:ℚ)≤
    ((SemiprimeSourceHistogramQueryCorrectness.originalCounts n F r a arity owner [] (n+F)).incidence:ℚ) := by
    exact_mod_cast SemiprimeD1IncidenceSearch.counts_le_initial n F r a arity owner
  have h := hs.trans (initial_incidence_le n F r a arity owner Δ ho hf)
  rw [terminal_eq] at h
  have hL : (0:ℚ)<(r^a:ℕ) := Nat.cast_pos.mpr (pow_pos (NeZero.pos r) a)
  have he : ((r^a:ℕ):ℚ)^4*
      (((ports n F a arity).length:ℚ)^2/((r^a:ℕ):ℚ)^2+
        2*(ports n F a arity).length*Δ)=
      ((r^a:ℕ):ℚ)^2*((ports n F a arity).length:ℚ)^2+
        2*(ports n F a arity).length*Δ*((r^a:ℕ):ℚ)^4 := by
    field_simp
  rw [←he] at h
  exact le_of_mul_le_mul_left h (pow_pos hL 4)

end RiemannGaussian.SemiprimeD1SelectedCollision
