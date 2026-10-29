/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1IncidenceSearch
import RiemannGaussian.SemiprimeSourceHistogramResources

/-! # Retained report of the actual incidence-only D1 selector
A conservative existing numerical envelope also covers unused setup fields.
This does not execute a head query or infer costs from an old output equality.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1IncidenceSearchBudget
open scoped BigOperators
open SemiprimeMaterializedWords SemiprimeRationalBits
open SemiprimeSourceWordIdControl SemiprimeSourceHistogramArithmeticBounds
open SemiprimeSourceHistogramQueryBounds

/-- Actual incidence/prefix report and width, derived only from original input. -/
theorem query_bound (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool)) (s : ℕ)
    (hf : InMenu (SemiprimeSourceCompactWordBank.acquire r a).ids fixed) :
    Width (SemiprimeD1IncidenceSearch.query
      (SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner) fixed s).word
      (outputWidth n (∑e,arity e) r a 0) ∧
    (SemiprimeD1IncidenceSearch.query
      (SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner) fixed s).clock≤
      scoreBudget n F (∑e,arity e) r a 0 fixed.length := by
  have hi := incidence_bound_original n F r a 0 arity owner fixed hf fixed.length s
  have hp := prefix_clock r a fixed hf
  refine ⟨widen hi.1 ?_,?_⟩
  · unfold outputWidth grow
    omega
  · unfold SemiprimeD1IncidenceSearch.query scoreBudget
    dsimp only
    omega

/-- New actual controller report with no supplied callback or output-width advice. -/
theorem run_work (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeD1IncidenceSearch.run n F r a arity owner).work≤
      SemiprimeSourceHistogramSearchBudget.budget n F r a 0 (∑e,arity e) (r^a) := by
  let cache := SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner
  let menu := (SemiprimeSourceCompactWordBank.acquire r a).ids
  let physical := fun (tokens : List Bool) (fixed : List (List Bool)) =>
    SemiprimeD1IncidenceSearch.query cache fixed tokens.length
  let H := scoreBudget n F (∑e,arity e) r a 0 (n+F)
  let W := outputWidth n (∑e,arity e) r a 0
  let B := Nat.clog 2 (r^a+1)
  have hc := SemiprimeSourceWordIdControl.run_work menu [] menu.tail physical (n+F) [] H W B (n+F)
    (SemiprimeSourceCompactWordBank.ids_bounded r a)
    (SemiprimeSourceHistogramSearch.candidates_valid r a) (by simp [InMenu])
    (fun tokens fixed hlen hf => by
      have h := query_bound n F r a arity owner fixed tokens.length hf
      exact ⟨h.2.trans (scoreBudget_prefix_mono n F (∑e,arity e) r a 0 (by omega)),h.1⟩)
    (by simp)
  rw [SemiprimeSourceHistogramSearchBudget.tail_length] at hc
  change (SemiprimeSourceChoiceBits.run [] menu.tail physical (n+F) []).work≤
    SemiprimeSourceHistogramSearchBudget.controllerBudget (n+F) (r^a-1) B H W at hc
  have hs := SemiprimeSourceHistogramSetupBounds.acquire_clock n F r a 0 arity owner (NeZero.pos r)
  have hn := SemiprimeSourceHistogramSearchBudget.original_depth n F r a 0 arity owner
  have hb := SemiprimeSourceHistogramSetup.bank_actual n F r a 0 arity owner
  change cache.clock+(SemiprimeSourceChoiceBits.run [] cache.rows.source.bank.ids.tail physical
      cache.data.metadata.indices.length []).work+cache.data.metadata.indices.length+4≤_
  rw [hb,hn]
  have h := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hs hc) (n+F)) 4
  simpa only [SemiprimeSourceHistogramSearchBudget.budget,Nat.add_assoc] using h

/-- Fixed-polynomial original-resource bound for the new actual report.
Native metadata, argument evaluation and full primitive-machine lowering remain open. -/
theorem run_resource_bound (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (S : ℕ)
    (hn : n≤S) (hF : F≤S) (hr : r≤S) (ha : a≤S)
    (hM : (∑e,arity e)≤S) (hL : r^a≤S) :
    (SemiprimeD1IncidenceSearch.run n F r a arity owner).work≤
      SemiprimeSourceHistogramResources.envelope S :=
  (run_work n F r a arity owner).trans
    (SemiprimeSourceHistogramResources.budget_polynomial n F r a 0 (∑e,arity e) S
      (NeZero.pos r) hn hF hr ha (Nat.zero_le _) hM hL)

end RiemannGaussian.SemiprimeD1IncidenceSearchBudget
