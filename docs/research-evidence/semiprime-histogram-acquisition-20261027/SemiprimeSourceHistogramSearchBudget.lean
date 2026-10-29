/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramSearch
import RiemannGaussian.SemiprimeSourceHistogramQueryBounds

/-! # Actual original histogram selector report
One original setup acquisition feeds the existing physical comparison/copy
controller. Every reachable callback budget and word shape is derived from the
concrete original histogram query, not supplied as an oracle contract.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeSourceHistogramSearchBudget
open scoped BigOperators
open SemiprimeRationalBits SemiprimeMaterializedWords
open SemiprimeSourceWordIdControl

/-- Exact token, tail-scan, score, physical comparison and prefix-copy envelope.
K is the actual candidate-tail count; N is the original assignment depth. -/
def controllerBudget (N K B H W : ℕ) : ℕ :=
  2*N+3+N*(K*(2*H+200*(W+1)^2+4*B+5)+4*B+2+N*(4*B+4)+4)+
    N*(4*B+4)+1

/-- Pure numerical enlargement has no source/callback or elaboration context. -/
theorem controllerBudget_mono {N K B H W N' K' B' H' W' : ℕ}
    (hN : N ≤ N') (hK : K ≤ K') (hB : B ≤ B') (hH : H ≤ H') (hW : W ≤ W') :
    controllerBudget N K B H W ≤ controllerBudget N' K' B' H' W' := by
  unfold controllerBudget
  gcongr

/-- Original complete selector envelope, including the once-acquired setup.
L is the explicit original alphabet cardinality r^Q at the semantic endpoint. -/
def budget (n F r Q lam M L : ℕ) : ℕ :=
  SemiprimeSourceHistogramSetupBounds.budget n F r Q lam M L+
    controllerBudget (n+F) (L-1) (Nat.clog 2 (L+1))
      (SemiprimeSourceHistogramQueryBounds.scoreBudget n F M r Q lam (n+F))
      (SemiprimeSourceHistogramQueryBounds.outputWidth n M r Q lam)+n+F+4

/-- Original input metadata supplies the actual assignment-token depth. -/
theorem original_depth (n F r Q lam : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).data.metadata.indices.length=n+F := by
  rw [SemiprimeSourceHistogramSetup.metadata_actual]
  exact (SemiprimeSourceHistogramMetadata.sizes n F Q arity).2.2.2.2

/-- The actual acquired compact candidate tail has its exact original size. -/
theorem tail_length (r Q : ℕ) : (SemiprimeSourceCompactWordBank.acquire r Q).ids.tail.length=r^Q-1 := by
  rw [List.length_tail,SemiprimeSourceCompactWordBank.ids_length,
    SemiprimeSourceCompactWordBank.acquire_length]

/-- Every reachable menu prefix discharges the controller's internal callback
contract from the actual original histogram score, not callback advice. -/
theorem callback_bound (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (tokens : List Bool) (fixed : List (List Bool))
    (hlen : tokens.length+fixed.length ≤ n+F)
    (hf : InMenu (SemiprimeSourceCompactWordBank.acquire r Q).ids fixed) :
    let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
    (SemiprimeSourceHistogramQuery.score cache fixed tokens.length).clock ≤
      SemiprimeSourceHistogramQueryBounds.scoreBudget n F (∑ e,arity e) r Q lam (n+F) ∧
    Width (SemiprimeSourceHistogramQuery.score cache fixed tokens.length).word
      (SemiprimeSourceHistogramQueryBounds.outputWidth n (∑ e,arity e) r Q lam) := by
  have h := SemiprimeSourceHistogramQueryBounds.score_bound n F r Q lam arity owner fixed tokens.length hf
  refine ⟨h.2.trans ?_,h.1⟩
  apply SemiprimeSourceHistogramQueryBounds.scoreBudget_prefix_mono
  omega

/-- Actual original source selection with every setup/query/compare/copy report.
No score, encoded word, Fits, callback-clock or final-label answer is supplied. -/
theorem run_work (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeSourceHistogramSearch.run n F r Q lam arity owner).work ≤
      budget n F r Q lam (∑ e,arity e) (r^Q) := by
  let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
  let menu := (SemiprimeSourceCompactWordBank.acquire r Q).ids
  let physical := fun (tokens : List Bool) (fixed : List (List Bool)) => SemiprimeSourceHistogramQuery.score cache fixed tokens.length
  let H := SemiprimeSourceHistogramQueryBounds.scoreBudget n F (∑ e,arity e) r Q lam (n+F)
  let W := SemiprimeSourceHistogramQueryBounds.outputWidth n (∑ e,arity e) r Q lam
  let B := Nat.clog 2 (r^Q+1)
  have hc := SemiprimeSourceWordIdControl.run_work menu [] menu.tail physical
    (n+F) [] H W B (n+F)
    (SemiprimeSourceCompactWordBank.ids_bounded r Q)
    (SemiprimeSourceHistogramSearch.candidates_valid r Q)
    (by simp [InMenu])
    (fun ts xs hlen hf => callback_bound n F r Q lam arity owner ts xs hlen hf)
    (by simp)
  rw [tail_length] at hc
  change (SemiprimeSourceChoiceBits.run [] menu.tail physical (n+F) []).work ≤
    controllerBudget (n+F) (r^Q-1) B H W at hc
  have hs := SemiprimeSourceHistogramSetupBounds.acquire_clock n F r Q lam arity owner (NeZero.pos r)
  have hn := original_depth n F r Q lam arity owner
  have hb := SemiprimeSourceHistogramSetup.bank_actual n F r Q lam arity owner
  change cache.clock+
    (SemiprimeSourceChoiceBits.run [] cache.rows.source.bank.ids.tail physical
      cache.data.metadata.indices.length []).work+cache.data.metadata.indices.length+4 ≤ _
  rw [hb,hn]
  have h := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hs hc) (n+F)) 4
  simpa only [budget,Nat.add_assoc] using h

end RiemannGaussian.SemiprimeSourceHistogramSearchBudget
