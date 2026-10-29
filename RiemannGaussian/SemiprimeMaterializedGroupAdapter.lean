/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedFibreNative

/-! # Retaining an executed replacement group throughout the actual counter

This adapter preserves the existing head, summary, support and Hermite loops.
Its group argument is an executed component, with every returned report retained.
The concrete word-backed caller supplies that component; the specification here
is a proof obligation, not a runtime answer. The outer rational folds remain
scalar and their reports are still paid.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeMaterializedGroupAdapter
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeLocalArrayFrontend
open SemiprimeFibreArrayExecution SemiprimePacketArrayExecution
open SemiprimeMaterializedFibre SemiprimeMaterializedFibrePacket
open SemiprimeIndexedNodeCertificate SemiprimeNativeGroupExecution
open SemiprimeCounterCompose SemiprimeCounterNative
open SemiprimeNodeArrayExecution (RuntimeDesign runtimeDesign)

variable {n F : ℕ} {arity : Fin F → ℕ}
variable {rows : (e : Fin F) → Fin (arity e) → Fin n → Polynomial ℚ} {t : ℚ}

/-- An executed group component at a fixed acquired design. -/
abbrev GroupCall (d : RuntimeDesign n F) :=
  Finset (Fin n) → (g : Fin d.r) → ((k : Fin d.r) → Fin (d.h k) → Bool) → Run

/-- Retain the executed group inside the complete cached summary scan. -/
def fibre (d : RuntimeDesign n F) (caches : Array HeadCache) (J : ℕ)
    (value : GroupCall d) (S U : Finset (Fin n)) : Run :=
  sumCached J d.r d.h d.m d.W caches
    (fun g i => decide (d.grouping.symm ⟨g,i⟩ ∈ S)) (value U)

/-- The replacement is used for every support term after one head acquisition. -/
def node (d : RuntimeDesign n F) (J : ℕ) (value : GroupCall d) : Run :=
  let caches := acquireHeads d.r d.h d.m d.C
  let result := rawRun J (List.ofFn (fun v : Fin n => v)) (fibre d caches J value)
  bump result (acquisitionWork d.r caches)

/-- Each node executes its replacement group; reconstruction retains its work. -/
def count (Q J : ℕ) (design : Fin Q → RuntimeDesign n F)
    (value : (a : Fin Q) → GroupCall (design a)) : SemiprimeAcquiredHermite.ScalarRun :=
  SemiprimeAcquiredHermite.reconstruct Q J (fun a => node (design a) J (value a))

/-- A coefficient refinement suffices; no equality of old and new work is used. -/
theorem fibre_spec (d : Data arity (fun e i v => (rows e i v).eval t)) (J R : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R)
    (hsource : ∀ e i v k, k ≤ R → coefficient (source e i v) k = (rows e i v).coeff k)
    (value : GroupCall (runtimeDesign d))
    (hv : ∀ U g a k, k<J → coefficient (value U g a).jet.coefficients k =
      coefficient (nativeGroup arity J R t source d.grouping d.assigned
        (fun v => decide (v ∈ U)) T g a).jet.coefficients k)
    (S U : Finset (Fin n)) :
    Spec J (fibre (runtimeDesign d) (acquireHeads d.r d.h d.m d.C) J value S U)
      (fibrePacket arity (fun e eta => ((T e eta).value : ℚ))
        (fun e i v => (rows e i v).eval t) (certificate d)
        (nativeCorrection arity rows t R U) S) := by
  classical
  rw [SemiprimeIndexedFibrePacket.packet_eq_sum, ← (summaryCode d.r d.h d.m d.W).sum_comp]
  apply sumCodes_spec
  intro code
  let P := fun g a => SemiprimeCounterSeparation.groupValue arity
    (fun e eta => ((T e eta).value : ℚ)) d.assigned (localRows d)
    (nativeCorrection arity rows t R U) g a
  have hvalue : ∀ g a, Spec J (value U g a) (P g a) := by
    intro g a k hk
    exact (hv U g a k hk).trans
      (nativeGroup_node_spec arity J R t source rows hrows hsource (certificate d) U T g a k hk)
  have old := fibreAt_native_spec d (fun e eta => ((T e eta).value : ℚ))
    (nativeCorrection arity rows t R U) S J (summaryCode d.r d.h d.m d.W code) (value U) hvalue
  intro i hi
  exact (fibreCached_coefficient_eq J d.r d.h d.m d.W d.C
    (summaryCode d.r d.h d.m d.W code) (forced d S) (value U) P hvalue i hi).trans (old i hi)

/-- The original support traversal now consumes the replacement component. -/
theorem node_spec (d : Data arity (fun e i v => (rows e i v).eval t)) (J R : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R)
    (hsource : ∀ e i v k, k ≤ R → coefficient (source e i v) k = (rows e i v).coeff k)
    (value : GroupCall (runtimeDesign d))
    (hv : ∀ U g a k, k<J → coefficient (value U g a).jet.coefficients k =
      coefficient (nativeGroup arity J R t source d.grouping d.assigned
        (fun v => decide (v ∈ U)) T g a).jet.coefficients k) :
    Spec J (node (runtimeDesign d) J value)
      (taylor t (globalPolynomial arity (fun e eta => ((T e eta).value : ℚ)) rows)) := by
  apply bump_spec
  apply rawRun_taylor_spec arity (fun e eta => ((T e eta).value : ℚ)) rows t R J
    (certificate d) hrows (List.ofFn (fun v : Fin n => v))
  · exact List.nodup_ofFn.mpr Function.injective_id
  · ext v; simp
  · exact fun S U => fibre_spec d J R source T hrows hsource value hv S U

/-- Count correctness transfers from actual group coefficients, keeping its new report. -/
theorem count_correct (Q J R : ℕ) (hJ : 0<J)
    (design : (a : Fin Q) → Data arity (fun e i v => (rows e i v).eval ((a.val : ℚ)+1)))
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R)
    (hsource : ∀ e i v k, k ≤ R → coefficient (source e i v) k = (rows e i v).coeff k)
    (hdegree : (∑ e, arity e)*R<Q*J)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (hrestore : ∀ e i v, (rows e i v).eval 0 = if v=coordinate e i then 1 else 0)
    (value : (a : Fin Q) → GroupCall (runtimeDesign (design a)))
    (hv : ∀ a U g x k, k<J → coefficient (value a U g x).jet.coefficients k =
      coefficient (nativeGroup arity J R ((a.val : ℚ)+1) source
        (design a).grouping (design a).assigned (fun v => decide (v ∈ U)) T g x).jet.coefficients k) :
    (count Q J (fun a => runtimeDesign (design a)) value).value =
      originalContraction arity (fun e eta => ((T e eta).value : ℚ)) coordinate := by
  have h := SemiprimeAcquiredHermite.reconstruct_correct Q J hJ
    (globalPolynomial arity (fun e eta => ((T e eta).value : ℚ)) rows)
    ((globalPolynomial_degree arity _ rows R hrows).trans_lt hdegree)
    (fun a => node (runtimeDesign (design a)) J (value a))
    (fun a => node_spec (design a) J R source T hrows hsource (value a) (hv a))
  exact h.trans (globalPolynomial_at_zero arity _ rows coordinate hrestore)

/-- Explicit cost of the unchanged summary machinery around a real group cost. -/
def fibreBudget (J r H M B Y : ℕ) : ℕ :=
  J+1+Y*(oneSummaryBudget J r H M B+(4*J+1))

/-- A bound on the component report is propagated, rather than replacing it. -/
theorem fibre_work (d : RuntimeDesign n F) (caches : Array HeadCache) (J H M B : ℕ)
    (value : GroupCall d) (hh : ∀ g, d.h g≤H) (hm : ∀ g, d.m g≤M)
    (hv : ∀ U g a, (value U g a).work≤B) (S U : Finset (Fin n)) :
    (fibre d caches J value S U).work ≤
      fibreBudget J d.r H M B (summaryCount d.r d.h d.m d.W) :=
  sumCached_work J d.r H M B d.h d.m d.W caches _ _ hh hm (hv U)

/-- The same support/head factors multiply the executed component's cost. -/
theorem node_work (d : RuntimeDesign n F) (J H M B : ℕ) (value : GroupCall d)
    (hh : ∀ g, d.h g≤H) (hm : ∀ g, d.m g≤M)
    (hv : ∀ U g a, (value U g a).work≤B) :
    (node d J value).work ≤
      SemiprimeCounterEnumeration.weightedCount n (J-1)*
        (fibreBudget J d.r H M B (summaryCount d.r d.h d.m d.W)+
          3*J+3*n+2+n*(8*J+3))+
        (d.r*(2^H*(H+M*(4*H+2)+3))+d.r+1) := by
  have hs := rawRun_work J
    (fibreBudget J d.r H M B (summaryCount d.r d.h d.m d.W))
    (List.ofFn (fun v : Fin n => v)) (fibre d (acquireHeads d.r d.h d.m d.C) J value)
    (fun S U => fibre_work d _ J H M B value hh hm hv S U)
  simp only [List.length_ofFn,Fintype.card_fin] at hs
  have ha := acquisitionWork_le d.r H M d.h d.m d.C hh hm
  unfold node
  rw [bump_work]
  exact Nat.add_le_add hs ha

/-- Every actual node report, including component arithmetic, remains in the count. -/
theorem count_work (Q J H M B : ℕ) (design : Fin Q → RuntimeDesign n F)
    (value : (a : Fin Q) → GroupCall (design a))
    (hh : ∀ a g, (design a).h g≤H) (hm : ∀ a g, (design a).m g≤M)
    (hv : ∀ a U g x, (value a U g x).work≤B) :
    (count Q J design value).work ≤
      (∑ a : Fin Q, (SemiprimeCounterEnumeration.weightedCount n (J-1)*
        (fibreBudget J (design a).r H M B
          (summaryCount (design a).r (design a).h (design a).m (design a).W)+
          3*J+3*n+2+n*(8*J+3))+
        ((design a).r*(2^H*(H+M*(4*H+2)+3))+(design a).r+1)))+
      Q*(2*J+4+2*SemiprimeHermiteArrayHeight.nodeWork Q J) := by
  apply (SemiprimeAcquiredHermite.reconstruct_work Q J _).trans
  apply Nat.add_le_add_right
  exact Finset.sum_le_sum (fun a _ => node_work (design a) J H M B (value a) (hh a) (hm a) (hv a))

end RiemannGaussian.SemiprimeMaterializedGroupAdapter
