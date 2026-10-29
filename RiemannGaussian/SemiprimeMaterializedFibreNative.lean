/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedFibrePacket
import RiemannGaussian.SemiprimeNodeArrayExecution

/-!
# Materialized-head execution with actual native local factors

The runtime interface has coefficient arrays, integer measurement rows, and
paid original Boolean entry callbacks. It has no polynomial, group-value,
fibre-value, representative, or count oracle. Polynomial rows occur only in
correctness statements. Head tables are acquired once outside the support loop.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedFibreNative
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeLocalArrayFrontend
open SemiprimeFibreArrayExecution SemiprimePacketArrayExecution
open SemiprimeMaterializedFibre SemiprimeMaterializedFibrePacket
open SemiprimeIndexedNodeCertificate SemiprimeNativeGroupExecution
open SemiprimeCounterCompose SemiprimeCounterNative
open SemiprimeNodeArrayExecution (RuntimeDesign runtimeDesign groupBudget)

variable {n F : ℕ} {arity : Fin F → ℕ}
variable {rows : (e : Fin F) → Fin (arity e) → Fin n → Polynomial ℚ} {t : ℚ}

/-- Complete cached fibre acquisition with the actual original local evaluator. -/
def fibre (t : ℚ) (d : RuntimeDesign n F) (caches : Array HeadCache) (J R : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (S U : Finset (Fin n)) : Run :=
  sumCached J d.r d.h d.m d.W caches
    (fun g i => decide (d.grouping.symm ⟨g,i⟩ ∈ S))
    (nativeGroup arity J R t source d.grouping d.assigned (fun v => decide (v ∈ U)) T)

/-- No local-group value premise remains: original entry calls supply everything. -/
theorem fibre_spec (d : Data arity (fun e i v => (rows e i v).eval t)) (J R : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R)
    (hsource : ∀ e i v k, k ≤ R → coefficient (source e i v) k = (rows e i v).coeff k)
    (S U : Finset (Fin n)) :
    Spec J (fibre t (runtimeDesign d) (acquireHeads d.r d.h d.m d.C) J R source T S U)
      (fibrePacket arity (fun e eta => ((T e eta).value : ℚ))
        (fun e i v => (rows e i v).eval t) (certificate d)
        (nativeCorrection arity rows t R U) S) := by
  classical
  rw [SemiprimeIndexedFibrePacket.packet_eq_sum, ← (summaryCode d.r d.h d.m d.W).sum_comp]
  apply sumCodes_spec
  intro code
  let value := nativeGroup arity J R t source d.grouping d.assigned (fun v => decide (v ∈ U)) T
  let P := fun g a => SemiprimeCounterSeparation.groupValue arity
    (fun e eta => ((T e eta).value : ℚ)) d.assigned (localRows d)
    (nativeCorrection arity rows t R U) g a
  have hv : ∀ g a, Spec J (value g a) (P g a) :=
    fun g a => nativeGroup_node_spec arity J R t source rows hrows hsource (certificate d) U T g a
  have old := fibreAt_native_spec d (fun e eta => ((T e eta).value : ℚ))
    (nativeCorrection arity rows t R U) S J (summaryCode d.r d.h d.m d.W code) value hv
  intro i hi
  exact (fibreCached_coefficient_eq J d.r d.h d.m d.W d.C
    (summaryCode d.r d.h d.m d.W code) (forced d S) value P hv i hi).trans (old i hi)

/-- Actual full node: cache all head words/measurements ONCE, then use the
existing finite support traversal and coefficientarray operations. -/
def node (t : ℚ) (d : RuntimeDesign n F) (J R : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport) : Run :=
  let caches := acquireHeads d.r d.h d.m d.C
  let result := rawRun J (List.ofFn (fun v : Fin n => v)) (fibre t d caches J R source T)
  bump result (acquisitionWork d.r caches)

/-- The resulting actual array is the genuine global Taylor packet. -/
theorem node_spec (d : Data arity (fun e i v => (rows e i v).eval t)) (J R : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R)
    (hsource : ∀ e i v k, k ≤ R → coefficient (source e i v) k = (rows e i v).coeff k) :
    Spec J (node t (runtimeDesign d) J R source T)
      (taylor t (globalPolynomial arity (fun e eta => ((T e eta).value : ℚ)) rows)) := by
  apply bump_spec
  apply rawRun_taylor_spec arity (fun e eta => ((T e eta).value : ℚ)) rows t R J
    (certificate d) hrows (List.ofFn (fun v : Fin n => v))
  · exact List.nodup_ofFn.mpr Function.injective_id
  · ext v; simp
  · exact fun S U => fibre_spec d J R source T hrows hsource S U

/-- Complete summary-box budget using the existing actual local tensor budget. -/
def fibreBudget (n F J R A w H M r Y : ℕ) : ℕ :=
  (J+1)+Y*(oneSummaryBudget J r H M (groupBudget n F J R A w)+(4*J+1))

/-- Only original Boolean table calls are assumptions in the runtime ledger. -/
theorem fibre_work (t : ℚ) (d : RuntimeDesign n F) (caches : Array HeadCache)
    (J R A w H M : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hh : ∀ g, d.h g ≤ H) (hm : ∀ g, d.m g ≤ M) (hw : ∀ e, arity e ≤ w)
    (hT : ∀ e eta, (T e eta).arithmetic ≤ A ∧ (T e eta).reads ≤ A)
    (S U : Finset (Fin n)) :
    (fibre t d caches J R source T S U).work ≤
      fibreBudget n F J R A w H M d.r (summaryCount d.r d.h d.m d.W) :=
  sumCached_work J d.r H M (groupBudget n F J R A w) d.h d.m d.W caches _ _ hh hm
    (fun g a => nativeGroup_work arity J R A w t source d.grouping d.assigned _ T g a hw hT)

/-- Acquisition is paid once; the support and summary loops remain separate
local-exponential factors, not a full-global-assignment traversal. -/
theorem node_work (t : ℚ) (d : RuntimeDesign n F) (J R A w H M : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hh : ∀ g, d.h g ≤ H) (hm : ∀ g, d.m g ≤ M) (hw : ∀ e, arity e ≤ w)
    (hT : ∀ e eta, (T e eta).arithmetic ≤ A ∧ (T e eta).reads ≤ A) :
    (node t d J R source T).work ≤
      SemiprimeCounterEnumeration.weightedCount n (J-1)*
        (fibreBudget n F J R A w H M d.r (summaryCount d.r d.h d.m d.W)+
          3*J+3*n+2+n*(8*J+3)) +
        (d.r*(2^H*(H+M*(4*H+2)+3))+d.r+1) := by
  have hs := rawRun_work J
    (fibreBudget n F J R A w H M d.r (summaryCount d.r d.h d.m d.W))
    (List.ofFn (fun v : Fin n => v)) (fibre t d (acquireHeads d.r d.h d.m d.C) J R source T)
    (fun S U => fibre_work t d _ J R A w H M source T hh hm hw hT S U)
  simp only [List.length_ofFn,Fintype.card_fin] at hs
  have ha := acquisitionWork_le d.r H M d.h d.m d.C hh hm
  unfold node
  rw [bump_work]
  exact Nat.add_le_add hs ha

/-- Reconstruct the scalar from the actually materialized native-node arrays. -/
def count (Q J R : ℕ)
    (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport) :
    SemiprimeAcquiredHermite.ScalarRun :=
  SemiprimeAcquiredHermite.reconstruct Q J (fun a => node ((a.val : ℚ)+1) (design a) J R source T)

/-- Complete materialized count correctness, with no count/coefficient oracle.
Source coefficients and native designs have the existing concrete acquisition suppliers. -/
theorem count_correct (Q J R : ℕ) (hJ : 0<J)
    (design : (a : Fin Q) → Data arity (fun e i v => (rows e i v).eval ((a.val : ℚ)+1)))
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R)
    (hsource : ∀ e i v k, k ≤ R → coefficient (source e i v) k = (rows e i v).coeff k)
    (hdegree : (∑ e, arity e)*R<Q*J)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (hrestore : ∀ e i v, (rows e i v).eval 0 = if v=coordinate e i then 1 else 0) :
    (count Q J R (fun a => runtimeDesign (design a)) source T).value =
      originalContraction arity (fun e eta => ((T e eta).value : ℚ)) coordinate := by
  have h := SemiprimeAcquiredHermite.reconstruct_correct Q J hJ
    (globalPolynomial arity (fun e eta => ((T e eta).value : ℚ)) rows)
    ((globalPolynomial_degree arity _ rows R hrows).trans_lt hdegree)
    (fun a => node ((a.val : ℚ)+1) (runtimeDesign (design a)) J R source T)
    (fun a => node_spec (design a) J R source T hrows hsource)
  exact h.trans (globalPolynomial_at_zero arity _ rows coordinate hrestore)

/-- All materialized node acquisitions are paid before scalar reconstruction. -/
theorem count_work (Q J R A w H M : ℕ)
    (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hh : ∀ a g, (design a).h g ≤ H) (hm : ∀ a g, (design a).m g ≤ M)
    (hw : ∀ e, arity e ≤ w)
    (hT : ∀ e eta, (T e eta).arithmetic ≤ A ∧ (T e eta).reads ≤ A) :
    (count Q J R design source T).work ≤
      (∑ a : Fin Q, (SemiprimeCounterEnumeration.weightedCount n (J-1)*
        (fibreBudget n F J R A w H M (design a).r
          (summaryCount (design a).r (design a).h (design a).m (design a).W)+
          3*J+3*n+2+n*(8*J+3))+
        ((design a).r*(2^H*(H+M*(4*H+2)+3))+(design a).r+1)))+
      Q*(2*J+4+2*SemiprimeHermiteArrayHeight.nodeWork Q J) := by
  apply (SemiprimeAcquiredHermite.reconstruct_work Q J _).trans
  apply Nat.add_le_add_right
  exact Finset.sum_le_sum (fun a _ => node_work ((a.val : ℚ)+1) (design a) J R A w H M source T
    (hh a) (hm a) hw hT)

end RiemannGaussian.SemiprimeMaterializedFibreNative
