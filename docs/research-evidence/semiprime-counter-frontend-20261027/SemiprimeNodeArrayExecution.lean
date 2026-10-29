/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePacketArrayExecution
import RiemannGaussian.SemiprimeIndexedFibrePacket
import RiemannGaussian.SemiprimeNativeGroupExecution
import RiemannGaussian.SemiprimeAcquiredHermite

/-!
# Native Taylor packets acquired from source row arrays

The runtime inputs are source row coefficient arrays, indexed integer
measurements, and paid local Boolean entry evaluators. Representatives,
group products, fibres, and Taylor packet arrays are all computed.
The work ledger counts supplied entry reports, arithmetic, reads and selected
control charges. Source/design generation, concrete indexing and bit costs
remain separate obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeNodeArrayExecution
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeLocalArrayFrontend
open SemiprimeFibreArrayExecution SemiprimePacketArrayExecution
open SemiprimeIndexedNodeCertificate SemiprimeNativeGroupExecution
open SemiprimeCounterCompose SemiprimeCounterNative

variable {n F : ℕ} {arity : Fin F → ℕ}
variable {rows : (e : Fin F) → Fin (arity e) → Fin n → Polynomial ℚ} {t : ℚ}

/-- Runtime-only indexed design; no polynomial or row-validity index is retained. -/
structure RuntimeDesign (n F : ℕ) where
  /-- Number of groups. -/
  r : ℕ
  /-- Local Boolean dimensions. -/
  h : Fin r → ℕ
  /-- Measurement counts. -/
  m : Fin r → ℕ
  /-- Integer measurement bounds. -/
  W : Fin r → ℕ
  /-- Explicit variable partition. -/
  grouping : Fin n ≃ ((g : Fin r) × Fin (h g))
  /-- Factor group ownership. -/
  assigned : Fin F → Fin r
  /-- Original integer measurement entries. -/
  C : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ

/-- Erase proof-only native rows and span certificates from the runtime interface. -/
def runtimeDesign (d : Data arity (fun e i v => (rows e i v).eval t)) : RuntimeDesign n F :=
  ⟨d.r,d.h,d.m,d.W,d.grouping,d.assigned,d.C⟩

/-- An actual acquired fibre: local entry callbacks are its only value supplier. -/
def fibre (t : ℚ) (d : RuntimeDesign n F) (J R : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (S U : Finset (Fin n)) : Run :=
  fibreSum J d.r d.h d.m d.W d.C
    (fun g i => decide (d.grouping.symm ⟨g,i⟩ ∈ S))
    (nativeGroup arity J R t source d.grouping d.assigned (fun v => decide (v ∈ U)) T)

/-- No fibre or group-value answer appears in the premises. -/
theorem fibre_spec (d : Data arity (fun e i v => (rows e i v).eval t)) (J R : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R)
    (hsource : ∀ e i v k, k ≤ R → coefficient (source e i v) k = (rows e i v).coeff k)
    (S U : Finset (Fin n)) :
    Spec J (fibre t (runtimeDesign d) J R source T S U)
      (fibrePacket arity (fun e eta => ((T e eta).value : ℚ))
        (fun e i v => (rows e i v).eval t) (certificate d)
        (nativeCorrection arity rows t R U) S) := by
  classical
  rw [SemiprimeIndexedFibrePacket.packet_eq_sum, ← (summaryCode d.r d.h d.m d.W).sum_comp]
  apply sumCodes_spec
  intro code
  exact fibreAt_native_spec d (fun e eta => ((T e eta).value : ℚ))
    (nativeCorrection arity rows t R U) S J (summaryCode d.r d.h d.m d.W code) _
    (fun g a => nativeGroup_node_spec arity J R t source rows hrows hsource
      (certificate d) U T g a)

/-- Full node acquisition, including the signed support traversal. -/
def node (t : ℚ) (d : RuntimeDesign n F) (J R : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport) : Run :=
  rawRun J (List.ofFn (fun v : Fin n => v)) (fibre t d J R source T)

/-- The acquired array contains the genuine global Taylor coefficients. -/
theorem node_spec (d : Data arity (fun e i v => (rows e i v).eval t)) (J R : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R)
    (hsource : ∀ e i v k, k ≤ R → coefficient (source e i v) k = (rows e i v).coeff k) :
    Spec J (node t (runtimeDesign d) J R source T)
      (taylor t (globalPolynomial arity (fun e eta => ((T e eta).value : ℚ)) rows)) := by
  apply rawRun_taylor_spec arity (fun e eta => ((T e eta).value : ℚ)) rows t R J
    (certificate d) hrows (List.ofFn (fun v : Fin n => v))
  · exact List.nodup_ofFn.mpr Function.injective_id
  · ext v
    simp
  · exact fun S U => fibre_spec d J R source T hrows hsource S U

/-- Fully explicit local callback budget, including source-row shifts and truth scans. -/
def groupBudget (n F J R A W : ℕ) : ℕ :=
  F * (localBudget n W R J A + J + 1 + (2*J*(J+1)+J+1)) + (J+1)+n+F+2

/-- Complete finite fibre budget, with the FULL summary-box cardinal. -/
def fibreBudget (n F J R A W H M r Y : ℕ) : ℕ :=
  (J+1)+Y*(r*(2^H*(groupBudget n F J R A W+M*(4*H+3)+4*H+5*J+6)+
    (2*J*(J+1)+J+1))+(J+1)+r*(2^H*(M*(4*H+3)+3))+1+(4*J+1))

theorem fibre_work (t : ℚ) (d : RuntimeDesign n F)
    (J R A W H M : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hh : ∀ g, d.h g ≤ H) (hm : ∀ g, d.m g ≤ M) (hw : ∀ e, arity e ≤ W)
    (hT : ∀ e eta, (T e eta).arithmetic ≤ A ∧ (T e eta).reads ≤ A)
    (S U : Finset (Fin n)) :
    (fibre t d J R source T S U).work ≤
      fibreBudget n F J R A W H M d.r (summaryCount d.r d.h d.m d.W) :=
  fibreSum_work J d.r H M (groupBudget n F J R A W) d.h d.m d.W d.C _ _ hh hm
    (fun g a => nativeGroup_work arity J R A W t source d.grouping d.assigned _ T g a hw hT)

/-- The exponential traversals are support, summary, local fibre and local truth,
with every local callback paid; this is an arithmetic/read/control ledger. -/
theorem node_work (t : ℚ) (d : RuntimeDesign n F)
    (J R A W H M : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hh : ∀ g, d.h g ≤ H) (hm : ∀ g, d.m g ≤ M) (hw : ∀ e, arity e ≤ W)
    (hT : ∀ e eta, (T e eta).arithmetic ≤ A ∧ (T e eta).reads ≤ A) :
    (node t d J R source T).work ≤ SemiprimeCounterEnumeration.weightedCount n (J-1)*
      (fibreBudget n F J R A W H M d.r (summaryCount d.r d.h d.m d.W)+
        3*J+3*n+2+n*(8*J+3)) := by
  have hs := rawRun_work J
    (fibreBudget n F J R A W H M d.r (summaryCount d.r d.h d.m d.W))
    (List.ofFn (fun v : Fin n => v)) (fibre t d J R source T)
    (fun S U => fibre_work t d J R A W H M source T hh hm hw hT S U)
  simpa only [node, List.length_ofFn, Fintype.card_fin] using hs

/-- Reconstruct the scalar from internally acquired node arrays. -/
def count (Q J R : ℕ)
    (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport) :
    SemiprimeAcquiredHermite.ScalarRun :=
  SemiprimeAcquiredHermite.reconstruct Q J (fun a => node ((a.val : ℚ)+1) (design a) J R source T)

/-- Actual coefficient-to-count computation, with only degree, source-array and
native row-design certificates. No Taylor, fibre or final count oracle is input. -/
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

/-- All source-node acquisitions are charged before the scalar reconstruction. -/
theorem count_work (Q J R A W H M : ℕ)
    (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array ℚ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hh : ∀ a g, (design a).h g ≤ H) (hm : ∀ a g, (design a).m g ≤ M)
    (hw : ∀ e, arity e ≤ W)
    (hT : ∀ e eta, (T e eta).arithmetic ≤ A ∧ (T e eta).reads ≤ A) :
    (count Q J R design source T).work ≤
      (∑ a : Fin Q, SemiprimeCounterEnumeration.weightedCount n (J-1)*
        (fibreBudget n F J R A W H M (design a).r
          (summaryCount (design a).r (design a).h (design a).m (design a).W)+
          3*J+3*n+2+n*(8*J+3)))+
      Q*(2*J+4+2*SemiprimeHermiteArrayHeight.nodeWork Q J) := by
  apply (SemiprimeAcquiredHermite.reconstruct_work Q J _).trans
  apply Nat.add_le_add_right
  exact Finset.sum_le_sum (fun a _ => node_work ((a.val : ℚ)+1) (design a) J R A W H M source T
    (hh a) (hm a) hw hT)

end RiemannGaussian.SemiprimeNodeArrayExecution
