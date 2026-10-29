/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFullSetupBudget
import RiemannGaussian.SemiprimeNativeCounterBudget
import RiemannGaussian.SemiprimeIndexedDesignResources

/-! # One bound on the actual acquired counter report
The setup and native reports are joined without replacing the executed counter.
Semantic design equality is used only inside the already acquired native phase;
its separately executed physical construction remains in the setup ledger.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeFullCounterBudget
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SemiprimeLocalArrayFrontend SemiprimeIndexedDesignResources
variable {n F r Q : ℕ} [NeZero r]

/-- The original acquired source values used to identify the native phase.
Their complete acquisition cost remains in FullSetupBudget.setupWork. -/
abbrev sourceReader (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R : ℕ) :=
  let en := SemiprimeFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let source := SemiprimeMaterializedOriginalSource.acquire owner Sigma.fst en eps R
  fun (e : Fin F) (i : Fin (arity e)) (v : Fin n) =>
    SemiprimeSourceArrayAcquisition.read en.incidences source.value ⟨e,i⟩ v

/-- Only native-phase work is transported along exact acquired design equality.
No physical selector or source-acquisition report is removed by this equality. -/
theorem native_work_eq_indexed (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q) :
    SemiprimeFullSetupBudget.nativeWork (r:=r) (Q:=Q) arity coordinate eps R B J T =
      (SemiprimeMaterializedFibreNative.count Q J R
        (indexedDesign (r:=r) arity coordinate eps R B)
        (sourceReader (r:=r) (Q:=Q) arity coordinate eps R) T).work := by
  simp only [SemiprimeFullSetupBudget.nativeWork,Array.getElem_ofFn,sourceReader]
  simp only [SemiprimePaidFiniteEnumerations.indexed_value]
  congr 2
  funext t
  change (SemiprimePaidRuntimeDesign.build
    (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F)
      (SemiprimePaidRawAcquisition.acquire arity coordinate
        (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value eps R B).value t)
    (SemiprimePaidRawAcquisition.reader (n:=n)
      (SemiprimePaidRawAcquisition.acquire arity coordinate
        (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value eps R B).value t)
    (SemiprimePaidMeasurementBound.bits B Q R)).value =
    indexedDesign (r:=r) arity coordinate eps R B t
  rw [SemiprimePaidFiniteEnumerations.indexed_value]
  exact physical_eq arity coordinate eps R B howner hQ hAQ t

/-- Explicit original-parameter setup plus uniform native resource envelope. -/
def budget (n F incidences r Q R B J A w H ranks Y : ℕ) : ℕ :=
  SemiprimeFullSetupBudget.setupBudget n F incidences r Q R B (r^(2*Q)) (r^Q)+
  SemiprimeNativeCounterBudget.nativeBudget n F Q J R A w H ranks r Y

/-- Complete retained counter report, with actual design resource hypotheses.
The public specialization discharges these hypotheses from the indexed layout. -/
theorem count_work (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ)
    (R B J A w H ranks Y : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (hr : 2 ≤ r)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hh : ∀ t g, (indexedDesign (r:=r) (Q:=Q) arity coordinate eps R B t).h g ≤ H)
    (hm : ∀ t g, (indexedDesign (r:=r) (Q:=Q) arity coordinate eps R B t).m g ≤ ranks)
    (hy : ∀ t, SemiprimePacketArrayExecution.summaryCount r
      (indexedDesign (r:=r) (Q:=Q) arity coordinate eps R B t).h
      (indexedDesign (r:=r) (Q:=Q) arity coordinate eps R B t).m
      (indexedDesign (r:=r) (Q:=Q) arity coordinate eps R B t).W ≤ Y)
    (hw : ∀ e, arity e ≤ w)
    (hT : ∀ e eta, (T e eta).arithmetic ≤ A ∧ (T e eta).reads ≤ A) :
    (SemiprimeFullSetupCounter.count (r:=r) (Q:=Q) arity coordinate eps R B J T).work ≤
      budget n F (∑ e,arity e) r Q R B J A w H ranks Y := by
  have hs := SemiprimeFullSetupBudget.setup_work_bound arity coordinate eps R B hr howner hQ hAQ
  have hn := SemiprimeNativeCounterBudget.count_work Q J R A w H ranks r Y
    (indexedDesign (r:=r) arity coordinate eps R B)
    (sourceReader (r:=r) (Q:=Q) arity coordinate eps R) T
    (fun _ => rfl) hh hm hw hT hy
  rw [SemiprimeFullSetupBudget.count_work_eq_setup_add_native,
    native_work_eq_indexed arity coordinate eps R B J T howner hQ hAQ]
  exact Nat.add_le_add hs hn

end RiemannGaussian.SemiprimeFullCounterBudget
