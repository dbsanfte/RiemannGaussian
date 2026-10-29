/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNativeBitsCounter
import RiemannGaussian.SemiprimeNativeInputBits
import RiemannGaussian.SemiprimeFullSetupCounter

/-! # Original network to the counter with executed physical native groups

The original source is acquired once, encoded once, and reused by the physical
corrected-port/local/group evaluator. Actual paid enumeration, integer rows,
physical designs, source/read/encoding reports and all native reports remain
in the result. Source production, outer scalar folds and address/control
refinements are still explicitly separate from a whole primitive clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeNativeBitsSetupCounter
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SemiprimeLocalBits SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeJetBits
open SemiprimeAcquiredSourceCounter (layout sourceDesign sourceDesign_runtime)
variable {n F r Q : ℕ} [NeZero r]

/-- Every source and native arithmetic component is executed from original inputs. -/
def count (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) :
    SemiprimeAcquiredHermite.ScalarRun :=
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let source := SemiprimeSourceWordAcquisition.acquire owner Sigma.fst en.value eps R B
  let raw := SemiprimePaidRawAcquisition.acquire arity coordinate en.value eps R B
  let bits := SemiprimePaidMeasurementBound.bits B Q R
  let designs := Array.ofFn (fun t : Fin Q => SemiprimePaidRuntimeDesign.build
    (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F) raw.value t)
    (SemiprimePaidRawAcquisition.reader (n:=n) raw.value t) bits)
  let out := SemiprimeNativeBitsCounter.count
    (SemiprimeNativeInputBits.inputBits n B Q R J) Q J R
    (fun t => (designs[t.val]'(by simp [designs])).value)
    (fun e i v => SemiprimeSourceWordAcquisition.readWords en.value.incidences source.words ⟨e,i⟩ v) T
  ⟨out.value,en.work+source.work+raw.work+(designs.toList.map (fun x => x.work)).sum+out.work+10*Q+20⟩

/-- The physical source/native path returns the original Boolean tensor contraction.
All coefficient, word and fit guards follow from the original constructor. -/
theorem count_correct (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hT : ∀ e eta,(T e eta).bits.value.natAbs≤1)
    (howner : ∀ v,(Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e,arity e)*R<Q*J) :
    (count (r:=r) (Q:=Q) arity coordinate eps R B J T).value=
      SemiprimeCounterNative.originalContraction arity
        (fun e eta => ((T e eta).bits.value:ℚ)) coordinate := by
  let en := SemiprimeFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let source := SemiprimeSourceWordAcquisition.acquire owner Sigma.fst en eps R B
  let read := fun (e : Fin F) (i : Fin (arity e)) (v : Fin n) =>
    SemiprimeSourceWordAcquisition.readWords en.incidences source.words ⟨e,i⟩ v
  let b := SemiprimeNativeInputBits.inputBits n B Q R J
  let design := fun t : Fin Q => sourceDesign (r:=r) (Q:=Q) arity coordinate eps R B howner hQ hAQ t
  have hvalid : ∀ e i v,SemiprimeJetBits.Valid (read e i v).value := by
    intro e i v
    exact SemiprimeSourceWordAcquisition.acquire_row_valid owner Sigma.fst en eps R B howner hQ hAQ ⟨e,i⟩ v
  have hs : ∀ e i v k,k≤R → Representation (coefficient (decode (read e i v).value) k)
      (SemiprimeSourceRowHeight.rowDenominator Q R)
      (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) := by
    intro e i v k hk
    exact SemiprimeSourceWordAcquisition.acquire_representation owner Sigma.fst en eps R B howner hQ hAQ ⟨e,i⟩ v k hk
  have hc : ∀ e i v k,k≤R → coefficient (decode (read e i v).value) k=
      ((layout (r:=r) (Q:=Q) arity coordinate eps R).row ⟨e,i⟩ v).coeff k := by
    intro e i v k hk
    exact SemiprimeSourceWordAcquisition.acquire_coefficient owner Sigma.fst en eps R B howner hQ hAQ ⟨e,i⟩ v k hk
  have hb := SemiprimeNativeInputBits.dimensions_le n B Q R J
  have h := SemiprimeNativeBitsCounter.count_correct (arity:=arity)
    (rows:=fun e i v => (layout (r:=r) (Q:=Q) arity coordinate eps R).row ⟨e,i⟩ v) b Q J R
    (SemiprimeSourceRowHeight.rowDenominator Q R)
    (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) hJ design read T hvalid
    (SemiprimeSourceRowHeight.rowDenominator_pos Q R)
    (SemiprimeNativeInputBits.denominator_le n B Q R J)
    (SemiprimeNativeInputBits.numerator_le n B Q R J) hb.2.1 hb.2.2.1 hb.1 hs hT
    (fun e i v => (layout (r:=r) (Q:=Q) arity coordinate eps R).row_degree ⟨e,i⟩ v)
    hc hprecision coordinate
    (fun e i v => (layout (r:=r) (Q:=Q) arity coordinate eps R).row_origin ⟨e,i⟩ v)
  simp only [design,sourceDesign_runtime] at h
  unfold count
  dsimp only
  simp only [Array.getElem_ofFn,SemiprimePaidFiniteEnumerations.indexed_value]
  have hd : (fun t : Fin Q =>
      (SemiprimePaidRuntimeDesign.build
        (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F)
          (SemiprimePaidRawAcquisition.acquire arity coordinate en eps R B).value t)
        (SemiprimePaidRawAcquisition.reader (n:=n)
          (SemiprimePaidRawAcquisition.acquire arity coordinate en eps R B).value t)
        (SemiprimePaidMeasurementBound.bits B Q R)).value)=
      (fun t : Fin Q => SemiprimeRuntimeDesignAcquisition.build
        (SemiprimeAcquiredSourceCounter.raw (r:=r) arity coordinate eps R B t)) := by
    funext t
    exact SemiprimeFullSetupCounter.physical_design arity coordinate eps R B howner hQ hAQ t
  change (SemiprimeNativeBitsCounter.count b Q J R _ read T).value=_
  let f := fun en : SemiprimeSourceLayout.Enumerations
      ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q =>
    fun t : Fin Q => (SemiprimePaidRuntimeDesign.build
      (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F)
        (SemiprimePaidRawAcquisition.acquire arity coordinate en eps R B).value t)
      (SemiprimePaidRawAcquisition.reader (n:=n)
        (SemiprimePaidRawAcquisition.acquire arity coordinate en eps R B).value t)
      (SemiprimePaidMeasurementBound.bits B Q R)).value
  have heq := congrArg f (SemiprimePaidFiniteEnumerations.indexed_value n F r Q arity)
  have hd' := heq.trans hd
  exact (congrArg (fun ds : Fin Q → SemiprimeNodeArrayExecution.RuntimeDesign n F =>
    (SemiprimeNativeBitsCounter.count b Q J R ds read T).value) hd').trans h

/-- The actual full source producer and encoding reports are retained in the setup work. -/
theorem work_retains_source (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) :
    (SemiprimeSourceWordAcquisition.acquire
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value eps R B).work≤
      (count (r:=r) (Q:=Q) arity coordinate eps R B J T).work := by
  unfold count
  dsimp only
  omega

end RiemannGaussian.SemiprimeNativeBitsSetupCounter
