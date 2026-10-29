/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteBitsSetupCounter
import RiemannGaussian.SemiprimeHermiteBitsCounterBudget
import RiemannGaussian.SemiprimeFullSetupBudget

/-! # Attached original setup and full word-node cost join
The actual original source guards discharge all physical source size/width
premises. Scalar source/digit arithmetic and address refinement remain
separate from a complete original-input primitive-bit clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace RiemannGaussian.SemiprimeHermiteBitsSetupBudget
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SemiprimeRationalBits SemiprimeJetBits SemiprimeLocalBits
open SemiprimeNodeArrayExecution (RuntimeDesign)
variable {n F r Q : ℕ} [NeZero r]

/-- Precisely the actual physical design values cached by the new setup counter. -/
def designs (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ) : Fin Q → RuntimeDesign n F :=
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let raw := SemiprimePaidRawAcquisition.acquire arity coordinate en.value eps R B
  let cached := Array.ofFn (fun t : Fin Q => SemiprimePaidRuntimeDesign.build
    (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F) raw.value t)
    (SemiprimePaidRawAcquisition.reader (n:=n) raw.value t)
    (SemiprimePaidMeasurementBound.bits B Q R))
  fun t => (cached[t.val]'(by simp [cached])).value

/-- Exactly the executed physical-native work, with actual encoded source getters. -/
def nativeWork (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) : ℕ :=
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let source := SemiprimeSourceWordAcquisition.acquire
    (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en.value eps R B
  (SemiprimeHermiteBitsCounter.count (SemiprimeNativeInputBits.inputBits n B Q R J) Q J R
    (designs (r:=r) (Q:=Q) arity coordinate eps R B)
    (fun e i v => SemiprimeSourceWordAcquisition.readWords en.value.incidences source.words ⟨e,i⟩ v) T).work

/-- Exactly the additional scalar encoding report, excluding retained original source work. -/
def encodingWork (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ) : ℕ :=
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  (SemiprimeSourceWordAcquisition.acquire
    (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en.value eps R B).encodingWork

/-- The new work is old ACTUAL setup plus its additional encoding and new ACTUAL word-node work.
No equality with the old native clock is asserted. -/
theorem count_work_eq (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord) :
    (SemiprimeHermiteBitsSetupCounter.count (r:=r) (Q:=Q) arity coordinate eps R B J T).work=
      SemiprimeFullSetupBudget.setupWork (r:=r) (Q:=Q) arity coordinate eps R B+
        encodingWork (r:=r) (Q:=Q) arity coordinate eps R B+1+
        nativeWork (r:=r) (Q:=Q) arity coordinate eps R B J T := by
  unfold SemiprimeHermiteBitsSetupCounter.count SemiprimeFullSetupBudget.setupWork
    encodingWork nativeWork designs SemiprimeSourceWordAcquisition.acquire
  dsimp only
  omega

/-- The actual additional source encoding has its closed original-dimension budget. -/
theorem encodingWork_le (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ) :
    encodingWork (r:=r) (Q:=Q) arity coordinate eps R B≤
      SemiprimeSourceWordAcquisition.encodingBudget (∑ e,arity e) n
        (SemiprimeSourceWordAcquisition.sourceBits B Q R) R := by
  unfold encodingWork SemiprimeSourceWordAcquisition.acquire
  dsimp only
  have h := SemiprimeSourceWordAcquisition.encodeFamily_work (n:=n)
    (SemiprimeSourceWordAcquisition.sourceBits B Q R) R
    (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.incidences
    (SemiprimeMaterializedOriginalSource.acquire
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value eps R).value
  rw [SemiprimePaidFiniteEnumerations.indexed_incidence_length] at h
  exact h

/-- Native budget including every cached source getter, actual node encoder and physical group. -/
def nativeBudget (n F M b Q J R H cap w E : ℕ) (arity : Fin F → ℕ) (d : Fin Q → RuntimeDesign n F) : ℕ :=
  M*n*(2*M+6)+Q*(4*(b+1)+4)+
    SemiprimeHermiteBitsCounterBudget.reductionBudget b Q J R H cap
      (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b M w (R+1) E) arity d+
    SemiprimeNativeBitsCounter.inputControl n F M R b+
    SemiprimeHermiteBitsCounter.control b Q J R arity d+10*Q+10

/-- Original constructor assumptions supply all physical source guards internally. -/
theorem nativeWork_le (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B J H cap w E : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (howner : ∀ v,(Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q)
    (hh : ∀ a g,(designs (r:=r) (Q:=Q) arity coordinate eps R B a).h g≤H)
    (hm : ∀ a g,(designs (r:=r) (Q:=Q) arity coordinate eps R B a).m g≤cap)
    (harity : ∀ e,arity e≤w) (hentry : ∀ e eta,(T e eta).clock≤E)
    (hentryWidth : ∀ e eta,(T e eta).bits.magnitude.length≤1) :
    nativeWork (r:=r) (Q:=Q) arity coordinate eps R B J T≤
      nativeBudget n F (∑ e,arity e) (SemiprimeNativeInputBits.inputBits n B Q R J)
        Q J R H cap w E arity (designs (r:=r) (Q:=Q) arity coordinate eps R B) := by
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let source := SemiprimeSourceWordAcquisition.acquire owner Sigma.fst en.value eps R B
  let read := fun (e : Fin F) (i : Fin (arity e)) (v : Fin n) =>
    SemiprimeSourceWordAcquisition.readWords en.value.incidences source.words ⟨e,i⟩ v
  let b := SemiprimeNativeInputBits.inputBits n B Q R J
  let W := SemiprimeNativeGroupBits.groupWidth b R F (∑ e,arity e)
  have hW : b+1≤W := by
    unfold W SemiprimeNativeGroupBits.groupWidth SemiprimeNativeLocalBits.publicWidth
    omega
  have hs : ∀ e i v,Bounded (read e i v).value W := by
    intro e i v k hk
    have h := SemiprimeSourceWordAcquisition.acquire_row_bounded owner Sigma.fst en.value eps R B
      howner hQ hAQ ⟨e,i⟩ v k hk
    have hb := (SemiprimeNativeInputBits.sourceWidth_le n B Q R J).trans
      ((Nat.le_succ b).trans hW)
    exact ⟨h.1.trans hb,h.2.trans hb⟩
  have hsize : ∀ e i v,(read e i v).value.size≤R+1 := by
    intro e i v
    exact le_of_eq (SemiprimeSourceWordAcquisition.acquire_row_size owner Sigma.fst en.value eps R B ⟨e,i⟩ v)
  have hew : ∀ e eta,(T e eta).bits.magnitude.length≤W := by
    intro e eta
    exact (hentryWidth e eta).trans ((by omega : 1≤b+1).trans hW)
  have hw := SemiprimeHermiteBitsCounterBudget.count_work b Q J R H cap w (R+1) E
    (designs (r:=r) (Q:=Q) arity coordinate eps R B) read T hh hm harity hs hsize hentry hew
  have hread (e : Fin F) (i : Fin (arity e)) (v : Fin n) : (read e i v).work≤2*(∑ e,arity e)+6 := by
    have h := SemiprimeSourceWordAcquisition.readWords_work en.value.incidences source.words ⟨e,i⟩ v
    rw [SemiprimePaidFiniteEnumerations.indexed_incidence_length] at h
    exact h
  have hsum := Finset.sum_le_sum (fun e (_ : e∈(Finset.univ : Finset (Fin F))) =>
    Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin (arity e)))) =>
      Finset.sum_le_sum (fun v (_ : v∈(Finset.univ : Finset (Fin n))) => hread e i v)))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  have hsum' : (∑ e,∑ i,∑ v,(read e i v).work)≤(∑ e,arity e)*n*(2*(∑ e,arity e)+6) := by
    simpa only [← Finset.sum_mul,Nat.mul_assoc] using hsum
  exact hw.trans (by
    unfold nativeBudget
    gcongr)

/-- Actual whole setup/native report bound, with no source/Fits/group-cost advice. -/
theorem count_work (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B J H cap w E : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hr : 2≤r)
    (howner : ∀ v,(Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q)
    (hh : ∀ a g,(designs (r:=r) (Q:=Q) arity coordinate eps R B a).h g≤H)
    (hm : ∀ a g,(designs (r:=r) (Q:=Q) arity coordinate eps R B a).m g≤cap)
    (harity : ∀ e,arity e≤w) (hentry : ∀ e eta,(T e eta).clock≤E)
    (hentryWidth : ∀ e eta,(T e eta).bits.magnitude.length≤1) :
    (SemiprimeHermiteBitsSetupCounter.count (r:=r) (Q:=Q) arity coordinate eps R B J T).work≤
      SemiprimeFullSetupBudget.setupBudget n F (∑ e,arity e) r Q R B (r^(2*Q)) (r^Q)+
      SemiprimeSourceWordAcquisition.encodingBudget (∑ e,arity e) n
        (SemiprimeSourceWordAcquisition.sourceBits B Q R) R+1+
      nativeBudget n F (∑ e,arity e) (SemiprimeNativeInputBits.inputBits n B Q R J)
        Q J R H cap w E arity (designs (r:=r) (Q:=Q) arity coordinate eps R B) := by
  rw [count_work_eq]
  exact Nat.add_le_add (Nat.add_le_add_right
    (Nat.add_le_add (SemiprimeFullSetupBudget.setup_work_bound arity coordinate eps R B hr howner hQ hAQ)
      (encodingWork_le arity coordinate eps R B)) 1)
    (nativeWork_le arity coordinate eps R B J H cap w E T howner hQ hAQ hh hm harity hentry hentryWidth)

end RiemannGaussian.SemiprimeHermiteBitsSetupBudget
