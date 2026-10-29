/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFibreArrayExecution
import RiemannGaussian.SemiprimeMixedRadix

/-!
# Streamed summary and signed-support acquisition of concrete packet arrays

Summary codes are decoded independently by mixed radix. The ternary support
traversal and all array additions execute actual callbacks and retain their work.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimePacketArrayExecution
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeArrayOps SemiprimeFibreArrayExecution
open SemiprimeCounterEnumeration SemiprimeRepresentativeExecution

/-- Tail-recursive finite-code traversal without a materialized code list. -/
def sumCodes (J N : ℕ) (f : Fin N → Run) : Run :=
  sumFrom J (fun i => if hi : i < N then f ⟨i,hi⟩ else zeroRun J) N 0 (zeroRun J)

theorem sumCodes_spec (J N : ℕ) (f : Fin N → Run) (P : Fin N → Polynomial ℚ)
    (hf : ∀ i, Spec J (f i) (P i)) : Spec J (sumCodes J N f) (∑ i, P i) := by
  classical
  have hs := sumFrom_spec J N 0
    (fun i => if hi : i < N then f ⟨i,hi⟩ else zeroRun J)
    (fun i => if hi : i < N then P ⟨i,hi⟩ else 0) (zeroRun J) 0 (zeroRun_spec J)
    (by intro i hi hj; have hj' : i < N := by omega
        simpa only [dite_eq_left hj'] using hf ⟨i,hj'⟩)
  simpa only [sumCodes,zero_add,← Finset.sum_fin_eq_sum_range] using hs

theorem sumCodes_work (J N B : ℕ) (f : Fin N → Run) (hf : ∀ i, (f i).work ≤ B) :
    (sumCodes J N f).work ≤ (J+1)+N*(B+(4*J+1)) := by
  have hs := sumFrom_work J N 0 B
    (fun i => if hi : i < N then f ⟨i,hi⟩ else zeroRun J) (zeroRun J)
    (by intro i hi hj; have hj' : i < N := by omega
        simpa only [dite_eq_left hj'] using hf ⟨i,hj'⟩)
  simpa only [sumCodes,zeroRun,Run.work,zeroJet,zero_add] using hs

/-- An actual extra control charge leaves the acquired jet unchanged. -/
def bump (r : Run) (amount : ℕ) : Run := ⟨r.jet,r.control+amount⟩

theorem bump_spec (J : ℕ) (r : Run) (P : Polynomial ℚ) (amount : ℕ)
    (h : Spec J r P) : Spec J (bump r amount) P := h

theorem bump_work (r : Run) (amount : ℕ) : (bump r amount).work = r.work+amount := by
  simp only [bump,Run.work]
  omega

/-- Actual array-valued ternary support stream; no subset-pair list is built. -/
def supportRun {A : Type} [DecidableEq A] (J : ℕ) :
    List A → ℕ → (Finset A → Finset A → Run) → Run
  | [], _, f => f ∅ ∅
  | _::tail, 0, f => bump (supportRun J tail 0 f) 1
  | a::tail, q+1, f =>
      let e := supportRun J tail (q+1) f
      let s := supportRun J tail q (fun S U => f (insert a S) U)
      let u := supportRun J tail q (fun S U => f (insert a S) (insert a U))
      bump (addRun J (addRun J e s) u) 1

theorem supportRun_spec {A : Type} [DecidableEq A] (J : ℕ) (todo : List A) (q : ℕ)
    (f : Finset A → Finset A → Run) (P : Finset A → Finset A → Polynomial ℚ)
    (hf : ∀ S U, Spec J (f S U) (P S U)) :
    Spec J (supportRun J todo q f) (stream todo q P) := by
  induction todo generalizing q f P with
  | nil => exact hf ∅ ∅
  | cons a tail ih =>
    cases q with
    | zero => exact bump_spec J _ _ 1 (ih 0 f P hf)
    | succ q =>
      exact bump_spec J _ _ 1 (addRun_spec J _ _ _ _
        (addRun_spec J _ _ _ _ (ih (q+1) f P hf)
          (ih q (fun S U => f (insert a S) U) (fun S U => P (insert a S) U)
            (fun S U => hf _ _)))
        (ih q (fun S U => f (insert a S) (insert a U))
          (fun S U => P (insert a S) (insert a U)) (fun S U => hf _ _)))

theorem supportRun_menu_spec {A : Type} [DecidableEq A] (J : ℕ) (todo : List A)
    (hn : todo.Nodup) (q : ℕ) (f : Finset A → Finset A → Run)
    (P : Finset A → Finset A → Polynomial ℚ)
    (hf : ∀ S U, Spec J (f S U) (P S U)) :
    Spec J (supportRun J todo q f) (menu todo.toFinset q P) := by
  rw [← stream_eq_menu todo hn q P]
  exact supportRun_spec J todo q f P hf

/-- Every value callback and the selected array/branch charges are retained.
Finite-set and mixed-radix encoding costs remain a separate polynomial overhead. -/
theorem supportRun_work {A : Type} [DecidableEq A] (J B : ℕ) (todo : List A) (q : ℕ)
    (f : Finset A → Finset A → Run) (hf : ∀ S U, (f S U).work ≤ B) :
    (supportRun J todo q f).work ≤ callbacks todo.length q * (B+todo.length*(8*J+3)) := by
  induction todo generalizing q f with
  | nil => simpa only [supportRun,List.length_nil,callbacks,Nat.zero_mul,Nat.add_zero,Nat.one_mul]
      using hf ∅ ∅
  | cons a tail ih =>
    cases q with
    | zero =>
      have ht := ih 0 f hf
      have hc : 1 ≤ callbacks tail.length 0 := by rw [callbacks_eq_weightedCount,weightedCount_zero]
      rw [supportRun,bump_work,List.length_cons,callbacks]
      nlinarith
    | succ q =>
      have he := ih (q+1) f hf
      have hs := ih q (fun S U => f (insert a S) U) (fun S U => hf _ _)
      have hu := ih q (fun S U => f (insert a S) (insert a U)) (fun S U => hf _ _)
      have hc : 1 ≤ callbacks tail.length (q+1) := by
        rw [callbacks_eq_weightedCount,weightedCount]
        have hzero := Finset.single_le_sum (f := fun j => 2^j*tail.length.choose j)
          (fun _ _ => Nat.zero_le _) (by simp : 0 ∈ Finset.range (q+1+1))
        simpa only [pow_zero,Nat.choose_zero_right,Nat.mul_one] using hzero
      rw [supportRun,bump_work,addRun_work,addRun_work,List.length_cons,callbacks]
      nlinarith

/-- Exact public cardinal of the FULL mixed-radix summary box. -/
def summaryCount (r : ℕ) (h m W : Fin r → ℕ) : ℕ :=
  ∏ g, ∏ _j : Fin (m g), (2*(Fintype.card (Fin (h g))*W g)+1)

/-- Literal code decoder; no list of summaries or attained-fibre advice. -/
def summaryCode (r : ℕ) (h m W : Fin r → ℕ) :
    Fin (summaryCount r h m W) ≃
      ((g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g)) :=
  by
    change Fin (∏ g, ∏ _j : Fin (m g), (2*(Fintype.card (Fin (h g))*W g)+1)) ≃
      ((g : Fin r) → (j : Fin (m g)) → Fin (2*(Fintype.card (Fin (h g))*W g)+1))
    exact SemiprimeMixedRadix.nested r m (fun g _ => 2*(Fintype.card (Fin (h g))*W g)+1)

/-- All summaries are scanned one at a time, each acquiring its representatives
and local fibres. The callback still supplies the paid actual local factor products. -/
def fibreSum (J r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run) : Run :=
  sumCodes J (summaryCount r h m W) (fun code =>
    fibreAt J r h m W rows (summaryCode r h m W code) forced value)

theorem fibreSum_spec (J r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run)
    (P : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Polynomial ℚ)
    (hv : ∀ g x, Spec J (value g x) (P g x)) :
    Spec J (fibreSum J r h m W rows forced value)
      (∑ y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g),
        ∏ g, ∑ bits : Fin (h g) → Bool,
          if (∀ j, (∑ i, if bits i then rows g j i else 0) =
                summaryTarget (h g) (m g) (W g) (y g) j) ∧
              (∀ i, forced g i = true → bits i = true)
          then P g (Function.update
            (fun k => summaryRepresentative (h k) (m k) (W k) (rows k) (y k)) g bits)
          else 0) := by
  classical
  rw [← (summaryCode r h m W).sum_comp]
  exact sumCodes_spec J _ _ _ (fun _code => fibreAt_spec J r h m W rows _ forced value P hv)

theorem fibreSum_work (J r H M B : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run)
    (hh : ∀ g, h g ≤ H) (hm : ∀ g, m g ≤ M) (hv : ∀ g x, (value g x).work ≤ B) :
    (fibreSum J r h m W rows forced value).work ≤ (J+1)+summaryCount r h m W *
      (r*(2^H*(B+M*(4*H+3)+4*H+5*J+6)+(2*J*(J+1)+J+1))+(J+1) +
        r*(2^H*(M*(4*H+3)+3))+1+(4*J+1)) :=
  sumCodes_work J _ _ _ (fun _code => fibreAt_work J r H M B h m W rows _ forced value hh hm hv)

/-- Repeated actual sign negation with its scalar operation count. -/
def signPower : ℕ → ℚ × ℕ
  | 0 => (1,0)
  | k+1 => let old := signPower k; (-old.1,old.2+1)

theorem signPower_value (k : ℕ) : (signPower k).1 = (-1 : ℚ)^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [signPower,ih,pow_succ]; ring

theorem signPower_work (k : ℕ) : (signPower k).2 = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [signPower,ih]

/-- One acquired fibre receives its actual Möbius sign; computation is paid. -/
def signedFibre {A : Type} (J : ℕ)
    (f : Finset A → Finset A → Run) (S U : Finset A) : Run :=
  let sign := signPower (S.card-U.card)
  bump (scaleRun J (f S U) sign.1) (sign.2+S.card+U.card+1)

theorem signedFibre_spec {A : Type} (J : ℕ)
    (f : Finset A → Finset A → Run) (P : Finset A → Finset A → Polynomial ℚ)
    (hf : ∀ S U, Spec J (f S U) (P S U)) (S U : Finset A) :
    Spec J (signedFibre J f S U) (C ((-1 : ℚ)^(S.card-U.card))*P S U) := by
  unfold signedFibre
  apply bump_spec
  rw [signPower_value]
  exact scaleRun_spec J (f S U) _ (P S U) (hf S U)

theorem signedFibre_work {A : Type} [Fintype A] (J B : ℕ)
    (f : Finset A → Finset A → Run) (hf : ∀ S U, (f S U).work ≤ B) (S U : Finset A) :
    (signedFibre J f S U).work ≤ B+3*J+3*Fintype.card A+2 := by
  rw [signedFibre,bump_work,scaleRun_work,signPower_work]
  have hs := Finset.card_le_univ S
  have hu := Finset.card_le_univ U
  have hb := hf S U
  omega

/-- Concrete array acquisition over the inclusive Taylor support cutoff. -/
def rawRun {A : Type} [DecidableEq A] (J : ℕ) (todo : List A)
    (f : Finset A → Finset A → Run) : Run :=
  supportRun J todo (J-1) (signedFibre J f)

theorem rawRun_work {A : Type} [Fintype A] [DecidableEq A] (J B : ℕ) (todo : List A)
    (f : Finset A → Finset A → Run) (hf : ∀ S U, (f S U).work ≤ B) :
    (rawRun J todo f).work ≤ weightedCount todo.length (J-1) *
      (B+3*J+3*Fintype.card A+2+todo.length*(8*J+3)) := by
  exact (supportRun_work J (B+3*J+3*Fintype.card A+2) todo (J-1) (signedFibre J f)
    (fun S U => signedFibre_work J B f hf S U)).trans_eq
      (by rw [callbacks_eq_weightedCount])

/-- The acquired raw array is exactly the pre-existing native packet expression.
The fibre callbacks must execute local scans; no global polynomial sample is input. -/
theorem rawRun_native_spec {A E : Type} [Fintype A] [DecidableEq A] [Fintype E]
    (arity : E → ℕ) (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → A → Polynomial ℚ) (t : ℚ) (R J : ℕ)
    (d : SemiprimeCounterCompose.NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (todo : List A) (hn : todo.Nodup) (hcomplete : todo.toFinset = Finset.univ)
    (f : Finset A → Finset A → Run)
    (hf : ∀ S U, Spec J (f S U)
      (SemiprimeCounterCompose.fibrePacket arity T (fun e i v => (rows e i v).eval t) d
        (SemiprimeCounterCompose.nativeCorrection arity rows t R U) S)) :
    Spec J (rawRun J todo f) (SemiprimeCounterCompose.rawPacket arity T rows t R J d) := by
  classical
  have hs := supportRun_menu_spec J todo hn (J-1) (signedFibre J f) _
    (fun S U => signedFibre_spec J f _ hf S U)
  rw [hcomplete] at hs
  unfold menu at hs
  unfold SemiprimeCounterCompose.rawPacket
  rw [Finset.sum_filter]
  exact hs

/-- No Taylor input oracle remains once the local fibre callback has its execution
specification: the acquired coefficients equal the true global Taylor packet. -/
theorem rawRun_taylor_spec {A E : Type} [Fintype A] [DecidableEq A] [Fintype E]
    (arity : E → ℕ) (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → A → Polynomial ℚ) (t : ℚ) (R J : ℕ)
    (d : SemiprimeCounterCompose.NodeCertificate arity (fun e i v => (rows e i v).eval t))
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R)
    (todo : List A) (hn : todo.Nodup) (hcomplete : todo.toFinset = Finset.univ)
    (f : Finset A → Finset A → Run)
    (hf : ∀ S U, Spec J (f S U)
      (SemiprimeCounterCompose.fibrePacket arity T (fun e i v => (rows e i v).eval t) d
        (SemiprimeCounterCompose.nativeCorrection arity rows t R U) S)) :
    Spec J (rawRun J todo f)
      (taylor t (SemiprimeCounterNative.globalPolynomial arity T rows)) := by
  intro i hi
  rw [rawRun_native_spec arity T rows t R J d todo hn hcomplete f hf i hi]
  exact SemiprimeCounterCompose.rawPacket_coeff arity T rows t R J d hrows i hi

end RiemannGaussian.SemiprimePacketArrayExecution
