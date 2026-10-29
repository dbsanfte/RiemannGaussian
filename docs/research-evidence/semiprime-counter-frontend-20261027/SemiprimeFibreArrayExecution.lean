/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeArrayOps
import RiemannGaussian.SemiprimeRepresentativeExecution
import RiemannGaussian.SemiprimeCounterEnumeration

/-!
# Executed array traversals for separated counter packets

These routines execute truncated-array operations and retain callback work.
Their polynomial specifications are proofs, not runtime polynomial suppliers.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeFibreArrayExecution
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeArrayOps
open SemiprimeRepresentativeExecution

/-- A concrete jet result, charged arithmetic/reads, and array/control charges. -/
structure Run where
  /-- Actual cached array and its arithmetic/access report. -/
  jet : InverseReport
  /-- Additional allocation and finite-loop control charges. -/
  control : ℕ

/-- Combined operation ledger; integer/rational bit costs are separate. -/
def Run.work (r : Run) : ℕ := r.jet.arithmetic + r.jet.reads + r.control

/-- Low coefficients of an actual array represent the specified polynomial. -/
def Spec (J : ℕ) (r : Run) (P : Polynomial ℚ) : Prop :=
  ∀ i < J, coefficient r.jet.coefficients i = P.coeff i

/-- Allocate a zero array with its finite allocation charge. -/
def zeroRun (J : ℕ) : Run := ⟨zeroJet J,J+1⟩
/-- Allocate the truncated constant-one array with its allocation charge. -/
def oneRun (J : ℕ) : Run := ⟨oneJet J,J+1⟩

/-- Both callback reports are included when their actual arrays are added. -/
def addRun (J : ℕ) (a b : Run) : Run :=
  let out := addJet a.jet.coefficients b.jet.coefficients J
  ⟨⟨out.coefficients,a.jet.arithmetic+b.jet.arithmetic+out.arithmetic,
      a.jet.reads+b.jet.reads+out.reads⟩,a.control+b.control+J+1⟩

/-- Both callback reports are included in the actual cached multiplication. -/
def mulRun (J : ℕ) (a b : Run) : Run :=
  let out := multiply a.jet.coefficients b.jet.coefficients J
  ⟨⟨out.coefficients,a.jet.arithmetic+b.jet.arithmetic+out.arithmetic,
      a.jet.reads+b.jet.reads+out.reads⟩,a.control+b.control+J+1⟩

/-- Actual scaling also retains the work acquiring the input array. -/
def scaleRun (J : ℕ) (a : Run) (c : ℚ) : Run :=
  let out := scaleJet a.jet.coefficients c J
  ⟨⟨out.coefficients,a.jet.arithmetic+out.arithmetic,a.jet.reads+out.reads⟩,
    a.control+J+1⟩

theorem zeroRun_spec (J : ℕ) : Spec J (zeroRun J) 0 := by
  intro i hi
  exact (zeroJet_coefficient J i).trans (coeff_zero i).symm

theorem oneRun_spec (J : ℕ) : Spec J (oneRun J) 1 := by
  intro i hi
  change coefficient (oneJet J).coefficients i = (1 : Polynomial ℚ).coeff i
  rw [oneJet_coefficient J i hi,coeff_one]

theorem addRun_spec (J : ℕ) (a b : Run) (P Q : Polynomial ℚ)
    (ha : Spec J a P) (hb : Spec J b Q) : Spec J (addRun J a b) (P+Q) := by
  intro i hi
  change coefficient (addJet a.jet.coefficients b.jet.coefficients J).coefficients i = _
  rw [addJet_coefficient _ _ _ _ hi,ha i hi,hb i hi,coeff_add]

theorem mulRun_spec (J : ℕ) (a b : Run) (P Q : Polynomial ℚ)
    (ha : Spec J a P) (hb : Spec J b Q) : Spec J (mulRun J a b) (P*Q) :=
  specification_of_asPolynomial _ _ _ (multiply_correct _ _ J P Q ha hb)

theorem scaleRun_spec (J : ℕ) (a : Run) (c : ℚ) (P : Polynomial ℚ)
    (ha : Spec J a P) : Spec J (scaleRun J a c) (C c*P) := by
  intro i hi
  change coefficient (scaleJet a.jet.coefficients c J).coefficients i = _
  rw [scaleJet_coefficient _ _ _ _ hi,ha i hi,coeff_C_mul]

theorem addRun_work (J : ℕ) (a b : Run) :
    (addRun J a b).work = a.work+b.work+(4*J+1) := by
  simp only [Run.work,addRun,addJet]
  omega

theorem mulRun_work (J : ℕ) (a b : Run) :
    (mulRun J a b).work = a.work+b.work+(2*J*(J+1)+J+1) := by
  simp only [Run.work,mulRun,(multiply_work _ _ _).1,(multiply_work _ _ _).2]
  ring

theorem scaleRun_work (J : ℕ) (a : Run) (c : ℚ) :
    (scaleRun J a c).work = a.work+(3*J+1) := by
  simp only [Run.work,scaleRun,scaleJet]
  omega

/-- Sum actual callback arrays over Boolean words, without a truth-table list. -/
def sumBits (J : ℕ) : (n : ℕ) → ((Fin n → Bool) → Run) → Run
  | 0, f => f Fin.elim0
  | n+1, f => addRun J (sumBits J n (fun x => f (Fin.cons false x)))
      (sumBits J n (fun x => f (Fin.cons true x)))

/-- All low coefficients of the binary array traversal are the literal finite sum. -/
theorem sumBits_spec (J n : ℕ) (f : (Fin n → Bool) → Run)
    (P : (Fin n → Bool) → Polynomial ℚ) (hf : ∀ x, Spec J (f x) (P x)) :
    Spec J (sumBits J n f) (∑ x, P x) := by
  classical
  induction n with
  | zero =>
    have he : (∑ x : Fin 0 → Bool, P x) = P Fin.elim0 := by
      rw [Fintype.sum_unique]
      congr 1
    exact he.symm ▸ hf Fin.elim0
  | succ n ih =>
    have h := addRun_spec J _ _ _ _
      (ih (fun x => f (Fin.cons false x)) (fun x => P (Fin.cons false x)) (fun x => hf _))
      (ih (fun x => f (Fin.cons true x)) (fun x => P (Fin.cons true x)) (fun x => hf _))
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp,
      Fintype.sum_prod_type,Fintype.sum_bool]
    change Spec J (addRun J _ _)
      ((∑ x, P (Fin.cons true x)) + ∑ x, P (Fin.cons false x))
    rw [add_comm (∑ x, P (Fin.cons true x)) (∑ x, P (Fin.cons false x))]
    exact h

/-- Callback work is multiplied only by the actual local Boolean scan size. -/
theorem sumBits_work (J n B : ℕ) (f : (Fin n → Bool) → Run)
    (hf : ∀ x, (f x).work ≤ B) :
    (sumBits J n f).work + (4*J+1) ≤ 2^n*(B+(4*J+1)) := by
  induction n with
  | zero => simpa only [sumBits,pow_zero,one_mul] using Nat.add_le_add_right (hf Fin.elim0) _
  | succ n ih =>
    have hl := ih (fun x => f (Fin.cons false x)) (fun x => hf _)
    have hr := ih (fun x => f (Fin.cons true x)) (fun x => hf _)
    rw [sumBits,addRun_work,pow_succ]
    nlinarith

/-- A finite factor/group product retains one recursive suffix and one callback. -/
def productList {A : Type} (J : ℕ) : List A → (A → Run) → Run
  | [], _ => oneRun J
  | a::tail, f => mulRun J (f a) (productList J tail f)

theorem productList_spec {A : Type} (J : ℕ) (xs : List A) (f : A → Run)
    (P : A → Polynomial ℚ) (hf : ∀ x ∈ xs, Spec J (f x) (P x)) :
    Spec J (productList J xs f) ((xs.map P).prod) := by
  induction xs with
  | nil => exact oneRun_spec J
  | cons a tail ih =>
    exact mulRun_spec J _ _ _ _ (hf a (by simp))
      (ih (fun x hx => hf x (by simp [hx])))

theorem productList_work {A : Type} (J B : ℕ) (xs : List A) (f : A → Run)
    (hf : ∀ x ∈ xs, (f x).work ≤ B) :
    (productList J xs f).work ≤ xs.length*(B+(2*J*(J+1)+J+1))+(J+1) := by
  induction xs with
  | nil => simp [productList,oneRun,Run.work,oneJet]
  | cons a tail ih =>
    have hh := hf a (by simp)
    have ht := ih (fun x hx => hf x (by simp [hx]))
    rw [productList,mulRun_work,List.length_cons]
    nlinarith

/-- Tail-recursive range sum: only the current array accumulator is passed onward. -/
def sumFrom (J : ℕ) (f : ℕ → Run) : ℕ → ℕ → Run → Run
  | 0, _, acc => acc
  | fuel+1, start, acc => sumFrom J f fuel (start+1) (addRun J acc (f start))

theorem sumFrom_spec (J fuel start : ℕ) (f : ℕ → Run) (P : ℕ → Polynomial ℚ)
    (acc : Run) (A : Polynomial ℚ) (ha : Spec J acc A)
    (hf : ∀ i, start ≤ i → i < start+fuel → Spec J (f i) (P i)) :
    Spec J (sumFrom J f fuel start acc) (A+∑ i ∈ Finset.range fuel, P (start+i)) := by
  induction fuel generalizing start acc A with
  | zero => simpa [sumFrom] using ha
  | succ fuel ih =>
    have h := ih (start+1) (addRun J acc (f start)) (A+P start)
      (addRun_spec J acc (f start) A (P start) ha (hf start (by omega) (by omega)))
      (fun i hi hj => hf i (by omega) (by omega))
    simpa only [sumFrom,Finset.sum_range_succ',Nat.add_zero,Nat.add_assoc,
      Nat.add_comm 1,add_assoc,add_comm (P start)] using h

theorem sumFrom_work (J fuel start B : ℕ) (f : ℕ → Run) (acc : Run)
    (hf : ∀ i, start ≤ i → i < start+fuel → (f i).work ≤ B) :
    (sumFrom J f fuel start acc).work ≤ acc.work+fuel*(B+(4*J+1)) := by
  induction fuel generalizing start acc with
  | zero => simp [sumFrom]
  | succ fuel ih =>
    have hh := hf start (by omega) (by omega)
    have ht := ih (start+1) (addRun J acc (f start)) (fun i hi hj => hf i (by omega) (by omega))
    rw [addRun_work] at ht
    change (sumFrom J f fuel (start+1) (addRun J acc (f start))).work ≤ _
    nlinarith

/-- Gate the actual callback, including the cost of a rejected local word. -/
def gateRun (J : ℕ) (test : TestReport) (body : Unit → Run) : Run :=
  if test.accepted then
    let result := body ()
    ⟨result.jet,result.control+test.work+1⟩
  else
    let result := zeroRun J
    ⟨result.jet,result.control+test.work+1⟩

theorem gateRun_spec (J : ℕ) (test : TestReport) (body : Unit → Run)
    (P : Polynomial ℚ) (hbody : Spec J (body ()) P) :
    Spec J (gateRun J test body) (if test.accepted then P else 0) := by
  cases ht : test.accepted
  · simpa only [gateRun,ht,Bool.false_eq_true,ite_false,Spec] using zeroRun_spec J
  · simpa only [gateRun,ht,ite_true,Spec] using hbody

theorem gateRun_work (J B : ℕ) (test : TestReport) (body : Unit → Run)
    (hb : (body ()).work ≤ B) :
    (gateRun J test body).work ≤ test.work+B+J+2 := by
  cases ht : test.accepted <;> simp only [gateRun,ht,Bool.false_eq_true,ite_false,ite_true,
    Run.work,zeroRun,zeroJet] at * <;> omega

/-- Literal measurement AND forced-bit gate, with both actual test reports. -/
def fibreTest (n m : ℕ) (rows : Fin m → Fin n → ℤ) (target : Fin m → ℤ)
    (forced bits : Fin n → Bool) : TestReport :=
  let measured := measurementTest n m rows target bits
  let fixed := forcedTest n forced bits
  ⟨measured.accepted && fixed.accepted,measured.work+fixed.work+1⟩

theorem fibreTest_correct (n m : ℕ) (rows : Fin m → Fin n → ℤ) (target : Fin m → ℤ)
    (forced bits : Fin n → Bool) :
    (fibreTest n m rows target forced bits).accepted = true ↔
      (∀ j, (∑ i, if bits i then rows j i else 0) = target j) ∧
        (∀ i, forced i = true → bits i = true) := by
  simp only [fibreTest,Bool.and_eq_true,measurementTest_correct,forcedTest_correct]

theorem fibreTest_work (n m : ℕ) (rows : Fin m → Fin n → ℤ) (target : Fin m → ℤ)
    (forced bits : Fin n → Bool) :
    (fibreTest n m rows target forced bits).work = m*(4*n+3)+4*n+3 := by
  simp only [fibreTest,measurementTest_work,forcedTest_work]
  omega

/-- One group's fibre is scanned directly; no fibre list is constructed. -/
def scanGroup (J n m : ℕ) (rows : Fin m → Fin n → ℤ) (target : Fin m → ℤ)
    (forced : Fin n → Bool) (value : (Fin n → Bool) → Run) : Run :=
  sumBits J n (fun bits => gateRun J (fibreTest n m rows target forced bits) (fun _ => value bits))

theorem scanGroup_spec (J n m : ℕ) (rows : Fin m → Fin n → ℤ) (target : Fin m → ℤ)
    (forced : Fin n → Bool) (value : (Fin n → Bool) → Run)
    (P : (Fin n → Bool) → Polynomial ℚ) (hv : ∀ bits, Spec J (value bits) (P bits)) :
    Spec J (scanGroup J n m rows target forced value)
      (∑ bits, if (∀ j, (∑ i, if bits i then rows j i else 0) = target j) ∧
          (∀ i, forced i = true → bits i = true) then P bits else 0) := by
  classical
  have h := sumBits_spec J n _ _ (fun bits => gateRun_spec J
    (fibreTest n m rows target forced bits) (fun _ => value bits) (P bits) (hv bits))
  simpa only [scanGroup,fibreTest_correct] using h

theorem scanGroup_work (J n m B : ℕ) (rows : Fin m → Fin n → ℤ) (target : Fin m → ℤ)
    (forced : Fin n → Bool) (value : (Fin n → Bool) → Run)
    (hv : ∀ bits, (value bits).work ≤ B) :
    (scanGroup J n m rows target forced value).work ≤
      2^n*(B+m*(4*n+3)+4*n+5*J+6) := by
  have hg (bits : Fin n → Bool) := gateRun_work J B
    (fibreTest n m rows target forced bits) (fun _ => value bits) (hv bits)
  simp only [fibreTest_work] at hg
  have hs := sumBits_work J n (m*(4*n+3)+4*n+3+B+J+2) _ hg
  change (sumBits J n _).work ≤ _
  nlinarith

/-- One concrete signed-box tuple; representatives are acquired once, then groups
are scanned separately and their actual arrays multiplied. -/
def fibreAt (J r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run) : Run :=
  let reps := acquireRepresentatives r h m W rows y
  let result := productList J (List.ofFn (fun g : Fin r => g)) (fun g =>
    scanGroup J (h g) (m g) (rows g) (summaryTarget (h g) (m g) (W g) (y g)) (forced g)
      (fun bits => value g (Function.update reps.words g bits)))
  ⟨result.jet,result.control+reps.work+1⟩

/-- Its exact value is the finite product of native forced measurement fibres.
The callback specification is local; no whole-fibre count or H value is supplied. -/
theorem fibreAt_spec (J r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run)
    (P : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Polynomial ℚ)
    (hv : ∀ g x, Spec J (value g x) (P g x)) :
    Spec J (fibreAt J r h m W rows y forced value)
      (∏ g, ∑ bits : Fin (h g) → Bool,
        if (∀ j, (∑ i, if bits i then rows g j i else 0) =
              summaryTarget (h g) (m g) (W g) (y g) j) ∧
            (∀ i, forced g i = true → bits i = true)
        then P g (Function.update
          (fun k => summaryRepresentative (h k) (m k) (W k) (rows k) (y k)) g bits)
        else 0) := by
  classical
  have hreps : (acquireRepresentatives r h m W rows y).words =
      (fun k => summaryRepresentative (h k) (m k) (W k) (rows k) (y k)) := by
    funext k
    exact acquireRepresentatives_words r h m W rows y k
  have hs := productList_spec J (List.ofFn (fun g : Fin r => g)) _ _
    (fun g _ => scanGroup_spec J (h g) (m g) (rows g)
      (summaryTarget (h g) (m g) (W g) (y g)) (forced g)
      (fun bits => value g (Function.update (acquireRepresentatives r h m W rows y).words g bits))
      (fun bits => P g (Function.update (acquireRepresentatives r h m W rows y).words g bits))
      (fun bits => hv g _))
  simp only [List.map_ofFn,List.prod_ofFn,Function.comp_apply,hreps] at hs
  simpa only [fibreAt,Spec,hreps] using hs

/-- Group scans contribute a SUM of local exponential costs, never a Cartesian
enumeration of all global Boolean assignments. -/
theorem fibreAt_work (J r H M B : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run)
    (hh : ∀ g, h g ≤ H) (hm : ∀ g, m g ≤ M) (hv : ∀ g x, (value g x).work ≤ B) :
    (fibreAt J r h m W rows y forced value).work ≤
      r*(2^H*(B+M*(4*H+3)+4*H+5*J+6)+(2*J*(J+1)+J+1))+(J+1) +
        r*(2^H*(M*(4*H+3)+3))+1 := by
  have hscan (g : Fin r) :
      (scanGroup J (h g) (m g) (rows g) (summaryTarget (h g) (m g) (W g) (y g))
        (forced g) (fun bits => value g (Function.update
          (acquireRepresentatives r h m W rows y).words g bits))).work ≤
          2^H*(B+M*(4*H+3)+4*H+5*J+6) := by
    apply (scanGroup_work J (h g) (m g) B _ _ _ _ (fun bits => hv g _)).trans
    apply Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (hh g))
    have hgh := hh g
    have hb := Nat.mul_le_mul (hm g) (show 4*h g+3 ≤ 4*H+3 by omega)
    omega
  have hp := productList_work J (2^H*(B+M*(4*H+3)+4*H+5*J+6))
    (List.ofFn (fun g : Fin r => g)) _ (fun g _ => hscan g)
  have hr := acquireRepresentatives_work_le r h m W rows y
  have hr' : (acquireRepresentatives r h m W rows y).work ≤ r*(2^H*(M*(4*H+3)+3)) := by
    apply hr.trans
    calc
      _ ≤ ∑ _g : Fin r, 2^H*(M*(4*H+3)+3) := by
        apply Finset.sum_le_sum
        intro g hg
        apply Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (hh g))
        have hgh := hh g
        have hb := Nat.mul_le_mul (hm g) (show 4*h g+3 ≤ 4*H+3 by omega)
        omega
      _ = _ := by simp
  simp only [List.length_ofFn] at hp
  simp only [fibreAt,Run.work]
  unfold Run.work at hp
  omega

end RiemannGaussian.SemiprimeFibreArrayExecution
