/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRationalBits
import RiemannGaussian.SemiprimeRepresentativeExecution

/-!
# Physical signed-word measurement tests

The measurement data path uses signed Boolean addition, paid copies and exact
word equality. Integer values occur only in specifications. Input matrix/target
word acquisition and the outer representative traversal are separate phases.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMeasurementBits
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitPrimeScan
open SemiprimeBitIndexRoots SemiprimeBitIndexClipping SemiprimeBitIndexGeometry SemiprimeBitIndexTraversal
open SemiprimeRepresentativeExecution

/-- Actual signed output together with the executed primitive work. -/
structure WordRun where
  /-- Physical signed output. -/
  word : SignedWord
  /-- Boolean arithmetic, word-copy, list and branch work. -/
  clock : ℕ

/-- Literal signed zero, including its empty magnitude. -/
def zero : SignedWord := ⟨false,[]⟩

/-- Copy a supplied signed word by its actual physical template. -/
def load (a : SignedWord) : SignedCopyWordReport := fitSignedBits a a.magnitude

theorem load_value (a : SignedWord) : (load a).word.value=a.value :=
  fitSignedBits_value (by rw [signedWord_natAbs]; exact bitValue_lt_width _)

theorem load_width (a : SignedWord) : (load a).word.magnitude.length=a.magnitude.length :=
  (fitSignedBits_cost_width _ _).2

theorem load_cost (a : SignedWord) : (load a).clock≤4*a.magnitude.length+4 :=
  (fitSignedBits_cost_width _ _).1

/-- A literal Boolean-masked signed dot product. Every visited row word is
copied, even on its zero branch, and one recursive suffix is retained once. -/
def dot : List SignedWord → List Bool → WordRun
  | [], _ => ⟨zero,4⟩
  | _::_, [] => ⟨zero,4⟩
  | a::as, b::bs =>
      let loaded := load a
      let tail := dot as bs
      if b then
        let sum := addSignedBits loaded.word tail.word
        ⟨sum.word,loaded.clock+tail.clock+sum.clock+8⟩
      else ⟨tail.word,loaded.clock+tail.clock+4⟩

/-- Mathematical dot meaning, with missing bits interpreted as false. -/
def dotValue : List SignedWord → List Bool → ℤ
  | [], _ => 0
  | _::_, [] => 0
  | a::as, b::bs => (if b then a.value else 0)+dotValue as bs

/-- The physical dot product equals the integer specification without fitting
or a supplied bound on its output value. -/
theorem dot_value (row : List SignedWord) (bits : List Bool) :
    (dot row bits).word.value=dotValue row bits := by
  induction row generalizing bits with
  | nil => simp [dot,dotValue,zero,SignedWord.value,bitValue]
  | cons a as ih =>
    cases bits with
    | nil => simp [dot,dotValue,zero,SignedWord.value,bitValue]
    | cons b bs =>
      cases b <;> simp only [dot,dotValue,Bool.false_eq_true,reduceIte,zero_add]
      · exact ih bs
      · rw [addSignedBits_value,load_value,ih]

/-- Physical scratch width grows by at most one cell per row entry. -/
theorem dot_width (row : List SignedWord) (bits : List Bool) (W : ℕ)
    (hrow : ∀ a ∈ row, a.magnitude.length≤W) :
    (dot row bits).word.magnitude.length≤W+row.length := by
  induction row generalizing bits with
  | nil => simp [dot,zero]
  | cons a as ih =>
    cases bits with
    | nil => simp [dot,zero]
    | cons b bs =>
      have ha := hrow a List.mem_cons_self
      have ht := ih bs (fun a h => hrow a (List.mem_cons_of_mem _ h))
      have hl : (load a).word.magnitude.length≤W+as.length := by rw [load_width]; omega
      have hs := (addSignedBits_cost_width hl ht).2
      cases b <;> simp only [dot,Bool.false_eq_true,reduceIte,List.length_cons] <;> omega

/-- The actual dot loop has polynomial bit cost at the supplied physical input
width. No common-denominator or output-fit premise is needed for integers. -/
theorem dot_cost (row : List SignedWord) (bits : List Bool) (W : ℕ)
    (hrow : ∀ a ∈ row, a.magnitude.length≤W) :
    (dot row bits).clock≤row.length*(50*(W+row.length+1))+4 := by
  induction row generalizing bits with
  | nil => simp [dot]
  | cons a as ih =>
    cases bits with
    | nil => simp [dot]
    | cons b bs =>
      have ha := hrow a List.mem_cons_self
      have htail := fun a h => hrow a (List.mem_cons_of_mem _ h)
      have hc := ih bs htail
      have hw := dot_width as bs W htail
      have hl := load_cost a
      have hlw : (load a).word.magnitude.length≤W+as.length := by rw [load_width]; omega
      have hs := (addSignedBits_cost_width hlw hw).1
      cases b <;> simp only [dot,Bool.false_eq_true,reduceIte,List.length_cons] <;> nlinarith

/-- Compare signed values by actual subtraction and full zero scan, including
opposite signed zero representations. -/
def equal (a b : SignedWord) : TestReport :=
  let difference := subSignedBits a b
  let scan := nonzeroBits difference.word.magnitude
  ⟨!scan.nonzero,difference.clock+scan.clock+3⟩

theorem equal_correct (a b : SignedWord) : (equal a b).accepted=true ↔ a.value=b.value := by
  simp only [equal,Bool.not_eq,Bool.not_eq_true,nonzeroBits_false_iff]
  rw [← signedWord_natAbs,Int.natAbs_eq_zero,subSignedBits_value,sub_eq_zero]

theorem equal_cost (a b : SignedWord) (W : ℕ)
    (ha : a.magnitude.length≤W) (hb : b.magnitude.length≤W) :
    (equal a b).work≤50*(W+2) := by
  have hs := subSignedBits_cost_width ha hb
  have hz := nonzeroBits_cost (subSignedBits a b).word.magnitude
  dsimp only [equal]
  omega

/-- Test all acquired measurement rows against their acquired signed targets.
Both the current dot and the sole recursive suffix are retained exactly once. -/
def test : List (List SignedWord × SignedWord) → List Bool → TestReport
  | [], _ => ⟨true,4⟩
  | pair::rest, bits =>
      let suffix := test rest bits
      let value := dot pair.1 bits
      let target := load pair.2
      let matched := equal value.word target.word
      ⟨matched.accepted && suffix.accepted,
        suffix.work+value.clock+target.clock+matched.work+5⟩

/-- Exact measurement equality on physical data; no integer comparison occurs
in the runtime definition. -/
theorem test_correct (pairs : List (List SignedWord × SignedWord)) (bits : List Bool) :
    (test pairs bits).accepted=true ↔ ∀ pair ∈ pairs, dotValue pair.1 bits=pair.2.value := by
  induction pairs with
  | nil => simp [test]
  | cons pair rest ih =>
    simp only [test,Bool.and_eq_true,equal_correct,dot_value,load_value,ih,
      List.forall_mem_cons]

/-- All physical measurement tests are charged, including target copies and
zero scans. The acquired matrix and targets remain explicit inputs. -/
theorem test_cost (pairs : List (List SignedWord × SignedWord)) (bits : List Bool)
    (n W : ℕ)
    (hp : ∀ pair ∈ pairs, pair.1.length≤n ∧
      (∀ a ∈ pair.1, a.magnitude.length≤W) ∧ pair.2.magnitude.length≤W+n) :
    (test pairs bits).work≤
      pairs.length*(n*(50*(W+n+1))+60*(W+n+2)+9)+4 := by
  induction pairs with
  | nil => simp [test]
  | cons pair rest ih =>
    have hh := hp pair List.mem_cons_self
    have ht := ih (fun p h => hp p (List.mem_cons_of_mem _ h))
    have hd := dot_cost pair.1 bits W hh.2.1
    have hw := dot_width pair.1 bits W hh.2.1
    have hl := load_cost pair.2
    have hlw : (load pair.2).word.magnitude.length≤W+n := by rw [load_width]; exact hh.2.2
    have he := equal_cost (dot pair.1 bits).word (load pair.2).word (W+n) (by omega) hlw
    have hdot : pair.1.length*(50*(W+pair.1.length+1))≤n*(50*(W+n+1)) := by
      gcongr
      all_goals exact hh.1
    simp only [test,List.length_cons]
    nlinarith

/-- Explicit finite rows have the same dot value as the original indexed
measurement interpreter. -/
theorem dotValue_ofFn (n : ℕ) (row : Fin n → SignedWord) (bits : Fin n → Bool) :
    dotValue (List.ofFn row) (List.ofFn bits)=
      SemiprimeRepresentativeExecution.dotBits n (fun i => (row i).value) bits := by
  induction n with
  | zero => simp [dotValue,SemiprimeRepresentativeExecution.dotBits]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    simp only [dotValue,SemiprimeRepresentativeExecution.dotBits,ih]

/-- Cached finite matrices are supplied as physical words; this adapter lists
the requested coordinates. Matrix/target acquisition is not an oracle result. -/
def indexedTest (n m : ℕ) (rows : Fin m → Fin n → SignedWord)
    (targets : Fin m → SignedWord) (bits : Fin n → Bool) : TestReport :=
  test (List.ofFn (fun j => (List.ofFn (rows j),targets j))) (List.ofFn bits)

/-- The bit-backed test has exactly the same acceptance condition as the old
integer measurement test, including all padded and signed-zero inputs. -/
theorem indexedTest_correct (n m : ℕ) (rows : Fin m → Fin n → SignedWord)
    (targets : Fin m → SignedWord) (bits : Fin n → Bool) :
    (indexedTest n m rows targets bits).accepted=true ↔
      ∀ j, (∑ i, if bits i then (rows j i).value else 0)=(targets j).value := by
  rw [indexedTest,test_correct]
  simp only [List.forall_mem_ofFn_iff,dotValue_ofFn,SemiprimeRepresentativeExecution.dotBits_value]

/-- Pointwise acceptance equality permits replacement in the old native
representative interface without changing which word is selected. -/
theorem indexedTest_accepted (n m : ℕ) (rows : Fin m → Fin n → SignedWord)
    (targets : Fin m → SignedWord) (bits : Fin n → Bool) :
    (indexedTest n m rows targets bits).accepted=
      (measurementTest n m (fun j i => (rows j i).value) (fun j => (targets j).value) bits).accepted := by
  apply Bool.eq_iff_iff.mpr
  rw [indexedTest_correct,measurementTest_correct]

/-- The bit-arithmetic leaf cost on a concrete finite matrix. Listing and
addressing supplied matrix callbacks is outside this arithmetic leaf ledger. -/
theorem indexedTest_cost (n m W : ℕ) (rows : Fin m → Fin n → SignedWord)
    (targets : Fin m → SignedWord) (bits : Fin n → Bool)
    (hrows : ∀ j i, (rows j i).magnitude.length≤W)
    (htargets : ∀ j, (targets j).magnitude.length≤W+n) :
    (indexedTest n m rows targets bits).work≤
      m*(n*(50*(W+n+1))+60*(W+n+2)+9)+4 := by
  have hp : ∀ pair ∈ List.ofFn (fun j => (List.ofFn (rows j),targets j)),
      pair.1.length≤n ∧ (∀ a ∈ pair.1, a.magnitude.length≤W) ∧ pair.2.magnitude.length≤W+n := by
    rw [List.forall_mem_ofFn_iff]
    intro j
    refine ⟨by simp,?_,htargets j⟩
    rw [List.forall_mem_ofFn_iff]
    exact hrows j
  simpa only [indexedTest,List.length_ofFn] using
    test_cost (List.ofFn (fun j => (List.ofFn (rows j),targets j))) (List.ofFn bits) n W hp

/-- False-first search depends on the acceptance flags, not the cost reports. -/
theorem findBits_found_congr (n : ℕ) (f g : (Fin n → Bool) → TestReport)
    (h : ∀ bits, (f bits).accepted=(g bits).accepted) :
    (findBits n f).found=(findBits n g).found := by
  induction n with
  | zero => simp only [findBits,h]
  | succ n ih =>
    have hl := ih (fun x => f (Fin.cons false x)) (fun x => g (Fin.cons false x)) (fun x => h _)
    have hr := ih (fun x => f (Fin.cons true x)) (fun x => g (Fin.cons true x)) (fun x => h _)
    simp only [findBits]
    rw [hl]
    split <;> simp only [hr]

/-- The fixed matrix can now be searched using actual signed-word leaf tests. -/
def representative (n m : ℕ) (rows : Fin m → Fin n → SignedWord)
    (targets : Fin m → SignedWord) : SearchReport n :=
  findBits n (indexedTest n m rows targets)

/-- Every returned representative solves the actual original measurements. -/
theorem representative_sound (n m : ℕ) (rows : Fin m → Fin n → SignedWord)
    (targets : Fin m → SignedWord) (bits : Fin n → Bool)
    (h : (representative n m rows targets).found=some bits) :
    ∀ j, (∑ i, if bits i then (rows j i).value else 0)=(targets j).value :=
  (indexedTest_correct n m rows targets bits).mp (findBits_sound n _ bits h)

/-- The physical tests choose the same actual representative as the previous
integer implementation, so the existing native packet semantics are reusable. -/
theorem representative_found (n m : ℕ) (rows : Fin m → Fin n → SignedWord)
    (targets : Fin m → SignedWord) :
    (representative n m rows targets).found=
      (measuredRepresentative n m (fun j i => (rows j i).value)
        (fun j => (targets j).value)).found :=
  findBits_found_congr n _ _ (indexedTest_accepted n m rows targets)

/-- Every visited measurement leaf is charged at physical bit cost. The native
search-control ledger is retained; its concrete closure/index implementation
and acquisition of the input matrix/target words remain separate. -/
theorem representative_work (n m W : ℕ) (rows : Fin m → Fin n → SignedWord)
    (targets : Fin m → SignedWord)
    (hrows : ∀ j i, (rows j i).magnitude.length≤W)
    (htargets : ∀ j, (targets j).magnitude.length≤W+n) :
    (representative n m rows targets).work+1≤
      2^n*(m*(n*(50*(W+n+1))+60*(W+n+2)+9)+6) :=
  findBits_work n (m*(n*(50*(W+n+1))+60*(W+n+2)+9)+4) _
    (fun bits => indexedTest_cost n m W rows targets bits hrows htargets)

end RiemannGaussian.SemiprimeMeasurementBits
