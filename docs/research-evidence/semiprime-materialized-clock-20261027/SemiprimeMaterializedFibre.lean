/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePacketArrayExecution
import RiemannGaussian.SemiprimeNativeGroupExecution

/-!
# Materialized Boolean head words and integer measurements

The tables below contain every LOCAL word, not every global assignment.
Measurements are acquired once into concrete arrays. Representatives ignore
forced bits; only the subsequent local fibre sums apply those bits.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeMaterializedFibre
open scoped BigOperators
open Polynomial SemiprimeRepresentativeExecution SemiprimeFibreArrayExecution
open SemiprimePacketArrayExecution

/-- Executable binary mixed-radix coding of one head's Boolean words. -/
def wordCode (n : ℕ) : Fin (2^n) ≃ (Fin n → Bool) :=
  (finCongr (by simp : 2^n = ∏ _i : Fin n, (2 : ℕ))).trans
    ((SemiprimeMixedRadix.decode n (fun _ => 2)).trans
      (Equiv.piCongrRight (fun _ => finTwoEquiv)))

/-- One actually stored local word and its acquired integer measurements. -/
structure Entry where
  /-- Boolean coordinates in their original head order. -/
  word : Array Bool
  /-- Literal integer row dot products. -/
  measured : Array ℤ
  deriving Inhabited

/-- A homogeneous cache permits dependent head sizes without polynomial indices. -/
structure HeadCache where
  /-- All local words, with their measurements. -/
  entries : Array Entry
  /-- Selected integer arithmetic, reads, allocation and traversal charges. -/
  work : ℕ
  deriving Inhabited

/-- Materialize every local word and every actual dot product exactly once. -/
def acquireHead (n m : ℕ) (rows : Fin m → Fin n → ℤ) : HeadCache :=
  let entries := Array.ofFn (fun code : Fin (2^n) =>
    let bits := Array.ofFn (wordCode n code)
    let dots := Array.ofFn (fun j : Fin m => dotRun n (rows j) (fun i => bits[i.val]!))
    ⟨bits,dots.map (fun d => d.value)⟩)
  ⟨entries,2^n*(n+m*(4*n+2)+3)⟩

/-- Exactly 2^n LOCAL records are allocated by acquisition. -/
theorem acquireHead_size (n m : ℕ) (rows : Fin m → Fin n → ℤ) :
    (acquireHead n m rows).entries.size = 2^n := by
  simp [acquireHead]

/-- Every allocated record stores n Boolean coordinates and m measurements. -/
theorem acquireHead_entry_sizes (n m : ℕ) (rows : Fin m → Fin n → ℤ)
    (code : Fin (2^n)) :
    ((acquireHead n m rows).entries[code.val]!.word.size = n) ∧
      ((acquireHead n m rows).entries[code.val]!.measured.size = m) := by
  simp [acquireHead]

/-- Read an acquired word by its explicit code. -/
def cachedWord (n : ℕ) (cache : HeadCache) (code : Fin (2^n)) : Fin n → Bool :=
  fun i => cache.entries[code.val]!.word[i.val]!

/-- Read one acquired measurement; there is no dot-product callback here. -/
def cachedMeasurement (cache : HeadCache) (code j : ℕ) : ℤ :=
  cache.entries[code]!.measured[j]!

/-- The stored word is the actual executable code's word. -/
theorem acquireHead_word (n m : ℕ) (rows : Fin m → Fin n → ℤ) (code : Fin (2^n)) :
    cachedWord n (acquireHead n m rows) code = wordCode n code := by
  funext i
  simp [cachedWord,acquireHead]

/-- Every stored measurement is the literal integer measurement of its word. -/
theorem acquireHead_measurement (n m : ℕ) (rows : Fin m → Fin n → ℤ)
    (code : Fin (2^n)) (j : Fin m) :
    cachedMeasurement (acquireHead n m rows) code.val j.val =
      ∑ i, if wordCode n code i then rows j i else 0 := by
  simp [cachedMeasurement,acquireHead,dotRun_value,dotBits_value]

/-- Cached measurement comparisons, including their finite scan charge. -/
def cachedTest (n m : ℕ) (cache : HeadCache) (target : Fin m → ℤ)
    (bits : Fin n → Bool) : TestReport :=
  ⟨decide (∀ j : Fin m,
    cachedMeasurement cache ((wordCode n).symm bits).val j.val = target j),2*m+1⟩

/-- The cached test has exactly the original measurement semantics. -/
theorem cachedTest_correct (n m : ℕ) (rows : Fin m → Fin n → ℤ)
    (target : Fin m → ℤ) (bits : Fin n → Bool) :
    (cachedTest n m (acquireHead n m rows) target bits).accepted = true ↔
      ∀ j, (∑ i, if bits i then rows j i else 0) = target j := by
  simp [cachedTest,acquireHead_measurement]

/-- Search output depends on accepted bits, not the accounting field. -/
theorem findBits_found_congr (n : ℕ) (a b : (Fin n → Bool) → TestReport)
    (hab : ∀ x, (a x).accepted = (b x).accepted) :
    (findBits n a).found = (findBits n b).found := by
  induction n with
  | zero => simp only [findBits,hab]
  | succ n ih =>
    have hl := ih (fun x => a (Fin.cons false x)) (fun x => b (Fin.cons false x)) (fun x => hab _)
    have hr := ih (fun x => a (Fin.cons true x)) (fun x => b (Fin.cons true x)) (fun x => hab _)
    simp only [findBits,hl,hr]
    cases (findBits n (fun x => b (Fin.cons false x))).found <;> rfl

/-- The unforced representative is found using only cached measurements. -/
def cachedRepresentative (n m : ℕ) (cache : HeadCache) (target : Fin m → ℤ) : Fin n → Bool :=
  representative n (cachedTest n m cache target)

/-- Cached and original searches select the SAME false-first representative. -/
theorem cachedRepresentative_eq (n m : ℕ) (rows : Fin m → Fin n → ℤ)
    (target : Fin m → ℤ) :
    cachedRepresentative n m (acquireHead n m rows) target =
      representative n (measurementTest n m rows target) := by
  unfold cachedRepresentative representative
  congr 1
  apply findBits_found_congr
  intro bits
  apply Bool.eq_iff_iff.mpr
  exact (cachedTest_correct n m rows target bits).trans
    (measurementTest_correct n m rows target bits).symm

/-- Cached measurement and actual forced-bit tests; no rejected value is called. -/
def cachedFibreTest (n m : ℕ) (cache : HeadCache) (target : Fin m → ℤ)
    (forced : Fin n → Bool) (code : Fin (2^n)) : TestReport :=
  let bits := cachedWord n cache code
  let measured := cachedTest n m cache target bits
  let fixed := forcedTest n forced bits
  ⟨measured.accepted && fixed.accepted,measured.work+fixed.work+1⟩

/-- Acquire a local fibre by scanning the actual cached words. -/
def scanHead (J n m : ℕ) (cache : HeadCache) (target : Fin m → ℤ)
    (forced : Fin n → Bool) (value : (Fin n → Bool) → Run) : Run :=
  sumCodes J (2^n) (fun code => gateRun J (cachedFibreTest n m cache target forced code)
    (fun _ => value (cachedWord n cache code)))

/-- The materialized scan equals the original exact local fibre sum. -/
theorem scanHead_spec (J n m : ℕ) (rows : Fin m → Fin n → ℤ) (target : Fin m → ℤ)
    (forced : Fin n → Bool) (value : (Fin n → Bool) → Run)
    (P : (Fin n → Bool) → Polynomial ℚ) (hv : ∀ bits, Spec J (value bits) (P bits)) :
    Spec J (scanHead J n m (acquireHead n m rows) target forced value)
      (∑ bits, if (∀ j, (∑ i, if bits i then rows j i else 0) = target j) ∧
        (∀ i, forced i = true → bits i = true) then P bits else 0) := by
  classical
  rw [← (wordCode n).sum_comp]
  apply sumCodes_spec
  intro code
  have h := gateRun_spec J (cachedFibreTest n m (acquireHead n m rows) target forced code)
    (fun _ => value (cachedWord n (acquireHead n m rows) code))
    (P (cachedWord n (acquireHead n m rows) code)) (hv _)
  have ht : (cachedFibreTest n m (acquireHead n m rows) target forced code).accepted = true ↔
      (∀ j, (∑ i, if wordCode n code i then rows j i else 0) = target j) ∧
        (∀ i, forced i = true → wordCode n code i = true) := by
    simp only [cachedFibreTest,Bool.and_eq_true,acquireHead_word,
      cachedTest_correct,forcedTest_correct]
  simpa only [acquireHead_word,ht] using h

/-- Every local value call and array operation is retained in this work bound. -/
theorem scanHead_work (J n m B : ℕ) (cache : HeadCache) (target : Fin m → ℤ)
    (forced : Fin n → Bool) (value : (Fin n → Bool) → Run)
    (hv : ∀ bits, (value bits).work ≤ B) :
    (scanHead J n m cache target forced value).work ≤
      (J+1)+2^n*(B+2*m+4*n+5*J+6) := by
  have hg (code : Fin (2^n)) :
      (gateRun J (cachedFibreTest n m cache target forced code)
        (fun _ => value (cachedWord n cache code))).work ≤ B+2*m+4*n+J+5 := by
    have h := gateRun_work J B (cachedFibreTest n m cache target forced code)
      (fun _ => value (cachedWord n cache code)) (hv _)
    simp only [cachedFibreTest,cachedTest,forcedTest_work] at h ⊢
    omega
  have hs := sumCodes_work J (2^n) (B+2*m+4*n+J+5) _ hg
  unfold scanHead
  convert hs using 1; ring

end RiemannGaussian.SemiprimeMaterializedFibre
