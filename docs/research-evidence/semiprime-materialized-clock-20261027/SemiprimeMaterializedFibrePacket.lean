/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedFibre
import RiemannGaussian.SemiprimeIndexedFibrePacket

/-!
# Complete cached-head fibre acquisition

Only each head's words are enumerated. The full paid summary box is permitted;
empty fibres contribute zero. Tables are materialized before this box is scanned.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedFibrePacket
open scoped BigOperators
open Polynomial SemiprimeRepresentativeExecution SemiprimeFibreArrayExecution
open SemiprimePacketArrayExecution SemiprimeMaterializedFibre

/-- Acquire all heads in one homogeneous array; there is no global-word table. -/
def acquireHeads (r : ℕ) (h m : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ) : Array HeadCache :=
  Array.ofFn (fun g => acquireHead (h g) (m g) (rows g))

/-- Literal read of an already acquired head. -/
def headAt (caches : Array HeadCache) (g : ℕ) : HeadCache := caches[g]!

/-- Accessing the materialized collection does not reacquire its measurements. -/
theorem headAt_acquireHeads (r : ℕ) (h m : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ) (g : Fin r) :
    headAt (acquireHeads r h m rows) g.val = acquireHead (h g) (m g) (rows g) := by
  simp [headAt,acquireHeads]

/-- All-head acquisition charges are read from the actual stored reports. -/
def acquisitionWork (r : ℕ) (caches : Array HeadCache) : ℕ :=
  (∑ g : Fin r, (headAt caches g.val).work)+r+1

/-- One-time acquisition has a sum, rather than product, of local word counts. -/
theorem acquisitionWork_le (r H M : ℕ) (h m : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (hh : ∀ g, h g ≤ H) (hm : ∀ g, m g ≤ M) :
    acquisitionWork r (acquireHeads r h m rows) ≤ r*(2^H*(H+M*(4*H+2)+3))+r+1 := by
  unfold acquisitionWork
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _g : Fin r, 2^H*(H+M*(4*H+2)+3) := by
      apply Finset.sum_le_sum
      intro g _
      simp only [headAt_acquireHeads,acquireHead]
      gcongr
      · exact hh g
      · exact hh g
      · exact hm g
      · exact hh g
    _ = _ := by simp

/-- Stored representative and its actual cached-search report charge. -/
structure RepresentativeEntry where
  /-- Materialized unforced representative coordinates. -/
  word : Array Bool
  /-- Search work, coordinate allocation, and one branch. -/
  work : ℕ
  deriving Inhabited

/-- Run a single unforced cached search and store its word once. -/
def acquireRepresentative (n m : ℕ) (cache : HeadCache) (target : Fin m → ℤ) : RepresentativeEntry :=
  let report := findBits n (cachedTest n m cache target)
  ⟨Array.ofFn (report.found.getD (fun _ => false)),report.work+n+1⟩

/-- Read the acquired representative's coordinates. -/
def representativeBits (n : ℕ) (rep : RepresentativeEntry) : Fin n → Bool :=
  fun i => rep.word[i.val]!

/-- A representative entry has exactly the already proved search semantics. -/
theorem acquireRepresentative_bits (n m : ℕ) (cache : HeadCache) (target : Fin m → ℤ) :
    representativeBits n (acquireRepresentative n m cache target) =
      cachedRepresentative n m cache target := by
  funext i
  simp [representativeBits,acquireRepresentative,cachedRepresentative,representative]

/-- Actual cached-search work, including the successful representative allocation. -/
theorem acquireRepresentative_work (n m : ℕ) (cache : HeadCache) (target : Fin m → ℤ) :
    (acquireRepresentative n m cache target).work ≤ 2^n*(2*m+3)+n+1 := by
  have hf := findBits_work n (2*m+1) (cachedTest n m cache target) (by intro x; exact Nat.le_refl _)
  have he : 2*m+1+2 = 2*m+3 := by omega
  rw [he] at hf
  simp only [acquireRepresentative]
  omega

/-- For one summary tuple, all unforced representatives are genuinely cached. -/
def acquireReps (r : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g)) :
    Array RepresentativeEntry :=
  Array.ofFn (fun g => acquireRepresentative (h g) (m g) (headAt caches g.val)
    (summaryTarget (h g) (m g) (W g) (y g)))

/-- Read the cached representatives without recreating any search. -/
def repsBits (r : ℕ) (h : Fin r → ℕ) (reps : Array RepresentativeEntry) :
    (g : Fin r) → Fin (h g) → Bool :=
  fun g => representativeBits (h g) reps[g.val]!

/-- Stored representative charges are counted once for this summary tuple. -/
def repsWork (r : ℕ) (reps : Array RepresentativeEntry) : ℕ :=
  (∑ g : Fin r, reps[g.val]!.work)+r+1

/-- Cached representative families coincide with the existing native family. -/
theorem acquireReps_bits (r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g)) :
    repsBits r h (acquireReps r h m W (acquireHeads r h m rows) y) =
      fun g => summaryRepresentative (h g) (m g) (W g) (rows g) (y g) := by
  funext g
  simp [repsBits,acquireReps,headAt_acquireHeads,acquireRepresentative_bits,
    cachedRepresentative_eq,summaryRepresentative]

/-- The exact separated native fibre polynomial for one summary tuple. -/
noncomputable def fibrePolynomial (r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (P : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Polynomial ℚ) : Polynomial ℚ :=
  ∏ g, ∑ bits, if (∀ j, (∑ i, if bits i then rows g j i else 0) =
      summaryTarget (h g) (m g) (W g) (y g) j) ∧
        (∀ i, forced g i = true → bits i = true)
    then P g (Function.update
      (fun k => summaryRepresentative (h k) (m k) (W k) (rows k) (y k)) g bits) else 0

/-- Complete one-summary algorithm: unforced cached representatives, forced local
sums, then the product of those sums. No product of local assignment spaces. -/
def fibreCached (J r : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run) : Run :=
  let reps := acquireReps r h m W caches y
  let result := productList J (List.ofFn (fun g : Fin r => g)) (fun g =>
    scanHead J (h g) (m g) (headAt caches g.val)
      (summaryTarget (h g) (m g) (W g) (y g)) (forced g)
      (fun bits => value g (Function.update (repsBits r h reps) g bits)))
  bump result (repsWork r reps)

/-- Exact equivalence with the existing separated fibre expression. -/
theorem fibreCached_spec (J r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run)
    (P : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Polynomial ℚ)
    (hv : ∀ g x, Spec J (value g x) (P g x)) :
    Spec J (fibreCached J r h m W (acquireHeads r h m rows) y forced value)
      (fibrePolynomial r h m W rows y forced P) := by
  classical
  unfold fibreCached
  apply bump_spec
  have hs := productList_spec J (List.ofFn (fun g : Fin r => g)) _ _ (fun g _ =>
    scanHead_spec J (h g) (m g) (rows g) (summaryTarget (h g) (m g) (W g) (y g)) (forced g)
      (fun bits => value g (Function.update
        (repsBits r h (acquireReps r h m W (acquireHeads r h m rows) y)) g bits))
      (fun bits => P g (Function.update
        (repsBits r h (acquireReps r h m W (acquireHeads r h m rows) y)) g bits))
      (fun _ => hv g _))
  simpa only [headAt_acquireHeads,List.map_ofFn,List.prod_ofFn,Function.comp_apply,
    acquireReps_bits,fibrePolynomial] using hs

/-- Coefficient-level equality to the already verified nonmaterialized traversal. -/
theorem fibreCached_coefficient_eq (J r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run)
    (P : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Polynomial ℚ)
    (hv : ∀ g x, Spec J (value g x) (P g x)) (i : ℕ) (hi : i < J) :
    SemiprimeJetArray.coefficient
        (fibreCached J r h m W (acquireHeads r h m rows) y forced value).jet.coefficients i =
      SemiprimeJetArray.coefficient (fibreAt J r h m W rows y forced value).jet.coefficients i :=
  (fibreCached_spec J r h m W rows y forced value P hv i hi).trans
    (fibreAt_spec J r h m W rows y forced value P hv i hi).symm

/-- Visit the full paid summary box using an already materialized collection. -/
def sumCached (J r : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run) : Run :=
  sumCodes J (summaryCount r h m W) (fun code =>
    fibreCached J r h m W caches (summaryCode r h m W code) forced value)

/-- The cached full-box traversal equals the native finite packet sum. -/
theorem sumCached_spec (J r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run)
    (P : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Polynomial ℚ)
    (hv : ∀ g x, Spec J (value g x) (P g x)) :
    Spec J (sumCached J r h m W (acquireHeads r h m rows) forced value)
      (∑ y, fibrePolynomial r h m W rows y forced P) := by
  classical
  rw [← (summaryCode r h m W).sum_comp]
  exact sumCodes_spec J _ _ _ (fun code => fibreCached_spec J r h m W rows _ forced value P hv)

/-- Acquire all head tables ONCE, then visit the full paid summary box. -/
def acquireFibre (J r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run) : Run :=
  let caches := acquireHeads r h m rows
  bump (sumCached J r h m W caches forced value) (acquisitionWork r caches)

/-- The full materialized fibre traversal is the native finite packet sum. -/
theorem acquireFibre_spec (J r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run)
    (P : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Polynomial ℚ)
    (hv : ∀ g x, Spec J (value g x) (P g x)) :
    Spec J (acquireFibre J r h m W rows forced value)
      (∑ y, fibrePolynomial r h m W rows y forced P) :=
  bump_spec J _ _ _ (sumCached_spec J r h m W rows forced value P hv)

/-- Polynomial-in-dimensions factor multiplying a single local word count. -/
def oneSummaryBudget (J r H M B : ℕ) : ℕ :=
  r*((J+1)+2^H*(B+2*M+4*H+5*J+6)+(2*J*(J+1)+J+1))+(J+1)+
    r*(2^H*(2*M+3)+H+1)+r+1

/-- Every representative scan is local and its cached allocation is included. -/
theorem repsWork_le (r H M : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (hh : ∀ g, h g ≤ H) (hm : ∀ g, m g ≤ M) :
    repsWork r (acquireReps r h m W caches y) ≤ r*(2^H*(2*M+3)+H+1)+r+1 := by
  unfold repsWork
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _g : Fin r, (2^H*(2*M+3)+H+1) := by
      apply Finset.sum_le_sum
      intro g _
      simpa [acquireReps] using
        (acquireRepresentative_work (h g) (m g) (headAt caches g.val)
          (summaryTarget (h g) (m g) (W g) (y g))).trans (by gcongr; exact hh g; exact hm g; exact hh g)
    _ = _ := by simp

/-- All value acquisition work is charged, separately for each head word. -/
theorem fibreCached_work (J r H M B : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run)
    (hh : ∀ g, h g ≤ H) (hm : ∀ g, m g ≤ M) (hv : ∀ g x, (value g x).work ≤ B) :
    (fibreCached J r h m W caches y forced value).work ≤ oneSummaryBudget J r H M B := by
  have hscan (g : Fin r) :
      (scanHead J (h g) (m g) (headAt caches g.val)
        (summaryTarget (h g) (m g) (W g) (y g)) (forced g)
        (fun bits => value g (Function.update (repsBits r h (acquireReps r h m W caches y)) g bits))).work ≤
          (J+1)+2^H*(B+2*M+4*H+5*J+6) := by
    apply (scanHead_work J (h g) (m g) B _ _ _ _ (fun _ => hv g _)).trans
    gcongr
    · exact hh g
    · exact hm g
    · exact hh g
  have hp := productList_work J ((J+1)+2^H*(B+2*M+4*H+5*J+6))
    (List.ofFn (fun g : Fin r => g)) _ (fun g _ => hscan g)
  simp only [List.length_ofFn] at hp
  have hr := repsWork_le r H M h m W caches y hh hm
  unfold fibreCached
  rw [bump_work]
  exact (Nat.add_le_add hp hr).trans_eq (by unfold oneSummaryBudget; ring)

/-- The complete box traversal costs Y local scans, never 2^(sum head sizes). -/
theorem sumCached_work (J r H M B : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → Run)
    (hh : ∀ g, h g ≤ H) (hm : ∀ g, m g ≤ M) (hv : ∀ g x, (value g x).work ≤ B) :
    (sumCached J r h m W caches forced value).work ≤
      (J+1)+summaryCount r h m W*(oneSummaryBudget J r H M B+(4*J+1)) :=
  sumCodes_work J _ _ _ (fun _ => fibreCached_work J r H M B h m W caches _ forced value hh hm hv)

end RiemannGaussian.SemiprimeMaterializedFibrePacket
