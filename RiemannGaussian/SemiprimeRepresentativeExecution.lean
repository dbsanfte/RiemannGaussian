/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterCompose
import RiemannGaussian.SemiprimeLayoutCertificates

/-!
# Executed search for a shared-summary representative

The binary traversal keeps a single found Boolean word and charges every actual
measurement callback. No table of all Boolean words or chosen representative
is an input. Its interpretation in a node certificate is proved separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeRepresentativeExecution
open scoped BigOperators

/-- A computed Boolean gate and its charged local work. -/
structure TestReport where
  /-- The actual comparison result. -/
  accepted : Bool
  /-- Arithmetic, reads and control operations of this test. -/
  work : ℕ

/-- Search output with the work of every visited test and branch. -/
structure SearchReport (n : ℕ) where
  /-- One successful assignment, or no successful assignment. -/
  found : Option (Fin n → Bool)
  /-- Callback work plus traversal control charges. -/
  work : ℕ
  /-- Number of actual leaf tests. -/
  tests : ℕ

/-- False-first depth-first search, stopping after its first successful leaf. -/
def findBits : (n : ℕ) → ((Fin n → Bool) → TestReport) → SearchReport n
  | 0, test =>
      let result := test Fin.elim0
      ⟨if result.accepted then some Fin.elim0 else none, result.work+1, 1⟩
  | n+1, test =>
      let left := findBits n (fun x => test (Fin.cons false x))
      match left.found with
      | some x => ⟨some (Fin.cons false x),left.work+1,left.tests⟩
      | none =>
          let right := findBits n (fun x => test (Fin.cons true x))
          ⟨right.found.map (Fin.cons true),left.work+right.work+1,left.tests+right.tests⟩

/-- Every returned word actually passed its supplied computed test. -/
theorem findBits_sound (n : ℕ) (test : (Fin n → Bool) → TestReport)
    (x : Fin n → Bool) (h : (findBits n test).found = some x) :
    (test x).accepted = true := by
  induction n with
  | zero =>
    have hx : x = Fin.elim0 := by funext i; exact Fin.elim0 i
    subst x
    cases ht : (test Fin.elim0).accepted <;> simp [findBits,ht] at h ⊢
  | succ n ih =>
    simp only [findBits] at h
    split at h
    · rename_i a ha
      have hx := Option.some.inj h
      subst x
      exact ih _ a ha
    · rename_i ha
      obtain ⟨a, ha', hx⟩ := Option.map_eq_some_iff.mp h
      subst x
      exact ih _ a ha'

/-- Failure is equivalent to failure of every Boolean assignment, not a search cap. -/
theorem findBits_none_iff (n : ℕ) (test : (Fin n → Bool) → TestReport) :
    (findBits n test).found = none ↔ ∀ x, (test x).accepted = false := by
  induction n with
  | zero =>
    have hx (x : Fin 0 → Bool) : x = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [findBits, hx]
  | succ n ih =>
    have hcons (x : Fin (n+1) → Bool) : Fin.cons (x 0) (fun i => x i.succ) = x := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    simp only [findBits]
    split
    · rename_i a ha
      constructor
      · intro h; cases h
      · intro h
        have ht := findBits_sound n (fun x => test (Fin.cons false x)) a ha
        rw [h (Fin.cons false a)] at ht
        cases ht
    · rename_i ha
      rw [Option.map_eq_none_iff, ih]
      have hf := (ih (fun x => test (Fin.cons false x))).mp ha
      constructor
      · intro ht x
        rw [← hcons x]
        cases h : x 0
        · exact hf _
        · exact ht _
      · intro h x
        exact h _

/-- Every tested word is paid; both branches together visit at most 2^n leaves. -/
theorem findBits_tests (n : ℕ) (test : (Fin n → Bool) → TestReport) :
    (findBits n test).tests ≤ 2^n := by
  induction n with
  | zero => simp [findBits]
  | succ n ih =>
    simp only [findBits]
    split
    · have hl := ih (fun x => test (Fin.cons false x))
      dsimp only
      rw [pow_succ]
      omega
    · have hl := ih (fun x => test (Fin.cons false x))
      have hr := ih (fun x => test (Fin.cons true x))
      dsimp only
      rw [pow_succ]
      omega

/-- The same actual search includes all supplied callback costs and tree control. -/
theorem findBits_work (n B : ℕ) (test : (Fin n → Bool) → TestReport)
    (h : ∀ x, (test x).work ≤ B) :
    (findBits n test).work + 1 ≤ 2^n * (B+2) := by
  induction n with
  | zero => simpa only [findBits, pow_zero, one_mul] using Nat.add_le_add_right (h Fin.elim0) 2
  | succ n ih =>
    have hl := ih (fun x => test (Fin.cons false x)) (fun x => h _)
    have hr := ih (fun x => test (Fin.cons true x)) (fun x => h _)
    simp only [findBits]
    split
    · rw [pow_succ]
      have hp : 0 < 2^n * (B+2) := by positivity
      nlinarith
    · rw [pow_succ]
      nlinarith

/-- Actual representative word; an empty fibre receives the literal false word. -/
def representative (n : ℕ) (test : (Fin n → Bool) → TestReport) : Fin n → Bool :=
  (findBits n test).found.getD (fun _ => false)

/-- A nonempty fibre always receives a computed successful representative. -/
theorem representative_valid (n : ℕ) (test : (Fin n → Bool) → TestReport)
    (h : ∃ x, (test x).accepted = true) :
    (test (representative n test)).accepted = true := by
  cases he : (findBits n test).found with
  | none =>
    obtain ⟨x,hx⟩ := h
    have hf := (findBits_none_iff n test).mp he x
    rw [hf] at hx
    cases hx
  | some x =>
    simpa only [representative,he,Option.getD_some] using findBits_sound n test x he

/-- Integer dot product of one measurement row with a Boolean word. -/
def dotBits : (n : ℕ) → (Fin n → ℤ) → (Fin n → Bool) → ℤ
  | 0, _, _ => 0
  | n+1, row, bits =>
      (if bits 0 then row 0 else 0) + dotBits n (fun i => row i.succ) (fun i => bits i.succ)

theorem dotBits_value (n : ℕ) (row : Fin n → ℤ) (bits : Fin n → Bool) :
    dotBits n row bits = ∑ i, if bits i then row i else 0 := by
  induction n with
  | zero => simp [dotBits]
  | succ n ih => rw [dotBits, Fin.sum_univ_succ, ih]

/-- The actual integer scalar and its charged reads, branch and addition. -/
structure DotReport where
  /-- Computed integer dot product. -/
  value : ℤ
  /-- Selected integer arithmetic/read charges. -/
  work : ℕ

/-- A dot-product loop with charges attached to its sole recursive call. -/
def dotRun : (n : ℕ) → (Fin n → ℤ) → (Fin n → Bool) → DotReport
  | 0, _, _ => ⟨0,1⟩
  | n+1, row, bits =>
      let tail := dotRun n (fun i => row i.succ) (fun i => bits i.succ)
      ⟨(if bits 0 then row 0 else 0)+tail.value,tail.work+4⟩

theorem dotRun_value (n : ℕ) (row : Fin n → ℤ) (bits : Fin n → Bool) :
    (dotRun n row bits).value = dotBits n row bits := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dotRun,dotBits,ih]

theorem dotRun_work (n : ℕ) (row : Fin n → ℤ) (bits : Fin n → Bool) :
    (dotRun n row bits).work = 4*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dotRun,ih]; omega

/-- Every row test computes its actual integer dot product and target equality. -/
def measurementTest (n : ℕ) : (m : ℕ) → (Fin m → Fin n → ℤ) →
    (Fin m → ℤ) → (Fin n → Bool) → TestReport
  | 0, _, _, _ => ⟨true,1⟩
  | m+1, rows, target, bits =>
      let tail := measurementTest n m (fun i => rows i.succ) (fun i => target i.succ) bits
      let dot := dotRun n (rows 0) bits
      ⟨decide (dot.value = target 0) && tail.accepted,tail.work+dot.work+2⟩

/-- Exact finite measurement equality; there is no supplied correct-test oracle. -/
theorem measurementTest_correct (n m : ℕ) (rows : Fin m → Fin n → ℤ)
    (target : Fin m → ℤ) (bits : Fin n → Bool) :
    (measurementTest n m rows target bits).accepted = true ↔
      ∀ j, (∑ i, if bits i then rows j i else 0) = target j := by
  induction m with
  | zero => simp [measurementTest]
  | succ m ih =>
    simp only [measurementTest,Bool.and_eq_true,decide_eq_true_eq,dotRun_value,dotBits_value,ih]
    constructor
    · rintro ⟨h0,hs⟩ j
      exact Fin.cases h0 hs j
    · intro h
      exact ⟨h 0,fun j => h j.succ⟩

/-- Measurement arithmetic/reads/control is linear in the literal matrix size.
Integer bit arithmetic and physical array lookup costs must still be supplied. -/
theorem measurementTest_work (n m : ℕ) (rows : Fin m → Fin n → ℤ)
    (target : Fin m → ℤ) (bits : Fin n → Bool) :
    (measurementTest n m rows target bits).work = m*(4*n+3)+1 := by
  induction m with
  | zero => simp [measurementTest]
  | succ m ih => simp only [measurementTest,ih,dotRun_work]; ring

/-- Concrete search over the actual integer measurement equations. -/
def measuredRepresentative (n m : ℕ) (rows : Fin m → Fin n → ℤ)
    (target : Fin m → ℤ) : SearchReport n := findBits n (measurementTest n m rows target)

theorem measuredRepresentative_sound (n m : ℕ) (rows : Fin m → Fin n → ℤ)
    (target : Fin m → ℤ) (bits : Fin n → Bool)
    (h : (measuredRepresentative n m rows target).found = some bits) :
    ∀ j, (∑ i, if bits i then rows j i else 0) = target j :=
  (measurementTest_correct n m rows target bits).mp (findBits_sound n _ bits h)

theorem measuredRepresentative_work (n m : ℕ) (rows : Fin m → Fin n → ℤ)
    (target : Fin m → ℤ) :
    (measuredRepresentative n m rows target).work + 1 ≤ 2^n*(m*(4*n+3)+3) :=
  findBits_work n (m*(4*n+3)+1) _ (fun x => (measurementTest_work n m rows target x).le)

/-- Decode a signed summary box using public natural dimensions. -/
def summaryTarget (n m W : ℕ)
    (y : SemiprimeLayoutCertificates.Summary (Fin n) (Fin m) W) : Fin m → ℤ :=
  fun j => (y j).val - (n*W : ℕ)

/-- Actual integer equality tests are exactly the existing node measurement. -/
theorem summaryTest_correct (n m W : ℕ) (rows : Fin m → Fin n → ℤ)
    (hrows : ∀ j i, |rows j i| ≤ (W : ℤ))
    (y : SemiprimeLayoutCertificates.Summary (Fin n) (Fin m) W) (bits : Fin n → Bool) :
    (measurementTest n m rows (summaryTarget n m W y) bits).accepted = true ↔
      SemiprimeLayoutCertificates.measurement rows W hrows bits = y := by
  rw [measurementTest_correct]
  have hs (j : Fin m) : SemiprimeLayoutCertificates.signature rows bits j =
      ∑ i, if bits i then rows j i else 0 := by
    simp only [SemiprimeLayoutCertificates.signature, mul_ite, mul_one, mul_zero]
  have hv (j : Fin m) :
      ((SemiprimeLayoutCertificates.measurement rows W hrows bits j).val : ℤ) =
        (∑ i, if bits i then rows j i else 0) + (n*W : ℕ) := by
    have hb := abs_le.mp (SemiprimeLayoutCertificates.signature_bound rows W hrows bits j)
    simp only [Fintype.card_fin, hs] at hb
    simp only [SemiprimeLayoutCertificates.measurement,Fintype.card_fin,hs]
    omega
  constructor
  · intro h
    funext j
    apply Fin.ext
    have hj := h j
    have he := hv j
    simp only [summaryTarget] at hj
    omega
  · intro h j
    have he := hv j
    rw [h] at he
    simp only [summaryTarget]
    omega

/-- The data path for the representative of an actual bounded integer row system. -/
def summaryRepresentative (n m W : ℕ) (rows : Fin m → Fin n → ℤ)
    (y : SemiprimeLayoutCertificates.Summary (Fin n) (Fin m) W) : Fin n → Bool :=
  representative n (measurementTest n m rows (summaryTarget n m W y))

/-- Native summary representatives are computed by finite scans, not chosen. -/
theorem summaryRepresentative_valid (n m W : ℕ) (rows : Fin m → Fin n → ℤ)
    (hrows : ∀ j i, |rows j i| ≤ (W : ℤ))
    (y : SemiprimeLayoutCertificates.Summary (Fin n) (Fin m) W)
    (hy : ∃ bits, SemiprimeLayoutCertificates.measurement rows W hrows bits = y) :
    SemiprimeLayoutCertificates.measurement rows W hrows
      (summaryRepresentative n m W rows y) = y := by
  apply (summaryTest_correct n m W rows hrows y _).mp
  apply representative_valid
  obtain ⟨bits,hbits⟩ := hy
  exact ⟨bits,(summaryTest_correct n m W rows hrows y bits).mpr hbits⟩

/-- Literal forced-bit conjunction on one local word. -/
def forcedTest : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → TestReport
  | 0, _, _ => ⟨true,1⟩
  | n+1, forced, bits =>
      let tail := forcedTest n (fun i => forced i.succ) (fun i => bits i.succ)
      ⟨(!forced 0 || bits 0) && tail.accepted,tail.work+4⟩

theorem forcedTest_correct (n : ℕ) (forced bits : Fin n → Bool) :
    (forcedTest n forced bits).accepted = true ↔
      ∀ i, forced i = true → bits i = true := by
  induction n with
  | zero => simp [forcedTest]
  | succ n ih =>
    simp only [forcedTest,Bool.and_eq_true,ih]
    have hh : (!forced 0 || bits 0) = true ↔ (forced 0 = true → bits 0 = true) := by
      cases forced 0 <;> cases bits 0 <;> decide
    rw [hh]
    constructor
    · rintro ⟨h0,hs⟩ i
      exact Fin.cases h0 hs i
    · intro h
      exact ⟨h 0,fun i => h i.succ⟩

theorem forcedTest_work (n : ℕ) (forced bits : Fin n → Bool) :
    (forcedTest n forced bits).work = 4*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [forcedTest,ih]; omega

/-- One retained computed Boolean representative per head group. -/
structure RepresentativeFamily {r : ℕ} (h : Fin r → ℕ) where
  /-- Retained computed local words. -/
  words : (g : Fin r) → Fin (h g) → Bool
  /-- Total representative search and branch charges. -/
  work : ℕ

/-- Every group search is executed once and its resulting word is retained. -/
def acquireRepresentatives : (r : ℕ) → (h m W : Fin r → ℕ) →
    ((g : Fin r) → Fin (m g) → Fin (h g) → ℤ) →
    ((g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g)) →
    RepresentativeFamily h
  | 0, _, _, _, _, _ => ⟨fun g => Fin.elim0 g,0⟩
  | r+1, h, m, W, rows, y =>
      let head := measuredRepresentative (h 0) (m 0) (rows 0) (summaryTarget (h 0) (m 0) (W 0) (y 0))
      let tail := acquireRepresentatives r (fun i => h i.succ) (fun i => m i.succ)
        (fun i => W i.succ) (fun i => rows i.succ) (fun i => y i.succ)
      ⟨Fin.cons (head.found.getD (fun _ => false)) tail.words,head.work+tail.work+1⟩

theorem acquireRepresentatives_words (r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (g : Fin r) :
    (acquireRepresentatives r h m W rows y).words g =
      summaryRepresentative (h g) (m g) (W g) (rows g) (y g) := by
  induction r with
  | zero => exact Fin.elim0 g
  | succ r ih =>
    refine Fin.cases ?_ (fun i => ?_) g
    · rfl
    · exact ih _ _ _ _ _ i

theorem acquireRepresentatives_work (r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g)) :
    (acquireRepresentatives r h m W rows y).work =
      (∑ g, (measuredRepresentative (h g) (m g) (rows g)
        (summaryTarget (h g) (m g) (W g) (y g))).work) + r := by
  induction r with
  | zero => simp [acquireRepresentatives]
  | succ r ih => simp only [acquireRepresentatives,ih,Fin.sum_univ_succ]; omega

theorem acquireRepresentatives_work_le (r : ℕ) (h m W : Fin r → ℕ)
    (rows : (g : Fin r) → Fin (m g) → Fin (h g) → ℤ)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g)) :
    (acquireRepresentatives r h m W rows y).work ≤
      ∑ g, 2^(h g)*((m g)*(4*(h g)+3)+3) := by
  rw [acquireRepresentatives_work]
  have he := Finset.sum_le_sum (s := Finset.univ) (fun (g : Fin r) _ =>
    measuredRepresentative_work (h g) (m g) (rows g) (summaryTarget (h g) (m g) (W g) (y g)))
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one] using he

end RiemannGaussian.SemiprimeRepresentativeExecution
