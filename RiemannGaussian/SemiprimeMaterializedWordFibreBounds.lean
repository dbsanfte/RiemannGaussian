/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedWordFibre
import RiemannGaussian.SemiprimeWordFoldBounds

/-! # Actual cached word-node buffers and retained clocks
Physical arithmetic and all callback reports are retained. Cached tests and
representatives keep their existing scalar/control ledger; source acquisition
and complete address/tape refinement remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeMaterializedWordFibreBounds
open scoped BigOperators
open SemiprimeMaterializedWordFibre SemiprimeRationalBits SemiprimeJetBits
open SemiprimeMaterializedFibre SemiprimeMaterializedFibrePacket SemiprimePacketArrayExecution
open SemiprimeRepresentativeExecution SemiprimeCounterEnumeration
open SemiprimeNodeArrayExecution (RuntimeDesign)

/-- The extra retained-control wrapper never changes physical data. -/
@[simp] theorem bump_size (r : JetReport) (amount : ℕ) : (bump r amount).words.size=r.words.size := rfl
/-- The extra wrapper retains its ACTUAL supplied report cost. -/
theorem bump_clock (r : JetReport) (amount : ℕ) : (bump r amount).clock=r.clock+amount := rfl

/-- Literal successful-body/zero gate output precision. -/
theorem gate_size (J : ℕ) (test : TestReport) (body : Unit → JetReport)
    (hb : (body ()).words.size=J) : (SemiprimeWordFoldArithmetic.gate J test body).words.size=J := by
  cases he : test.accepted
  · simpa only [SemiprimeWordFoldArithmetic.gate,he,Bool.false_eq_true,ite_false] using SemiprimeWordFoldArithmetic.zero_size J
  · simpa only [SemiprimeWordFoldArithmetic.gate,he,ite_true] using hb

/-- A scanned head always returns the requested finite precision. -/
@[simp] theorem scanHead_size (template : List Bool) (J n m : ℕ) (cache : HeadCache) (target : Fin m → ℤ)
    (forced : Fin n → Bool) (value : (Fin n → Bool) → JetReport) :
    (scanHead template J n m cache target forced value).words.size=J :=
  SemiprimeWordFoldBounds.sumCodes_size template J _ _

/-- All scanned head output words occupy the actual physical template. -/
theorem scanHead_bounded (template : List Bool) (J n m : ℕ) (cache : HeadCache) (target : Fin m → ℤ)
    (forced : Fin n → Bool) (value : (Fin n → Bool) → JetReport) (ht : 0< template.length) :
    Bounded (scanHead template J n m cache target forced value).words template.length :=
  SemiprimeWordFoldBounds.sumCodes_bounded template J _ _ ht

@[simp] theorem fibreCached_size (template : List Bool) (J r : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → JetReport) :
    (fibreCached template J r h m W caches y forced value).words.size=J := by
  simp only [SemiprimeMaterializedWordFibre.fibreCached,bump_size,SemiprimeWordFoldArithmetic.productList,SemiprimeNativeGroupBits.productList_size]

theorem fibreCached_bounded (template : List Bool) (J r : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → JetReport) (ht : 0< template.length) :
    Bounded (fibreCached template J r h m W caches y forced value).words template.length :=
  SemiprimeNativeGroupBitsBudget.productList_bounded template J _ _ ht

@[simp] theorem sumCached_size (template : List Bool) (J r : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → JetReport) :
    (sumCached template J r h m W caches forced value).words.size=J :=
  SemiprimeWordFoldBounds.sumCodes_size template J _ _

theorem sumCached_bounded (template : List Bool) (J r : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → JetReport) (ht : 0< template.length) :
    Bounded (sumCached template J r h m W caches forced value).words template.length :=
  SemiprimeWordFoldBounds.sumCodes_bounded template J _ _ ht

@[simp] theorem signedFibre_size {A : Type} (template : List Bool) (J : ℕ)
    (f : Finset A → Finset A → JetReport) (S U : Finset A) :
    (signedFibre template J f S U).words.size=J := by
  simp only [SemiprimeMaterializedWordFibre.signedFibre,bump_size,SemiprimeWordFoldArithmetic.scale_size]

theorem signedFibre_bounded {A : Type} (template : List Bool) (J : ℕ)
    (f : Finset A → Finset A → JetReport) (S U : Finset A) :
    Bounded (signedFibre template J f S U).words template.length :=
  SemiprimeWordFoldBounds.scale_bounded template J _ _

/-- Every actual support prefix keeps the requested physical precision. -/
theorem supportRun_size {A : Type} [DecidableEq A] (template : List Bool) (J : ℕ)
    (todo : List A) (q : ℕ) (f : Finset A → Finset A → JetReport)
    (hf : ∀ S U,(f S U).words.size=J) : (supportRun template J todo q f).words.size=J := by
  induction todo generalizing q f with
  | nil => exact hf ∅ ∅
  | cons a tail ih =>
    cases q with
    | zero => exact ih 0 f hf
    | succ q => exact SemiprimeWordFoldArithmetic.add_size template J _ _

/-- Every actual support prefix occupies the same physical template. -/
theorem supportRun_bounded {A : Type} [DecidableEq A] (template : List Bool) (J : ℕ)
    (todo : List A) (q : ℕ) (f : Finset A → Finset A → JetReport)
    (hf : ∀ S U,Bounded (f S U).words template.length) :
    Bounded (supportRun template J todo q f).words template.length := by
  induction todo generalizing q f with
  | nil => exact hf ∅ ∅
  | cons a tail ih =>
    cases q with
    | zero => exact ih 0 f hf
    | succ q => exact SemiprimeWordFoldBounds.add_bounded template J _ _

@[simp] theorem rawRun_size {A : Type} [DecidableEq A] (template : List Bool) (J : ℕ)
    (todo : List A) (f : Finset A → Finset A → JetReport) : (rawRun template J todo f).words.size=J :=
  supportRun_size template J todo _ _ (signedFibre_size template J f)

theorem rawRun_bounded {A : Type} [DecidableEq A] (template : List Bool) (J : ℕ)
    (todo : List A) (f : Finset A → Finset A → JetReport) :
    Bounded (rawRun template J todo f).words template.length :=
  supportRun_bounded template J todo _ _ (signedFibre_bounded template J f)

@[simp] theorem node_size {n F : ℕ} (template : List Bool) (J : ℕ) (d : RuntimeDesign n F) (value : GroupCall d) :
    (node template J d value).words.size=J := rawRun_size template J _ _

theorem node_bounded {n F : ℕ} (template : List Bool) (J : ℕ) (d : RuntimeDesign n F) (value : GroupCall d) :
    Bounded (node template J d value).words template.length := rawRun_bounded template J _ _

/-- Exact physical head-scan envelope; original cached tests retain their cost. -/
def headBudget (W J H M B : ℕ) : ℕ :=
  3*J+1+2^H*(B+2*M+4*H+3*J+5+SemiprimeWordFoldBounds.addBudget W J)

/-- Actual rejected tests skip body callbacks, but all test work is paid. -/
theorem scanHead_clock (template : List Bool) (J n m B : ℕ) (cache : HeadCache) (target : Fin m → ℤ)
    (forced : Fin n → Bool) (value : (Fin n → Bool) → JetReport) (ht : 0< template.length)
    (hv : ∀ bits,(value bits).clock≤ B) (hw : ∀ bits,Bounded (value bits).words template.length)
    (hs : ∀ bits,(value bits).words.size=J) :
    (scanHead template J n m cache target forced value).clock≤ headBudget template.length J n m B := by
  have hg (code : Fin (2^n)) := SemiprimeWordFoldBounds.gate_clock J B
    (cachedFibreTest n m cache target forced code) (fun _ => value (cachedWord n cache code)) (hv _)
  have htest (code : Fin (2^n)) : (cachedFibreTest n m cache target forced code).work=2*m+4*n+3 := by
    simp only [cachedFibreTest,cachedTest,forcedTest_work]
    omega
  have hh := SemiprimeWordFoldBounds.sumCodes_clock template J (2^n) (B+2*m+4*n+3*J+5)
    (fun code => SemiprimeWordFoldArithmetic.gate J (cachedFibreTest n m cache target forced code)
      (fun _ => value (cachedWord n cache code))) ht (by
        intro code
        refine ⟨by have h:=hg code; rw [htest code] at h; omega,?_,?_⟩
        · exact SemiprimeWordFoldBounds.gate_bounded J _ _ _ ht (hw _)
        · exact (gate_size J _ _ (hs _)).le)
  exact hh

/-- All head sums, same-order products and representative scans are retained. -/
def oneSummaryBudget (W J r H M B : ℕ) : ℕ :=
  r*(headBudget W J H M B+SemiprimeNativeGroupBitsBudget.multiplyBudget W J+J+3)+(3*J+1)+
    r*(2^H*(2*M+3)+H+1)+r+1

theorem fibreCached_clock (template : List Bool) (J r H M B : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → JetReport)
    (ht : 0< template.length) (hh : ∀ g,h g≤ H) (hm : ∀ g,m g≤ M)
    (hv : ∀ g a,(value g a).clock≤ B) (hw : ∀ g a,Bounded (value g a).words template.length)
    (hs : ∀ g a,(value g a).words.size=J) :
    (fibreCached template J r h m W caches y forced value).clock≤ oneSummaryBudget template.length J r H M B := by
  let reps := acquireReps r h m W caches y
  let callback := fun g => scanHead template J (h g) (m g) (headAt caches g.val)
    (summaryTarget (h g) (m g) (W g) (y g)) (forced g)
    (fun bits => value g (Function.update (repsBits r h reps) g bits))
  have hc (g : Fin r) : (callback g).clock≤ headBudget template.length J H M B := by
    have hl := scanHead_clock template J (h g) (m g) B (headAt caches g.val)
      (summaryTarget (h g) (m g) (W g) (y g)) (forced g)
      (fun bits => value g (Function.update (repsBits r h reps) g bits)) ht
      (fun bits => hv g _) (fun bits => hw g _) (fun bits => hs g _)
    apply hl.trans
    unfold headBudget
    gcongr
    · exact hh g
    · exact hm g
    · exact hh g
  have hp := SemiprimeWordFoldBounds.productList_clock template J (headBudget template.length J H M B)
    (List.ofFn (fun g : Fin r => g)) callback ht (fun g _ => hc g)
    (fun g _ => scanHead_bounded template J _ _ _ _ _ _ ht)
    (fun g _ => (scanHead_size template J _ _ _ _ _ _).le)
  simp only [List.length_ofFn] at hp
  have hr := repsWork_le r H M h m W caches y hh hm
  unfold SemiprimeMaterializedWordFibre.fibreCached
  rw [bump_clock]
  exact (Nat.add_le_add hp hr).trans_eq (by unfold oneSummaryBudget; ring)

/-- The literal acquired summary box multiplies local scans, never global 2^n. -/
def fibreBudget (W J r H M B Y : ℕ) : ℕ :=
  3*J+1+Y*(oneSummaryBudget W J r H M B+SemiprimeWordFoldBounds.addBudget W J)

theorem sumCached_clock (template : List Bool) (J r H M B : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → JetReport)
    (ht : 0< template.length) (hh : ∀ g,h g≤ H) (hm : ∀ g,m g≤ M)
    (hv : ∀ g a,(value g a).clock≤ B) (hw : ∀ g a,Bounded (value g a).words template.length)
    (hs : ∀ g a,(value g a).words.size=J) :
    (sumCached template J r h m W caches forced value).clock≤
      fibreBudget template.length J r H M B (summaryCount r h m W) :=
  SemiprimeWordFoldBounds.sumCodes_clock template J _ _ _ ht
    (fun _ => ⟨fibreCached_clock template J r H M B h m W caches _ forced value ht hh hm hv hw hs,
      fibreCached_bounded template J r h m W caches _ forced value ht,(fibreCached_size template J r h m W caches _ forced value).le⟩)

/-- The literal repeated sign-flag steps are exactly its input count. -/
theorem signFlag_steps (k : ℕ) : (signFlag k).2=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [signFlag,ih]

theorem signedFibre_clock (template : List Bool) (J n B : ℕ)
    (f : Finset (Fin n) → Finset (Fin n) → JetReport) (S U : Finset (Fin n))
    (ht : 0< template.length) (hf : (f S U).clock≤ B)
    (hw : Bounded (f S U).words template.length) (hs : (f S U).words.size=J) :
    (signedFibre template J f S U).clock≤ B+SemiprimeWordFoldBounds.scaleBudget template.length J+3*n+1 := by
  have hp := SemiprimeWordFoldBounds.scale_clock template J (f S U) (signFlag (S.card-U.card)).1 ht hw hs.le
  have hS : S.card≤ n := by simpa using Finset.card_le_univ S
  have hU : U.card≤ n := by simpa using Finset.card_le_univ U
  unfold SemiprimeMaterializedWordFibre.signedFibre
  rw [bump_clock,signFlag_steps]
  omega

/-- Actual support recursion has the same weighted-binomial callback count;
each internal node pays TWO real physical additions and branch control. -/
theorem supportRun_clock {A : Type} [DecidableEq A] (template : List Bool) (J B : ℕ)
    (todo : List A) (q : ℕ) (f : Finset A → Finset A → JetReport) (ht : 0< template.length)
    (hf : ∀ S U,(f S U).clock≤ B) (hw : ∀ S U,Bounded (f S U).words template.length)
    (hs : ∀ S U,(f S U).words.size=J) :
    (supportRun template J todo q f).clock≤ callbacks todo.length q *
      (B+todo.length*(2*SemiprimeWordFoldBounds.addBudget template.length J+1)) := by
  induction todo generalizing q f with
  | nil => simpa only [SemiprimeMaterializedWordFibre.supportRun,List.length_nil,callbacks,Nat.zero_mul,Nat.add_zero,Nat.one_mul] using hf ∅ ∅
  | cons a tail ih =>
    cases q with
    | zero =>
      have ho := ih 0 f hf hw hs
      have hc : 1≤ callbacks tail.length 0 := by rw [callbacks_eq_weightedCount,weightedCount_zero]
      rw [SemiprimeMaterializedWordFibre.supportRun,bump_clock,List.length_cons,callbacks]
      nlinarith only [ho,hc]
    | succ q =>
      have he := ih (q+1) f hf hw hs
      have hs' := ih q (fun S U => f (insert a S) U) (fun S U => hf _ _) (fun S U => hw _ _) (fun S U => hs _ _)
      have hu := ih q (fun S U => f (insert a S) (insert a U)) (fun S U => hf _ _) (fun S U => hw _ _) (fun S U => hs _ _)
      let er := SemiprimeMaterializedWordFibre.supportRun template J tail (q+1) f
      let sr := SemiprimeMaterializedWordFibre.supportRun template J tail q (fun S U => f (insert a S) U)
      let ur := SemiprimeMaterializedWordFibre.supportRun template J tail q (fun S U => f (insert a S) (insert a U))
      have hab := SemiprimeWordFoldBounds.add_clock template J er sr ht
        (supportRun_bounded template J tail (q+1) f hw)
        (supportRun_bounded template J tail q (fun S U => f (insert a S) U) (fun S U => hw _ _))
        (supportRun_size template J tail (q+1) f hs).le
        (supportRun_size template J tail q (fun S U => f (insert a S) U) (fun S U => hs _ _)).le
      have habc := SemiprimeWordFoldBounds.add_clock template J
        (SemiprimeWordFoldArithmetic.add template J er sr) ur ht
        (SemiprimeWordFoldBounds.add_bounded template J er sr)
        (supportRun_bounded template J tail q (fun S U => f (insert a S) (insert a U)) (fun S U => hw _ _))
        (SemiprimeWordFoldArithmetic.add_size template J er sr).le
        (supportRun_size template J tail q (fun S U => f (insert a S) (insert a U)) (fun S U => hs _ _)).le
      dsimp only [er,sr,ur] at hab habc
      have hc : 1≤ callbacks tail.length (q+1) := by
        rw [callbacks_eq_weightedCount,weightedCount]
        have hz := Finset.single_le_sum (f:=fun j => 2^j*tail.length.choose j)
          (fun _ _ => Nat.zero_le _) (by simp : 0∈Finset.range (q+1+1))
        simpa only [pow_zero,Nat.choose_zero_right,Nat.one_mul] using hz
      rw [SemiprimeMaterializedWordFibre.supportRun,bump_clock,List.length_cons,callbacks]
      nlinarith only [he,hs',hu,hab,habc,hc]

/-- Physical group/fibre terms, sign metadata and literal support arithmetic. -/
def rawBudget (W n J B Cq : ℕ) : ℕ :=
  Cq*(B+SemiprimeWordFoldBounds.scaleBudget W J+3*n+1+n*(2*SemiprimeWordFoldBounds.addBudget W J+1))

theorem rawRun_clock {n : ℕ} (template : List Bool) (J B : ℕ) (todo : List (Fin n))
    (f : Finset (Fin n) → Finset (Fin n) → JetReport) (ht : 0< template.length)
    (hf : ∀ S U,(f S U).clock≤ B) (hw : ∀ S U,Bounded (f S U).words template.length)
    (hs : ∀ S U,(f S U).words.size=J) (hlen : todo.length≤ n) :
    (rawRun template J todo f).clock≤ rawBudget template.length n J B (callbacks todo.length (J-1)) := by
  have hp := supportRun_clock template J (B+SemiprimeWordFoldBounds.scaleBudget template.length J+3*n+1)
    todo (J-1) (signedFibre template J f) ht
    (fun S U => signedFibre_clock template J n B f S U ht (hf S U) (hw S U) (hs S U))
    (signedFibre_bounded template J f) (signedFibre_size template J f)
  apply hp.trans
  unfold rawBudget
  gcongr

/-- Explicit actual-node budget, with separate local head and summary counts. -/
def nodeBudget (W n J r H M B Y : ℕ) : ℕ :=
  rawBudget W n J (fibreBudget W J r H M B Y) (weightedCount n (J-1))+
    (r*(2^H*(H+M*(4*H+2)+3))+r+1)

/-- All arithmetic/test/group reports are retained by the ACTUAL word node.
This is the selected physical/scalar ledger, not a full address/tape theorem. -/
theorem node_clock {n F : ℕ} (template : List Bool) (J : ℕ) (d : RuntimeDesign n F)
    (value : GroupCall d) (H M B : ℕ) (ht : 0< template.length)
    (hh : ∀ g,d.h g≤ H) (hm : ∀ g,d.m g≤ M)
    (hv : ∀ U g a,(value U g a).clock≤ B)
    (hw : ∀ U g a,Bounded (value U g a).words template.length)
    (hs : ∀ U g a,(value U g a).words.size=J) :
    (node template J d value).clock≤ nodeBudget template.length n J d.r H M B
      (summaryCount d.r d.h d.m d.W) := by
  let caches := acquireHeads d.r d.h d.m d.C
  have hf (S U : Finset (Fin n)) :
      (fibre template J d caches value S U).clock≤
        fibreBudget template.length J d.r H M B (summaryCount d.r d.h d.m d.W) :=
    sumCached_clock template J d.r H M B d.h d.m d.W caches _ (value U) ht hh hm (hv U) (hw U) (hs U)
  have hp := rawRun_clock template J _ (List.ofFn (fun v : Fin n => v)) (fibre template J d caches value) ht hf
    (fun _ _ => sumCached_bounded template J d.r d.h d.m d.W caches _ _ ht)
    (fun _ _ => sumCached_size template J d.r d.h d.m d.W caches _ _) (by simp)
  simp only [List.length_ofFn,callbacks_eq_weightedCount] at hp
  have ha := acquisitionWork_le d.r H M d.h d.m d.C hh hm
  unfold node nodeBudget
  rw [bump_clock]
  exact Nat.add_le_add hp ha

/-- Replacing the ACTUAL summary cardinality by its acquired closed envelope
only increases this explicit node clock budget. -/
theorem nodeBudget_mono_summary (W n J r H M B : ℕ) {Y Z : ℕ} (hYZ : Y≤ Z) :
    nodeBudget W n J r H M B Y≤ nodeBudget W n J r H M B Z := by
  unfold nodeBudget rawBudget fibreBudget
  gcongr

/-- A larger derived physical width increases only fixed polynomial arithmetic
costs; no global Boolean traversal is introduced by this coarsening. -/
theorem nodeBudget_mono_width (n J r H M B Y : ℕ) {W V : ℕ} (hWV : W≤ V) :
    nodeBudget W n J r H M B Y≤ nodeBudget V n J r H M B Y := by
  unfold nodeBudget rawBudget fibreBudget oneSummaryBudget headBudget
    SemiprimeWordFoldBounds.scaleBudget SemiprimeWordFoldBounds.addBudget
    SemiprimeCorrectedPortBitsBounds.addBudget SemiprimeNativeGroupBitsBudget.multiplyBudget
  gcongr

end RiemannGaussian.SemiprimeMaterializedWordFibreBounds
