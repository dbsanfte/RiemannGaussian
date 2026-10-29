/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWordFoldArithmetic
import RiemannGaussian.SemiprimeMaterializedGroupAdapter
import RiemannGaussian.SemiprimeWordPacketWidth

/-! # Actual physical word arithmetic through cached heads and signed supports
The scalar cached tests and representative searches retain their reports. Every
jet addition, sign scaling and product is executed on words; group outputs are
not decoded to feed a scalar fold. Decoding occurs only in refinement statements.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace RiemannGaussian.SemiprimeMaterializedWordFibre
open scoped BigOperators
open SemiprimeRationalBits SemiprimeJetBits SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeLocalExecutionHeight SemiprimeMaterializedFibre SemiprimeMaterializedFibrePacket
open SemiprimeRepresentativeExecution SemiprimePacketArrayExecution
open SemiprimeNodeArrayExecution (RuntimeDesign)

/-- Extra finite control retains the acquired word jet verbatim. -/
def bump (r : JetReport) (amount : ℕ) : JetReport := ⟨r.words,r.clock+amount⟩

/-- Actual finite cached head scan, including rejected test reports and no rejected callback. -/
def scanHead (template : List Bool) (J n m : ℕ) (cache : HeadCache) (target : Fin m → ℤ)
    (forced : Fin n → Bool) (value : (Fin n → Bool) → JetReport) : JetReport :=
  SemiprimeWordFoldArithmetic.sumCodes template J (2^n) (fun code =>
    SemiprimeWordFoldArithmetic.gate J (cachedFibreTest n m cache target forced code)
      (fun _ => value (cachedWord n cache code)))

/-- One actual summary: cache unforced representatives once, scan forced head
fibres, and multiply the head sums in precisely the original order. -/
def fibreCached (template : List Bool) (J r : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → JetReport) : JetReport :=
  let reps := acquireReps r h m W caches y
  let out := SemiprimeWordFoldArithmetic.productList template J (List.ofFn (fun g : Fin r => g)) (fun g =>
    scanHead template J (h g) (m g) (headAt caches g.val)
      (summaryTarget (h g) (m g) (W g) (y g)) (forced g)
      (fun bits => value g (Function.update (repsBits r h reps) g bits)))
  bump out (repsWork r reps)

/-- The exact same acquired summary-code box, now accumulating physical jets. -/
def sumCached (template : List Bool) (J r : ℕ) (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → JetReport) : JetReport :=
  SemiprimeWordFoldArithmetic.sumCodes template J (summaryCount r h m W) (fun code =>
    fibreCached template J r h m W caches (summaryCode r h m W code) forced value)

/-- Compute only a Boolean sign and its actual repeated-negation metadata work. -/
def signFlag : ℕ → Bool × ℕ
  | 0 => (false,0)
  | k+1 => let old := signFlag k; (!old.1,old.2+1)

/-- Actual sign scaling uses a literal physical ±1 word, never a rational sign supplier. -/
def signedFibre {A : Type} (template : List Bool) (J : ℕ)
    (f : Finset A → Finset A → JetReport) (S U : Finset A) : JetReport :=
  let sign := signFlag (S.card-U.card)
  bump (SemiprimeWordFoldArithmetic.scale template J (f S U) sign.1) (sign.2+S.card+U.card+1)

/-- Same ternary support recursion and order as the original executed stream. -/
def supportRun {A : Type} [DecidableEq A] (template : List Bool) (J : ℕ) :
    List A → ℕ → (Finset A → Finset A → JetReport) → JetReport
  | [],_,f => f ∅ ∅
  | _::tail,0,f => bump (supportRun template J tail 0 f) 1
  | a::tail,q+1,f =>
      let e := supportRun template J tail (q+1) f
      let s := supportRun template J tail q (fun S U => f (insert a S) U)
      let u := supportRun template J tail q (fun S U => f (insert a S) (insert a U))
      bump (SemiprimeWordFoldArithmetic.add template J
        (SemiprimeWordFoldArithmetic.add template J e s) u) 1

/-- Actual inclusive Taylor support traversal, with physical signed jet arithmetic. -/
def rawRun {A : Type} [DecidableEq A] (template : List Bool) (J : ℕ) (todo : List A)
    (f : Finset A → Finset A → JetReport) : JetReport :=
  supportRun template J todo (J-1) (signedFibre template J f)

/-- Executed original group interface; no scalar group decoding appears here. -/
abbrev GroupCall {n F : ℕ} (d : RuntimeDesign n F) :=
  Finset (Fin n) → (g : Fin d.r) → ((k : Fin d.r) → Fin (d.h k) → Bool) → JetReport

/-- One actual support term consumes its actual physical group callback. -/
def fibre {n F : ℕ} (template : List Bool) (J : ℕ) (d : RuntimeDesign n F)
    (caches : Array HeadCache) (value : GroupCall d) (S U : Finset (Fin n)) : JetReport :=
  sumCached template J d.r d.h d.m d.W caches
    (fun g i => decide (d.grouping.symm ⟨g,i⟩ ∈ S)) (value U)

/-- Acquire the exact original head tables once, then retain word jets through
all summary/head/group/support arithmetic. Scalar Hermite is outside this node. -/
def node {n F : ℕ} (template : List Bool) (J : ℕ) (d : RuntimeDesign n F)
    (value : GroupCall d) : JetReport :=
  let caches := acquireHeads d.r d.h d.m d.C
  let out := rawRun template J (List.ofFn (fun v : Fin n => v)) (fibre template J d caches value)
  bump out (acquisitionWork d.r caches)

/-- Boolean sign metadata is exactly the old sign value and repeated-step count. -/
theorem signFlag_correct (k : ℕ) :
    (if (signFlag k).1 then (-1:ℚ) else 1)=(signPower k).1 ∧ (signFlag k).2=(signPower k).2 := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    simp only [signFlag,signPower]
    constructor
    · rw [← ih.1]
      by_cases hf : (signFlag k).1=true <;> simp [hf]
    · exact congrArg (fun n => n+1) ih.2

/-- Physical cached head scanning refines the SAME scalar code/test order and
keeps one denominator across every accepted or rejected local word. -/
theorem scanHead_correct (template : List Bool) (J n m D B : ℕ)
    (cache : HeadCache) (target : Fin m → ℤ) (forced : Fin n → Bool)
    (value : (Fin n → Bool) → JetReport) (legacy : (Fin n → Bool) → SemiprimeFibreArrayExecution.Run)
    (hd : 0<D) (hden : D<2^template.length) (hnum : 2^n*B<2^template.length)
    (hv : ∀ bits,decode (value bits).words=(legacy bits).jet.coefficients ∧
      Valid (value bits).words ∧ ArrayBound (decode (value bits).words) J D B) :
    decode (scanHead template J n m cache target forced value).words=
      (SemiprimeMaterializedFibre.scanHead J n m cache target forced legacy).jet.coefficients ∧
    Valid (scanHead template J n m cache target forced value).words ∧
    ArrayBound (decode (scanHead template J n m cache target forced value).words) J D (2^n*B) := by
  apply SemiprimeWordFoldArithmetic.sumCodes_correct template J (2^n) D B _ _ hd hden hnum
  intro code
  exact SemiprimeWordFoldArithmetic.gate_correct J D B _ _ _
    (hv (cachedWord n cache code)).1 (hv (cachedWord n cache code)).2.1
    (hv (cachedWord n cache code)).2.2

/-- One summary's physical head product retains its ORIGINAL common group
representations; all head/product prefixes derive from their finite counts. -/
theorem fibreCached_correct (template : List Bool) (J r D B P N k : ℕ)
    (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (y : (g : Fin r) → SemiprimeLayoutCertificates.Summary (Fin (h g)) (Fin (m g)) (W g))
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → JetReport)
    (legacy : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → SemiprimeFibreArrayExecution.Run)
    (hd : 0<D) (hden : D<2^template.length) (hnum : P*B<2^template.length)
    (hP : ∀ g,2^(h g) ≤ P)
    (hDN : D ≤ N) (hBN : P*B ≤ N) (hJN : J ≤ N) (hNk : N ≤ 2^k)
    (hwidth : k*(2*r+2)<template.length)
    (hv : ∀ g a,decode (value g a).words=(legacy g a).jet.coefficients ∧
      Valid (value g a).words ∧ ArrayBound (decode (value g a).words) J D B) :
    decode (fibreCached template J r h m W caches y forced value).words=
      (SemiprimeMaterializedFibrePacket.fibreCached J r h m W caches y forced legacy).jet.coefficients ∧
    Valid (fibreCached template J r h m W caches y forced value).words ∧
    ArrayBound (decode (fibreCached template J r h m W caches y forced value).words) J (D^r) (N^(2*r)) := by
  let reps := acquireReps r h m W caches y
  let f := fun g => scanHead template J (h g) (m g) (headAt caches g.val)
    (summaryTarget (h g) (m g) (W g) (y g)) (forced g)
    (fun bits => value g (Function.update (repsBits r h reps) g bits))
  let old := fun g => SemiprimeMaterializedFibre.scanHead J (h g) (m g) (headAt caches g.val)
    (summaryTarget (h g) (m g) (W g) (y g)) (forced g)
    (fun bits => legacy g (Function.update (repsBits r h reps) g bits))
  have hf (g : Fin r) (_ : g∈List.ofFn (fun g : Fin r => g)) :
      decode (f g).words=(old g).jet.coefficients ∧ Valid (f g).words ∧
        ArrayBound (decode (f g).words) J D (P*B) := by
    have hh := scanHead_correct template J (h g) (m g) D B (headAt caches g.val)
      (summaryTarget (h g) (m g) (W g) (y g)) (forced g) _ _ hd hden
      ((Nat.mul_le_mul_right B (hP g)).trans_lt hnum)
      (fun bits => hv g (Function.update (repsBits r h reps) g bits))
    exact ⟨hh.1,hh.2.1,arrayBound_mono hh.2.2 (Nat.mul_le_mul_right B (hP g))⟩
  have hp := SemiprimeNativeGroupBits.productList_correct template J D (P*B) N k
    (List.ofFn (fun g : Fin r => g)) f old hd hDN hBN hJN hNk
    (by simpa only [List.length_ofFn] using hwidth) hf
  simpa only [fibreCached,SemiprimeMaterializedFibrePacket.fibreCached,
    SemiprimeWordFoldArithmetic.productList,SemiprimePacketArrayExecution.bump,bump,
    List.length_ofFn,f,old,reps] using hp

/-- The physical full summary box has a common product denominator, so adding
Y summaries multiplies only the numerator bound, never the denominator exponent. -/
theorem sumCached_correct (template : List Bool) (J r D B P N k Y : ℕ)
    (h m W : Fin r → ℕ) (caches : Array HeadCache)
    (forced : (g : Fin r) → Fin (h g) → Bool)
    (value : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → JetReport)
    (legacy : (g : Fin r) → ((k : Fin r) → Fin (h k) → Bool) → SemiprimeFibreArrayExecution.Run)
    (hd : 0<D) (hden : D<2^template.length) (hnum : P*B<2^template.length)
    (hP : ∀ g,2^(h g) ≤ P) (hDN : D ≤ N) (hBN : P*B ≤ N) (hJN : J ≤ N) (hNk : N ≤ 2^k)
    (hwidth : k*(2*r+2)<template.length) (hY : summaryCount r h m W ≤ Y)
    (hdenF : D^r<2^template.length) (hnumF : Y*N^(2*r)<2^template.length)
    (hv : ∀ g a,decode (value g a).words=(legacy g a).jet.coefficients ∧
      Valid (value g a).words ∧ ArrayBound (decode (value g a).words) J D B) :
    decode (sumCached template J r h m W caches forced value).words=
      (SemiprimeMaterializedFibrePacket.sumCached J r h m W caches forced legacy).jet.coefficients ∧
    Valid (sumCached template J r h m W caches forced value).words ∧
    ArrayBound (decode (sumCached template J r h m W caches forced value).words) J (D^r) (Y*N^(2*r)) := by
  have hh := SemiprimeWordFoldArithmetic.sumCodes_correct template J (summaryCount r h m W)
    (D^r) (N^(2*r))
    (fun code => fibreCached template J r h m W caches (summaryCode r h m W code) forced value)
    (fun code => SemiprimeMaterializedFibrePacket.fibreCached J r h m W caches
      (summaryCode r h m W code) forced legacy) (pow_pos hd _) hdenF
    ((Nat.mul_le_mul_right (N^(2*r)) hY).trans_lt hnumF)
    (fun code => fibreCached_correct template J r D B P N k h m W caches
      (summaryCode r h m W code) forced value legacy
      hd hden hnum hP hDN hBN hJN hNk hwidth hv)
  exact ⟨hh.1,hh.2.1,arrayBound_mono hh.2.2 (Nat.mul_le_mul_right _ hY)⟩

/-- Physical ±1 scaling preserves the common denominator and exactly matches
the original signed support value, without rational sign data in the runtime. -/
theorem signedFibre_correct {A : Type} (template : List Bool) (J D B : ℕ)
    (f : Finset A → Finset A → JetReport)
    (legacy : Finset A → Finset A → SemiprimeFibreArrayExecution.Run)
    (hd : 0<D) (hden : D<2^template.length) (hnum : B<2^template.length)
    (hf : ∀ S U,decode (f S U).words=(legacy S U).jet.coefficients ∧
      Valid (f S U).words ∧ ArrayBound (decode (f S U).words) J D B) (S U : Finset A) :
    decode (signedFibre template J f S U).words=
      (SemiprimePacketArrayExecution.signedFibre J legacy S U).jet.coefficients ∧
    Valid (signedFibre template J f S U).words ∧
    ArrayBound (decode (signedFibre template J f S U).words) J D B := by
  have hs := SemiprimeWordFoldArithmetic.scale_correct template J D B (f S U)
    (signFlag (S.card-U.card)).1 (hf S U).2.1 hd hden hnum (hf S U).2.2
  refine ⟨?_,hs.2.1,hs.2.2⟩
  change decode (SemiprimeWordFoldArithmetic.scale template J (f S U)
    (signFlag (S.card-U.card)).1).words=_
  rw [hs.1,(hf S U).1,(signFlag_correct (S.card-U.card)).1]
  rfl

/-- Every signed-support prefix keeps the original callback denominator. The
numerator grows only by the ACTUAL weighted-binomial callback count. -/
theorem supportRun_correct {A : Type} [DecidableEq A] (template : List Bool) (J D B : ℕ)
    (todo : List A) (q : ℕ) (f : Finset A → Finset A → JetReport)
    (legacy : Finset A → Finset A → SemiprimeFibreArrayExecution.Run)
    (hd : 0<D) (hden : D<2^template.length)
    (hnum : SemiprimeCounterEnumeration.callbacks todo.length q*B<2^template.length)
    (hf : ∀ S U,decode (f S U).words=(legacy S U).jet.coefficients ∧
      Valid (f S U).words ∧ ArrayBound (decode (f S U).words) J D B) :
    decode (supportRun template J todo q f).words=
      (SemiprimePacketArrayExecution.supportRun J todo q legacy).jet.coefficients ∧
    Valid (supportRun template J todo q f).words ∧
    ArrayBound (decode (supportRun template J todo q f).words) J D
      (SemiprimeCounterEnumeration.callbacks todo.length q*B) := by
  induction todo generalizing q f legacy with
  | nil => simpa only [supportRun,SemiprimePacketArrayExecution.supportRun,List.length_nil,
      SemiprimeCounterEnumeration.callbacks,Nat.one_mul] using hf ∅ ∅
  | cons a tail ih =>
    cases q with
    | zero =>
      have hh := ih 0 f legacy hnum hf
      simpa only [supportRun,SemiprimePacketArrayExecution.supportRun,bump,
        SemiprimePacketArrayExecution.bump,List.length_cons,SemiprimeCounterEnumeration.callbacks] using hh
    | succ q =>
      let Ce := SemiprimeCounterEnumeration.callbacks tail.length (q+1)
      let Cs := SemiprimeCounterEnumeration.callbacks tail.length q
      have hcap : Ce*B+Cs*B+Cs*B<2^template.length := by
        simpa only [List.length_cons,SemiprimeCounterEnumeration.callbacks,Nat.add_mul,Ce,Cs] using hnum
      have he := ih (q+1) f legacy (by dsimp only [Ce,Cs] at hcap; omega) hf
      have hs := ih q (fun S U => f (insert a S) U) (fun S U => legacy (insert a S) U)
        (by dsimp only [Ce,Cs] at hcap; omega) (fun S U => hf _ _)
      have hu := ih q (fun S U => f (insert a S) (insert a U))
        (fun S U => legacy (insert a S) (insert a U))
        (by dsimp only [Ce,Cs] at hcap; omega) (fun S U => hf _ _)
      have hab := SemiprimeWordFoldArithmetic.add_correct template J D (Ce*B) (Cs*B)
        _ _ he.2.1 hs.2.1 hd hden (by omega) he.2.2 hs.2.2
      have habc := SemiprimeWordFoldArithmetic.add_correct template J D (Ce*B+Cs*B) (Cs*B)
        _ _ hab.2.1 hu.2.1 hd hden hcap hab.2.2 hu.2.2
      refine ⟨?_,habc.2.1,?_⟩
      · change decode (SemiprimeWordFoldArithmetic.add template J
          (SemiprimeWordFoldArithmetic.add template J _ _) _).words=_
        rw [habc.1,hab.1,he.1,hs.1,hu.1]
        rfl
      · simpa only [supportRun,bump,List.length_cons,SemiprimeCounterEnumeration.callbacks,
          Nat.add_mul,Ce,Cs] using habc.2.2

/-- The exact signed Taylor support traversal, with one shared denominator
across all actual supports and summary terms. -/
theorem rawRun_correct {A : Type} [DecidableEq A] (template : List Bool) (J D B Cq : ℕ)
    (todo : List A) (f : Finset A → Finset A → JetReport)
    (legacy : Finset A → Finset A → SemiprimeFibreArrayExecution.Run)
    (hd : 0<D) (hden : D<2^template.length) (hB : B<2^template.length)
    (hnum : Cq*B<2^template.length)
    (hC : SemiprimeCounterEnumeration.callbacks todo.length (J-1) ≤ Cq)
    (hf : ∀ S U,decode (f S U).words=(legacy S U).jet.coefficients ∧
      Valid (f S U).words ∧ ArrayBound (decode (f S U).words) J D B) :
    decode (rawRun template J todo f).words=
      (SemiprimePacketArrayExecution.rawRun J todo legacy).jet.coefficients ∧
    Valid (rawRun template J todo f).words ∧
    ArrayBound (decode (rawRun template J todo f).words) J D (Cq*B) := by
  have hh := supportRun_correct template J D B todo (J-1) (signedFibre template J f)
    (SemiprimePacketArrayExecution.signedFibre J legacy) hd hden
    ((Nat.mul_le_mul_right B hC).trans_lt hnum)
    (signedFibre_correct template J D B f legacy hd hden hB hf)
  exact ⟨hh.1,hh.2.1,arrayBound_mono hh.2.2 (Nat.mul_le_mul_right B hC)⟩

/-- Exact physical word node, initialized only by ORIGINAL common group
representations and public finite traversal counts. All sum/product/support
fits follow from the derived packet width, never intermediate fit advice. -/
theorem node_correct {n F : ℕ} (template : List Bool) (b R s J P Y Cq DG BG : ℕ)
    (d : RuntimeDesign n F) (value : GroupCall d)
    (legacy : SemiprimeMaterializedGroupAdapter.GroupCall d)
    (hwidth : SemiprimeWordPacketWidth.packetWidth b R n F s J d.r P Y Cq ≤ template.length)
    (hd : 0<DG)
    (hDG : DG ≤ 2^(SemiprimeNativeGroupBitsHeight.exponent b R F s))
    (hBG : BG ≤ 2^(SemiprimeNativeGroupBitsHeight.exponent b R F s))
    (hP : ∀ g,2^(d.h g) ≤ P)
    (hY : summaryCount d.r d.h d.m d.W ≤ Y)
    (hC : SemiprimeCounterEnumeration.callbacks n (J-1) ≤ Cq)
    (hv : ∀ U g a,decode (value U g a).words=(legacy U g a).jet.coefficients ∧
      Valid (value U g a).words ∧ ArrayBound (decode (value U g a).words) J DG BG) :
    decode (node template J d value).words=
      (SemiprimeMaterializedGroupAdapter.node d J legacy).jet.coefficients ∧
    Valid (node template J d value).words ∧
    ArrayBound (decode (node template J d value).words) J (DG^d.r)
      (Cq*(Y*(SemiprimeWordPacketWidth.productBase J DG BG P)^(2*d.r))) := by
  let N := SemiprimeWordPacketWidth.productBase J DG BG P
  let k := SemiprimeWordPacketWidth.productExponent b R F s J P
  let caches := acquireHeads d.r d.h d.m d.C
  have hp := Nat.pow_le_pow_right (by decide : 0<2) hwidth
  have hden := (SemiprimeWordPacketWidth.head_denominator_lt b R n F s J d.r P Y Cq DG hDG).trans_le hp
  have hnum := (SemiprimeWordPacketWidth.head_numerator_lt b R n F s J d.r P Y Cq BG hBG).trans_le hp
  have hg := SemiprimeWordPacketWidth.productBase_guards J DG BG P
  have hn := SemiprimeWordPacketWidth.productBase_dyadic b R F s J P DG BG hDG hBG
  have hw := (SemiprimeWordPacketWidth.product_width b R n F s J d.r P Y Cq).trans_le hwidth
  have hdenF := (SemiprimeWordPacketWidth.fibre_denominator_lt b R n F s J d.r P Y Cq DG hDG).trans_le hp
  have hnumF := (SemiprimeWordPacketWidth.summary_numerator_lt b R n F s J d.r P Y Cq DG BG hDG hBG).trans_le hp
  have hnumC := (SemiprimeWordPacketWidth.support_numerator_lt b R n F s J d.r P Y Cq DG BG hDG hBG).trans_le hp
  have hf (S U : Finset (Fin n)) :
      decode (fibre template J d caches value S U).words=
        (SemiprimeMaterializedGroupAdapter.fibre d caches J legacy S U).jet.coefficients ∧
      Valid (fibre template J d caches value S U).words ∧
      ArrayBound (decode (fibre template J d caches value S U).words) J (DG^d.r) (Y*N^(2*d.r)) :=
    sumCached_correct template J d.r DG BG P N k Y d.h d.m d.W caches
      (fun g i => decide (d.grouping.symm ⟨g,i⟩ ∈ S)) (value U) (legacy U)
      hd hden hnum hP hg.1 hg.2.1 hg.2.2 hn hw hY hdenF hnumF (hv U)
  have hr := rawRun_correct template J (DG^d.r) (Y*N^(2*d.r)) Cq
    (List.ofFn (fun v : Fin n => v)) (fibre template J d caches value)
    (SemiprimeMaterializedGroupAdapter.fibre d caches J legacy) (pow_pos hd _) hdenF hnumF
    (by simpa only [Nat.mul_assoc] using hnumC)
    (by simpa only [List.length_ofFn] using hC) hf
  simpa only [node,SemiprimeMaterializedGroupAdapter.node,bump,
    SemiprimePacketArrayExecution.bump,caches,N] using hr

end RiemannGaussian.SemiprimeMaterializedWordFibre

