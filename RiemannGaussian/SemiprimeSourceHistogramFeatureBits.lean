/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramPortKeys
import RiemannGaussian.SemiprimeSourceHistogramKeyBits
import RiemannGaussian.SemiprimeSourceHistogramSquares
import RiemannGaussian.SemiprimeSourceCompactWordIds
import RiemannGaussian.SemiprimeSourceIncidenceHistogram

/-! # Executed filtered joint keys for the sixteen original source features
Runtime inputs are cached physical port records and an actual dict trie. No
source Word functions, semantic labels, count answers or histogram bins occur
on the data path. Dictionary representation assumptions are erased intermediate
proof obligations for the original dict/bank adapter, not runtime advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeSourceHistogramFeatureBits
open SemiprimeMaterializedWords SemiprimeBitArithmetic
open SemiprimeSourceCompactBits (Compact Report)
open SemiprimeSourceHistogramPortKeys (PortRecord)
open SemiprimeSourceHistogramTrie (Trie)
open SemiprimeSourceIncidenceHistogram (Feature)

/-- Native finite-dict interval test; no remaining-list scan is executed. -/
def active (k s code : ℕ) : Bool := decide (k≤code ∧ code<k+s)

/-- Actual zero/one feature eligibility, before any component-label acquisition. -/
def eligible (k s : ℕ) (f : Feature) (code : ℕ) : Bool :=
  if f=0 then true else if f=1 then active k s code else !(active k s code)

/-- Acquire only the component required by this fixed feature.
The variable key is copied; a fixed label is physically looked up and copied. -/
def component (dict : Trie) (f : Feature) (key : List Bool) : Report :=
  if f=1 then SemiprimeSourceCompactBits.copy key
  else if f=2 then SemiprimeSourceHistogramTrie.lookup dict key else ⟨[],1⟩

/-- Mathematical component bytes used only in refinement statements. -/
def componentKey (dict : Trie) (f : Feature) (key : List Bool) : List Bool :=
  if f=1 then key else if f=2 then SemiprimeSourceHistogramTrie.stored dict key else []

/-- Exact output of the actually acquired component. -/
theorem component_bits (dict : Trie) (f : Feature) (key : List Bool) :
    (component dict f key).bits=componentKey dict f key := by
  by_cases h1 : f=1 <;> by_cases h2 : f=2 <;>
    simp [component,componentKey,h1,h2,SemiprimeSourceCompactBits.copy_bits,
      SemiprimeSourceHistogramTrie.lookup_bits]

/-- Proof-only original joint-byte key; the runtime executes pair, not frame. -/
def jointBytes (dict : Trie) (f g : Feature) (row : PortRecord) : List Bool :=
  SemiprimeSourceHistogramKeyBits.frame
    (componentKey dict f row.ownerKey) (componentKey dict g row.factorKey)

/-- Both masks are determined before any labels are read. Rejected ports skip
both label lookups and framing; all executed component/framing reports remain. -/
def one (dict : Trie) (k s : ℕ) (f g : Feature) (row : PortRecord) :
    Run (Option (List Bool)) :=
  let own := eligible k s f row.ownerCode
  let fac := eligible k s g row.factorCode
  if own && fac then
    let a := component dict f row.ownerKey
    let b := component dict g row.factorKey
    let out := SemiprimeSourceHistogramKeyBits.pair a.bits b.bits
    ⟨some out.bits,a.clock+b.clock+out.clock+20⟩
  else ⟨none,12⟩

/-- Actual returned byte key, with no supplied joined-key answer. -/
theorem one_value (dict : Trie) (k s : ℕ) (f g : Feature) (row : PortRecord) :
    (one dict k s f g row).value=
      if eligible k s f row.ownerCode && eligible k s g row.factorCode
      then some (jointBytes dict f g row) else none := by
  by_cases hm : (eligible k s f row.ownerCode && eligible k s g row.factorCode)=true
  · simp [one,hm,SemiprimeSourceHistogramKeyBits.pair_bits,component_bits,jointBytes]
  · simp [one,hm]

/-- Traverse the actual cache once and keep only physically acquired eligible keys. -/
def produce (dict : Trie) (k s : ℕ) (f g : Feature) :
    List PortRecord→Run (List (List Bool))
  | [] => ⟨[],1⟩
  | row::rows =>
    let first := one dict k s f g row
    let rest := produce dict k s f g rows
    match first.value with
    | none => ⟨rest.value,first.work+rest.work+3⟩
    | some key => ⟨key::rest.value,first.work+rest.work+4⟩

/-- The produced list is the derived actual filtered cache, with all multiplicities. -/
theorem produce_value (dict : Trie) (k s : ℕ) (f g : Feature) (rows : List PortRecord) :
    (produce dict k s f g rows).value=
      (rows.filter (fun row => eligible k s f row.ownerCode && eligible k s g row.factorCode)).map
        (jointBytes dict f g) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [produce,one_value]
    by_cases hm : (eligible k s f row.ownerCode && eligible k s g row.factorCode)=true
    · simp [hm,ih]
    · simp [hm,ih]

/-- Actual key production followed by the executed sparse square-count fold. -/
def acquire (dict : Trie) (k s : ℕ) (f g : Feature) (rows : List PortRecord) :
    SemiprimeSourceHistogramSquares.State :=
  let keys := produce dict k s f g rows
  let out := SemiprimeSourceHistogramSquares.acquire keys.value
  ⟨out.trie,out.bits,keys.work+out.clock+3⟩

/-- The native finite interval is exactly the original remaining-key range. -/
theorem active_value (k s code : ℕ) : active k s code=decide (code∈List.range' k s) := by
  unfold active
  congr 1
  simp only [List.mem_range',one_mul]
  apply propext
  constructor
  · intro h
    exact ⟨code-k,by omega,by omega⟩
  · rintro ⟨i,hi,he⟩
    omega

/-- The executed mask is the original feature's literal zero/one weight. -/
theorem eligible_weight (k s : ℕ) (f : Feature) (code : ℕ) :
    SemiprimeSourceIncidenceHistogram.featureWeight (List.range' k s) f code=
      if eligible k s f code then (1:ℚ) else 0 := by
  by_cases h0 : f=0 <;> by_cases h1 : f=1 <;>
    by_cases ha : code∈List.range' k s <;>
    simp [SemiprimeSourceIncidenceHistogram.featureWeight,eligible,active_value,h0,h1,ha]

/-- Both masks together are exactly the original joint eligibility predicate. -/
theorem joint_eligible (k s : ℕ) (f g : Feature) (row : PortRecord) :
    (eligible k s f row.ownerCode && eligible k s g row.factorCode)=
      decide (SemiprimeSourceIncidenceHistogram.jointWeight (List.range' k s)
        PortRecord.ownerCode PortRecord.factorCode f g row=1) := by
  unfold SemiprimeSourceIncidenceHistogram.jointWeight
  rw [eligible_weight,eligible_weight]
  cases eligible k s f row.ownerCode <;> cases eligible k s g row.factorCode <;> simp

/-- Exact actual feature-filter list, without a supplied selected-port list. -/
theorem produce_selected (dict : Trie) (k s : ℕ) (f g : Feature) (rows : List PortRecord) :
    (produce dict k s f g rows).value=
      (SemiprimeSourceIncidenceHistogram.eligiblePorts rows (List.range' k s)
        PortRecord.ownerCode PortRecord.factorCode f g).map (jointBytes dict f g) := by
  rw [produce_value]
  simp only [SemiprimeSourceIncidenceHistogram.eligiblePorts,joint_eligible]

/-- Original-dimensional represented physical variable key. -/
def KeyRep (N code : ℕ) (key : List Bool) : Prop :=
  Compact key ∧ bitValue key=code ∧ code<N

/-- Both physical keys of one actually acquired original port. -/
def RecordRep (N : ℕ) (row : PortRecord) : Prop :=
  KeyRep N row.ownerCode row.ownerKey ∧ KeyRep N row.factorCode row.factorKey

/-- Internal equality representation of a concrete dict dictionary.
The original dict/compact-bank adapter discharges this erased relation. -/
def DictRep {W : Type*} (dict : Trie) (ω : ℕ→W) (N : ℕ) : Prop :=
  ∀ a b ka kb,KeyRep N a ka→KeyRep N b kb→
    (SemiprimeSourceHistogramTrie.stored dict ka=SemiprimeSourceHistogramTrie.stored dict kb ↔ ω a=ω b)

/-- Each fixed feature's actual byte equality matches its original semantic key. -/
theorem component_eq_iff {W : Type*} (dict : Trie) (ω : ℕ→W) (N : ℕ)
    (hd : DictRep dict ω N) (f : Feature) (a b : ℕ) (ka kb : List Bool)
    (ha : KeyRep N a ka) (hb : KeyRep N b kb) :
    componentKey dict f ka=componentKey dict f kb ↔
      SemiprimeSourceIncidenceHistogram.featureKey ω f a=SemiprimeSourceIncidenceHistogram.featureKey ω f b := by
  by_cases h1 : f=1
  · subst f
    simp only [componentKey,ite_true,SemiprimeSourceIncidenceHistogram.featureKey,Sum.inl.injEq]
    constructor
    · intro h
      exact ha.2.1.symm.trans ((congrArg bitValue h).trans hb.2.1)
    · intro h
      exact SemiprimeSourceCompactWordIds.compact_value_injective ka kb ha.1 hb.1
        (ha.2.1.trans (h.trans hb.2.1.symm))
  · by_cases h2 : f=2
    · subst f
      simpa only [componentKey,SemiprimeSourceIncidenceHistogram.featureKey,h1,ite_false,
        ite_true,Sum.inr.injEq] using hd a b ka kb ha hb
    · simp [componentKey,SemiprimeSourceIncidenceHistogram.featureKey,h1,h2]

/-- Framing preserves exactly both component equalities for a fixed feature pair. -/
theorem joint_eq_iff {W : Type*} (dict : Trie) (ω : ℕ→W) (N : ℕ)
    (hd : DictRep dict ω N) (f g : Feature) (a b : PortRecord)
    (ha : RecordRep N a) (hb : RecordRep N b) :
    jointBytes dict f g a=jointBytes dict f g b ↔
      SemiprimeSourceIncidenceHistogram.jointKey ω PortRecord.ownerCode PortRecord.factorCode f g a=
      SemiprimeSourceIncidenceHistogram.jointKey ω PortRecord.ownerCode PortRecord.factorCode f g b := by
  unfold jointBytes
  rw [show (SemiprimeSourceHistogramKeyBits.frame
      (componentKey dict f a.ownerKey) (componentKey dict g a.factorKey)=
      SemiprimeSourceHistogramKeyBits.frame (componentKey dict f b.ownerKey) (componentKey dict g b.factorKey)) ↔
      componentKey dict f a.ownerKey=componentKey dict f b.ownerKey ∧
      componentKey dict g a.factorKey=componentKey dict g b.factorKey from by
        constructor
        · exact SemiprimeSourceHistogramKeyBits.frame_injective _ _ _ _
        · rintro ⟨h1,h2⟩;rw [h1,h2]]
  rw [component_eq_iff dict ω N hd f _ _ _ _ ha.1 hb.1,
    component_eq_iff dict ω N hd g _ _ _ _ ha.2 hb.2]
  simp only [SemiprimeSourceIncidenceHistogram.jointKey,Prod.mk.injEq]


/-- Pair scans of mapped physical records preserve the actual occurrence list. -/
theorem pairs_map {A B R : Type*} [AddCommMonoid R] (xs : List A) (h : A→B) (F : B→B→R) :
    SemiprimeSourceHistogramGrouping.pairs (xs.map h) F=
      SemiprimeSourceHistogramGrouping.pairs xs (fun a b => F (h a) (h b)) := by
  simp only [SemiprimeSourceHistogramGrouping.pairs,List.map_map,Function.comp_def]

/-- Actual square-count acquisition equals the original per-feature histogram.
Only the erased intermediate dictionary representation is assumed here. -/
theorem acquire_value_rows {W : Type*} [DecidableEq W] (dict : Trie) (ω : ℕ→W) (N : ℕ)
    (hd : DictRep dict ω N) (k s : ℕ) (f g : Feature) (rows : List PortRecord)
    (hr : ∀ row∈rows,RecordRep N row) :
    ((bitValue (acquire dict k s f g rows).bits:ℕ):ℚ)=
      SemiprimeSourceIncidenceHistogram.histogram rows (List.range' k s) ω
        PortRecord.ownerCode PortRecord.factorCode f g := by
  let selected := SemiprimeSourceIncidenceHistogram.eligiblePorts rows (List.range' k s)
    PortRecord.ownerCode PortRecord.factorCode f g
  have hs (a : PortRecord) (ha : a∈selected) : RecordRep N a :=
    hr a (List.mem_of_mem_filter ha)
  calc
    _=((SemiprimeSourceHistogramGrouping.pairs selected (fun a b =>
      if jointBytes dict f g a=jointBytes dict f g b then (1:ℕ) else 0):ℕ):ℚ) := by
        simp only [acquire,SemiprimeSourceHistogramSquares.acquire_value,produce_selected,
          SemiprimeSourceHistogramSquares.collisions,pairs_map,selected]
    _=((SemiprimeSourceHistogramGrouping.pairs selected (fun a b =>
      if SemiprimeSourceIncidenceHistogram.jointKey ω PortRecord.ownerCode PortRecord.factorCode f g a=
        SemiprimeSourceIncidenceHistogram.jointKey ω PortRecord.ownerCode PortRecord.factorCode f g b
      then (1:ℕ) else 0):ℕ):ℚ) := by
        congr 1
        unfold SemiprimeSourceHistogramGrouping.pairs
        congr 1
        apply List.map_congr_left
        intro a ha
        congr 1
        apply List.map_congr_left
        intro b hb
        dsimp only
        simp only [joint_eq_iff dict ω N hd f g a b (hs a ha) (hs b hb)]
    _= _ := by
      have h:=congrArg (fun z : ℕ => (z:ℚ))
        (SemiprimeSourceHistogramGrouping.pair_grouping
          (SemiprimeSourceIncidenceHistogram.jointKey ω PortRecord.ownerCode PortRecord.factorCode f g) selected)
      rw [SemiprimeSourceIncidenceHistogram.histogram_filtered]
      simpa only [SemiprimeSourceHistogramGrouping.pairs,Nat.cast_sum,Nat.cast_pow] using h

/-- Histograms commute with the actual record map, including repeated ports. -/
theorem histogram_map {I : Type*} {W : Type*} [DecidableEq W] (xs : List I)
    (row : I→PortRecord) (remaining : List ℕ) (ω : ℕ→W) (f g : Feature) :
    SemiprimeSourceIncidenceHistogram.histogram (xs.map row) remaining ω
      PortRecord.ownerCode PortRecord.factorCode f g=
    SemiprimeSourceIncidenceHistogram.histogram xs remaining ω
      (fun i => (row i).ownerCode) (fun i => (row i).factorCode) f g := by
  rw [← SemiprimeSourceIncidenceHistogram.feature_grouping,
    ← SemiprimeSourceIncidenceHistogram.feature_grouping,pairs_map]

/-- Actual original record acquisition supplies every represented variable key. -/
theorem acquirePorts_rep {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (ports : List ((e : Fin F)×Fin (arity e))) :
    ∀ row∈(SemiprimeSourceHistogramPortKeys.acquirePorts owner ports).value,RecordRep (n+F) row := by
  intro row hr
  rw [SemiprimeSourceHistogramPortKeys.acquirePorts_value] at hr
  rcases List.mem_map.mp hr with ⟨i,_,rfl⟩
  have hg:=SemiprimeSourceHistogramPortKeys.record_good owner i
  have hv:=SemiprimeSourceHistogramPortKeys.record_values owner i
  have ho:=(owner i).isLt
  have hf:=i.1.isLt
  exact ⟨⟨hg.1,hv.1,by change (owner i).val<n+F;omega⟩,
    ⟨hg.2.1,hv.2,by change n+i.1.val<n+F;omega⟩⟩

/-- The actual original cached ports produce exactly their original feature
histogram. No represented rows, semantic key bytes or count answer is supplied. -/
theorem acquirePorts_histogram_value {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (ports : List ((e : Fin F)×Fin (arity e))) {W : Type*} [DecidableEq W]
    (dict : Trie) (ω : ℕ→W) (hd : DictRep dict ω (n+F))
    (k s : ℕ) (f g : Feature) :
    ((bitValue (acquire dict k s f g
      (SemiprimeSourceHistogramPortKeys.acquirePorts owner ports).value).bits:ℕ):ℚ)=
      SemiprimeSourceIncidenceHistogram.histogram ports (List.range' k s) ω
        (fun i => (owner i).val) (fun i => n+i.1.val) f g := by
  rw [acquire_value_rows dict ω (n+F) hd k s f g _ (acquirePorts_rep owner ports)]
  rw [SemiprimeSourceHistogramPortKeys.acquirePorts_value,histogram_map]
  rfl

end RiemannGaussian.SemiprimeSourceHistogramFeatureBits
