/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramMetadata
import RiemannGaussian.SemiprimeSourceWordIdEnvironmentBounds
import RiemannGaussian.SemiprimeSourceCompactBits

/-! # Direct original port codes and acquired compact physical keys
No original index scan, source word, score term or histogram answer is a runtime
field. Original typed owner/factor access and natural control keep their explicit
native stage. Encoding setup is conservatively magnitude-polynomial, not claimed
near-linear; compact output keys have logarithmic width for later lookup passes.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceHistogramPortKeys
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.LocalExpectation
open SemiprimeMaterializedWords SemiprimeBitArithmetic
open SemiprimeSourceHistogramMetadata
open SemiprimeReportPolynomialGrowth

/-- The exact original left/right variable order is acquired without index searches. -/
theorem indices_value (n F Q : ℕ) (arity : Fin F→ℕ) :
    (acquire n F Q arity).indices=
      (List.finRange n).map Sum.inl++(List.finRange F).map Sum.inr := by
  simp only [acquire,SemiprimePaidFiniteEnumerationLists.sum_value,finFast_value]

/-- A supplied injective relabelling preserves the original decidable scan. -/
theorem indexCode_map {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A→B) (hf : Function.Injective f) (xs : List A) (a : A) :
    indexCode (xs.map f) (f a)=indexCode xs a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [indexCode,List.map_cons,List.idxOf_cons] at ih ⊢
    by_cases h : x=a <;> simp [hf.eq_iff,h,ih]

/-- Generic decidable-index append law avoids a different structural Sum BEq. -/
theorem indexCode_append_mem {A : Type*} [DecidableEq A] (xs ys : List A) (a : A)
    (ha : a∈xs) : indexCode (xs++ys) a=indexCode xs a := by
  unfold indexCode
  exact List.idxOf_append_of_mem ha

/-- Generic absent-left append law for the original decidable-equality scan. -/
theorem indexCode_append_notMem {A : Type*} [DecidableEq A] (xs ys : List A) (a : A)
    (ha : a∉xs) : indexCode (xs++ys) a=xs.length+indexCode ys a := by
  unfold indexCode
  exact List.idxOf_append_of_notMem ha

/-- Every actual original owner code is its native vertex index. -/
theorem indexCode_inl (n F Q : ℕ) (arity : Fin F→ℕ) (v : Fin n) :
    indexCode (acquire n F Q arity).indices (.inl v)=v.val := by
  rw [indices_value,indexCode_append_mem _ _ _ (by simp)]
  rw [indexCode_map Sum.inl Sum.inl_injective]
  exact List.idxOf_finRange v

/-- Every actual original factor code is its native factor index plus n. -/
theorem indexCode_inr (n F Q : ℕ) (arity : Fin F→ℕ) (e : Fin F) :
    indexCode (acquire n F Q arity).indices (.inr e)=n+e.val := by
  rw [indices_value,indexCode_append_notMem _ _ _ (by simp)]
  rw [List.length_map,List.length_finRange,indexCode_map Sum.inr Sum.inr_injective]
  exact congrArg (fun k => n+k) (List.idxOf_finRange e)

/-- Acquire actual Boolean key digits and remove high zeros, retaining both reports. -/
def encodeKey (k : ℕ) : SemiprimeSourceCompactBits.Report :=
  let raw := SemiprimeSourceWordIdEnvironment.acquireKey k
  let out := SemiprimeSourceCompactBits.trim raw.value
  ⟨out.bits,raw.work+out.clock+3⟩

/-- Exact encoded key value without supplied digits. -/
theorem encodeKey_value (k : ℕ) : bitValue (encodeKey k).bits=k := by
  simp only [encodeKey,SemiprimeSourceCompactBits.trim_value,
    SemiprimeSourceWordIdEnvironment.acquireKey_value]

/-- Every actual key is compact, including the empty zero key. -/
theorem encodeKey_compact (k : ℕ) : SemiprimeSourceCompactBits.Compact (encodeKey k).bits :=
  SemiprimeSourceCompactBits.trim_compact _

/-- Compact original code width used by subsequent physical dictionary passes. -/
def keyWidth (N : ℕ) : ℕ := Nat.clog 2 (N+1)

/-- Width comes from the actual original code cap, not intermediate encoding advice. -/
theorem encodeKey_length (k N : ℕ) (hk : k≤N) :
    (encodeKey k).bits.length≤keyWidth N := by
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ (encodeKey_compact k)
  rw [encodeKey_value]
  have hp := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (N+1)
  unfold keyWidth
  omega

/-- Conservative full key-encoding setup budget; no logarithmic encoder claim. -/
def encodeBudget (N : ℕ) : ℕ := 20*(N+1)^2+6*(N+1)+6

/-- Both actual digit acquisition and the high-zero scan remain in setup work. -/
theorem encodeKey_clock (k N : ℕ) (hk : k≤N) :
    (encodeKey k).clock≤encodeBudget N := by
  have hc := SemiprimeSourceWordIdEnvironment.acquireKey_work k
  have hl := SemiprimeSourceWordIdEnvironmentBounds.acquireKey_length k
  have hm : 20*(k+1)^2≤20*(N+1)^2 := by gcongr
  have ht := SemiprimeSourceCompactBits.trim_clock
    (SemiprimeSourceWordIdEnvironment.acquireKey k).value
  simp only [encodeKey,encodeBudget]
  omega

/-- Cached original native codes and their acquired compact physical key payloads. -/
structure PortRecord where
  /-- Original left-variable code. -/
  ownerCode : ℕ
  /-- Original right-factor code. -/
  factorCode : ℕ
  /-- Actual compact owner key. -/
  ownerKey : List Bool
  /-- Actual compact factor key. -/
  factorKey : List Bool

/-- Acquire one original port record; owner/factor access is an explicit native stage. -/
def record {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) : Run PortRecord :=
  let v := owner i
  let a := encodeKey v.val
  let b := encodeKey (n+i.1.val)
  ⟨⟨v.val,n+i.1.val,a.bits,b.bits⟩,a.clock+b.clock+8⟩

/-- Direct records equal the original mathematical index codes, without runtime scans. -/
theorem record_codes {n F Q : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) :
    (record owner i).value.ownerCode=indexCode (acquire n F Q arity).indices (.inl (owner i)) ∧
    (record owner i).value.factorCode=indexCode (acquire n F Q arity).indices (.inr i.1) := by
  rw [indexCode_inl,indexCode_inr]
  exact ⟨rfl,rfl⟩

/-- Both physical key values are the original cached native codes. -/
theorem record_values {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) :
    bitValue (record owner i).value.ownerKey=(record owner i).value.ownerCode ∧
    bitValue (record owner i).value.factorKey=(record owner i).value.factorCode := by
  exact ⟨encodeKey_value _,encodeKey_value _⟩

/-- Original dimensions derive both compact record widths and canonicality. -/
theorem record_good {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) :
    SemiprimeSourceCompactBits.Compact (record owner i).value.ownerKey ∧
    SemiprimeSourceCompactBits.Compact (record owner i).value.factorKey ∧
    (record owner i).value.ownerKey.length≤keyWidth (n+F) ∧
    (record owner i).value.factorKey.length≤keyWidth (n+F) := by
  have hv := (owner i).isLt
  have he := i.1.isLt
  exact ⟨encodeKey_compact _,encodeKey_compact _,
    encodeKey_length _ _ (by omega),encodeKey_length _ _ (by omega)⟩

/-- One conservative actual original-port acquisition budget. -/
def recordBudget (N : ℕ) : ℕ := 2*encodeBudget N+8

/-- Record setup pays both complete encoder reports and native record construction. -/
theorem record_work {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : (e : Fin F)×Fin (arity e)) :
    (record owner i).work≤recordBudget (n+F) := by
  have hv := (owner i).isLt
  have he := i.1.isLt
  have ha := encodeKey_clock (owner i).val (n+F) (by omega)
  have hb := encodeKey_clock (n+i.1.val) (n+F) (by omega)
  simp only [record,recordBudget]
  omega

/-- Cache every original record once in original incidence-list order. -/
def acquirePorts {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    List ((e : Fin F)×Fin (arity e))→Run (List PortRecord)
  | [] => ⟨[],1⟩
  | i::is =>
    let row := record owner i
    let rest := acquirePorts owner is
    ⟨row.value::rest.value,row.work+rest.work+3⟩

/-- Exact original port occurrences/order, without deduplication or source rereads. -/
theorem acquirePorts_value {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (is : List ((e : Fin F)×Fin (arity e))) :
    (acquirePorts owner is).value=is.map (fun i => (record owner i).value) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [acquirePorts,List.map_cons,ih]

/-- Every actual record encoder and list constructor remains paid. -/
theorem acquirePorts_work {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (is : List ((e : Fin F)×Fin (arity e))) :
    (acquirePorts owner is).work ≤ is.length*(recordBudget (n+F)+3)+1 := by
  induction is with
  | nil => simp [acquirePorts]
  | cons i is ih =>
    have h := record_work owner i
    simp only [acquirePorts,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Original sparse metadata and its actual once-acquired port cache. -/
structure Acquired (n F Q : ℕ) (arity : Fin F→ℕ) where
  /-- Actual metadata; no word functions or quadratic score fields. -/
  metadata : Metadata n F Q arity
  /-- Every compact original port record. -/
  records : List PortRecord
  /-- Metadata, encoding, normalization and constructor work. -/
  clock : ℕ

/-- Acquire metadata once and cache its original port records once. -/
def acquireOriginal (n F Q : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) : Acquired n F Q arity :=
  let data := acquire n F Q arity
  let rows := acquirePorts owner data.incidences
  ⟨data,rows.value,data.clock+rows.work+3⟩

/-- Complete setup bound is conservative in original N, not falsely near-linear. -/
def budget (n F Q M : ℕ) : ℕ :=
  SemiprimeSourceHistogramMetadata.budget n F Q M+M*(recordBudget (n+F)+3)+4

/-- Actual acquired metadata supplies M internally; no record-count or width advice. -/
theorem acquireOriginal_clock (n F Q : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquireOriginal n F Q arity owner).clock≤budget n F Q (∑ e,arity e) := by
  have hm := acquire_clock n F Q arity
  have hs := (sizes n F Q arity).2.2.1
  have hp := acquirePorts_work owner (acquire n F Q arity).incidences
  rw [hs] at hp
  simp only [acquireOriginal,budget]
  omega


/-- The returned metadata is the actually acquired sparse original metadata. -/
theorem acquireOriginal_metadata (n F Q : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquireOriginal n F Q arity owner).metadata=acquire n F Q arity := rfl

/-- The actual cache contains every original port record in its original order. -/
theorem acquireOriginal_records (n F Q : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquireOriginal n F Q arity owner).records=
      (acquire n F Q arity).incidences.map (fun i => (record owner i).value) :=
  acquirePorts_value owner _

/-- The cached record count is the actual total original incidence count. -/
theorem acquireOriginal_length (n F Q : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquireOriginal n F Q arity owner).records.length=∑ e,arity e := by
  rw [acquireOriginal_records,List.length_map]
  exact (sizes n F Q arity).2.2.1

/-- Every actually acquired cached record has exact physical values and compact
original-dimension width; there is no supplied record/width representation. -/
theorem acquireOriginal_good (n F Q : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (row : PortRecord) (hr : row∈(acquireOriginal n F Q arity owner).records) :
    bitValue row.ownerKey=row.ownerCode ∧ bitValue row.factorKey=row.factorCode ∧
    SemiprimeSourceCompactBits.Compact row.ownerKey ∧
    SemiprimeSourceCompactBits.Compact row.factorKey ∧
    row.ownerKey.length≤keyWidth (n+F) ∧ row.factorKey.length≤keyWidth (n+F) := by
  rw [acquireOriginal_records] at hr
  rcases List.mem_map.mp hr with ⟨i,_,rfl⟩
  exact ⟨(record_values owner i).1,(record_values owner i).2,record_good owner i⟩

/-- Original source owner/factor codes are recovered from the actual cached records. -/
theorem acquireOriginal_codes (n F Q : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ((acquireOriginal n F Q arity owner).records.map (fun row => (row.ownerCode,row.factorCode)))=
      (acquire n F Q arity).incidences.map (fun i =>
        (indexCode (acquire n F Q arity).indices (.inl (owner i)),
          indexCode (acquire n F Q arity).indices (.inr i.1))) := by
  rw [acquireOriginal_records,List.map_map]
  apply List.map_congr_left
  intro i _
  exact Prod.ext (record_codes (Q:=Q) owner i).1 (record_codes (Q:=Q) owner i).2


/-- A fixed original-dimension polynomial pays the complete acquired port-key setup. -/
theorem budget_monomial : ∃ C k : ℕ,∀ n F Q M S,
    n≤S → F≤S → Q≤S → M≤S → budget n F Q M≤C*(S+1)^k := by
  have hp : Bound (fun S => budget S S S S) := by
    simp only [budget,recordBudget,encodeBudget,SemiprimeSourceHistogramMetadata.budget]
    boundArithmetic
  obtain ⟨C,k,h⟩ := hp
  refine ⟨C,k,?_⟩
  intro n F Q M S hn hF hQ hM
  apply le_trans _ (h S)
  simp only [budget,recordBudget,encodeBudget,SemiprimeSourceHistogramMetadata.budget]
  gcongr

end RiemannGaussian.SemiprimeSourceHistogramPortKeys
