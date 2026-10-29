/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryChildBits
import RiemannGaussian.SemiprimeD1NetworkStateResources
import RiemannGaussian.SemiprimeSourceHistogramPortKeys

/-! # Actual Boolean-addressed literal network owner reads
The setup traverses literal rows and acquires every owner key. Subsequent reads
scan/copy physical rows and operate on physical address words. Native Fin payload
and digit acquisition in setup remain an explicit interface, not a tape theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1NetworkOwnerBits
open SemiprimeBitArithmetic SemiprimeD1TensorNetwork
open SemiprimeSourceHistogramPortKeys SemiprimeD1RecoveryChildBits

/-- Acquired physical owner-row cache and retained setup report. -/
structure Bank where
  /-- Actual nested Boolean owner words. -/
  rows : List (List (List Bool))
  /-- All setup encoder and traversal reports. -/
  clock : ℕ

/-- Acquire every literal owner payload once, preserving repeated ports. -/
def acquireRow {n : ℕ} : List (Fin n) → RowReport
  | [] => ⟨[],1⟩
  | v::vs =>
    let key:=encodeKey v.val
    let tail:=acquireRow vs
    ⟨key.bits::tail.words,key.clock+tail.clock+4⟩

/-- Acquire all literal factor rows, including empty factors. -/
def acquire {n : ℕ} : Rows n → Bank
  | [] => ⟨[],1⟩
  | row::rows =>
    let head:=acquireRow row
    let tail:=acquire rows
    ⟨head.words::tail.rows,head.clock+tail.clock+4⟩

/-- Setup has the exact literal encoded owner sequence. -/
theorem acquireRow_words {n : ℕ} (row : List (Fin n)) :
    (acquireRow row).words=row.map (fun v => (encodeKey v.val).bits) := by
  induction row with
  | nil => rfl
  | cons v vs ih => simp only [acquireRow,List.map_cons,ih]

/-- No factor or repeated occurrence disappears during acquisition. -/
theorem acquire_rows {n : ℕ} (rows : Rows n) :
    (acquire rows).rows=rows.map (fun row => row.map (fun v => (encodeKey v.val).bits)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [acquire,List.map_cons,acquireRow_words,ih]

/-- Actual read: both addresses are Boolean words, never native lookup callbacks. -/
def read (bank : Bank) (factor port : List Bool) : SemiprimeD1RecoveryIntegerBits.UnsignedReport :=
  SemiprimeD1RecoveryChildBits.read bank.rows factor port

/-- Exact owner lookup at every original typed incidence. -/
theorem read_owner {n : ℕ} (rows : Rows n) (i : Incidence rows)
    (factor port : List Bool) (hf : bitValue factor=i.1.val) (hp : bitValue port=i.2.val) :
    bitValue (read (acquire rows) factor port).bits=(owner rows i).val := by
  simp only [read,read_bits,acquire_rows,hf,hp,List.getElem?_map]
  rw [List.getElem?_eq_getElem i.1.isLt]
  simp only [Option.map_some,Option.getD_some]
  rw [List.getElem?_map,List.getElem?_eq_getElem i.2.isLt]
  simp only [Option.map_some,Option.getD_some,encodeKey_value]
  rfl

/-- Every acquired owner word has derived compact width. -/
theorem acquire_shape {n : ℕ} (rows : Rows n) (A : ℕ)
    (hr : ∀ row∈rows,row.length ≤ A) :
    ∀ row∈(acquire rows).rows,row.length ≤ A ∧
      ∀ key∈row,key.length ≤ keyWidth n := by
  rw [acquire_rows]
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨original,ho,rfl⟩
  refine ⟨by simpa using hr original ho,?_⟩
  intro key hk
  rcases List.mem_map.mp hk with ⟨v,hv,rfl⟩
  exact encodeKey_length v.val n (Nat.le_of_lt v.isLt)

/-- All scalar-digit acquisition reports and list cells are retained in setup. -/
theorem acquireRow_clock {n : ℕ} (row : List (Fin n)) :
    (acquireRow row).clock ≤ row.length*(encodeBudget n+4)+1 := by
  induction row with
  | nil => simp [acquireRow]
  | cons v vs ih =>
    have h:=encodeKey_clock v.val n (Nat.le_of_lt v.isLt)
    simp only [acquireRow,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- A closed setup bound in the actual literal network dimensions. -/
theorem acquire_clock {n : ℕ} (rows : Rows n) :
    (acquire rows).clock ≤ rows.flatten.length*(encodeBudget n+4)+5*rows.length+1 := by
  induction rows with
  | nil => simp [acquire]
  | cons row rows ih =>
    have h:=acquireRow_clock row
    simp only [acquire,List.flatten_cons,List.length_append,List.length_cons]
    nlinarith

/-- Boolean-addressed reading pays all visited owner payloads and decrements. -/
theorem read_clock {n : ℕ} (rows : Rows n) (factor port : List Bool) (A B : ℕ)
    (hB : 1 ≤ B) (hf : factor.length ≤ B) (hp : port.length ≤ B)
    (hr : ∀ row∈rows,row.length ≤ A) :
    (read (acquire rows) factor port).clock ≤
      (rows.length+1)*(A*(4*keyWidth n+4)+15*B+40)+
      (A+1)*(4*keyWidth n+15*B+30)+4 := by
  have h:=SemiprimeD1RecoveryChildBits.read_clock (acquire rows).rows factor port
    A (keyWidth n) B hB hf hp (acquire_shape rows A hr)
  simpa only [read,acquire_rows,List.length_map] using h

/-- Any literal factor row is bounded by the actual total occurrence count. -/
theorem row_length_le_total {n : ℕ} (rows : Rows n) :
    ∀ row∈rows,row.length ≤ rows.flatten.length := by
  induction rows with
  | nil => simp
  | cons x xs ih =>
    intro row hr
    rcases List.mem_cons.mp hr with h | h
    · subst row; simp only [List.flatten_cons,List.length_append]; omega
    · have hh:=ih row h
      simp only [List.flatten_cons,List.length_append]; omega

/-- Native incidence descriptors acquire physical addresses once per query. -/
def query (bank : Bank) (factor port : ℕ) : SemiprimeD1RecoveryIntegerBits.UnsignedReport :=
  let f:=encodeKey factor
  let p:=encodeKey port
  let out:=read bank f.bits p.bits
  ⟨out.bits,f.clock+p.clock+out.clock+6⟩

/-- Closed owner refinement: no supplied address, serialized row or owner answer. -/
theorem query_owner {n : ℕ} (rows : Rows n) (i : Incidence rows) :
    bitValue (query (acquire rows) i.1.val i.2.val).bits=(owner rows i).val :=
  read_owner rows i _ _ (encodeKey_value _) (encodeKey_value _)

/-- One fixed polynomial for actual setup and read dimensions. -/
def queryBudget (S : ℕ) : ℕ :=
  2*encodeBudget S+(S+1)*(S*(4*(S+1)+4)+15*(S+1)+40)+
    (S+1)*(4*(S+1)+15*(S+1)+30)+10

/-- Compact key width is bounded without a magnitude-as-log assumption. -/
theorem keyWidth_le (n S : ℕ) (h : n ≤ S) : keyWidth n ≤ S+1 := by
  unfold keyWidth
  apply Nat.clog_le_of_le_pow
  exact (Nat.add_le_add_right h 1).trans (Nat.le_of_lt Nat.lt_two_pow_self)

/-- Original-state dimensions discharge every row and address width internally. -/
theorem query_clock {n : ℕ} (rows : Rows n) (i : Incidence rows) (S : ℕ)
    (hn : n ≤ S) (hF : rows.length ≤ S) (hM : rows.flatten.length ≤ S) :
    (query (acquire rows) i.1.val i.2.val).clock ≤ queryBudget S := by
  have hfi : i.1.val ≤ S := (Nat.le_of_lt i.1.isLt).trans hF
  have hpi : i.2.val ≤ S := (Nat.le_of_lt i.2.isLt).trans
    ((row_length_le_total rows _ (List.getElem_mem i.1.isLt)).trans hM)
  have hf:=encodeKey_clock i.1.val S hfi
  have hp:=encodeKey_clock i.2.val S hpi
  have hfw: (encodeKey i.1.val).bits.length ≤ S+1 :=
    (encodeKey_length _ S hfi).trans (keyWidth_le S S le_rfl)
  have hpw: (encodeKey i.2.val).bits.length ≤ S+1 :=
    (encodeKey_length _ S hpi).trans (keyWidth_le S S le_rfl)
  have hr:=read_clock rows (encodeKey i.1.val).bits (encodeKey i.2.val).bits S (S+1)
    (by omega) hfw hpw (fun row hrow => (row_length_le_total rows row hrow).trans hM)
  have hkey:=keyWidth_le n S hn
  have hr' : (read (acquire rows) (encodeKey i.1.val).bits (encodeKey i.2.val).bits).clock ≤
      (S+1)*(S*(4*(S+1)+4)+15*(S+1)+40)+
      (S+1)*(4*(S+1)+15*(S+1)+30)+4 := by
    apply hr.trans
    gcongr
  unfold query queryBudget
  dsimp only
  omega

/-- Cache setup has a fixed polynomial original-state envelope. -/
theorem acquire_clock_uniform {n : ℕ} (rows : Rows n) (S : ℕ)
    (hn : n ≤ S) (hF : rows.length ≤ S) (hM : rows.flatten.length ≤ S) :
    (acquire rows).clock ≤ S*(encodeBudget S+4)+5*S+1 := by
  apply (acquire_clock rows).trans
  unfold encodeBudget
  gcongr

/-- Closed one-shot path retaining acquisition once and the actual owner query. -/
def fromRows {n : ℕ} (rows : Rows n) (factor port : ℕ) :
    SemiprimeD1RecoveryIntegerBits.UnsignedReport :=
  let bank:=acquire rows
  let out:=query bank factor port
  ⟨out.bits,bank.clock+out.clock+3⟩

/-- Closed one-shot owner semantics, including its actual acquired cache. -/
theorem fromRows_owner {n : ℕ} (rows : Rows n) (i : Incidence rows) :
    bitValue (fromRows rows i.1.val i.2.val).bits=(owner rows i).val :=
  query_owner rows i

/-- The one-shot path retains both setup and physical query work. -/
theorem fromRows_clock {n : ℕ} (rows : Rows n) (i : Incidence rows) (S : ℕ)
    (hn : n ≤ S) (hF : rows.length ≤ S) (hM : rows.flatten.length ≤ S) :
    (fromRows rows i.1.val i.2.val).clock ≤
      S*(encodeBudget S+4)+5*S+1+queryBudget S+3 := by
  have hs:=acquire_clock_uniform rows S hn hF hM
  have hq:=query_clock rows i S hn hF hM
  unfold fromRows
  dsimp only
  omega

end RiemannGaussian.SemiprimeD1NetworkOwnerBits
