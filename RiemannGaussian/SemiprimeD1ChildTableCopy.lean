/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTables
import RiemannGaussian.SemiprimeD1ModeRoutingBits

/-! # Eager physical copy and port reindexing of CURRENT local tables
The source is an already materialized table. Every assignment is gathered from
an explicit cached index list, physically read, zero-extended and reduced at the
new precision. There is no tensor truth callback or creator replay.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1ChildTableCopy
open SemiprimeD1JetAxes SemiprimeD1TensorTables

/-- Actual assignment-bit gather in the supplied cached port order. -/
def gather (bits : List Bool) : List ℕ→SemiprimeMaterializedWords.Run (List Bool)
  | [] => ⟨[],1⟩
  | i::is =>
    let bit := SemiprimeD1ModeRoutingBits.readBit bits i
    let tail := gather bits is
    ⟨bit.value::tail.value,bit.work+tail.work+4⟩

/-- The computed assignment is the literal selected-bit vector. -/
theorem gather_value (bits : List Bool) (order : List ℕ) :
    (gather bits order).value=order.map (fun i => (bits[i]?).getD false) := by
  induction order with
  | nil => rfl
  | cons i is ih => simp only [gather,SemiprimeD1ModeRoutingBits.readBit_value,ih,List.map_cons]

/-- Gathering never invents or removes a source port. -/
theorem gather_length (bits : List Bool) (order : List ℕ) :
    (gather bits order).value.length=order.length := by rw [gather_value,List.length_map]

/-- A padded read cannot visit more cells than the actual assignment list. -/
theorem readBit_clock_length (bits : List Bool) (i : ℕ) :
    (SemiprimeD1ModeRoutingBits.readBit bits i).work≤4*bits.length+2 := by
  induction bits generalizing i with
  | nil => simp [SemiprimeD1ModeRoutingBits.readBit]
  | cons b bs ih =>
    cases i with
    | zero => simp [SemiprimeD1ModeRoutingBits.readBit]
    | succ i =>
      have h := ih i
      simp only [SemiprimeD1ModeRoutingBits.readBit,List.length_cons]
      omega

/-- Every actual bit scan and gathered list cell is paid. -/
theorem gather_clock (bits : List Bool) (order : List ℕ) :
    (gather bits order).work≤order.length*(4*bits.length+7)+1 := by
  induction order with
  | nil => simp [gather]
  | cons i is ih =>
    have h := readBit_clock_length bits i
    simp only [gather,List.length_cons]
    nlinarith

/-- Reduce every copied coefficient physically, including at a smaller precision. -/
def normalize (p : ℕ) : List (List Bool)→SemiprimeD1JetRingBits.Run
  | [] => ⟨[],1⟩
  | w::ws =>
    let out := SemiprimeD1JetScalarBits.reduce p w
    let tail := normalize p ws
    ⟨out.bits::tail.words,out.clock+tail.clock+4⟩

/-- Exact literal coefficient transformation performed by normalization. -/
theorem normalize_words (p : ℕ) (ws : List (List Bool)) :
    (normalize p ws).words=ws.map (fun w => (SemiprimeD1JetScalarBits.reduce p w).bits) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [normalize,ih,List.map_cons]

/-- Physical canonical output shape needs only the actual vector length. -/
theorem normalize_good (ctx : Context) (ws : List (List Bool)) (hs : ws.length=ctx.rank) :
    GoodWords ctx (normalize ctx.precision ws).words := by
  rw [normalize_words]
  refine ⟨by simpa only [List.length_map] using hs,?_⟩
  intro w hw
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hw
  exact ⟨SemiprimeD1JetScalarBits.reduce_compact _ _,SemiprimeD1JetScalarBits.reduce_length _ _⟩

/-- Every physical coefficient reduction and vector cell is retained. -/
theorem normalize_clock (p : ℕ) (ws : List (List Bool)) :
    (normalize p ws).clock≤ws.length*(9*p+9)+1 := by
  induction ws with
  | nil => simp [normalize]
  | cons w ws ih =>
    have h := SemiprimeD1JetScalarBits.reduce_clock p w
    simp only [normalize,List.length_cons]
    nlinarith

/-- At a larger precision the CURRENT canonical literal bytes are unchanged. -/
theorem normalize_stable (old : Context) (p : ℕ) (ws : List (List Bool))
    (hg : GoodWords old ws) (hp : old.precision≤p) : (normalize p ws).words=ws := by
  rw [normalize_words]
  conv_rhs => rw [←List.map_id ws]
  apply List.map_congr_left
  intro w hw
  apply SemiprimeSourceCompactWordIds.compact_value_injective
  · exact SemiprimeD1JetScalarBits.reduce_compact _ _
  · exact (hg.2 w hw).1
  · have hlt := (SemiprimeBitArithmetic.bitValue_lt_width w).trans_le
      (Nat.pow_le_pow_right (by omega : 0<2) ((hg.2 w hw).2.trans hp))
    exact (SemiprimeD1JetScalarBits.reduce_value p w).trans (Nat.mod_eq_of_lt hlt)

/-- Copy ALL current coordinates, append zero axes, then reduce the same literal
integer coefficients at the new precision. -/
def lift (old : Context) (extra : List ℕ) (p : ℕ) (ws : List (List Bool)) :
    SemiprimeD1JetRingBits.Run :=
  let copied := embed ⟨old,old,ws⟩ extra p
  let out := normalize p copied.value.coefficients
  ⟨out.words,copied.clock+out.clock+3⟩

/-- Exact physical current-integer lift, including every old coordinate. -/
theorem lift_words (old : Context) (extra : List ℕ) (p : ℕ) (ws : List (List Bool)) :
    (lift old extra p ws).words=
      (ws++List.replicate (old.rank*(extra.prod-1)) []).map
        (fun w => (SemiprimeD1JetScalarBits.reduce p w).bits) := by
  simp only [lift,normalize_words,embed_coefficients]

/-- When the child precision is larger, every current literal byte is copied
unchanged and only genuinely new axis coordinates are zero. -/
theorem lift_stable (old : Context) (extra : List ℕ) (p : ℕ) (ws : List (List Bool))
    (hg : GoodWords old ws) (hp : old.precision≤p) :
    (lift old extra p ws).words=ws++List.replicate (old.rank*(extra.prod-1)) [] := by
  rw [lift_words,List.map_append]
  have hm := normalize_stable old p ws hg hp
  rw [normalize_words] at hm
  rw [hm,List.map_replicate]
  congr 2
  simp only [SemiprimeD1JetScalarBits.reduce,SemiprimeD1JetScalarBits.takeBits_bits,
    List.take_nil,SemiprimeSourceCompactBits.trim]

/-- Actual shape and canonicality follow from the old vector and positive new axes. -/
theorem lift_good (old : Context) (extra : List ℕ) (p : ℕ) (ws : List (List Bool))
    (hs : ws.length=old.rank) (he : 0<extra.prod) :
    GoodWords ⟨extra++old.axes,p⟩ (lift old extra p ws).words := by
  exact normalize_good ⟨extra++old.axes,p⟩ _ (embed_shape ⟨old,old,ws⟩ extra p hs he)

/-- Explicit finite physical copy/reduction budget, retaining every old coordinate. -/
def liftBudget (old : Context) (extra : List ℕ) (p : ℕ) : ℕ :=
  old.rank*(3*old.precision+5)+old.rank*(extra.prod-1)+extra.length+old.axes.length+8+
    (extra.prod*old.rank)*(9*p+9)+4

/-- The literal vector loop obeys its computed budget, not a clock annotation. -/
theorem lift_clock (old : Context) (extra : List ℕ) (p : ℕ) (ws : List (List Bool))
    (hg : GoodWords old ws) (he : 0<extra.prod) :
    (lift old extra p ws).clock≤liftBudget old extra p := by
  have hc := embed_clock_le ⟨old,old,ws⟩ extra p old.precision hg.1 (fun w hw => (hg.2 w hw).2)
  have hn := normalize_clock p (embed ⟨old,old,ws⟩ extra p).value.coefficients
  rw [embed_shape ⟨old,old,ws⟩ extra p hg.1 he,embed_rank] at hn
  change (embed ⟨old,old,ws⟩ extra p).clock+
    (normalize p (embed ⟨old,old,ws⟩ extra p).value.coefficients).clock+3≤_
  exact Nat.add_le_add_right (Nat.add_le_add hc hn) 3

/-- The producer is a concrete cached-table read, not an arbitrary tensor oracle. -/
def entry {oldDegree : ℕ} (old : Context) (extra : List ℕ) (p : ℕ)
    (table : Table oldDegree) (order : List ℕ) (bits : List Bool) :
    SemiprimeD1JetRingBits.Run :=
  let selected := gather bits order
  let value := lookup table selected.value
  let copied := lift old extra p value.words
  ⟨copied.words,selected.work+value.clock+copied.clock+5⟩

/-- Materialize the entire child table using actual cached parent table entries. -/
def acquire {oldDegree : ℕ} (old : Context) (extra : List ℕ) (p childDegree : ℕ)
    (table : Acquired oldDegree) (order : List ℕ) : Acquired childDegree :=
  let out := build childDegree (entry old extra p table.table order)
  ⟨out.table,table.clock+out.clock+order.length+5⟩

/-- Exact entry refinement to the actual copied parent read. -/
theorem acquire_value {oldDegree : ℕ} (old : Context) (extra : List ℕ) (p childDegree : ℕ)
    (table : Acquired oldDegree) (order : List ℕ) (bits : List Bool) (hb : bits.length=childDegree) :
    (lookup (acquire old extra p childDegree table order).table bits).words=
      (lift old extra p (lookup table.table (gather bits order).value).words).words :=
  build_value childDegree (entry old extra p table.table order) bits hb

/-- Every newly materialized entry is canonical at the new CURRENT context. -/
theorem acquire_good {oldDegree : ℕ} (old : Context) (extra : List ℕ) (p childDegree : ℕ)
    (table : Acquired oldDegree) (order : List ℕ) (ht : Good old table.table)
    (he : 0<extra.prod) : Good ⟨extra++old.axes,p⟩ (acquire old extra p childDegree table order).table := by
  apply build_good
  intro bits _
  exact lift_good old extra p _ (lookup_good old table.table ht _).1 he

/-- Full table-copy work has exactly the eager local `2^degree` scale. -/
theorem acquire_clock {oldDegree : ℕ} (old : Context) (extra : List ℕ) (p childDegree : ℕ)
    (table : Acquired oldDegree) (order : List ℕ) (ht : Good old table.table)
    (he : 0<extra.prod) :
    (acquire old extra p childDegree table order).clock≤table.clock+
      (order.length*(4*childDegree+7)+1+old.rank*(3*old.precision+4)+1+
        4*oldDegree+liftBudget old extra p+12)*2^childDegree+order.length := by
  have h := build_clock childDegree
    (order.length*(4*childDegree+7)+1+old.rank*(3*old.precision+4)+1+
      4*oldDegree+liftBudget old extra p+5) (entry old extra p table.table order) (by
    intro bits hb
    have hg := gather_clock bits order
    rw [hb] at hg
    have hv := lookup_clock old table.table ht (gather bits order).value
    have hl := lift_clock old extra p (lookup table.table (gather bits order).value).words
      (lookup_good old table.table ht (gather bits order).value) he
    change (gather bits order).work+(lookup table.table (gather bits order).value).clock+
      (lift old extra p (lookup table.table (gather bits order).value).words).clock+5≤_
    omega)
  change (build childDegree (entry old extra p table.table order)).clock+5≤
    (order.length*(4*childDegree+7)+1+old.rank*(3*old.precision+4)+1+
      4*oldDegree+liftBudget old extra p+12)*2^childDegree at h
  change table.clock+(build childDegree (entry old extra p table.table order)).clock+order.length+5≤_
  omega

end RiemannGaussian.SemiprimeD1ChildTableCopy
