/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftTableStorage
import RiemannGaussian.SemiprimeD1ChildNetworkTape
/-! # Exact whole-table fusion of alignment, individual lifting and canonical recopy
The actual134 source can read the original parent table directly. Alignment
and final recopy have the same full literal payload, so neither intermediate
table needs to be acquired merely to obtain those bytes. Native clocks are
never identified; the physical source retains its own proved clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1ChildTableDirect
open SemiprimeD1TensorTables (Table build lookup)
/-- Eager copying at the same exact degree preserves the ENTIRE original ordered table. -/
theorem build_lookup_identity {n : ℕ} (table : Table n) : (build n (lookup table)).table=table := by
  induction table with
  | leaf words =>
    change Table.leaf (SemiprimeD1JetAxes.copyVector words).1=Table.leaf words
    rw [SemiprimeD1JetAxes.copyVector_value]
  | @fork n low high ihlow ihhigh =>
    have hl := SemiprimeD1TensorTapeLeaf.build_table_congr n
      (fun bits => lookup (Table.fork low high) (false::bits)) (lookup low) (fun _ => rfl)
    have hh := SemiprimeD1TensorTapeLeaf.build_table_congr n
      (fun bits => lookup (Table.fork low high) (true::bits)) (lookup high) (fun _ => rfl)
    change Table.fork (build n (fun bits => lookup (Table.fork low high) (false::bits))).table
      (build n (fun bits => lookup (Table.fork low high) (true::bits))).table=Table.fork low high
    rw [hl,hh,ihlow,ihhigh]
/-- The actual sequential serialized-table reader has the same complete identity-copy payload. -/
theorem build_tape_lookup_identity {n : ℕ} (table : Table n) :
    (build n (fun bits => SemiprimeD1TensorTapeLookup.fromTable table bits)).table=table :=
  (SemiprimeD1TensorTapeLeaf.build_table_congr n _ _
    (fun bits => SemiprimeD1TensorTapeLookup.fromTable_words table bits)).trans (build_lookup_identity table)
/-- Canonical-port recopy contributes no different table or port bytes at the matching degree. -/
theorem canonical_recopy (ports : List ℕ) (table : Table ports.length) :
    (SemiprimeD1ChildNetworkTape.copyTable ports table).1=(⟨ports,table⟩ : SemiprimeD1LeafCounter.Vertex) := by
  change (⟨ports,(build ports.length (fun bits => SemiprimeD1TensorTapeLookup.fromTable table bits)).table⟩ :
    SemiprimeD1LeafCounter.Vertex)=⟨ports,table⟩
  rw [build_tape_lookup_identity]
/-- Original alignment view, described only for exact-byte comparison, never as a runtime supplier. -/
def aligned {d : ℕ} (n : ℕ) (parent : Table d) : Table n :=
  (build n (fun bits => SemiprimeD1TensorTapeLookup.fromTable parent bits)).table
/-- EVERY complete aligned assignment reads the original parent bytes, including default FALSE lookups. -/
theorem aligned_read {d : ℕ} (n : ℕ) (parent : Table d) (bits : List Bool) (hb : bits.length=n) :
    (lookup (aligned n parent) bits).words=(lookup parent bits).words :=
  (SemiprimeD1TensorTables.build_value n
    (fun raw => SemiprimeD1TensorTapeLookup.fromTable parent raw) bits hb).trans
      (SemiprimeD1TensorTapeLookup.fromTable_words parent bits)
/-- Paid gather ALWAYS has the actual old-order length, so alignment can be bypassed for ALL raw assignments. -/
theorem entry_aligned {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (p : ℕ)
    (parent : Table d) (order : List ℕ) (bits : List Bool) :
    (SemiprimeD1ChildTableCopyTape.entry old extra p (aligned order.length parent) order bits).words=
      (SemiprimeD1ChildTableCopyTape.entry old extra p parent order bits).words := by
  have h := aligned_read order.length parent (SemiprimeD1ChildTableCopy.gather bits order).value
    (SemiprimeD1ChildTableCopy.gather_length bits order)
  simp only [SemiprimeD1ChildTableCopyTape.entry,SemiprimeD1TensorTapeLookup.fromTable_words]
  exact congrArg (fun words => (SemiprimeD1ChildTableCopy.lift old extra p words).words) h
/-- The ENTIRE lifted child table is unchanged when its alignment intermediate is eliminated. -/
theorem table_aligned {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (p n : ℕ)
    (parent : Table d) (order : List ℕ) :
    SemiprimeD1StackChildLiftTableMeaning.table old extra p n (aligned order.length parent) order=
      SemiprimeD1StackChildLiftTableMeaning.table old extra p n parent order :=
  SemiprimeD1TensorTapeLeaf.build_table_congr n _ _ (entry_aligned old extra p parent order)
/-- Both full intermediates disappear using the acquired old-order and canonical-scope counts. -/
theorem copy_lift_aligned {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (p : ℕ)
    (parent : Table d) (order ports : List ℕ) (oldDegree childDegree : ℕ)
    (ho : order.length=oldDegree) (hc : ports.length=childDegree) :
    (SemiprimeD1ChildNetworkTape.copyTable ports
      (SemiprimeD1StackChildLiftTableMeaning.table old extra p childDegree (aligned oldDegree parent) order)).1=
      (⟨ports,SemiprimeD1StackChildLiftTableMeaning.table old extra p ports.length parent order⟩ :
        SemiprimeD1LeafCounter.Vertex) := by
  subst oldDegree
  subst childDegree
  rw [table_aligned,canonical_recopy]
end RiemannGaussian.SemiprimeD1ChildTableDirect
