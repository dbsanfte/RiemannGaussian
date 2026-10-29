/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetWordPacketEntryBits
import RiemannGaussian.SemiprimeD1PacketTensorTables
import RiemannGaussian.SemiprimeD1TensorTapeLeaf

/-! # Eager actual packet tables from original word producers
The unchanged actual prepared header and node are retained once. Every entry
executes the new physical word backend, and all distinct reports remain paid.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1JetWordPacketTables
open SemiprimeD1JetAxes SemiprimeD1TensorTables
open SemiprimeD1PacketTensorTables (Header prepare)

/-- Materialize every entry with the new actual word backend. -/
def acquire {V : ℕ} (header : Header V) (ctx : Context)
    (z : SemiprimeD1JetAffineCoefficient.JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) : Acquired header.endpoints.length :=
  let out:=build header.endpoints.length
    (SemiprimeD1JetWordPacketEntryBits.evaluate ctx (SemiprimeD1PacketEntryBits.borrow z) a i t
      header.masks header.endpoints beta)
  ⟨out.table,header.clock+z.clock+out.clock+beta.length+12⟩

/-- Original eager-table bytes are preserved; their different clocks are not equated. -/
theorem acquire_table {V : ℕ} (header : Header V) (ctx : Context) (hpos:ctx.Positive)
    (z : SemiprimeD1JetAffineCoefficient.JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    (acquire header ctx z a i t beta).table=
      (SemiprimeD1PacketTensorTables.acquire header ctx z a i t beta).table := by
  apply SemiprimeD1TensorTapeLeaf.build_table_congr
  intro bits
  exact SemiprimeD1JetWordPacketEntryBits.evaluate_words ctx hpos _ _ _ _ _ _ _ _

/-- Every acquired table entry is canonical by the actual final physical multiply. -/
theorem acquire_good {V : ℕ} (header : Header V) (ctx : Context)
    (z : SemiprimeD1JetAffineCoefficient.JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    Good ctx (acquire header ctx z a i t beta).table := by
  apply build_good
  intro bits _
  exact SemiprimeD1JetWordPacketEntryBits.evaluate_canonical ctx _ _ _ _ _ _ _ _

/-- Original source/graph/mask acquisition is executed through the actual header. -/
def acquireOriginal {n F r a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (source : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin source.packets.state.packets.length) (i : Fin a) (g : Fin r)
    (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :=
  acquire (prepare owner source packet i g) ctx z a i t beta

/-- The actual original source and node reports remain in every eager table. -/
theorem acquire_retains {V : ℕ} (header : Header V) (ctx : Context)
    (z : SemiprimeD1JetAffineCoefficient.JetRun) (a : ℕ) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) :
    header.clock+z.clock≤(acquire header ctx z a i t beta).clock := by
  dsimp only [acquire]
  omega
end RiemannGaussian.SemiprimeD1JetWordPacketTables
