/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildWordOriginalClock

/-! # Exact source-linear decomposition of the new word/tape child budget
The source-free part retains inventory and all eager/table-storage factors.
This algebraic identity does not transfer the frozen original child's clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildWordBudgetLinear
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork
open SemiprimeD1ChildOriginalClock (source ports dataCap graphCap orderCap)
open SemiprimeD1WordPacketTableClock

/-- Actual per-right source/header and fresh-node reports occur additively once. -/
theorem right_source_linear (ctx : Context) (a A K P T B L E S H Z G e : ℕ) :
    rightClock ctx a A K P T B L E (S+H) Z G e=
      S+Z+rightClock ctx a A K P T B L E H 0 G e := by
  unfold rightClock tableClock
  ring

/-- Original-derived prefactor with ONLY source/fresh acquisition reports removed.
It keeps all parent inventory, table storage, finite coefficient recursion and
native metadata dimensions for a subsequent resource-envelope substitution. -/
def sourceFree (net : Network) (old : Context) (extra : List ℕ) (D a u : ℕ) (i : Fin a) : ℕ :=
  let src:=source net old a u i
  let M:=ports net
  let NF:=net.leftCount+net.rows.length
  let K:=SemiprimeD1ChildModeResources.catalogueLength net a u i old.precision
  let E:=SemiprimeD1PacketReplayBudget.budget net.leftCount net.rows.length 64 a M
  let H:=SemiprimeD1PacketModeMaskBudget.prepareOverhead net.leftCount net.rows.length 64 a M src.precision
  dataCap net a+graphCap net a+
    (NF*SemiprimeD1ChildNetworkTapeBudget.leftBudget old extra src.precision D (orderCap net a)
      (SemiprimeD1NetworkStateResources.inventory net) NF+10*(NF+1))+
    M*rightClock ⟨extra++old.axes,src.precision⟩ a (2*2^a) K src.precision (2^a) src.precision K E H 0 (graphCap net a) M+
    10*(NF+M+2*M^2+1)^3

/-- Exact multiplicity of both actual source and node reports in the computed bound. -/
theorem budget_linear (net : Network) (old : Context) (extra : List ℕ) (D a u : ℕ)
    (i : Fin a) (Z : ℕ) :
    SemiprimeD1ChildWordOriginalClock.budget net old extra D a u i Z=
      (ports net+1)*((source net old a u i).work+Z)+sourceFree net old extra D a u i := by
  dsimp only [SemiprimeD1ChildWordOriginalClock.budget,sourceFree]
  rw [right_source_linear]
  ring
end RiemannGaussian.SemiprimeD1ChildWordBudgetLinear
