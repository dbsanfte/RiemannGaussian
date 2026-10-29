/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootOwnerTables
import RiemannGaussian.SemiprimePublicAcquiredExecution
import RiemannGaussian.SemiprimePaidFiniteEnumerations
import RiemannGaussian.SemiprimePublicBudgetDimensions
import RiemannGaussian.SemiprimeD1PublicPackingReady

/-! # Original-N eager root tables, without table/verdict advice
Every factor invokes the actual arithmetic/equality checker. Every owner table
is built from the actual cached incidence fibre and the literal current prefix.
Native public configuration/target/index construction remains an explicit
source-metadata boundary, separate from the retained checker/table reports.
-/
set_option autoImplicit false
set_option maxHeartbeats 30000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RootTensorTables
open scoped BigOperators
open SemiprimePublicAcquiredExecution SemiprimeD1TensorTables
open SemiprimeD1RootOwnerTables (rootContext)
open SemiprimeD1JetAffineCoefficient (JetRun)
open SemiprimeBitArithmetic

/-- Actual original indexed incidence type, not an input graph/table family. -/
abbrev Port (N : ℕ) := (e : Fin (factorCount N))×Fin (indexedArity N e)

/-- Materialized original port metadata, with the native owner index cached once. -/
structure PortRecord (n F : ℕ) (arity : Fin F→ℕ) where
  /-- Original factor and its local ordered port. -/
  port : (e : Fin F)×Fin (arity e)
  /-- Actual original indexed wire variable. -/
  owner : Fin n

/-- Original-N specialization of the concrete metadata record. -/
abbrev Record (N : ℕ) := PortRecord (wireCount N) (factorCount N) (indexedArity N)

/-- Complete literal node: ordered original ports and eager table, no entry closure. -/
structure Node (I : Type) where
  /-- All actual original incidences attached to this vertex. -/
  ports : List I
  /-- Every local assignment has its literal acquired word vector. -/
  table : Table ports.length
  /-- Complete producer, port-list and materialization report. -/
  clock : ℕ

/-- Original graph data with complete cached tables for BOTH tensor sides. -/
structure Acquired (n F : ℕ) (arity : Fin F→ℕ) where
  /-- All original incidences with their actual cached owner index. -/
  records : List (PortRecord n F arity)
  /-- Actual original factor tables in Fin-factor order. -/
  factors : List (Node ((e : Fin F)×Fin (arity e)))
  /-- Actual wire-owner tables in Fin-variable order. -/
  owners : List (Node ((e : Fin F)×Fin (arity e)))
  /-- All incidence/list/table reports, retained once. -/
  clock : ℕ
  /-- Explicit number of original native coordinate constructions, not a hidden free cache. -/
  coordinateCalls : ℕ

/-- Original-N specialization, with all data physically materialized. -/
abbrev Data (N : ℕ) := Acquired (wireCount N) (factorCount N) (indexedArity N)

/-- Actual factor callback caches its Boolean assignment once in a native array,
executes the real arithmetic/equality checker and emits canonical scalar0/1. -/
def factorProducer (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) (bits : List Bool) : JetRun :=
  let input:=bits.toArray
  let check:=indexedEntry N hN e (fun i=>(input[i.val]?).getD false)
  ⟨[if check.accepted then [true] else []],check.clock+3*bits.length+5⟩

/-- Every factor entry is canonical root data from an actual computed Boolean. -/
theorem factorProducer_good (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) (bits : List Bool) :
    GoodWords rootContext (factorProducer N hN e bits).words := by
  constructor
  · rfl
  · intro w hw
    rcases List.mem_cons.mp hw with rfl|h
    · split <;> simp [SemiprimeSourceCompactBits.Compact,rootContext]
    · cases h

/-- The actual scalar factor word is exactly the actual public checker verdict. -/
theorem factorProducer_value (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) (bits : List Bool) :
    SemiprimeD1JetRingBits.coefficient rootContext (factorProducer N hN e bits).words 0=
      if (indexedEntry N hN e (fun i=>(bits.toArray[i.val]?).getD false)).accepted then (1:ZMod 4) else 0 := by
  change (bitValue (if (indexedEntry N hN e (fun i=>(bits.toArray[i.val]?).getD false)).accepted
    then [true] else []):ZMod 4)=_
  split <;> simp [bitValue,bitNat]

/-- No local truth oracle: the actual indexed checker equals the literal public arithmetic tensor. -/
theorem factorProducer_original (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) (bits : List Bool) :
    SemiprimeD1JetRingBits.coefficient rootContext (factorProducer N hN e bits).words 0=
      if SemiprimeMacroGraphSemantics.subdividedTable (SemiprimePublicFactorCount.publicConfig N hN)
        ((vertexEnumeration N).equivFin e) (fun i=>(bits.toArray[i.val]?).getD false) then (1:ZMod 4) else 0 := by
  rw [factorProducer_value,indexedEntry_correct]
  rfl

/-- Complete retained factor callback report, with actual assignment-array cells. -/
theorem factorProducer_clock (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) (bits : List Bool) :
    (factorProducer N hN e bits).clock ≤ 1048576*(64*SemiprimeMacroParameters.bitLength N+2)^10+3*bits.length+5 := by
  have h:=indexedEntry_clock N hN e (fun i=>(bits.toArray[i.val]?).getD false)
  change (indexedEntry N hN e (fun i=>(bits.toArray[i.val]?).getD false)).clock+3*bits.length+5 ≤ _
  omega

/-- Materialize the actual factor's dependent ports and every original local assignment. -/
def factorNode (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) : Node (Port N) :=
  let ps:=SemiprimePaidFiniteEnumerations.ports (indexedArity N) e
  let out:=build ps.value.length (factorProducer N hN e)
  ⟨ps.value,out.table,ps.work+out.clock+3⟩

/-- The factor's actual local port order is the original ascending source order. -/
theorem factorNode_ports (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) :
    (factorNode N hN e).ports=(List.finRange (indexedArity N e)).map (Sigma.mk e) :=
by
  dsimp only [factorNode]
  exact SemiprimePaidFiniteEnumerations.ports_value (F:=factorCount N) (indexedArity N) e

/-- No factor scope is an external resource parameter. -/
theorem factorNode_degree (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) :
    (factorNode N hN e).ports.length=indexedArity N e := by
  rw [factorNode_ports,List.length_map,List.length_finRange]

/-- Exact physical factor table read is its real original checker producer. -/
theorem factorNode_value (N : ℕ) (hN : 0<N) (e : Fin (factorCount N))
    (bits : List Bool) (hb : bits.length=indexedArity N e) :
    (lookup (factorNode N hN e).table bits).words=(factorProducer N hN e bits).words := by
  dsimp only [factorNode]
  have hpv:=SemiprimePaidFiniteEnumerations.ports_value (F:=factorCount N) (indexedArity N) e
  have hlen : (SemiprimePaidFiniteEnumerations.ports (indexedArity N) e).value.length=indexedArity N e := by
    simpa only [List.length_map,List.length_finRange] using congrArg List.length hpv
  exact build_value (SemiprimePaidFiniteEnumerations.ports (indexedArity N) e).value.length
    (factorProducer N hN e) bits (hb.trans hlen.symm)

/-- Every actual factor table is intrinsically canonical. -/
theorem factorNode_good (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) :
    Good rootContext (factorNode N hN e).table := by
  dsimp only [factorNode]
  generalize (SemiprimePaidFiniteEnumerations.ports (indexedArity N) e).value.length=degree
  exact build_good rootContext degree (factorProducer N hN e) (fun bits _=>factorProducer_good N hN e bits)

/-- Acquire original owner metadata exactly once per original incidence. -/
def records (N : ℕ) (hN : 0<N) (ps : List (Port N)) : List (Record N) :=
  ps.map (fun p=>⟨p,indexedCoordinate N hN p.1 p.2⟩)

/-- Actual cached owner fibre, with no row/count answer. -/
def ownerPorts (N : ℕ) (rs : List (Record N)) (v : Fin (wireCount N)) : List (Port N) :=
  (rs.filter (fun p=>decide (p.owner=v))).map PortRecord.port

/-- Materialize all owner-copy entries after one actual cached-owner scan. -/
def ownerNode (N : ℕ) (fixed : List (Fin (wireCount N)×Bool))
    (rs : List (Record N)) (v : Fin (wireCount N)) : Node (Port N) :=
  let ps:=ownerPorts N rs v
  let out:=SemiprimeD1RootOwnerTables.acquire fixed v ps.length
  ⟨ps,out.table,out.clock+5*rs.length+3*ps.length+5⟩

/-- Complete actual owner entry, preserving isolated-variable multiplicity. -/
theorem ownerNode_value (N : ℕ) (fixed : List (Fin (wireCount N)×Bool))
    (rs : List (Record N)) (v : Fin (wireCount N)) (bits : List Bool)
    (hb : bits.length=(ownerPorts N rs v).length) :
    (lookup (ownerNode N fixed rs v).table bits).words=
      (SemiprimeD1RootOwnerTables.producer fixed v bits).words :=
  SemiprimeD1RootOwnerTables.acquire_value fixed v _ bits hb

/-- Every actual owner table is intrinsically canonical at the root context. -/
theorem ownerNode_good (N : ℕ) (fixed : List (Fin (wireCount N)×Bool))
    (rs : List (Record N)) (v : Fin (wireCount N)) :
    Good rootContext (ownerNode N fixed rs v).table := SemiprimeD1RootOwnerTables.acquire_good _ _ _

/-- Complete positive-input acquisition: incidence metadata, both cached families and all reports. -/
def acquirePositive (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) : Data N :=
  let ps:=SemiprimePaidFiniteEnumerations.incidences (factorCount N) (indexedArity N)
  let rs:=records N hN ps.value
  let es:=SemiprimePaidFiniteEnumerationLists.fin (factorCount N)
  let vs:=SemiprimePaidFiniteEnumerationLists.fin (wireCount N)
  let fs:=es.value.map (factorNode N hN)
  let os:=vs.value.map (ownerNode N fixed rs)
  ⟨rs,fs,os,ps.work+5*ps.value.length+es.work+vs.work+
    (fs.map Node.clock).sum+(os.map Node.clock).sum+5*(fs.length+os.length+1),ps.value.length⟩

/-- Original-N and current-prefix-only entry point; zero is rejected by a decidable branch. -/
def acquire (N : ℕ) (fixed : List (Fin (wireCount N)×Bool)) : Option (Data N) :=
  if hN : 0<N then some (acquirePositive N hN fixed) else none

/-- Actual factor table count and original order, not supplied family advice. -/
theorem acquirePositive_factors (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    (acquirePositive N hN fixed).factors=(List.finRange (factorCount N)).map (factorNode N hN) := by
  simp only [acquirePositive,SemiprimePaidFiniteEnumerationLists.fin_value]

/-- Actual wire-owner table count and original order. -/
theorem acquirePositive_owners (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    (acquirePositive N hN fixed).owners=(List.finRange (wireCount N)).map
      (ownerNode N fixed (acquirePositive N hN fixed).records) := by
  simp only [acquirePositive,SemiprimePaidFiniteEnumerationLists.fin_value]

/-- All original coordinate labels are computed from the native original source once. -/
theorem acquirePositive_records (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    (acquirePositive N hN fixed).records=records N hN
      (SemiprimeFiniteEnumerations.indexedIncidences (factorCount N) (indexedArity N)).values := by
  simp only [acquirePositive,SemiprimePaidFiniteEnumerations.incidences_value]

/-- Actual arithmetic/equality source producer work is retained; no final table verdict is accepted. -/
theorem acquirePositive_retains (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    ((acquirePositive N hN fixed).factors.map Node.clock).sum+
      ((acquirePositive N hN fixed).owners.map Node.clock).sum ≤ (acquirePositive N hN fixed).clock := by
  dsimp only [acquirePositive]
  omega

/-- The actual root incidence count fits a fixed original bit-length scale. -/
theorem actual_incidence_bound (N : ℕ) (hN : 0<N) :
    (∑ e,indexedArity N e) ≤ 12800*SemiprimeMacroParameters.bitLength N := by
  rw [indexed_incidence_count N hN,wireCount_eq]
  have h:=SemiprimeMacroParameters.variableCount_le (SemiprimeMacroParameters.bitLength_pos hN)
  omega

/-- The original root-size scale covers incidence count, not merely Boolean-wire count. -/
theorem actual_incidence_scale (N : ℕ) (hN : 0<N) :
    (∑ e,indexedArity N e) ≤ SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength N) :=
  (actual_incidence_bound N hN).trans (Nat.mul_le_mul_right _ (by norm_num : 12800≤2^20))

end RiemannGaussian.SemiprimeD1RootTensorTables
