/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootTensorTables

/-! # Original root table family dimensions and retained eager report
The final bound has no table/verdict or callback-clock premise. Native public
configuration/target/coordinate construction and full address-bit lowering are
explicitly separate from this checker/list/table report.
-/
set_option autoImplicit false
set_option maxHeartbeats 40000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RootTensorTablesBounds
open scoped BigOperators
open SemiprimePublicAcquiredExecution SemiprimeD1RootTensorTables SemiprimeD1TensorTables
open SemiprimeD1RootOwnerTables (rootContext)

/-- Cached owner records filter to the exact original incidence fibre. -/
theorem ownerPorts_records (N : ℕ) (hN : 0<N) (ps : List (Port N)) (v : Fin (wireCount N)) :
    ownerPorts N (records N hN ps) v=ps.filter (fun p=>decide (indexedCoordinate N hN p.1 p.2=v)) := by
  simp only [ownerPorts,records,List.filter_map,List.map_map,Function.comp_def,List.map_id']

/-- Original complete incidence lists contain each actual port once. -/
theorem incidence_toFinset (N : ℕ) :
    (SemiprimeFiniteEnumerations.indexedIncidences (factorCount N) (indexedArity N)).values.toFinset=
      (Finset.univ : Finset (Port N)) := by
  classical
  ext p
  simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
  exact (SemiprimeFiniteEnumerations.indexedIncidences _ _).complete p

/-- Actual cached owner degrees have the original occurrence-two bound, with no load answer. -/
theorem owner_degree_le (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (v : Fin (wireCount N)) :
    (ownerPorts N (acquirePositive N hN fixed).records v).length ≤ 2 := by
  classical
  rw [acquirePositive_records,ownerPorts_records]
  let en:=SemiprimeFiniteEnumerations.indexedIncidences (factorCount N) (indexedArity N)
  have hn : (en.values.filter (fun p=>decide (indexedCoordinate N hN p.1 p.2=v))).Nodup:=en.nodup.filter _
  have hc:=List.toFinset_card_of_nodup hn
  have hs : (en.values.filter (fun p=>decide (indexedCoordinate N hN p.1 p.2=v))).toFinset=
      Finset.univ.filter (fun p : Port N=>indexedCoordinate N hN p.1 p.2=v) := by
    ext p
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_filter,Finset.mem_univ,true_and]
    exact and_iff_right (en.complete p)
  exact hc.symm.trans_le (by rw [hs];exact indexed_occurrences N hN v)

/-- Every actual factor scope fits the public original scope envelope. -/
theorem factor_degree_le (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) :
    (factorNode N hN e).ports.length ≤ SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength N) := by
  rw [factorNode_degree]
  exact indexedArity_le N e

/-- Native dependent finite port construction has its actual polynomial report. -/
theorem ports_work {F : ℕ} (arity : Fin F→ℕ) (e : Fin F) :
    (SemiprimePaidFiniteEnumerations.ports arity e).work ≤ 3*(arity e+1)^2+3*arity e+3 := by
  have hf:=SemiprimePaidFiniteEnumerationLists.fin_work (arity e)
  have hm:=SemiprimeMaterializedSourceUniversal.collect_work
    (fun i : Fin (arity e)=>(⟨Sigma.mk e i,1⟩ : SemiprimeMaterializedSourceUniversal.Run ((e:Fin F)×Fin (arity e))))
    (SemiprimePaidFiniteEnumerationLists.fin (arity e)).value 1 (fun _ _=>le_rfl)
  rw [SemiprimePaidFiniteEnumerationLists.fin_value,List.length_finRange] at hm
  change (SemiprimePaidFiniteEnumerationLists.fin (arity e)).work+
    (SemiprimeMaterializedSourceUniversal.collect
      (fun i : Fin (arity e)=>(⟨Sigma.mk e i,1⟩ : SemiprimeMaterializedSourceUniversal.Run ((e:Fin F)×Fin (arity e))))
      (SemiprimePaidFiniteEnumerationLists.fin (arity e)).value).work+2 ≤ _
  rw [SemiprimePaidFiniteEnumerationLists.fin_value]
  omega

/-- Actual original checker bound, fixed before the local assignments. -/
def checkerBudget (N : ℕ) : ℕ:=1048576*(64*SemiprimeMacroParameters.bitLength N+2)^10

/-- Explicit scope envelope from the original input dimensions. -/
def scope (N : ℕ) : ℕ:=SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength N)

/-- Fixed polynomial per-factor header plus the literal eager assignment scale. -/
def factorBudget (N : ℕ) : ℕ:=
  3*(scope N+1)^2+3*scope N+6+(checkerBudget N+3*scope N+12)*2^(scope N)

/-- Every physical factor checker call and materialized assignment is retained. -/
theorem factorNode_clock (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) :
    (factorNode N hN e).clock ≤ factorBudget N := by
  let ps:=SemiprimePaidFiniteEnumerations.ports (indexedArity N) e
  have hp:=ports_work (indexedArity N) e
  have hs:=indexedArity_le N e
  have hl : ps.value.length=indexedArity N e := by
    simpa only [List.length_map,List.length_finRange] using congrArg List.length
      (SemiprimePaidFiniteEnumerations.ports_value (F:=factorCount N) (indexedArity N) e)
  have hb:=build_clock ps.value.length (checkerBudget N+3*ps.value.length+5)
    (factorProducer N hN e) (fun bits hlen=>by simpa only [hlen,checkerBudget] using factorProducer_clock N hN e bits)
  have hpow:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hs
  have hmul : (checkerBudget N+3*indexedArity N e+12)*2^(indexedArity N e) ≤
      (checkerBudget N+3*scope N+12)*2^(scope N) :=
    Nat.mul_le_mul (by unfold scope;omega) hpow
  rw [hl] at hb
  have hs' : indexedArity N e ≤ scope N:=hs
  have hp' : 3*(indexedArity N e+1)^2+3*indexedArity N e+3 ≤
      3*(scope N+1)^2+3*scope N+3 := by gcongr
  dsimp only [factorNode]
  change ps.work+(build ps.value.length (factorProducer N hN e)).clock+3 ≤ _
  rw [hl]
  unfold factorBudget
  nlinarith

/-- Exact actual cached incidence/coordinate call count. -/
theorem records_length (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    (acquirePositive N hN fixed).records.length=∑ e,indexedArity N e := by
  simp only [acquirePositive,records,List.length_map,SemiprimePaidFiniteEnumerations.incidences_length]

/-- All wire-owner tables have a fixed low-degree producer envelope. -/
def ownerBudget (N P : ℕ) : ℕ:=(16*P+87)*4+5*(2*wireCount N)+11

/-- Every owner prefix scan, copy test, eager entry and fibre scan is paid from original data. -/
theorem ownerNode_clock (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (v : Fin (wireCount N)) :
    (ownerNode N fixed (acquirePositive N hN fixed).records v).clock ≤ ownerBudget N fixed.length := by
  let rs:=(acquirePositive N hN fixed).records
  let degree:=(ownerPorts N rs v).length
  have hd : degree ≤ 2:=owner_degree_le N hN fixed v
  have hc:=SemiprimeD1RootOwnerTables.acquire_clock fixed v degree
  have hp : 2^degree ≤ 4:=by simpa using Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hd
  have hm : (16*fixed.length+10*degree+67)*2^degree ≤ (16*fixed.length+87)*4:=
    Nat.mul_le_mul (by omega) hp
  have hlen : rs.length=2*wireCount N:=(records_length N hN fixed).trans (indexed_incidence_count N hN)
  dsimp only [ownerNode]
  change (SemiprimeD1RootOwnerTables.acquire fixed v degree).clock+5*rs.length+3*degree+5 ≤ _
  unfold ownerBudget
  omega

/-- Literal source table-report sum is bounded without a table/function answer oracle. -/
theorem map_node_clock_le {A : Type*} {I : Type} (xs : List A) (f : A→Node I) (B : ℕ)
    (h : ∀x∈xs,(f x).clock ≤ B) : ((xs.map f).map Node.clock).sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh:=h x List.mem_cons_self
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Full retained root acquisition budget from actual original dimensions and prefix length. -/
def budget (N P : ℕ) : ℕ:=
  SemiprimePaidFiniteEnumerations.incidenceBudget (factorCount N) (2*wireCount N)+10*wireCount N+
    3*(factorCount N+1)^2+3*(wireCount N+1)^2+
    factorCount N*factorBudget N+wireCount N*ownerBudget N P+5*(factorCount N+wireCount N+1)

/-- Every source/list/checker/table report of the actual N-only construction has a closed eager bound.
Native public configuration/target/coordinate arithmetic is explicitly a separate stage. -/
theorem acquirePositive_clock (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    (acquirePositive N hN fixed).clock ≤ budget N fixed.length := by
  have hi:=SemiprimePaidFiniteEnumerations.incidences_work (factorCount N) (indexedArity N)
  rw [indexed_incidence_count N hN] at hi
  have he:=SemiprimePaidFiniteEnumerationLists.fin_work (factorCount N)
  have hv:=SemiprimePaidFiniteEnumerationLists.fin_work (wireCount N)
  have hps : (SemiprimePaidFiniteEnumerations.incidences (factorCount N) (indexedArity N)).value.length=
      2*wireCount N := (SemiprimePaidFiniteEnumerations.incidences_length _ _).trans (indexed_incidence_count N hN)
  have hf : (((List.finRange (factorCount N)).map (factorNode N hN)).map Node.clock).sum ≤
      factorCount N*factorBudget N := by
    simpa only [List.length_finRange] using
      map_node_clock_le (List.finRange (factorCount N)) (factorNode N hN) (factorBudget N)
        (fun e _=>factorNode_clock N hN e)
  have ho : (((List.finRange (wireCount N)).map (ownerNode N fixed (acquirePositive N hN fixed).records)).map Node.clock).sum ≤
      wireCount N*ownerBudget N fixed.length := by
    have hgen (xs : List (Fin (wireCount N))) :
        ((xs.map (ownerNode N fixed (acquirePositive N hN fixed).records)).map Node.clock).sum ≤
          xs.length*ownerBudget N fixed.length := by
      induction xs with
      | nil => simp
      | cons v vs ih =>
        have hh:=ownerNode_clock N hN fixed v
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
    simpa only [List.length_finRange] using hgen (List.finRange (wireCount N))
  dsimp only [acquirePositive] at ho ⊢
  simp only [SemiprimePaidFiniteEnumerationLists.fin_value,List.length_map,List.length_finRange]
  rw [hps]
  unfold budget
  omega

end RiemannGaussian.SemiprimeD1RootTensorTablesBounds
