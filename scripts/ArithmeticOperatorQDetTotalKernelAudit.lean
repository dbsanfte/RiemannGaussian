/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Finite total prime-trace kernel

The actual cyclotomic-to-prime-trace bridge is the preceding isolated
ArithmeticOperatorQDetUnsaturatedTraceAudit. This leaf proves the arithmetic
kernel's finite arbitrary-prime-weight reindexing and saturated endpoint.
It proves no new cyclotomic bridge, Mellin continuation or source theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace OpenAIReview.QDetTotalKernel

/-- Literal rational primes at the physical integer cutoff. -/
def primes (X : ℕ) : Finset ℕ := (Finset.Icc 2 X).filter Nat.Prime

/-- Allowed nontrivial finite-field orders, each counted once. -/
def orders (N p : ℕ) : Finset ℕ :=
  (p-1).divisors.filter (fun d => 2≤d ∧ d≤N)

/-- Full-residue prime incidence count; division by p is outside this integer count. -/
def count (N p : ℕ) : ℕ := (if p≤N then 1 else 0)+∑ d∈orders N p,d.totient

/-- The divisor set equals the actual cutoff interval filtered by divisibility. -/
theorem orders_eq (N p : ℕ) (hp : 2≤p) :
    orders N p=(Finset.Icc 2 N).filter (fun d => d∣p-1) := by
  ext d
  simp only [orders,Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
  have hn : p-1≠0 := by omega
  tauto

/-- The finite residue count in interval rather than divisor notation. -/
theorem count_range (N p : ℕ) (hp : 2≤p) :
    count N p=(if p≤N then 1 else 0)+
      ∑ d∈Finset.Icc 2 N,if d∣p-1 then d.totient else 0 := by
  rw [count,orders_eq N p hp,Finset.sum_filter]

/-- Complete-prime trace reindexing holds for every scalar weight on literal primes. -/
theorem arbitrary_weights (N X : ℕ) (w : ℕ→ℂ) :
    (∑ p∈primes X,w p*(count N p : ℂ))=
      (∑ p∈primes X,if p≤N then w p else 0)+
      ∑ d∈Finset.Icc 2 N,(d.totient : ℂ)*
        ∑ p∈primes X,if d∣p-1 then w p else 0 := by
  have hs : (∑ p∈primes X,w p*(count N p : ℂ))=
      ∑ p∈primes X,((if p≤N then w p else 0)+
        ∑ d∈Finset.Icc 2 N,if d∣p-1 then w p*(d.totient : ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hprime := (Finset.mem_filter.mp hp).2
    rw [count_range N p hprime.two_le]
    push_cast
    rw [mul_add,Finset.mul_sum]
    congr 1
    · split_ifs <;> simp
    · apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
  rw [hs,Finset.sum_add_distrib,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp [mul_comm]

/-- In the saturated window every nontrivial divisor order is available. -/
theorem orders_saturated (N p : ℕ) (hp : 2≤p) (hpN : p≤N) :
    orders N p=(p-1).divisors.erase 1 := by
  ext d
  constructor
  · intro hd
    obtain ⟨hm,hd2,_⟩:=Finset.mem_filter.mp hd
    exact Finset.mem_erase.mpr ⟨by omega,hm⟩
  · intro hd
    obtain ⟨hd1,hm⟩:=Finset.mem_erase.mp hd
    have hpn : 0<p-1 := by omega
    have hdiv := (Nat.mem_divisors.mp hm).1
    have hdpos := Nat.pos_of_dvd_of_pos hdiv hpn
    have hdle := Nat.le_of_dvd hpn hdiv
    exact Finset.mem_filter.mpr ⟨hm,by omega,by omega⟩

/-- The arithmetic count is p−1 at the saturated endpoint. -/
theorem count_saturated (N p : ℕ) (hp : 2≤p) (hpN : p≤N) : count N p=p-1 := by
  have hm : 1∈(p-1).divisors := Nat.one_mem_divisors.mpr (by omega)
  have hs := Finset.sum_erase_add (s:=(p-1).divisors) (f:=Nat.totient) hm
  rw [Nat.sum_totient] at hs
  simpa [count,orders_saturated N p hp hpN,hpN,Nat.totient_one,add_comm] using hs

/-- For X≤N the complete prime kernel is uncoded, for arbitrary literal-prime weights. -/
theorem saturated_arbitrary_weights (N X : ℕ) (hXN : X≤N) (w : ℕ→ℂ) :
    (∑ p∈primes X,w p*(count N p : ℂ))=
      ∑ p∈primes X,w p*((p-1 : ℕ) : ℂ) := by
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpX,hprime⟩:=Finset.mem_filter.mp hp
  rw [count_saturated N p hprime.two_le ((Finset.mem_Icc.mp hpX).2.trans hXN)]

end OpenAIReview.QDetTotalKernel

#lint+ in OpenAIReview.QDetTotalKernel

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty total-kernel audit."
  logInfo m!"Total-kernel audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-qdet-total-source-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-qdet-total-source-gate/axioms.json"
    (Json.mkObj [("scope",toJson "literal-prime finite divisor kernel, arbitrary scalar reindexing and saturated endpoint; actual cyclotomic bridge in preceding isolated leaf, total Mellin source unproved"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr reports)]).pretty
