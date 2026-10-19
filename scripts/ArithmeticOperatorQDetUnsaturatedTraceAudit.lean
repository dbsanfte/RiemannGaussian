/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Literal unsaturated prime trace

For p>N the actual once-counted cyclotomic product's prime incidence,
averaged over unit residue representatives that are genuine integer bases,
is exactly a truncated divisor sum on p−1. No prime-zero source, proper-power
estimate or assertion that a complete trace equals one common base is formalized.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace OpenAIReview.QDetUnsaturatedTrace

/-- The same once-counted integer product, with index one omitted. -/
def productValue (b N : ℕ) : ℤ :=
  ∏ n∈Finset.Icc 2 N,(Polynomial.cyclotomic n ℤ).eval (b : ℤ)

/-- A unit residue represented by an actual integer base at least p. -/
def representative {p : ℕ} (u : (ZMod p)ˣ) : ℕ := (u : ZMod p).val+p

/-- The representatives are permitted bases, rather than the artificial base one. -/
theorem representative_ge_two {p : ℕ} [hp : Fact p.Prime] (u : (ZMod p)ˣ) :
    2≤representative u := by
  have := hp.out.two_le
  unfold representative
  omega

/-- Reducing the integer representative restores its literal unit residue. -/
theorem representative_cast {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) :
    (representative u : ZMod p)=u := by
  simp [representative]

/-- The integer product maps to the actual finite-field cyclotomic product. -/
theorem product_cast {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) (N : ℕ) :
    Int.castRingHom (ZMod p) (productValue (representative u) N)=
      ∏ n∈Finset.Icc 2 N,(Polynomial.cyclotomic n (ZMod p)).eval (u : ZMod p) := by
  simp only [productValue,map_prod]
  apply Finset.prod_congr rfl
  intro n _
  rw [← Polynomial.cyclotomic.eval_apply]
  congr 1
  simpa using representative_cast u

/-- Below the characteristic, cyclotomic roots have exactly the prescribed order. -/
theorem root_iff_order {p : ℕ} [Fact p.Prime] (N n : ℕ) (hNp : N<p)
    (hn : n∈Finset.Icc 2 N) (u : (ZMod p)ˣ) :
    (Polynomial.cyclotomic n (ZMod p)).eval (u : ZMod p)=0 ↔ orderOf u=n := by
  have hnpos : 0<n := by have := (Finset.mem_Icc.mp hn).1; omega
  have hnlt : n<p := (Finset.mem_Icc.mp hn).2.trans_lt hNp
  have : NeZero (n : ZMod p) := ⟨by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt hnpos hnlt) ((ZMod.natCast_eq_zero_iff _ _).1 h)⟩
  rw [← Polynomial.IsRoot.def,Polynomial.isRoot_cyclotomic_iff,
    IsPrimitiveRoot.iff_orderOf,orderOf_units]

/-- Exact native prime incidence at every literal unit representative. -/
theorem incidence_iff_order {p : ℕ} [Fact p.Prime] (N : ℕ) (hNp : N<p)
    (u : (ZMod p)ˣ) :
    (p : ℤ)∣productValue (representative u) N ↔ orderOf u∈Finset.Icc 2 N := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change Int.castRingHom (ZMod p) (productValue (representative u) N)=0 ↔ _
  rw [product_cast,Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨n,hn,hr⟩
    have ho:=(root_iff_order N n hNp hn u).1 hr
    rwa [ho]
  · intro hu
    exact ⟨orderOf u,hu,(root_iff_order N (orderOf u) hNp hu u).2 rfl⟩

/-- Complete unit-residue trace of actual integer prime divisibility. -/
def primeTrace (p N : ℕ) [Fact p.Prime] : ℕ :=
  (Finset.univ.filter (fun u : (ZMod p)ˣ =>
    (p : ℤ)∣productValue (representative u) N)).card

/-- Exact unsaturated prime trace, with the genuine cyclic-field divisor weights. -/
theorem primeTrace_eq {p : ℕ} [Fact p.Prime] (N : ℕ) (hNp : N<p) :
    primeTrace p N=∑ d∈Finset.Icc 2 N,if d∣p-1 then d.totient else 0 := by
  classical
  have hfilter : (Finset.univ.filter (fun u : (ZMod p)ˣ =>
      (p : ℤ)∣productValue (representative u) N))=
      Finset.univ.filter (fun u : (ZMod p)ˣ => orderOf u∈Finset.Icc 2 N) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,incidence_iff_order N hNp]
  rw [primeTrace,hfilter,← Finset.sum_card_fiberwise_eq_card_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d∣p-1
  · have hc := IsCyclic.card_orderOf_eq_totient (α:=(ZMod p)ˣ) (d:=d)
      (by rw [ZMod.card_units]; exact hd)
    simpa only [hd,↓reduceIte] using hc
  · simp only [hd,↓reduceIte]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have ho := (Finset.mem_filter.mp hu).2
    have hdiv := orderOf_dvd_card (x:=u)
    rw [ZMod.card_units,ho] at hdiv
    exact hd hdiv

end OpenAIReview.QDetUnsaturatedTrace

#lint+ in OpenAIReview.QDetUnsaturatedTrace

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
  unless declarations>0 do throwError "Empty unsaturated trace audit."
  logInfo m!"Unsaturated trace audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-qdet-unsaturated-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-qdet-unsaturated-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual integer cyclotomic product, unit-representative prime incidence and complete unsaturated cyclic-field trace; higher depths and source paper-level"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr reports)]).pretty
