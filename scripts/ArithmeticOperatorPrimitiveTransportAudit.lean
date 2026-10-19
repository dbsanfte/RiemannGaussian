/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorTotalTraceSourceAudit
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# Actual primitive-prime transport through cyclotomic descendants

This leaf proves exact incidence for a supplied literal primitive root and
the actual signed-product valuation ledger at all descendants. It also
proves that a nonprimitive child has a unique possible nonprimitive prime.
Descendant valuation one, exceptional two-adic head weights, primitive-prime
existence and the collective height/source estimates remain paper-level.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace OpenAIReview.PrimitiveTransport
open TotalTraceSource
attribute [local instance] Classical.propDecidable

/-- The exact native root-incidence chain, including characteristic-divisible indices
and primitive order one. No valuation-one assertion is implicit here. -/
theorem dvd_value_iff_prime_chain (b d q e : ℕ) [hq : Fact q.Prime]
    (hd : 0 < d) (he : 0 < e) (hprim : IsPrimitiveRoot (b : ZMod q) d) :
    (q : ℤ) ∣ value b e ↔ ∃ j : ℕ, e = d * q ^ j := by
  rw [dvd_value_iff_root]
  constructor
  · intro hr
    obtain ⟨j, m, hqm, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd he.ne' q hq.out.ne_one
    have : NeZero (m : ZMod q) := ⟨by
      intro h
      exact hqm ((ZMod.natCast_eq_zero_iff _ _).mp h)⟩
    have hp : IsPrimitiveRoot (b : ZMod q) m := by
      apply Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp
      simpa [hem] using hr
    have hmd : m = d := hp.unique hprim
    refine ⟨j, ?_⟩
    simpa [hmd, Nat.mul_comm] using hem
  · rintro ⟨j, rfl⟩
    have hdq := primitive_order_lt_prime b d q hd hprim
    have : NeZero (d : ZMod q) := ⟨by
      intro h
      exact (Nat.not_dvd_of_pos_of_lt hd hdq)
        ((ZMod.natCast_eq_zero_iff _ _).mp h)⟩
    have hr : (Polynomial.cyclotomic (q ^ j * d) (ZMod q)).IsRoot
        (b : ZMod q) :=
      Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mpr hprim
    simpa [Nat.mul_comm] using hr

/-- Every prime dividing a nonprimitive child is at most the transported prime.
This is a statement about index primes, not primes dividing its primitive value part. -/
theorem nonprimitive_index_prime_le (b d q e r : ℕ) [hq : Fact q.Prime]
    (hd : 0 < d) (he : 0 < e) (hprim : IsPrimitiveRoot (b : ZMod q) d)
    (hdiv : (q : ℤ) ∣ value b e) (hr : r.Prime) (hre : r ∣ e) : r ≤ q := by
  obtain ⟨j, rfl⟩ := (dvd_value_iff_prime_chain b d q e hd he hprim).mp hdiv
  rcases hr.dvd_mul.mp hre with hrd | hrq
  · have hrd' := Nat.le_of_dvd hd hrd
    have hdq := primitive_order_lt_prime b d q hd hprim
    omega
  · have hrq' : r ∣ q := hr.dvd_of_dvd_pow hrq
    exact Nat.le_of_dvd hq.out.pos hrq'

/-- A child distinct from the primitive root order has its transported prime in its index. -/
theorem nonprimitive_prime_dvd_index (b d q e : ℕ) [hq : Fact q.Prime]
    (hd : 0 < d) (he : 0 < e) (hprim : IsPrimitiveRoot (b : ZMod q) d)
    (hdiv : (q : ℤ) ∣ value b e) (hed : e ≠ d) : q ∣ e := by
  obtain ⟨j, hj⟩ := (dvd_value_iff_prime_chain b d q e hd he hprim).mp hdiv
  have hjpos : 0 < j := by
    by_contra h
    have : j = 0 := by omega
    simp [this] at hj
    exact hed hj
  rw [hj]
  exact dvd_mul_of_dvd_right (dvd_pow_self q hjpos.ne') d

/-- The same actual cyclotomic child cannot pay two different nonprimitive primes. -/
theorem nonprimitive_prime_unique (b d1 d2 q1 q2 e : ℕ)
    [hq1 : Fact q1.Prime] [hq2 : Fact q2.Prime]
    (hd1 : 0 < d1) (hd2 : 0 < d2) (he : 0 < e)
    (hp1 : IsPrimitiveRoot (b : ZMod q1) d1)
    (hp2 : IsPrimitiveRoot (b : ZMod q2) d2)
    (hv1 : (q1 : ℤ) ∣ value b e) (hv2 : (q2 : ℤ) ∣ value b e)
    (he1 : e ≠ d1) (he2 : e ≠ d2) : q1 = q2 := by
  have h1 := nonprimitive_prime_dvd_index b d1 q1 e hd1 he hp1 hv1 he1
  have h2 := nonprimitive_prime_dvd_index b d2 q2 e hd2 he hp2 hv2 he2
  exact Nat.le_antisymm
    (nonprimitive_index_prime_le b d2 q2 e q1 hd2 he hp2 hv2 hq1.out h1)
    (nonprimitive_index_prime_le b d1 q1 e q2 hd1 he hp1 hv1 hq2.out h2)

/-- The actual all-index valuation ledger also covers primitive order one, hence
the two-adic chain. Every exceptional head valuation stays literal. -/
theorem signedProduct_chain_valuation (b M d q : ℕ) [Fact q.Prime]
    (hb : 2 ≤ b) (hd : 0 < d)
    (hprim : IsPrimitiveRoot (b : ZMod q) d) (beta : ℕ → ℤ) :
    padicValRat q (signedProduct b M beta) =
      ∑ e ∈ Finset.Icc 2 M,
        if ∃ j : ℕ, e = d * q ^ j then
          beta e * (padicValInt q (value b e) : ℤ) else 0 := by
  classical
  rw [signedProduct_valuation b M q hb beta]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs with hex
  · rfl
  · have he' := Finset.mem_Icc.mp he
    have hn : ¬(q : ℤ) ∣ value b e := by
      rw [dvd_value_iff_prime_chain b d q e hd (by omega) hprim]
      exact hex
    simp [padicValInt.eq_zero_of_not_dvd hn]

/-- Exact full signed-product valuation, with the actual root valuation and every
actual descendant valuation retained. This is not a reset of any depth phase. -/
theorem signedProduct_transport (b M d q : ℕ) [Fact q.Prime]
    (hb : 2 ≤ b) (hd : 2 ≤ d) (hdM : d ≤ M)
    (hprim : IsPrimitiveRoot (b : ZMod q) d) (beta : ℕ → ℤ) :
    padicValRat q (signedProduct b M beta) =
      beta d * (padicValInt q (value b d) : ℤ) +
      ∑ e ∈ (Finset.Icc 2 M).erase d,
        if ∃ j : ℕ, e = d * q ^ j then
          beta e * (padicValInt q (value b e) : ℤ) else 0 := by
  classical
  rw [signedProduct_valuation b M q hb beta]
  have hm : d ∈ Finset.Icc 2 M := Finset.mem_Icc.mpr ⟨hd, hdM⟩
  rw [← Finset.sum_erase_add _ _ hm, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  split_ifs with hex
  · rfl
  · have he' := Finset.mem_Icc.mp (Finset.mem_of_mem_erase he)
    have hn : ¬(q : ℤ) ∣ value b e := by
      rw [dvd_value_iff_prime_chain b d q e (by omega) (by omega) hprim]
      exact hex
    simp [padicValInt.eq_zero_of_not_dvd hn]

/-- Native integrality gives the exact coupled descendant inequality before estimates.
The non-root chain entries still carry their actual valuations. -/
theorem integral_transport_nonneg (b M d q : ℕ) [Fact q.Prime]
    (hb : 2 ≤ b) (hd : 2 ≤ d) (hdM : d ≤ M)
    (hprim : IsPrimitiveRoot (b : ZMod q) d) (beta : ℕ → ℤ)
    (hint : ∃ z : ℤ, signedProduct b M beta = (z : ℚ)) :
    0 ≤ beta d * (padicValInt q (value b d) : ℤ) +
      ∑ e ∈ (Finset.Icc 2 M).erase d,
        if ∃ j : ℕ, e = d * q ^ j then
          beta e * (padicValInt q (value b e) : ℤ) else 0 := by
  classical
  rw [← signedProduct_transport b M d q hb hd hdM hprim beta]
  obtain ⟨z, hz⟩ := hint
  rw [hz, padicValRat.of_int]
  exact Nat.cast_nonneg _

end OpenAIReview.PrimitiveTransport

#lint+ in OpenAIReview.PrimitiveTransport

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    details := details.push (Json.mkObj [("declaration", toJson n.toString),
      ("isTheorem", toJson ci.isTheorem), ("axioms", toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty primitive-transport audit."
  logInfo m!"Primitive transport audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-primitive-transport-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-primitive-transport-gate/axioms.json"
    (Json.mkObj [("scope", toJson "actual cyclotomic primitive incidence, unique nonprimitive prime and exact signed-product valuation ledger; LTE/source bounds paper-level"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
