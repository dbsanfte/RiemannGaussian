/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Primitive witnesses constrain actual signed cyclotomic products

An actual primitive root modulo a literal prime isolates its cyclotomic
factor below the next possible collision. Integrality of the actual rational
product then forces that factor's exponent to be nonnegative. Primitive-prime
existence, the global growing-row corollary and every Mellin/source statement
remain paper-level. No prime-power phase is linearized here.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace OpenAIReview.TotalTraceSource

/-- The literal integer cyclotomic value at the common integer base. -/
def value (b d : ℕ) : ℤ := (Polynomial.cyclotomic d ℤ).eval (b : ℤ)

/-- The actual rational product, allowing signed order exponents. -/
def signedProduct (b M : ℕ) (beta : ℕ → ℤ) : ℚ :=
  ∏ e ∈ Finset.Icc 2 M, (value b e : ℚ) ^ beta e

/-- Every factor is positive at an allowed integer base. -/
theorem value_pos (b d : ℕ) (hb : 2 ≤ b) : 0 < value b d :=
  Polynomial.cyclotomic_pos' d (by exact_mod_cast (show 1 < b by omega))

/-- Divisibility of the actual integer value is exactly the finite-field root condition. -/
theorem dvd_value_iff_root (b e q : ℕ) [Fact q.Prime] :
    (q : ℤ) ∣ value b e ↔
      (Polynomial.cyclotomic e (ZMod q)).IsRoot (b : ZMod q) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (Int.castRingHom (ZMod q)) (value b e) = 0 ↔ _
  have hc : (Int.castRingHom (ZMod q)) (value b e) =
      (Polynomial.cyclotomic e (ZMod q)).eval (b : ZMod q) := by
    simpa [value] using
      (Polynomial.cyclotomic.eval_apply (b : ℤ) e (Int.castRingHom (ZMod q))).symm
  rw [hc, Polynomial.IsRoot.def]

/-- A primitive witness has prime strictly larger than its order. -/
theorem primitive_order_lt_prime (b d q : ℕ) [hq : Fact q.Prime]
    (hd : 0 < d) (hprim : IsPrimitiveRoot (b : ZMod q) d) : d < q := by
  have hdiv : d ∣ q - 1 := hprim.dvd_of_pow_eq_one _
    (ZMod.pow_card_sub_one_eq_one (hprim.ne_zero hd.ne'))
  have hle := Nat.le_of_dvd (show 0 < q - 1 by have := hq.out.two_le; omega) hdiv
  omega

/-- Before the next possible prime collision, the primitive witness detects exactly one
actual cyclotomic factor, including indices divisible by the characteristic. -/
theorem primitive_isolation (b d q M e : ℕ) [hq : Fact q.Prime]
    (hd : 0 < d) (he : 0 < e) (heM : e ≤ M) (hM : M < d * q)
    (hprim : IsPrimitiveRoot (b : ZMod q) d) :
    (q : ℤ) ∣ value b e ↔ e = d := by
  rw [dvd_value_iff_root]
  constructor
  · intro hr
    have hpow : (b : ZMod q) ^ e = 1 :=
      Polynomial.isRoot_of_unity_of_root_cyclotomic
        (Nat.mem_divisors.mpr ⟨dvd_rfl, he.ne'⟩) hr
    have hde : d ∣ e := hprim.dvd_of_pow_eq_one e hpow
    have hdq : d < q := primitive_order_lt_prime b d q hd hprim
    have hqe : ¬q ∣ e := by
      intro h
      obtain ⟨k, rfl⟩ := hde
      have hqd : ¬q ∣ d := Nat.not_dvd_of_pos_of_lt hd hdq
      have hqk : q ∣ k := (hq.out.dvd_mul.mp h).resolve_left hqd
      have hk : 0 < k := by nlinarith
      have hle := Nat.le_of_dvd hk hqk
      nlinarith
    have : NeZero (e : ZMod q) := ⟨by
      intro h
      exact hqe ((ZMod.natCast_eq_zero_iff _ _).mp h)⟩
    have hp := Polynomial.isRoot_cyclotomic_iff.mp hr
    exact hp.eq_orderOf.trans hprim.eq_orderOf.symm
  · rintro rfl
    exact hprim.isRoot_cyclotomic hd

/-- The simpler square-root shell condition suffices for native prime isolation. -/
theorem primitive_isolation_of_square (b d q M e : ℕ) [Fact q.Prime]
    (hd : 0 < d) (he : 0 < e) (heM : e ≤ M) (hM : M < d * d)
    (hprim : IsPrimitiveRoot (b : ZMod q) d) :
    (q : ℤ) ∣ value b e ↔ e = d := by
  apply primitive_isolation b d q M e hd he heM _ hprim
  have := primitive_order_lt_prime b d q hd hprim
  nlinarith

private theorem valuation_prod {q : ℕ} [Fact q.Prime] (s : Finset ℕ)
    (f : ℕ → ℚ) (hf : ∀ e ∈ s, f e ≠ 0) :
    padicValRat q (∏ e ∈ s, f e) = ∑ e ∈ s, padicValRat q (f e) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    rw [Finset.prod_insert he, Finset.sum_insert he, padicValRat.mul
      (hf e (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- Exact valuation of the actual signed product; every order remains present. -/
theorem signedProduct_valuation (b M q : ℕ) [Fact q.Prime] (hb : 2 ≤ b)
    (beta : ℕ → ℤ) :
    padicValRat q (signedProduct b M beta) =
      ∑ e ∈ Finset.Icc 2 M, beta e * (padicValInt q (value b e) : ℤ) := by
  rw [signedProduct, valuation_prod]
  · simp
  · intro e _
    apply zpow_ne_zero
    exact_mod_cast (value_pos b e hb).ne'

/-- Integrality at ONE common base forces the isolated factor's actual signed exponent
to be nonnegative. The primitive witness is supplied, not postulated to exist globally. -/
theorem integral_exponent_nonneg (b M d q : ℕ) [hq : Fact q.Prime]
    (hb : 2 ≤ b) (hd : 2 ≤ d) (hdM : d ≤ M) (hM : M < d * q)
    (hprim : IsPrimitiveRoot (b : ZMod q) d) (beta : ℕ → ℤ)
    (hint : ∃ z : ℤ, signedProduct b M beta = (z : ℚ)) : 0 ≤ beta d := by
  have hval : padicValRat q (signedProduct b M beta) =
      beta d * (padicValInt q (value b d) : ℤ) := by
    rw [signedProduct_valuation b M q hb beta]
    apply Finset.sum_eq_single d
    · intro e he hed
      have he' := Finset.mem_Icc.mp he
      have hn : ¬(q : ℤ) ∣ value b e := by
        rw [primitive_isolation b d q M e (by omega) (by omega) he'.2 hM hprim]
        exact hed
      simp [padicValInt.eq_zero_of_not_dvd hn]
    · intro h
      exact (h (Finset.mem_Icc.mpr ⟨hd, hdM⟩)).elim
  have hdiv : (q : ℤ) ∣ value b d :=
    (dvd_value_iff_root b d q).mpr (hprim.isRoot_cyclotomic (by omega))
  have hn : padicValInt q (value b d) ≠ 0 := by
    intro hz
    rcases padicValInt.eq_zero_iff.mp hz with h | h | h
    · exact hq.out.ne_one h
    · exact (value_pos b d hb).ne' h
    · exact h hdiv
  have hp : (0 : ℤ) < padicValInt q (value b d) := by exact_mod_cast Nat.pos_of_ne_zero hn
  obtain ⟨z, hz⟩ := hint
  have hnonneg : 0 ≤ padicValRat q (signedProduct b M beta) := by
    rw [hz, padicValRat.of_int]
    exact Nat.cast_nonneg _
  rw [hval] at hnonneg
  nlinarith

/-- The literal square-root shell corollary, with the same actual product and witness. -/
theorem integral_exponent_nonneg_of_square (b M d q : ℕ) [Fact q.Prime]
    (hb : 2 ≤ b) (hd : 2 ≤ d) (hdM : d ≤ M) (hM : M < d * d)
    (hprim : IsPrimitiveRoot (b : ZMod q) d) (beta : ℕ → ℤ)
    (hint : ∃ z : ℤ, signedProduct b M beta = (z : ℚ)) : 0 ≤ beta d := by
  apply integral_exponent_nonneg b M d q hb hd hdM _ hprim beta hint
  have := primitive_order_lt_prime b d q (by omega) hprim
  nlinarith

/-- A literal nonvacuous witness: base two has exact order four modulo five. -/
theorem base_two_order_four : IsPrimitiveRoot (2 : ZMod 5) 4 := by
  rw [IsPrimitiveRoot.iff (by omega : 0 < 4)]
  constructor
  · decide
  · intro l hl hl4
    interval_cases l <;> decide

/-- Hence every actual integral signed product through index nineteen has a
nonnegative fourth exponent at base two. -/
theorem base_two_fourth_exponent (beta : ℕ → ℤ)
    (hint : ∃ z : ℤ, signedProduct 2 19 beta = (z : ℚ)) : 0 ≤ beta 4 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact integral_exponent_nonneg 2 19 4 5 (by omega) (by omega)
    (by omega) (by norm_num) base_two_order_four beta hint

end OpenAIReview.TotalTraceSource

#lint+ in OpenAIReview.TotalTraceSource

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
  unless declarations > 0 do throwError "Empty primitive-witness audit."
  logInfo m!"Primitive-witness audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-total-trace-frontier-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-total-trace-frontier-gate/axioms.json"
    (Json.mkObj [("scope", toJson "actual cyclotomic signed-product integrality and supplied primitive witness; existence and source remain paper-level"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
