/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual mixed-base common depths and the saturated factorial endpoint

Synchronized powers retain the lcm of the two actual orders at EVERY
modulus p^r. Choosing factorial exponents saturates the small physical
window and gives an exact arbitrary-weight ordinary prime-power packet.
No multiplicative-order source, gcd estimate or zero exclusion is assumed.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace OpenAIReview.MixedBaseSource
attribute [local instance] Classical.propDecidable

/-- The common integer uses one exponent and two literal fixed bases. -/
def commonPower (b c n : ℕ) : ℕ := Nat.gcd (b^n-1) (c^n-1)

/-- A literal modulus depth divides a power difference exactly at its actual order. -/
theorem power_depth_order (b n q : ℕ) (hb : 2≤b) :
    q∣b^n-1 ↔ orderOf (b:ZMod q)∣n := by
  have hb0 : 0<b := by omega
  have hle : 1≤b^n := Nat.succ_le_of_lt (pow_pos hb0 n)
  rw [orderOf_dvd_iff_pow_eq_one,←ZMod.natCast_eq_zero_iff (b^n-1) q]
  simp only [Nat.cast_sub hle,Nat.cast_pow,Nat.cast_one,sub_eq_zero]

/-- Synchronized common divisibility retains both orders at the complete depth q. -/
theorem common_depth_orders (b c n q : ℕ) (hb : 2≤b) (hc : 2≤c) :
    q∣commonPower b c n ↔
      Nat.lcm (orderOf (b:ZMod q)) (orderOf (c:ZMod q))∣n := by
  rw [commonPower,Nat.dvd_gcd_iff,power_depth_order b n q hb,
    power_depth_order c n q hc,Nat.lcm_dvd_iff]

/-- The exact finite common-integer observation retains arbitrary complex depth weights. -/
theorem common_depth_weights (b c n : ℕ) (hb : 2≤b) (hc : 2≤c)
    (S : Finset (ℕ×ℕ)) (w : ℕ×ℕ→ℂ) :
    (∑a∈S,if a.1^a.2∣commonPower b c n then w a else 0)=
    ∑a∈S,if Nat.lcm (orderOf (b:ZMod (a.1^a.2)))
      (orderOf (c:ZMod (a.1^a.2)))∣n then w a else 0 := by
  apply Finset.sum_congr rfl
  intro a _
  simp only [common_depth_orders b c n (a.1^a.2) hb hc]

/-- Every eligible small prime-power order divides the actual factorial exponent. -/
theorem factorial_power_coverage (b N p r : ℕ) (hb : 2≤b) (hp : p.Prime)
    (hpb : ¬p∣b) (hcut : p^r≤N) : p^r∣b^(Nat.factorial N)-1 := by
  have ht := (Nat.ModEq.pow_totient (hp.coprime_pow_of_not_dvd (m:=r) hpb)).symm.dvd'
  have hd := (power_depth_order b (p^r).totient (p^r) hb).mp ht
  have htf : (p^r).totient∣Nat.factorial N :=
    Nat.dvd_factorial (Nat.totient_pos.mpr (pow_pos hp.pos _)) ((Nat.totient_le _).trans hcut)
  exact (power_depth_order b (Nat.factorial N) (p^r) hb).mpr (hd.trans htf)

/-- A base prime cannot enter a positive-exponent power difference. -/
theorem base_prime_absent (b n p : ℕ) (hb : 2≤b) (hp : p.Prime)
    (hn : 0<n) (hpb : p∣b) : ¬p∣b^n-1 := by
  intro h
  have hpow : p∣b^n := dvd_pow hpb hn.ne'
  have hb0 : 0<b := by omega
  have hle : 1≤b^n := Nat.succ_le_of_lt (pow_pos hb0 n)
  have hone : p∣1 := by
    simpa only [Nat.sub_sub_self hle] using Nat.dvd_sub hpow h
  exact hp.not_dvd_one hone

/-- The factorial mixed-base common integer has exactly uncoded physical support. -/
theorem factorial_common_support (b c N p r : ℕ) (hb : 2≤b) (hc : 2≤c)
    (hp : p.Prime) (hr : 0<r) (hcut : p^r≤N) :
    p^r∣commonPower b c (Nat.factorial N) ↔ ¬p∣b*c := by
  constructor
  · intro hd
    have hboth := Nat.dvd_gcd_iff.mp hd
    intro hbc
    rcases hp.dvd_mul.mp hbc with hpb|hpc
    · exact base_prime_absent b (Nat.factorial N) p hb hp (Nat.factorial_pos _) hpb
        ((dvd_pow_self p hr.ne').trans hboth.1)
    · exact base_prime_absent c (Nat.factorial N) p hc hp (Nat.factorial_pos _) hpc
        ((dvd_pow_self p hr.ne').trans hboth.2)
  · intro hbc
    exact Nat.dvd_gcd
      (factorial_power_coverage b N p r hb hp (fun h=>hbc (dvd_mul_of_dvd_left h _)) hcut)
      (factorial_power_coverage c N p r hc hp (fun h=>hbc (dvd_mul_of_dvd_right h _)) hcut)

/-- The whole saturated common-integer packet retains every prescribed prime-power weight. -/
theorem factorial_common_weights (b c N : ℕ) (hb : 2≤b) (hc : 2≤c)
    (S : Finset (ℕ×ℕ))
    (hS : ∀a∈S,a.1.Prime ∧ 0<a.2 ∧ a.1^a.2≤N) (w : ℕ×ℕ→ℂ) :
    (∑a∈S,if a.1^a.2∣commonPower b c (Nat.factorial N) then w a else 0)=
      ∑a∈S,if ¬a.1∣b*c then w a else 0 := by
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨hp,hr,hcut⟩ := hS a ha
  simp only [factorial_common_support b c N a.1 a.2 hb hc hp hr hcut]

end OpenAIReview.MixedBaseSource
#lint+ in OpenAIReview.MixedBaseSource

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    details := details.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  logInfo m!"Mixed base source audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/arithmetic-operator-mixed-base-source-gate/axioms.json"
    (Json.mkObj [("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr details)]).pretty
