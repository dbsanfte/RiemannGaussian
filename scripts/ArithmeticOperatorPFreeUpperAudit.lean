/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorPFreeUnitAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# The larger prime has no carry on an ordinary common binomial row

For actual primes p<q and every k<pq, the q-adic valuation of
choose(pq-1,k) is exactly zero. Consequently q-free extraction is the
literal binomial itself, while the smaller-p extraction remains exact
and unrestricted. This is finite arithmetic infrastructure only; no
prime-index nonlinear zero source or signed arithmetic payment follows.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ArithmeticOperatorPFreeUpperAudit
open ArithmeticOperatorPFreeUnitAudit

theorem common_row_last_digit {p q : ℕ} (hp : 0<p) (hq : 0<q) :
    (p*q-1)%q=q-1 := by
  have he : p*q-1=(p-1)*q+(q-1) := by
    rw [Nat.sub_mul,one_mul]
    have hm : q≤p*q := Nat.le_mul_of_pos_left q hp
    omega
  rw [he,Nat.add_mod]
  simp [Nat.mod_eq_of_lt (by omega : q-1<q)]

/-- The complete low q digit leaves no first carry, at every native order. -/
theorem common_row_first_carry_absent {p q k : ℕ} (hp : 0<p) (hq : 0<q)
    (hk : k≤p*q-1) : k%q+(p*q-1-k)%q<q := by
  have he : k+(p*q-1-k)=p*q-1 := by omega
  have hm : (k%q+(p*q-1-k)%q)%q=q-1 := by
    rw [←Nat.add_mod,he,common_row_last_digit hp hq]
  have hkmod := Nat.mod_lt k hq
  have hnkmod := Nat.mod_lt (p*q-1-k) hq
  by_contra h
  have hs : q≤k%q+(p*q-1-k)%q := by omega
  have hdlo : 0<(k%q+(p*q-1-k)%q)/q := Nat.div_pos hs hq
  have hdhi : (k%q+(p*q-1-k)%q)/q<2 :=
    (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
  have hd : (k%q+(p*q-1-k)%q)/q=1 := by omega
  have ht := Nat.mod_add_div (k%q+(p*q-1-k)%q) q
  rw [hm,hd,mul_one] at ht
  omega

/-- Kummer has only one possible level since p<q; that level is absent.
No binomial coefficient, endpoint or carry valuation is dropped. -/
theorem larger_prime_choose_valuation_zero {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (hk : k<p*q) : padicValNat q ((p*q-1).choose k)=0 := by
  let : Fact q.Prime := ⟨hq⟩
  have hk' : k≤p*q-1 := by omega
  have hn : p*q-1<q^2 := by
    have hm := Nat.mul_lt_mul_of_pos_right hpq hq.pos
    rw [pow_two]
    omega
  have hlog : Nat.log q (p*q-1)<2 := Nat.log_lt_of_lt_pow' (by norm_num) hn
  rw [padicValNat_choose hk' hlog]
  have hi : Finset.Ico 1 2=({1} : Finset ℕ) := by ext i;simp
  rw [hi]
  have hc := common_row_first_carry_absent hp.pos hq.pos hk'
  simp only [pow_one,Finset.filter_singleton]
  rw [ite_eq_right (Nat.not_le_of_gt hc)]
  rfl

theorem larger_prime_choose_not_dvd {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (hk : k<p*q) : ¬q∣(p*q-1).choose k := by
  let : Fact q.Prime := ⟨hq⟩
  have hn : (p*q-1).choose k≠0 := Nat.choose_ne_zero (by omega)
  intro hd
  have hh := one_le_padicValNat_of_dvd hn hd
  rw [larger_prime_choose_valuation_zero hp hq hpq hk] at hh
  omega

/-- The larger-q character is the actual binomial residue, not an approximation. -/
theorem larger_prime_binomialUnit_eq {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (hk : k<p*q) : binomialUnit q (p*q) k=(p*q-1).choose k := by
  unfold binomialUnit
  exact unitPart_of_not_dvd (larger_prime_choose_not_dvd hp hq hpq hk)

/-- Only the larger-prime extraction disappears. All smaller-p valuations
and character values remain in the exact joined atom. -/
theorem unitAtom_larger_leg_eq_raw {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (hk : k<p*q) (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q) :
    unitAtom χ η (p*q) k=
      χ (binomialUnit p (p*q) k)*η (((p*q-1).choose k : ℕ) : ZMod q) := by
  unfold unitAtom
  rw [larger_prime_binomialUnit_eq hp hq hpq hk]

/-- The smaller leg really can carry even on an ordinary two-prime row. -/
theorem smaller_prime_carry_example : padicValNat 2 ((2*3-1).choose 2)=1 := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hc : (2*3-1).choose 2=10 := by decide
  rw [hc]
  have h1 : 1≤padicValNat 2 10 :=
    (padicValNat_dvd_iff_le (p := 2) (a := 10) (n := 1) (by norm_num)).mp (by norm_num)
  have h2 : ¬2≤padicValNat 2 10 := by
    rw [←padicValNat_dvd_iff_le (p := 2) (a := 10) (n := 2) (by norm_num)]
    norm_num
  omega

/-- Extraction retains a nonzero unit in the same example whose raw residue vanishes. -/
theorem smaller_prime_unit_example : binomialUnit 2 (2*3) 2=5 := by
  unfold binomialUnit unitPart
  rw [smaller_prime_carry_example]
  norm_num [Nat.choose]

theorem smaller_prime_raw_and_unit_residues :
    (((2*3-1).choose 2 : ℕ) : ZMod 2)=0 ∧ (binomialUnit 2 (2*3) 2 : ZMod 2)=1 := by
  rw [smaller_prime_unit_example]
  constructor <;> decide

end RiemannGaussian.ArithmeticOperatorPFreeUpperAudit

#lint+ in RiemannGaussian.ArithmeticOperatorPFreeUpperAudit

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
  unless declarations>0 do throwError "Empty larger-prime unit audit."
  logInfo m!"P-free upper audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-pfree-upper"
  IO.FS.writeFile ".lake/arithmetic-operator-pfree-upper/axioms.json"
    (Json.mkObj [("scope",toJson "exact larger-prime valuation-zero on every ordinary common binomial-row order; smaller-prime carry and actual source remain open"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
