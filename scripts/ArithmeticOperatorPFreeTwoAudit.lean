/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorPFreeUnitAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Exact unmarked p-free cofactor-two collapse

At p=2 the genuine unit character is identically one. The other ordinary
prime q has two exact native q-blocks, with both unit endpoints retained.
The resonant complete trace is only the character parity selector; the
uncoded trace has one exact inverse-q endpoint. Arbitrary exterior weights,
physical masks, factorial weights and phases therefore see exactly that
old selector, not an additional unit/carry restriction.

This is ONLY the unmarked ordinary-q cofactor-two class. An explicit
nonconstant valuation mark, p=3, growing p, general q-power rows and
source-sensitive independent estimates remain separate. No actual zero
residue is inferred here from finite rows or diagnostic power models.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorPFreeTwoAudit
open Complex Filter ArithmeticOperatorPFreeUnitAudit

/-- Every genuine positive binomial unit modulo two is one. -/
theorem two_binomialUnit_eq_one {D k : ℕ} (hk : k≤D-1) :
    (binomialUnit 2 D k : ZMod 2)=1 := by
  apply ZMod.natCast_eq_one_iff_odd.mpr
  exact ZMod.natCast_ne_zero_iff_odd.mp (binomialUnit_ne_zero_mod Nat.prime_two hk)

theorem two_character_binomialUnit {D k : ℕ} (hk : k≤D-1)
    (chi : DirichletCharacter ℂ 2) : chi (binomialUnit 2 D k)=1 := by
  rw [two_binomialUnit_eq_one hk,map_one]

/-- The full raw q-residue on the literal row 2q-1, including both endpoints. -/
theorem raw_two_row {q k : ℕ} (hq : q.Prime) (hk : k<2*q) :
    (((2*q-1).choose k : ℕ) : ZMod q)=(-1 : ZMod q)^(k%q) := by
  have h := ArithmeticOperatorLucasUnitAudit.commonRow_first_digit hq
    (by norm_num : (0 : ℕ)<2) k
  rw [mul_comm q 2] at h
  have hd : k/q<2 := (Nat.div_lt_iff_lt_mul hq.pos).mpr (by omega)
  have hchoose : Nat.choose 1 (k/q)=1 := by
    have he : (k/q : ℕ)=0 ∨ (k/q : ℕ)=1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hd)
    rcases he with he|he <;> simp [he]
  simpa only [show (2 : ℕ)-1=1 by norm_num,hchoose,Nat.cast_one,mul_one] using h

/-- No q-carry is lost: the entire row has exact q-valuation zero. -/
theorem two_row_not_dvd {q k : ℕ} (hq : q.Prime) (hk : k<2*q) :
    ¬q∣(2*q-1).choose k := by
  let : Fact q.Prime := ⟨hq⟩
  intro hd
  have hzero : (((2*q-1).choose k : ℕ) : ZMod q)=0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hd
  rw [raw_two_row hq hk] at hzero
  exact (pow_ne_zero _ (show (-1 : ZMod q)≠0 from neg_ne_zero.mpr one_ne_zero)) hzero

theorem two_row_valuation_zero {q k : ℕ} (hq : q.Prime) (hk : k<2*q) :
    padicValNat q ((2*q-1).choose k)=0 :=
  padicValNat.eq_zero_of_not_dvd (two_row_not_dvd hq hk)

/-- The genuine q-unit equals its raw residue because its valuation is ZERO,
not because zero-residue carry layers were silently removed. -/
theorem two_row_unit {q k : ℕ} (hq : q.Prime) (hk : k<2*q) :
    (binomialUnit q (2*q) k : ZMod q)=(-1 : ZMod q)^(k%q) := by
  rw [binomialUnit,unitPart_of_not_dvd (two_row_not_dvd hq hk),raw_two_row hq hk]

/-- Exact joined two-column atom: p=2 is the trivial unit character. -/
theorem unitAtom_two {q k : ℕ} (hq : q.Prime) (hk : k<2*q)
    (chi : DirichletCharacter ℂ 2) (eta : DirichletCharacter ℂ q) :
    unitAtom chi eta (2*q) k=(eta (-1))^(k%q) := by
  unfold unitAtom
  rw [two_character_binomialUnit (by omega) chi,two_row_unit hq hk,
    map_pow,one_mul]

/-- Both native q-blocks have exactly the same uncoded atom sequence. -/
theorem unitAtom_two_blocks {q t : ℕ} (hq : q.Prime) (ht : t<q)
    (chi : DirichletCharacter ℂ 2) (eta : DirichletCharacter ℂ q) :
    unitAtom chi eta (2*q) t=eta (-1)^t ∧
    unitAtom chi eta (2*q) (q+t)=eta (-1)^t := by
  constructor
  · rw [unitAtom_two hq (by omega) chi eta,Nat.mod_eq_of_lt ht]
  · rw [unitAtom_two hq (by omega) chi eta,Nat.add_mod,Nat.mod_self,
      zero_add,Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt ht]

theorem two_character_neg_one (chi : DirichletCharacter ℂ 2) : chi (-1)=1 := by
  have he : (-1 : ZMod 2)=1 := ZMod.neg_one_eq_one_iff.mpr (Or.inr rfl)
  rw [he,map_one]

theorem resonance_two {q : ℕ} (chi : DirichletCharacter ℂ 2)
    (eta : DirichletCharacter ℂ q) :
    resonance chi eta=eta (-1) := by
  rw [resonance,two_character_neg_one,one_mul]

theorem character_parity_sq {q : ℕ} (eta : DirichletCharacter ℂ q) :
    eta (-1)^2=1 := by
  rw [←map_pow]
  simp

theorem character_parity_odd_pow {q n : ℕ} (eta : DirichletCharacter ℂ q)
    (hn : Odd n) : eta (-1)^n=eta (-1) := by
  rw [←map_pow,hn.neg_one_pow]

/-- Resonant coding turns the first entire q-block into one and the second
entire block into eta(-1). No incomplete endpoint is paid. -/
theorem resonant_two_blocks {q t : ℕ} (hq : q.Prime) (hodd : Odd q)
    (ht : t<q) (chi : DirichletCharacter ℂ 2) (eta : DirichletCharacter ℂ q) :
    eta (-1)^t*unitAtom chi eta (2*q) t=1 ∧
    eta (-1)^(q+t)*unitAtom chi eta (2*q) (q+t)=eta (-1) := by
  rw [(unitAtom_two_blocks hq ht chi eta).1,(unitAtom_two_blocks hq ht chi eta).2]
  have hs (t : ℕ) : eta (-1)^t*eta (-1)^t=1 := by
    rw [←mul_pow,←pow_two,character_parity_sq,one_pow]
  constructor
  · exact hs t
  · rw [pow_add,mul_assoc,hs t,mul_one,character_parity_odd_pow eta hodd]

/-- The normalized native resonant trace has lost ALL unit/carry geometry:
only the old character parity selector remains. -/
theorem codedUnitTrace_two_resonant {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    (chi : DirichletCharacter ℂ 2) (eta : DirichletCharacter ℂ q) :
    codedUnitTrace chi eta (2*q) (resonance chi eta)=(1+eta (-1))/2 := by
  have hq0 : (q : ℂ)≠0 := by exact_mod_cast hq.ne_zero
  unfold codedUnitTrace
  rw [resonance_two,show 2*q=q+q by omega,Finset.sum_range_add]
  have hfirst : (∑ k∈Finset.range q,eta (-1)^k*unitAtom chi eta (q+q) k)=(q : ℂ) := by
    have hterm : ∀ k∈Finset.range q,eta (-1)^k*unitAtom chi eta (q+q) k=1 := by
      intro k hk
      simpa only [show q+q=2*q by omega] using
        (resonant_two_blocks hq hodd (Finset.mem_range.mp hk) chi eta).1
    simp_rw [Finset.sum_congr rfl hterm]
    simp
  have hsecond : (∑ k∈Finset.range q,
      eta (-1)^(q+k)*unitAtom chi eta (q+q) (q+k))=(q : ℂ)*eta (-1) := by
    have hterm : ∀ k∈Finset.range q,
        eta (-1)^(q+k)*unitAtom chi eta (q+q) (q+k)=eta (-1) := by
      intro k hk
      simpa only [show q+q=2*q by omega] using
        (resonant_two_blocks hq hodd (Finset.mem_range.mp hk) chi eta).2
    simp_rw [Finset.sum_congr rfl hterm]
    simp
  rw [hfirst,hsecond]
  push_cast
  field_simp [hq0]
  ring

theorem sum_parity_even {q : ℕ} (eta : DirichletCharacter ℂ q) (H : ℕ) :
    (∑ k∈Finset.range (2*H),eta (-1)^k)=(H : ℂ)*(1+eta (-1)) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [show 2*(H+1)=2*H+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,ih]
    have he : eta (-1)^(2*H)=1 := by rw [pow_mul,character_parity_sq,one_pow]
    rw [pow_succ,he]
    push_cast
    ring

theorem sum_parity_odd {q : ℕ} (eta : DirichletCharacter ℂ q) (H : ℕ) :
    (∑ k∈Finset.range (2*H+1),eta (-1)^k)=(H : ℂ)*(1+eta (-1))+1 := by
  rw [Finset.sum_range_succ,sum_parity_even]
  have he : eta (-1)^(2*H)=1 := by rw [pow_mul,character_parity_sq,one_pow]
  rw [he]

/-- Exact uncoded endpoint, not an estimated or completed carry layer. -/
theorem codedUnitTrace_two_uncoded {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    (chi : DirichletCharacter ℂ 2) (eta : DirichletCharacter ℂ q) :
    codedUnitTrace chi eta (2*q) 1=(1+eta (-1))/2+(1-eta (-1))/(2*q) := by
  have hq0 : (q : ℂ)≠0 := by exact_mod_cast hq.ne_zero
  have ht : (∑ k∈Finset.range (2*q),unitAtom chi eta (2*q) k)=
      2*(∑ t∈Finset.range q,eta (-1)^t) := by
    rw [show 2*q=q+q by omega,Finset.sum_range_add]
    have hfirst : (∑ k∈Finset.range q,unitAtom chi eta (q+q) k)=
        ∑ k∈Finset.range q,eta (-1)^k := by
      apply Finset.sum_congr rfl
      intro k hk
      simpa only [show q+q=2*q by omega] using
        (unitAtom_two_blocks hq (Finset.mem_range.mp hk) chi eta).1
    have hsecond : (∑ k∈Finset.range q,unitAtom chi eta (q+q) (q+k))=
        ∑ k∈Finset.range q,eta (-1)^k := by
      apply Finset.sum_congr rfl
      intro k hk
      simpa only [show q+q=2*q by omega] using
        (unitAtom_two_blocks hq (Finset.mem_range.mp hk) chi eta).2
    rw [hfirst,hsecond]
    ring
  obtain ⟨H,hH⟩ := hodd
  have heq : q=2*H+1 := by omega
  have hsum : (∑ t∈Finset.range q,eta (-1)^t)=(H : ℂ)*(1+eta (-1))+1 := by
    simpa only [←heq] using sum_parity_odd eta H
  have hqcast : (q : ℂ)=2*(H : ℂ)+1 := by exact_mod_cast heq
  unfold codedUnitTrace
  simp only [one_pow,one_mul]
  rw [ht,hsum]
  push_cast
  field_simp [hq0]
  rw [hqcast]
  ring

/-- Exact all-mask/all-phase collapse, with every native physical coefficient
retained. No universal free-weight estimate is obtained from this identity. -/
theorem weighted_resonant_collapse (Q : Finset ℕ) (chi : DirichletCharacter ℂ 2)
    (eta : (q : ℕ) → DirichletCharacter ℂ q) (w : ℕ → ℂ)
    (hQ : ∀ q∈Q,q.Prime ∧ Odd q) :
    (∑ q∈Q,w q*codedUnitTrace chi (eta q) (2*q) (resonance chi (eta q)))=
      ∑ q∈Q,w q*((1+eta q (-1))/2) := by
  apply Finset.sum_congr rfl
  intro q hq
  rw [codedUnitTrace_two_resonant (hQ q hq).1 (hQ q hq).2]

/-- The nonresonant-looking uncoded endpoint is exactly a scalar boundary,
not additional independent binomial arithmetic after the join. -/
theorem weighted_uncoded_collapse (Q : Finset ℕ) (chi : DirichletCharacter ℂ 2)
    (eta : (q : ℕ) → DirichletCharacter ℂ q) (w : ℕ → ℂ)
    (hQ : ∀ q∈Q,q.Prime ∧ Odd q) :
    (∑ q∈Q,w q*codedUnitTrace chi (eta q) (2*q) 1)=
      (∑ q∈Q,w q*((1+eta q (-1))/2))+
        ∑ q∈Q,w q*((1-eta q (-1))/(2*q)) := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [codedUnitTrace_two_uncoded (hQ q hq).1 (hQ q hq).2,mul_add]

end RiemannGaussian.ArithmeticOperatorPFreeTwoAudit

#lint+ in RiemannGaussian.ArithmeticOperatorPFreeTwoAudit

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
  unless declarations>0 do throwError "Empty p-free cofactor-two audit."
  logInfo m!"P-free two audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-pfree-two"
  IO.FS.writeFile ".lake/arithmetic-operator-pfree-two/axioms.json"
    (Json.mkObj [("scope",toJson "unmarked ordinary-q cofactor-two trace is exactly the old character parity selector and inverse-q endpoint; no source or arithmetic estimate inferred"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
