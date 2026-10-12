/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorPFreeUpperAudit
import RiemannGaussian.ArithmeticOperatorKummerCutoff
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Divisibility times the upper carry of an unaligned prime dilation

An unaligned base-p row adds the n-divisibility tower to the upper row
choose(n-1,k). Those towers cannot both contribute at a large prime:
the upper row has no first carry when p divides n. Thus their interaction
requires p^2 <= n and, at the literal cutoff p*n <= X, p^3 <= X.

This is a finite support theorem, not a source-small collective estimate.
Every carry order and an arbitrary complex exterior weight remain intact.
Neither cofactor-row cardinality nor a physical cutoff discrepancy is paid.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ArithmeticOperatorKummerDilationSupport
open ArithmeticOperatorPFreeUpperAudit

/-- Immediately before a divisible endpoint, the complete low digit has
no carry, including every nonunit and both binomial endpoints. -/
theorem upper_first_carry_absent {d n k : ℕ} (hd : 0<d) (hn : 0<n)
    (hdiv : d∣n) (hk : k<n) : k%d+(n-1-k)%d<d := by
  obtain ⟨a,ha⟩ := hdiv
  have ha0 : 0<a := by nlinarith
  have he : n=a*d := by simpa only [Nat.mul_comm] using ha
  rw [he]
  apply common_row_first_carry_absent ha0 hd
  omega

/-- With no second possible level, the entire actual upper-row valuation
is zero. The multiplier n/p need not be prime. -/
theorem upper_valuation_zero_of_lt_square {p n k : ℕ} (hp : p.Prime)
    (hn : 0<n) (hdiv : p∣n) (hk : k<n) (hsmall : n<p^2) :
    padicValNat p ((n-1).choose k)=0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hk' : k≤n-1 := by omega
  have hlog : Nat.log p (n-1)<2 :=
    Nat.log_lt_of_lt_pow' (by norm_num) (by omega)
  rw [padicValNat_choose hk' hlog]
  have hi : Finset.Ico 1 2=({1} : Finset ℕ) := by ext i;simp
  rw [hi]
  have hc := upper_first_carry_absent hp.pos hn hdiv hk
  simp only [pow_one,Finset.filter_singleton]
  rw [ite_eq_right (Nat.not_le_of_gt hc)]
  rfl

/-- The nonlinear divisibility/upper-valuation interaction is genuinely
confined to p^2 <= n. This is actual binomial arithmetic, not a free array. -/
theorem valuation_interaction_square_support {p n k : ℕ} (hp : p.Prime)
    (hn : 0<n) (hk : k<n)
    (hactive : 0<padicValNat p n*padicValNat p ((n-1).choose k)) : p^2≤n := by
  let : Fact p.Prime := ⟨hp⟩
  have hv : padicValNat p n≠0 := by intro h;rw [h,zero_mul] at hactive;omega
  have hd : p∣n := by
    by_contra h
    exact hv (padicValNat.eq_zero_of_not_dvd h)
  by_contra h
  rw [upper_valuation_zero_of_lt_square hp hn hd hk (by omega),mul_zero] at hactive
  omega

/-- The native total endpoint is p*n, so the same interaction is supported
at p^3 <= X; no cutoff p*n is replaced by an asymptotic endpoint. -/
theorem valuation_interaction_cube_support {p n k X : ℕ} (hp : p.Prime)
    (hn : 0<n) (hk : k<n) (hcut : p*n≤X)
    (hactive : 0<padicValNat p n*padicValNat p ((n-1).choose k)) : p^3≤X := by
  have hs := valuation_interaction_square_support hp hn hk hactive
  calc
    p^3=p*p^2 := by ring
    _ ≤ p*n := Nat.mul_le_mul_left p hs
    _ ≤ X := hcut

/-- Order-by-order support: a divisibility level and any active upper
carry force a second upper level before any phases are combined. -/
theorem layer_interaction_square_support {p n k r s : ℕ} (hp : p.Prime)
    (hn : 0<n) (hk : k<n) (hr : 0<r) (hs : 0<s)
    (hdiv : p^r∣n) (hcarry : p^s≤k%(p^s)+(n-1-k)%(p^s)) : p^2≤n := by
  have hd : p∣n := (dvd_pow_self p (Nat.ne_of_gt hr)).trans hdiv
  have hs2 : 2≤s := by
    by_contra h
    have he : s=1 := by omega
    rw [he,pow_one] at hcarry
    have hc := upper_first_carry_absent hp.pos hn hd hk
    omega
  have htotal : k+(n-1-k)=n-1 := by omega
  calc
    p^2 ≤ p^s := Nat.pow_le_pow_right hp.pos hs2
    _ ≤ k%(p^s)+(n-1-k)%(p^s) := hcarry
    _ ≤ k+(n-1-k) := Nat.add_le_add (Nat.mod_le _ _) (Nat.mod_le _ _)
    _ ≤ n := by omega

theorem layer_interaction_cube_support {p n k r s X : ℕ} (hp : p.Prime)
    (hn : 0<n) (hk : k<n) (hr : 0<r) (hs : 0<s) (hcut : p*n≤X)
    (hdiv : p^r∣n) (hcarry : p^s≤k%(p^s)+(n-1-k)%(p^s)) : p^3≤X := by
  have hh := layer_interaction_square_support hp hn hk hr hs hdiv hcarry
  calc
    p^3=p*p^2 := by ring
    _ ≤ p*n := Nat.mul_le_mul_left p hh
    _ ≤ X := hcut

/-- Full complex weights, including both shifted prime-power phases,
cannot move an absent carry outside its exact native support. -/
theorem phased_layer_zero_of_cube_lt {p n k r s X : ℕ} (hp : p.Prime)
    (hn : 0<n) (hk : k<n) (hr : 0<r) (hs : 0<s) (hcut : p*n≤X)
    (hlarge : X<p^3) (weight : ℂ) :
    weight*(if p^r∣n ∧ p^s≤k%(p^s)+(n-1-k)%(p^s) then (1 : ℂ) else 0)=0 := by
  have hnot : ¬(p^r∣n ∧ p^s≤k%(p^s)+(n-1-k)%(p^s)) := by
    rintro ⟨hd,hc⟩
    have hh := layer_interaction_cube_support hp hn hk hr hs hcut hd hc
    omega
  simp only [hnot,ite_false,mul_zero]

/-- Every selected order pair is retained. Codes may contain its actual
height, modular phases and correlated cutoff data; no norms are taken. -/
theorem coded_layers_zero_of_cube_lt {p n k X : ℕ} (hp : p.Prime)
    (hn : 0<n) (hk : k<n) (hcut : p*n≤X) (hlarge : X<p^3)
    (S : Finset (ℕ×ℕ)) (hS : ∀ rs∈S,0<rs.1 ∧ 0<rs.2)
    (weight : ℕ → ℕ → ℂ) :
    (∑ rs∈S,weight rs.1 rs.2*
      (if p^rs.1∣n ∧ p^rs.2≤k%(p^rs.2)+(n-1-k)%(p^rs.2) then (1 : ℂ) else 0))=0 := by
  apply Finset.sum_eq_zero
  intro rs hrs
  exact phased_layer_zero_of_cube_lt hp hn hk (hS rs hrs).1 (hS rs hrs).2 hcut hlarge _

end RiemannGaussian.ArithmeticOperatorKummerDilationSupport

#lint+ in RiemannGaussian.ArithmeticOperatorKummerDilationSupport

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
  unless declarations>0 do throwError "Empty unaligned carry/divisibility audit."
  logInfo m!"Kummer dilation support: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-carry-divisor-inverse"
  IO.FS.writeFile ".lake/arithmetic-operator-carry-divisor-inverse/axioms.json"
    (Json.mkObj [("scope",toJson "exact p^2<=n and p^3<=X support of actual divisibility-times-upper-carry interaction; all prime-power order pairs and complex phases retained; no collective source estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
