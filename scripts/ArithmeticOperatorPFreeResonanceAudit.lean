/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorPFreeUnitAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Resonant p-free units: the unpaid spatial transition moment

The unweighted jump identity is conservation, not cancellation of the row.
The exact first spatial moment below recovers the complete resonant trace.
Both endpoints and every carry crossing remain literal. In particular,
even row lengths are not silently treated as odd.

Actual principal unit characters give a native obstruction to any small
row estimate deduced from zeroth-jump conservation alone. This does not
refute an estimate for prescribed nonprincipal, valuation-marked rows.
No prime-index Mellin residue or RH payment is inferred from this identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ArithmeticOperatorPFreeResonanceAudit
open Complex ArithmeticOperatorPFreeUnitAudit

theorem resonance_sq {p q : ℕ} (χ : DirichletCharacter ℂ p)
    (η : DirichletCharacter ℂ q) : resonance χ η ^ 2 = 1 := by
  have hx : χ (-1)*χ (-1)=1 := by rw [←map_mul]; simp
  have hy : η (-1)*η (-1)=1 := by rw [←map_mul]; simp
  calc
    _ = (χ (-1)*χ (-1))*(η (-1)*η (-1)) := by unfold resonance; ring
    _ = 1 := by rw [hx,hy,mul_one]

/-- Exact finite first-moment summation, with the last endpoint retained. -/
theorem sum_eq_last_sub_weighted_jumps (H : ℕ) (a : ℕ → ℂ) :
    (∑ k∈Finset.range (H+1),a k)=
      ((H+1 : ℕ) : ℂ)*a H-
        ∑ k∈Finset.range H,((k+1 : ℕ) : ℂ)*(a (k+1)-a k) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_range_succ]
    push_cast
    ring

/-- The first spatially weighted transition moment, not its absolute value. -/
def firstCrossingMoment {p q : ℕ} (χ : DirichletCharacter ℂ p)
    (η : DirichletCharacter ℂ q) (D : ℕ) : ℂ :=
  ∑ k∈crossingOrders p q D,((k+1 : ℕ) : ℂ)*resonance χ η^(k+1)*
    (unitAtom χ η D (k+1)-resonance χ η*unitAtom χ η D k)

/-- Exactly the old complete row, recovered from its signed first jump moment.
The boundary is sigma^(D-1), not always one. -/
theorem resonant_trace_eq_first_moment {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) (hpd : p∣D) (hqd : q∣D)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q) :
    codedUnitTrace χ η D (resonance χ η)=
      resonance χ η^(D-1)-firstCrossingMoment χ η D/(D : ℂ) := by
  have hD0 : (D : ℂ)≠0 := by exact_mod_cast hD.ne'
  have he : D-1+1=D := by omega
  have hs := resonance_sq χ η
  have hd (k : ℕ) :
      resonance χ η^(k+1)*(unitAtom χ η D (k+1)-resonance χ η*unitAtom χ η D k)=
        resonance χ η^(k+1)*unitAtom χ η D (k+1)-
          resonance χ η^k*unitAtom χ η D k := by
    rw [pow_succ]
    have hss : resonance χ η*resonance χ η=1 := by simpa only [pow_two] using hs
    calc
      _ = resonance χ η^k*resonance χ η*unitAtom χ η D (k+1)-
          resonance χ η^k*(resonance χ η*resonance χ η)*unitAtom χ η D k := by ring
      _ = _ := by rw [hss,mul_one]
  have ht := sum_eq_last_sub_weighted_jumps (D-1)
    (fun k => resonance χ η^k*unitAtom χ η D k)
  rw [he,show unitAtom χ η D (D-1)=1 by simp [unitAtom,binomialUnit_last],mul_one] at ht
  have hj : (∑ k∈Finset.range (D-1),((k+1 : ℕ) : ℂ)*
      (resonance χ η^(k+1)*unitAtom χ η D (k+1)-resonance χ η^k*unitAtom χ η D k))=
        firstCrossingMoment χ η D := by
    unfold firstCrossingMoment crossingOrders
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : p∣k+1 ∨ q∣k+1
    · simp only [h,ite_true]
      rw [←hd]
      ring
    · simp only [h,ite_false]
      have hh := unitAtom_succ hp hq hD hpd hqd (Finset.mem_range.mp hk) χ η
        (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))
      rw [←hd,hh,sub_self,mul_zero,mul_zero]
  rw [hj] at ht
  unfold codedUnitTrace
  rw [ht]
  field_simp

/-- On an odd row the boundary is one; this identity makes no size claim. -/
theorem odd_resonant_trace_eq_first_moment {p q H : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpd : p∣2*H+1) (hqd : q∣2*H+1)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q) :
    codedUnitTrace χ η (2*H+1) (resonance χ η)=
      1-firstCrossingMoment χ η (2*H+1)/((2*H+1 : ℕ) : ℂ) := by
  rw [resonant_trace_eq_first_moment hp hq (by omega) hpd hqd]
  simp only [Nat.add_sub_cancel,pow_mul,resonance_sq,one_pow]

theorem principal_unitColumn {p D k : ℕ} (hp : p.Prime) (hk : k≤D-1) :
    (1 : DirichletCharacter ℂ p) (binomialUnit p D k)=1 := by
  apply MulChar.one_apply
  rw [ZMod.isUnit_iff_coprime,Nat.coprime_comm,Nat.Prime.coprime_iff_not_dvd hp]
  exact unitPart_not_dvd hp (Nat.choose_ne_zero hk)

theorem principal_unitAtom {p q D k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hk : k<D) : unitAtom (1 : DirichletCharacter ℂ p) (1 : DirichletCharacter ℂ q) D k=1 := by
  unfold unitAtom
  rw [principal_unitColumn hp (by omega),principal_unitColumn hq (by omega),mul_one]

theorem principal_resonance (p q : ℕ) :
    resonance (1 : DirichletCharacter ℂ p) (1 : DirichletCharacter ℂ q)=1 := by
  unfold resonance
  rw [MulChar.one_apply (isUnit_one.neg),
    MulChar.one_apply (isUnit_one.neg),mul_one]

/-- Every extracted column has full character norm, including carried atoms
whose raw residue would be zero. A raw-support allowance is inapplicable. -/
theorem norm_unitColumn_eq_one {p D k : ℕ} (hp : p.Prime) (hk : k≤D-1)
    (χ : DirichletCharacter ℂ p) : ‖χ (binomialUnit p D k)‖=1 := by
  have hu : IsUnit (binomialUnit p D k : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime,Nat.coprime_comm,Nat.Prime.coprime_iff_not_dvd hp]
    exact unitPart_not_dvd hp (Nat.choose_ne_zero hk)
  exact χ.unit_norm_eq_one hu.unit

theorem norm_unitAtom_eq_one {p q D k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hk : k<D) (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q) :
    ‖unitAtom χ η D k‖=1 := by
  rw [unitAtom,norm_mul,norm_unitColumn_eq_one hp (by omega),
    norm_unitColumn_eq_one hq (by omega),mul_one]

/-- Joining phases is essential: every unit row has exactly D absolute mass,
regardless of any cancellation of its signed trace. -/
theorem absolute_unit_row_mass {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q) (D : ℕ) :
    (∑ k∈Finset.range D,‖unitAtom χ η D k‖)=(D : ℝ) := by
  calc
    _ = ∑ _k∈Finset.range D,(1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact norm_unitAtom_eq_one hp hq (Finset.mem_range.mp hk) χ η
    _ = _ := by simp

theorem principal_firstCrossingMoment_eq_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (D : ℕ) : firstCrossingMoment (1 : DirichletCharacter ℂ p)
      (1 : DirichletCharacter ℂ q) D=0 := by
  unfold firstCrossingMoment
  apply Finset.sum_eq_zero
  intro k hk
  have hh := Finset.mem_filter.mp hk
  have hkr := Finset.mem_range.mp hh.1
  rw [principal_unitAtom hp hq (by omega),principal_unitAtom hp hq (by omega),
    principal_resonance,one_mul,sub_self,mul_zero]

/-- An actual native row with every carry retained can have full resonant mean. -/
theorem principal_resonant_trace_eq_one {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) :
    codedUnitTrace (1 : DirichletCharacter ℂ p) (1 : DirichletCharacter ℂ q) D 1=1 := by
  have hD0 : (D : ℂ)≠0 := by exact_mod_cast hD.ne'
  unfold codedUnitTrace
  have hh : (∑ k∈Finset.range D,(1 : ℂ)^k*
      unitAtom (1 : DirichletCharacter ℂ p) (1 : DirichletCharacter ℂ q) D k)=(D : ℂ) := by
    calc
      _ = ∑ _k∈Finset.range D,(1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [principal_unitAtom hp hq (Finset.mem_range.mp hk),one_pow,mul_one]
      _ = _ := by simp
  rw [hh,div_self hD0]

/-- With principal unit codes the whole outer packet is the original arbitrary
prime-pair weight, not a new integer constraint. All exterior phases remain. -/
theorem principal_unitPacket_eq (P Q : Finset ℕ)
    (coefficient : ℕ → ℕ → ℂ)
    (hp : ∀ p∈P,p.Prime) (hq : ∀ q∈Q,q.Prime) :
    unitPacket P Q (fun _ => 1) (fun _ => 1) coefficient (fun _ _ => 1)=
      ∑ p∈P,∑ q∈Q,coefficient p q := by
  unfold unitPacket
  apply Finset.sum_congr rfl
  intro p hpp
  apply Finset.sum_congr rfl
  intro q hqq
  rw [principal_resonant_trace_eq_one (hp p hpp) (hq q hqq)
    (Nat.mul_pos (hp p hpp).pos (hq q hqq).pos),mul_one]

/-- Zeroth conservation does not force even an arbitrarily small positive
power saving on all actual unit characters. Only this uniform class is closed. -/
theorem no_uniform_resonant_row_bound {p q D : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hD : 0<D) {epsilon : ℝ} (he : epsilon<1) :
    ¬(∀ (χ : DirichletCharacter ℂ p) (η : DirichletCharacter ℂ q),
      ‖codedUnitTrace χ η D (resonance χ η)‖≤epsilon) := by
  intro h
  have hh := h 1 1
  rw [principal_resonance,principal_resonant_trace_eq_one hp hq hD,norm_one] at hh
  exact (not_le_of_gt he) hh

end RiemannGaussian.ArithmeticOperatorPFreeResonanceAudit

#lint+ in RiemannGaussian.ArithmeticOperatorPFreeResonanceAudit

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
  unless declarations>0 do throwError "Empty resonant unit audit."
  logInfo m!"P-free resonance audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-pfree-resonance"
  IO.FS.writeFile ".lake/arithmetic-operator-pfree-resonance/axioms.json"
    (Json.mkObj [("scope",toJson "exact first spatial transition moment and principal-character obstruction to zeroth-jump row decay; no nonprincipal source or arithmetic bound inferred"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
