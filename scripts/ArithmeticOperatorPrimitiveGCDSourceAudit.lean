/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual gcd/order constraints and the first unsaturated prime annulus

All prime-power intersections of the ordinary power differences are retained.
For an actual square integer base, every allowed prime through 2M+1 already
has a literal primitive cyclotomic factor with index at most M. This finite
inclusion is not a bound or a source theorem for the full extra-prime sector.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
namespace OpenAIReview.PrimitiveGCDSource

/-- The exact gcd of two actual integer-base power differences. -/
theorem power_difference_gcd (b d e : ℕ) :
    Nat.gcd (b^d-1) (b^e-1)=b^(Nat.gcd d e)-1 :=
  Nat.pow_sub_one_gcd_pow_sub_one b d e

/-- The gcd identity retains every literal prime-power depth. -/
theorem common_power_depth (b d e p r : ℕ) :
    p^r∣b^d-1 ∧ p^r∣b^e-1 ↔ p^r∣b^(Nat.gcd d e)-1 := by
  rw [←Nat.dvd_gcd_iff,power_difference_gcd]

/-- Evaluation divisibility is the actual finite-field cyclotomic root condition. -/
theorem cyclotomic_dvd_iff_root (b d p : ℕ) [Fact p.Prime] :
    (p:ℤ)∣(Polynomial.cyclotomic d ℤ).eval (b:ℤ) ↔
      (Polynomial.cyclotomic d (ZMod p)).IsRoot (b:ZMod p) := by
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (Int.castRingHom (ZMod p)) ((Polynomial.cyclotomic d ℤ).eval (b:ℤ))=0 ↔ _
  have hc := (Polynomial.cyclotomic.eval_apply (b:ℤ) d (Int.castRingHom (ZMod p))).symm
  rw [hc]
  simp only [Polynomial.IsRoot,Int.coe_castRingHom,Int.cast_natCast]

/-- Retained primitive roots at two good indices cannot share a prime. -/
theorem primitive_parent_unique (b d e p : ℕ) [Fact p.Prime]
    (hd : ¬p∣d) (he : ¬p∣e)
    (hvd : (p:ℤ)∣(Polynomial.cyclotomic d ℤ).eval (b:ℤ))
    (hve : (p:ℤ)∣(Polynomial.cyclotomic e ℤ).eval (b:ℤ)) : d=e := by
  have : NeZero (d:ZMod p) := ⟨by
    intro h;exact hd ((ZMod.natCast_eq_zero_iff _ _).mp h)⟩
  have : NeZero (e:ZMod p) := ⟨by
    intro h;exact he ((ZMod.natCast_eq_zero_iff _ _).mp h)⟩
  have hpd := Polynomial.isRoot_cyclotomic_iff.mp ((cyclotomic_dvd_iff_root b d p).mp hvd)
  have hpe := Polynomial.isRoot_cyclotomic_iff.mp ((cyclotomic_dvd_iff_root b e p).mp hve)
  exact hpd.unique hpe

/-- Every allowed prime through twice the row scale occurs at an actual primitive
index of a square integer base; no prime-density assertion is assumed. -/
theorem square_base_primitive_window (c M p : ℕ) (hp : p.Prime) (h2 : p≠2)
    (hcut : p≤2*M+1) (hhead : ¬p∣c^2*(c^2-1)) :
    ∃d∈Finset.Icc 2 M,
      (p:ℤ)∣(Polynomial.cyclotomic d ℤ).eval ((c^2:ℕ):ℤ) ∧ ¬p∣d := by
  have : Fact p.Prime := ⟨hp⟩
  have hpb : ¬p∣c^2 := fun h => hhead (dvd_mul_of_dvd_left h _)
  have hpb1 : ¬p∣c^2-1 := fun h => hhead (dvd_mul_of_dvd_right h _)
  have hbpos : 0<c^2 := Nat.pos_of_ne_zero (by
    intro h
    exact hpb (by rw [h];exact dvd_zero p))
  have hc : (c:ZMod p)≠0 := by
    intro h
    apply hpb
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simp [Nat.cast_pow,h]
  have hb1 : ((c^2:ℕ):ZMod p)≠1 := by
    intro h
    apply hpb1
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub hbpos,Nat.cast_one,h,sub_self]
  have hodd : p%2=1 := hp.eq_two_or_odd.resolve_left h2
  have hdouble : 2*((p-1)/2)=p-1 := by omega
  have hpow : (((c^2:ℕ):ZMod p))^((p-1)/2)=1 := by
    rw [Nat.cast_pow,←pow_mul,hdouble]
    exact ZMod.pow_card_sub_one_eq_one hc
  let d := orderOf (((c^2:ℕ):ZMod p))
  have hdiv : d∣(p-1)/2 := orderOf_dvd_of_pow_eq_one hpow
  have hpp : 0<(p-1)/2 := by have := hp.two_le;omega
  have hdp : 0<d := Nat.pos_of_dvd_of_pos hdiv hpp
  have hdle : d≤(p-1)/2 := Nat.le_of_dvd hpp hdiv
  have hdne : d≠1 := fun h => hb1 (orderOf_eq_one_iff.mp h)
  have hprim : IsPrimitiveRoot (((c^2:ℕ):ZMod p)) d := IsPrimitiveRoot.orderOf _
  refine ⟨d,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_,?_⟩
  · exact (cyclotomic_dvd_iff_root (c^2) d p).mpr (hprim.isRoot_cyclotomic hdp)
  · exact Nat.not_dvd_of_pos_of_lt hdp (by omega)

/-- The literal first extra annulus has every arbitrary prime weight, without
independent bases or a source assigned to the order mask. -/
theorem square_base_extra_annulus_weights (c M : ℕ) (S : Finset ℕ)
    (hS : ∀p∈S,p.Prime ∧ p≠2 ∧ M<p ∧ p≤2*M+1 ∧ ¬p∣c^2*(c^2-1))
    (w : ℕ→ℂ) :
    (∑p∈S,if ∃d∈Finset.Icc 2 M,
      (p:ℤ)∣(Polynomial.cyclotomic d ℤ).eval ((c^2:ℕ):ℤ) ∧ ¬p∣d
      then w p else 0)=∑p∈S,w p := by
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hprime,h2,_hlo,hhi,hhead⟩ := hS p hp
  simp only [ite_eq_left (square_base_primitive_window c M p hprime h2 hhi hhead)]

end OpenAIReview.PrimitiveGCDSource
#lint+ in OpenAIReview.PrimitiveGCDSource

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
  logInfo m!"Primitive gcd source audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-primitive-gcd-source-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-primitive-gcd-source-gate/axioms.json"
    (Json.mkObj [("scope",toJson "literal all-depth gcd identity, primitive parent uniqueness, square-base first-annulus primitive inclusion; no analytic source or signed bound"),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr details)]).pretty
