/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# A growing-shift resultant gate for one literal gapped Pascal minor

The non-block minor with rows `t,t+2,t+4` and columns `0,2,3` is exactly
`4*(t^2+3*t+1)`. Its simultaneous divisibility roots at a shift `h` lie
over the single resultant `h^2*(h^2-5)`, and there are at most two residue
roots at EVERY prime power. In particular the prime-five singular case is
retained rather than silently covered by a simple-root argument.

These are exact integer and common-residue support statements. The separate
discrepancy budget can then center the literal denominator-layer packet.
No bound on the original single-polynomial prime packet or uncentered
moving density, no actual zero-source response, and no RH estimate follows.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
set_option warningAsError true
noncomputable section
open scoped BigOperators Matrix
namespace OpenAIReview.GappedMinor

/-- The genuinely additional discriminant-five factor of the gapped minor. -/
def q (t : ℕ) : ℕ := t^2+3*t+1

/-- The same polynomial on integer arguments. -/
def qZ (t : ℤ) : ℤ := t^2+3*t+1

/-- The one common integer controlling simultaneous roots at shift `h`. -/
def resultant (h : ℕ) : ℕ := Int.natAbs ((h : ℤ)^2*((h : ℤ)^2-5))

/-- Literal simultaneous divisor residues, including their endpoints. -/
def jointRoots (h d : ℕ) : Finset ℕ :=
  (Finset.range d).filter (fun t => d ∣ q t ∧ d ∣ q (t+h))

/-- Literal single-polynomial residues used only for the uniform cardinal bound. -/
def roots (d : ℕ) : Finset ℕ := (Finset.range d).filter (fun t => d ∣ q t)

/-- Membership in the simultaneous root set retains the literal range. -/
@[simp] theorem mem_jointRoots {h d t : ℕ} : t ∈ jointRoots h d ↔
    t<d ∧ d ∣ q t ∧ d ∣ q (t+h) := by simp [jointRoots]

/-- Membership in the single-polynomial root set retains the literal range. -/
@[simp] theorem mem_roots {d t : ℕ} : t ∈ roots d ↔ t<d ∧ d ∣ q t := by
  simp [roots]

/-- Integer and natural evaluation agree exactly. -/
@[simp, norm_cast] theorem q_cast (t : ℕ) : (q t : ℤ) = qZ t := by simp [q, qZ]

/-- Divisibility transports to the same integer polynomial without loss. -/
theorem q_dvd_cast {d t : ℕ} : d ∣ q t ↔ (d : ℤ) ∣ qZ t := by
  rw [← q_cast]
  exact Int.natCast_dvd_natCast.symm

/-- An exact resultant identity before any divisor or phase is extracted. -/
theorem resultant_identity (t h : ℤ) :
    h^2*(h^2-5) = 4*h^2*qZ t - (qZ (t+h)-qZ t)^2 +
      2*h^2*(qZ (t+h)-qZ t) := by unfold qZ; ring

/-- Every literal common divisor divides the SAME resultant integer. -/
theorem common_divisor_resultant {t h d : ℕ}
    (hleft : d ∣ q t) (hright : d ∣ q (t+h)) : d ∣ resultant h := by
  have hl : (d : ℤ) ∣ qZ t := q_dvd_cast.mp hleft
  have hr : (d : ℤ) ∣ qZ ((t : ℤ)+h) := by
    simpa only [Nat.cast_add] using q_dvd_cast.mp hright
  have hs := dvd_sub hr hl
  have hsq : (d : ℤ) ∣ (qZ ((t : ℤ)+h)-qZ t)^2 :=
    hs.trans (dvd_pow_self _ (by decide : (2 : ℕ) ≠ 0))
  have he : (d : ℤ) ∣ (h : ℤ)^2*((h : ℤ)^2-5) := by
    rw [resultant_identity]
    exact dvd_add (dvd_sub (dvd_mul_of_dvd_right hl _) hsq)
      (dvd_mul_of_dvd_right hs _)
  exact_mod_cast (Int.dvd_natAbs.mpr he)

/-- There is no integer square equal to five, so every positive shift has
a positive resultant. Shift zero remains explicitly outside this gate. -/
theorem resultant_pos {h : ℕ} (hh : 0<h) : 0 < resultant h := by
  have hneq : (h : ℤ)^2 ≠ 5 := by
    intro he
    have hsmall : (h : ℤ) < 3 := by nlinarith
    have hsmall' : h < 3 := by exact_mod_cast hsmall
    interval_cases h <;> norm_num at he
  unfold resultant
  apply Int.natAbs_pos.mpr
  exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt hh))) (sub_ne_zero.mpr hneq)

/-- A residue outside the common resultant support cannot occur. -/
theorem jointRoots_empty_of_not_dvd_resultant (h d : ℕ)
    (hd : ¬d ∣ resultant h) : jointRoots h d = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have ht' := (Finset.mem_filter.mp ht).2
  exact hd (common_divisor_resultant ht'.1 ht'.2)

/-- Equality of two representatives in the same literal range follows from
the integer divisibility congruence, with no endpoint approximation. -/
theorem eq_of_dvd_sub {d x y : ℕ} (hx : x<d) (hy : y<d)
    (h : (d : ℤ) ∣ (x : ℤ)-y) : x=y := by
  have he : Nat.ModEq d y x := Nat.modEq_iff_dvd.mpr h
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using he.symm

/-- At any prime other than five, a root has invertible derivative modulo
that prime. This is proved from the exact discriminant identity. -/
theorem prime_not_dvd_derivative {p : ℕ} (hp : p.Prime) (hp5 : p≠5)
    (y : ℤ) (hy : (p : ℤ) ∣ qZ y) : ¬(p : ℤ) ∣ 2*y+3 := by
  intro hd
  have hfive : (p : ℤ) ∣ 5 := by
    have hsq : (p : ℤ) ∣ (2*y+3)^2 := by simpa only [pow_two] using dvd_mul_of_dvd_left hd (2*y+3)
    have hsub := dvd_sub hsq (dvd_mul_of_dvd_right hy 4)
    convert hsub using 1
    unfold qZ
    ring
  have hfive' : p ∣ 5 := by exact_mod_cast hfive
  exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hfive')

/-- Every prime-power root belongs to one of two exact classes relative to
a chosen root; no Hensel or squarefree-modulus shortcut is assumed. -/
theorem root_two_classes {p r : ℕ} (hp : p.Prime) (hp5 : p≠5) (hr : 0<r)
    (x y : ℤ) (hx : (p : ℤ)^r ∣ qZ x) (hy : (p : ℤ)^r ∣ qZ y) :
    (p : ℤ)^r ∣ x-y ∨ (p : ℤ)^r ∣ x+y+3 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hy' : (p : ℤ) ∣ qZ y := (dvd_pow_self _ (Nat.ne_of_gt hr)).trans hy
  have hder := prime_not_dvd_derivative hp hp5 y hy'
  have hprod : (p : ℤ)^r ∣ (x-y)*(x+y+3) := by
    convert dvd_sub hx hy using 1
    unfold qZ
    ring
  by_cases hd : (p : ℤ) ∣ x-y
  · have hother : ¬(p : ℤ) ∣ x+y+3 := by
      intro hs
      apply hder
      convert dvd_sub hs hd using 1
      ring
    exact Or.inl (hpZ.pow_dvd_of_dvd_mul_right r hother hprod)
  · exact Or.inr (hpZ.pow_dvd_of_dvd_mul_left r hd hprod)

/-- The singular prime five has no roots at the square level or above. -/
theorem not_twentyfive_dvd (t : ℕ) : ¬25 ∣ q t := by
  have hf : ∀ a : Fin 25, ¬25 ∣ q a.val := by decide
  intro ht
  apply hf ⟨t%25, Nat.mod_lt t (by decide)⟩
  rw [Nat.dvd_iff_mod_eq_zero]
  have he : q (t%25)%25 = q t%25 := by simp [q, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  rw [he, Nat.mod_eq_zero_of_dvd ht]

/-- Uniform root count at EVERY prime power, including the singular prime. -/
theorem roots_prime_power_card_le_two {p r : ℕ} (hp : p.Prime) :
    (roots (p^r)).card ≤ 2 := by
  by_cases hr : r=0
  · subst r
    norm_num [roots, q]
  have hr0 : 0<r := Nat.pos_of_ne_zero hr
  by_cases hp5 : p=5
  · subst p
    by_cases hr1 : r=1
    · subst r
      decide
    · have hr2 : 2≤r := by omega
      have he : roots (5^r) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro t ht
        have hd := (Finset.mem_filter.mp ht).2
        exact not_twentyfive_dvd t ((by norm_num : 25=5^2) ▸
          (pow_dvd_pow 5 hr2).trans hd)
      rw [he]
      simp
  · by_cases hempty : roots (p^r) = ∅
    · rw [hempty]
      simp
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have ha' := Finset.mem_filter.mp ha
    by_cases hsingle : roots (p^r) ⊆ {a}
    · exact (Finset.card_le_card hsingle).trans (by simp)
    obtain ⟨b, hb, hba⟩ := Finset.not_subset.mp hsingle
    have hb' := Finset.mem_filter.mp hb
    have hba' : b≠a := by simpa using hba
    have hclasses (x : ℕ) (hx : x∈roots (p^r)) :
        x=a ∨ (p : ℤ)^r ∣ (x : ℤ)+a+3 := by
      have hx' := Finset.mem_filter.mp hx
      have hrootx : (p : ℤ)^r ∣ qZ x := by
        simpa only [Nat.cast_pow] using q_dvd_cast.mp hx'.2
      have hroota : (p : ℤ)^r ∣ qZ a := by
        simpa only [Nat.cast_pow] using q_dvd_cast.mp ha'.2
      rcases root_two_classes hp hp5 hr0 x a hrootx hroota with he | he
      · left
        apply eq_of_dvd_sub (Finset.mem_range.mp hx'.1) (Finset.mem_range.mp ha'.1)
        exact_mod_cast he
      · exact Or.inr he
    have hsumB : (p : ℤ)^r ∣ (b : ℤ)+a+3 := by
      rcases hclasses b hb with heq | he
      · exact (hba' heq).elim
      · exact he
    have hsub : roots (p^r) ⊆ {a,b} := by
      intro x hx
      rcases hclasses x hx with heq | he
      · simp [heq]
      · have hd : (p : ℤ)^r ∣ (x : ℤ)-b := by
          convert dvd_sub he hsumB using 1
          ring
        have heq : x=b := by
          apply eq_of_dvd_sub (Finset.mem_range.mp (Finset.mem_filter.mp hx).1)
            (Finset.mem_range.mp hb'.1)
          exact_mod_cast hd
        simp [heq]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- The simultaneous root set is a literal subset of the polynomial roots. -/
theorem jointRoots_subset_roots (h d : ℕ) : jointRoots h d ⊆ roots d := by
  intro t ht
  have hmem := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hmem.1, hmem.2.1⟩

/-- Final native arithmetic input to the uniform discrepancy budget. -/
theorem jointRoots_prime_power_card_le_two (h : ℕ) {p r : ℕ} (hp : p.Prime) :
    (jointRoots h (p^r)).card ≤ 2 :=
  (Finset.card_le_card (jointRoots_subset_roots h (p^r))).trans
    (roots_prime_power_card_le_two hp)

/-- Polynomial periodicity at the exact simultaneous divisor residues. -/
theorem joint_divisibility_iff_mod_mem (h d t : ℕ) (hd : 0<d) :
    (d ∣ q t ∧ d ∣ q (t+h)) ↔ t%d ∈ jointRoots h d := by
  have hleft : q (t%d)%d = q t%d := by
    simp [q, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  have hright : q (t%d+h)%d = q (t+h)%d := by
    simp [q, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  simp only [jointRoots, Finset.mem_filter, Finset.mem_range, Nat.dvd_iff_mod_eq_zero]
  rw [hleft, hright]
  simp [Nat.mod_lt t hd]

/-- The literal cutoff joint-divisor count is the sum of its exact residue
counts. This supplies the native prefix bridge for the discrepancy budget. -/
theorem prefix_joint_count (T h d : ℕ) (hd : 0<d) :
    T.count (fun t => d ∣ q t ∧ d ∣ q (t+h)) =
      ∑ a∈jointRoots h d, T.count (fun t => Nat.ModEq d t a) := by
  calc
    _ = ((Finset.range T).filter (fun t => t%d ∈ jointRoots h d)).card := by
      rw [Nat.count_eq_card_filter_range]
      congr 1
      ext t
      simp only [Finset.mem_filter]
      rw [joint_divisibility_iff_mod_mem h d t hd]
    _ = ∑ a∈jointRoots h d, ((Finset.range T).filter (fun t => t%d=a)).card :=
      (Finset.sum_card_fiberwise_eq_card_filter (Finset.range T) (jointRoots h d)
        (fun t => t%d)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Nat.count_eq_card_filter_range]
      congr 1
      ext t
      have hal : a<d := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      simp only [Finset.mem_filter, Nat.ModEq, Nat.mod_eq_of_lt hal]

/-- The small cast identity needed to evaluate the literal Pascal entries. -/
theorem choose_three_cast (n : ℕ) : (n.choose 3 : ℚ) =
    (n : ℚ)*((n : ℚ)-1)*((n : ℚ)-2)/6 := by
  rcases n with _ | n
  · norm_num [Nat.choose]
  rcases n with _ | n
  · norm_num [Nat.choose]
  have hz := congrArg (fun x : ℕ => (x : ℚ))
    (Nat.descFactorial_eq_factorial_mul_choose (n+2) 3)
  norm_num only [Nat.descFactorial_succ, Nat.add_sub_cancel, Nat.cast_mul,
    Nat.cast_descFactorial_two, Nat.descFactorial_zero, Nat.cast_one, mul_one,
    Nat.factorial] at hz
  push_cast at hz ⊢
  nlinarith

/-- One common NON-BLOCK integral Pascal matrix, with genuinely gapped rows
and columns. All entries are literal binomial coefficients. -/
def pascalMatrix (t : ℕ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1,(t.choose 2 : ℤ),(t.choose 3 : ℤ);
     1,((t+2).choose 2 : ℤ),((t+2).choose 3 : ℤ);
     1,((t+4).choose 2 : ℤ),((t+4).choose 3 : ℤ)]

/-- Exact literal determinant: the factorial baseline is four and the
additional irreducible factor is the discriminant-five polynomial. -/
theorem pascalMatrix_det (t : ℕ) : (pascalMatrix t).det = 4*(q t : ℤ) := by
  have he : ((pascalMatrix t).det : ℚ) = 4*(q t : ℚ) := by
    norm_num [pascalMatrix, Matrix.det_fin_three]
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two,
      choose_three_cast, choose_three_cast, choose_three_cast]
    simp only [q]
    push_cast
    ring
  apply (Int.cast_injective (α := ℚ))
  simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using he

end OpenAIReview.GappedMinor

#lint+ in OpenAIReview.GappedMinor

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
  unless declarations>0 do throwError "Empty gapped-minor audit."
  logInfo m!"Gapped-minor audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-gapped-minor-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-gapped-minor-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual gapped quadratic factor, common resultant support and at most two roots at every prime power; no original prime-packet estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
