/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorTotalTraceSourceAudit
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Literal primitive-product first-layer support

The integer primitive part retains the full prime multiplicity of each
actual cyclotomic value, removing only primes dividing its order index.
Below the row cutoff its prime layer is uncoded away from b(b-1).
Higher-depth error and Mellin/source consequences remain paper-level.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators
namespace OpenAIReview.PrimitivePacketSource
open TotalTraceSource

/-- The literal factorization of the actual cyclotomic value, pruned at index primes. -/
def primitiveFactors (b e : ℕ) : ℕ →₀ ℕ :=
  (value b e).natAbs.factorization.filter (fun p => ¬p∣e)

/-- Actual positive integer primitive part, with every retained prime power. -/
def primitiveValue (b e : ℕ) : ℕ := (primitiveFactors b e).prod (fun p v => p^v)

/-- Once-counted actual primitive product; order one remains omitted. -/
def primitiveProduct (b M : ℕ) : ℕ := ∏ e ∈ Finset.Icc 2 M, primitiveValue b e

/-- Pruning only removes factors of the actual integer. -/
theorem primitiveFactors_le (b e : ℕ) :
    primitiveFactors b e ≤ (value b e).natAbs.factorization := by
  intro p
  simp only [primitiveFactors,Finsupp.filter_apply]
  split_ifs <;> omega

/-- Exact factorization of the actual pruned integer. -/
theorem primitiveValue_factorization (b e : ℕ) :
    (primitiveValue b e).factorization=primitiveFactors b e :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization (primitiveFactors_le b e)

/-- The primitive integer is an actual divisor of the cyclotomic value. -/
theorem primitiveValue_dvd (b e : ℕ) : primitiveValue b e ∣ (value b e).natAbs :=
  Nat.prod_pow_dvd_of_le_factorization (primitiveFactors_le b e)

/-- The pruned integer cannot vanish at an allowed base. -/
theorem primitiveValue_ne_zero (b e : ℕ) (hb : 2≤b) : primitiveValue b e ≠ 0 := by
  intro h
  have hv := primitiveValue_dvd b e
  rw [h,zero_dvd_iff] at hv
  exact (value_pos b e hb).ne' (Int.natAbs_eq_zero.mp hv)

/-- Exact native prime support of each primitive factor. -/
theorem prime_dvd_primitiveValue (b e p : ℕ) (hb : 2≤b) (hp : p.Prime) :
    p∣primitiveValue b e ↔ (p:ℤ)∣value b e ∧ ¬p∣e := by
  rw [hp.dvd_iff_one_le_factorization (primitiveValue_ne_zero b e hb),
    primitiveValue_factorization]
  simp only [primitiveFactors,Finsupp.filter_apply]
  by_cases he : p∣e
  · simp [he]
  · simp only [he,not_false_eq_true,ite_true,and_true]
    rw [←hp.dvd_iff_one_le_factorization
      (show (value b e).natAbs≠0 from Int.natAbs_ne_zero.mpr (value_pos b e hb).ne'),
      ←Int.natCast_dvd]

/-- The complete actual product has the union of its native primitive supports. -/
theorem prime_dvd_primitiveProduct (b M p : ℕ) (hb : 2≤b) (hp : p.Prime) :
    p∣primitiveProduct b M ↔
      ∃e∈Finset.Icc 2 M, (p:ℤ)∣value b e ∧ ¬p∣e := by
  rw [primitiveProduct,hp.prime.dvd_finsetProd_iff]
  simp_rw [prime_dvd_primitiveValue b _ p hb hp]

/-- A retained prime has the literal primitive root of its actual row index. -/
theorem primitive_root_of_retained (b e p : ℕ) [Fact p.Prime]
    (hd : (p:ℤ)∣value b e) (he : ¬p∣e) :
    IsPrimitiveRoot (b:ZMod p) e := by
  have : NeZero (e:ZMod p) := ⟨by
    intro h
    exact he ((ZMod.natCast_eq_zero_iff _ _).mp h)⟩
  exact Polynomial.isRoot_cyclotomic_iff.mp ((dvd_value_iff_root b e p).mp hd)

/-- The prime layer saturates at p<=M, with the exact finite base/order-one head. -/
theorem saturated_prime_support (b M p : ℕ) (hb : 2≤b) (hp : p.Prime) (hcut : p≤M) :
    p∣primitiveProduct b M ↔ ¬p∣b*(b-1) := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hd hhead
    obtain ⟨e,he,hd,hep⟩ := (prime_dvd_primitiveProduct b M p hb hp).mp hd
    have hp0 := primitive_root_of_retained b e p hd hep
    have hepos : 0<e := by have := (Finset.mem_Icc.mp he).1;omega
    rcases hp.dvd_mul.mp hhead with hpb | hpb
    · exact hp0.ne_zero hepos.ne' ((ZMod.natCast_eq_zero_iff _ _).mpr hpb)
    · have hc : ((b-1:ℕ):ZMod p)=(b:ZMod p)-1 := by
        rw [Nat.cast_sub (by omega : 1≤b),Nat.cast_one]
      have hz : (b:ZMod p)=1 := by
        have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hpb
        rw [hc] at hz
        exact sub_eq_zero.mp hz
      have ho : e=1 := by simpa [hz] using hp0.eq_orderOf
      have := (Finset.mem_Icc.mp he).1
      omega
  · intro hhead
    have hpb : ¬p∣b := fun h => hhead (dvd_mul_of_dvd_left h _)
    have hpb1 : ¬p∣b-1 := fun h => hhead (dvd_mul_of_dvd_right h _)
    have hn0 : (b:ZMod p)≠0 := by
      intro h;exact hpb ((ZMod.natCast_eq_zero_iff _ _).mp h)
    have hn1 : (b:ZMod p)≠1 := by
      intro h
      apply hpb1
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [Nat.cast_sub (by omega : 1≤b),Nat.cast_one,h,sub_self]
    let e := orderOf (b:ZMod p)
    have hdiv : e∣p-1 := ZMod.orderOf_dvd_card_sub_one hn0
    have hepos : 0<e := Nat.pos_of_dvd_of_pos hdiv (by have := hp.one_lt;omega)
    have hene : e≠1 := by intro h;exact hn1 (orderOf_eq_one_iff.mp h)
    have hep : e<p := lt_of_le_of_lt (Nat.le_of_dvd (by have := hp.one_lt;omega) hdiv)
      (Nat.sub_lt hp.pos (by norm_num))
    have hp0 : IsPrimitiveRoot (b:ZMod p) e := IsPrimitiveRoot.orderOf _
    apply (prime_dvd_primitiveProduct b M p hb hp).mpr
    refine ⟨e,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_,?_⟩
    · exact (dvd_value_iff_root b e p).mpr (hp0.isRoot_cyclotomic hepos)
    · exact Nat.not_dvd_of_pos_of_lt hepos hep

/-- Any literal prime weights have the same saturated first-layer observation. -/
theorem saturated_prime_weights (b M : ℕ) (hb : 2≤b)
    (s : Finset ℕ) (hs : ∀p∈s,p.Prime ∧ p≤M) (w : ℕ→ℂ) :
    (∑p∈s,if p∣primitiveProduct b M then w p else 0)=
      ∑p∈s,if ¬p∣b*(b-1) then w p else 0 := by
  apply Finset.sum_congr rfl
  intro p hp
  simp only [saturated_prime_support b M p hb (hs p hp).1 (hs p hp).2]

end OpenAIReview.PrimitivePacketSource
#lint+ in OpenAIReview.PrimitivePacketSource

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
  logInfo m!"Primitive packet audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-positive-primitive-source-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-positive-primitive-source-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual integer primitive product and arbitrary-weight saturated prime layer; higher depths/Mellin source paper-level"),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr details)]).pretty
