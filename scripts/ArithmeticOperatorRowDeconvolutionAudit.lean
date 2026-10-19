/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual cyclotomic row reweighting

Signed row products reweight the actual cyclotomic factors. The literal
Mobius-six quotient need not be an integer. No resultant/source theorem
or physical prime-power phase transport is assumed or proved here.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace OpenAIReview.RowDeconvolution

/-- Actual integer cyclotomic value. -/
def value (b d:ℕ) : ℤ := (Polynomial.cyclotomic d ℤ).eval (b:ℤ)
/-- Actual once-counted integer row, omitting index one. -/
def C (b N:ℕ) : ℤ := ∏d∈Finset.Icc 2 N,value b d

/-- The actual factors are positive at every allowed base. -/
theorem value_pos (b d:ℕ) (hb:2≤b) : 0<value b d :=
  Polynomial.cyclotomic_pos' d (by exact_mod_cast (show 1<b by omega))

/-- Units retain the actual factors while permitting signed row exponents. -/
def factor (b d:ℕ) (hb:2≤b) : ℚˣ :=
  Units.mk0 (value b d:ℚ) (by exact_mod_cast (value_pos b d hb).ne')
/-- The actual row interpreted in the rational unit group. -/
def row (b N:ℕ) (hb:2≤b) : ℚˣ := ∏d∈Finset.Icc 2 N,factor b d hb

/-- Rational units do not change the original integer row. -/
theorem row_val (b N:ℕ) (hb:2≤b) : (row b N hb:ℚ)=(C b N:ℚ) := by
  simp [row,C,factor]

/-- The same row can be zero-extended to a larger fixed finite order band. -/
theorem row_extended (b N R:ℕ) (hb:2≤b) (hNR:N≤R) :
    row b N hb=∏d∈Finset.Icc 2 R,if d≤N then factor b d hb else 1 := by
  rw [←Finset.prod_filter]
  have hi:Finset.Icc 2 N=(Finset.Icc 2 R).filter (fun d=>d≤N) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  exact congrArg (fun s:Finset ℕ=>∏d∈s,factor b d hb) hi

private theorem zpow_sum_eq {G:Type*} [CommGroup G] (s:Finset ℕ)
    (a:ℕ→ℤ) (x:G) : x^(∑n∈s,a n)=∏n∈s,x^(a n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih => simp [hn,zpow_add,ih]

/-- Exact signed reweighting of ACTUAL integer rows, in rational units.
The order coefficient is the tail sum of the original row exponents. -/
theorem actual_row_reweight (b R:ℕ) (hb:2≤b) (a:ℕ→ℤ) :
    (∏N∈Finset.Icc 2 R,(row b N hb)^(a N))=
      ∏d∈Finset.Icc 2 R,(factor b d hb)^
        (∑N∈Finset.Icc 2 R,if d≤N then a N else 0) := by
  have hrow (N:ℕ) (hN:N∈Finset.Icc 2 R) :
      (row b N hb)^(a N)=∏d∈Finset.Icc 2 R,
        if d≤N then (factor b d hb)^(a N) else 1 := by
    rw [row_extended b N R hb (Finset.mem_Icc.mp hN).2,←Finset.prod_zpow]
    apply Finset.prod_congr rfl
    intro d _
    split_ifs <;> simp
  rw [Finset.prod_congr rfl hrow,Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro d _
  rw [zpow_sum_eq]
  apply Finset.prod_congr rfl
  intro N _
  split_ifs <;> simp

/-- Actual second cyclotomic value. -/
theorem value_two (b:ℕ) : value b 2=(b:ℤ)+1 := by
  simp [value,Polynomial.cyclotomic_two]

/-- Actual fourth cyclotomic value. -/
theorem value_four (b:ℕ) : value b 4=(b:ℤ)^2+1 := by
  have h:Polynomial.cyclotomic 4 ℤ=Polynomial.X^2+1 := by
    simpa using Polynomial.cyclotomic_prime_pow_eq_geom_sum (R:=ℤ) (n:=1) (by norm_num :Nat.Prime 2)
  simp [value,h]

/-- Actual fifth cyclotomic value, with every coefficient retained. -/
theorem value_five (b:ℕ) : value b 5=(b:ℤ)^4+(b:ℤ)^3+(b:ℤ)^2+(b:ℤ)+1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  norm_num [value,Polynomial.cyclotomic_prime,Finset.sum_range_succ]
  ring

/-- Actual sixth cyclotomic value. -/
theorem value_six (b:ℕ) : value b 6=(b:ℤ)^2-(b:ℤ)+1 := by
  simp [value,Polynomial.cyclotomic_six]

/-- Numerator of the actual sixth Mobius-row quotient after exact cancellation. -/
def numeratorSix (b:ℕ) : ℤ := value b 4*value b 5*value b 6

/-- Literal Mobius weights at divisors1,2,3,6 give this actual rational quotient. -/
theorem mobius_six_quotient (b:ℕ) (hb:2≤b) :
    (C b 6:ℚ)/((C b 2:ℚ)*(C b 3:ℚ))=
      (numeratorSix b:ℚ)/(value b 2:ℚ) := by
  have h2:(value b 2:ℚ)≠0 := by exact_mod_cast (value_pos b 2 hb).ne'
  have h3:(value b 3:ℚ)≠0 := by exact_mod_cast (value_pos b 3 hb).ne'
  have hs3:Finset.Icc 2 3={2,3} := by decide
  have hs6:Finset.Icc 2 6={2,3,4,5,6} := by decide
  simp [C,hs3,hs6,numeratorSix]
  field_simp

/-- The actual denominator shares precisely the fixed resultant remainder6. -/
theorem numeratorSix_remainder (b:ℕ) :
    numeratorSix b=((b:ℤ)+1)*
      ((b:ℤ)^7-(b:ℤ)^6+3*(b:ℤ)^5-2*(b:ℤ)^4+
        4*(b:ℤ)^3-3*(b:ℤ)^2+5*(b:ℤ)-5)+6 := by
  rw [numeratorSix,value_four,value_five,value_six]
  ring

/-- Integrality of this reduced actual quotient is a genuine divisibility condition. -/
theorem denominator_dvd_iff (b:ℕ) :
    ((b:ℤ)+1)∣numeratorSix b ↔ ((b:ℤ)+1)∣6 := by
  rw [numeratorSix_remainder]
  exact dvd_add_right (dvd_mul_right _ _)

/-- The legitimate base three refutes automatic integer-valued Mobius row inversion. -/
theorem base_three_not_integral : ¬((3:ℤ)+1)∣numeratorSix 3 := by
  intro h
  have hh:((3:ℤ)+1)∣6 := (denominator_dvd_iff 3).mp h
  norm_num at hh

/-- Integrality here means the actual rational row quotient is an integer. -/
theorem quotient_integral_iff (b:ℕ) (hb:2≤b) :
    (∃z:ℤ,(C b 6:ℚ)/((C b 2:ℚ)*(C b 3:ℚ))=(z:ℚ)) ↔
      ((b:ℤ)+1)∣6 := by
  rw [mobius_six_quotient b hb,value_two]
  have hn:(((b:ℤ)+1:ℤ):ℚ)≠0 := by positivity
  constructor
  · rintro ⟨z,hz⟩
    have hq: (numeratorSix b:ℚ)=(z:ℚ)*(((b:ℤ)+1:ℤ):ℚ) :=
      (div_eq_iff hn).mp hz
    have hi: numeratorSix b=z*((b:ℤ)+1) := by exact_mod_cast hq
    apply (denominator_dvd_iff b).mp
    exact ⟨z,by simpa [mul_comm] using hi⟩
  · intro h
    obtain ⟨z,hz⟩ := (denominator_dvd_iff b).mpr h
    refine ⟨z,(div_eq_iff hn).mpr ?_⟩
    exact_mod_cast (by simpa [mul_comm] using hz : numeratorSix b=z*((b:ℤ)+1))

/-- Automatic integer preservation fails for the original rows at base three. -/
theorem base_three_quotient_not_integer :
    ¬∃z:ℤ,(C 3 6:ℚ)/((C 3 2:ℚ)*(C 3 3:ℚ))=(z:ℚ) := by
  rw [quotient_integral_iff 3 (by omega)]
  norm_num

end OpenAIReview.RowDeconvolution

#lint+ in OpenAIReview.RowDeconvolution

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
  unless declarations>0 do throwError "Empty actual row-deconvolution audit."
  logInfo m!"Row deconvolution audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-row-deconvolution-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-row-deconvolution-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual cyclotomic row reweighting and literal sixth quotient integrality; general resultant/density/source statements remain paper-level"),
      ("namespaceLinters",toJson (15:Nat)),("onlyStandardAxioms",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr details)]).pretty
