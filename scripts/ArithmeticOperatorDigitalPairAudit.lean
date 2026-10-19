/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorDigitalCarryAudit
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# The literal adjacent digital pair restores the odd prime-power row

Prime-power weights stay INSIDE the amplitude before its square. Odd
translated rows have constant pair sign on all odd prime powers; every
remaining two-power term is retained. The finite two-variable and Hermitian
ledgers do not infer a meromorphic source from the denominator diagonal.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace OpenAIReview.DigitalPair
open OpenAIReview.DigitalCarry

/-- Literal adjacent central-binomial parity product. -/
def pairSign (n : ℕ) : ℤ := epsilon n*epsilon (n+1)

/-- The identical sign in the coefficient field. -/
def pairCoeff (n : ℕ) : ℂ := (pairSign n : ℂ)

/-- Positive powers of two, with the order retained existentially. -/
def twoPower (d : ℕ) : Prop := ∃ r : ℕ,0<r ∧ d=2^r

/-- All arithmetic weights and phases are joined before the square. -/
def amplitude (D : Finset ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d∈D,w d*pairCoeff (n+d)

/-- The complete uncoded odd-denominator contribution. -/
def oddPart (D : Finset ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ d∈D,if d%2=1 then w d else 0

/-- Every exceptional two-power contribution, with its literal weight. -/
def twoTower (D : Finset ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d∈D,if twoPower d then w d*pairCoeff (n+d) else 0

/-- A holomorphic-style two-variable ledger has two independent arrays. -/
def polarized (D : Finset ℕ) (w v : ℕ → ℂ) (n : ℕ) : ℂ :=
  amplitude D w n*amplitude D v n

/-- The genuine Hermitian square keeps its conjugated second array. -/
def hermitian (D : Finset ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  amplitude D w n*conj (amplitude D w n)

/-- Single-denominator diagonal: its arithmetic phase is conjugated away. -/
def diagonal (D : Finset ℕ) (w : ℕ → ℂ) : ℂ := ∑ d∈D,w d*conj (w d)

/-- True distinct-denominator terms, including distinct prime bases. -/
def cross (D : Finset ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d∈D,∑ e∈D.erase d,
    (w d*pairCoeff (n+d))*conj (w e*pairCoeff (n+e))

/-- Actual Mangoldt with an arbitrary literal denominator phase. -/
def mangoldtWeight (phase : ℕ → ℂ) (d : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt d : ℂ)*phase d

/-- The adjacent pair has unit magnitude at every actual integer. -/
@[simp] theorem abs_pairSign (n : ℕ) : |pairSign n|=1 := by
  simp [pairSign,abs_mul]

/-- Every even argument has exactly negative pair sign. -/
@[simp] theorem pairSign_double (n : ℕ) : pairSign (2*n)= -1 := by
  unfold pairSign
  rw [epsilon_double,epsilon_double_add_one]
  have he:=abs_epsilon n
  rcases le_or_gt 0 (epsilon n) with hs | hs
  · rw [abs_of_nonneg hs] at he
    simp [he]
  · rw [abs_of_neg hs] at he
    have ht : epsilon n= -1 := by omega
    simp [ht]

/-- The even residue form retains the original integer endpoint. -/
theorem pairSign_of_even {n : ℕ} (hn : n%2=0) : pairSign n= -1 := by
  obtain ⟨q,hq⟩:=Nat.dvd_of_mod_eq_zero hn
  rw [hq,pairSign_double]

/-- Odd translations of odd denominators land on the exact negative row. -/
theorem pairCoeff_odd_odd {n d : ℕ} (hn : n%2=1) (hd : d%2=1) :
    pairCoeff (n+d)= -1 := by
  have he : (n+d)%2=0 := by rw [Nat.add_mod,hn,hd]
  simp [pairCoeff,pairSign_of_even he]

/-- The digital factor cancels on a genuine Hermitian denominator diagonal. -/
@[simp] theorem pairCoeff_mul_conj (n : ℕ) : pairCoeff n*conj (pairCoeff n)=1 := by
  have he:=abs_pairSign n
  rcases le_or_gt 0 (pairSign n) with hs | hs
  · rw [abs_of_nonneg hs] at he
    simp [pairCoeff,he]
  · rw [abs_of_neg hs] at he
    have ht : pairSign n= -1 := by omega
    simp [pairCoeff,ht]

/-- A positive two-power is actually even, including all proper powers. -/
theorem twoPower_mod_two {d : ℕ} (hd : twoPower d) : d%2=0 := by
  obtain ⟨r,hr,rfl⟩:=hd
  simp [Nat.pow_mod,hr.ne']

/-- Every even prime power belongs to the one literal two-power tower. -/
theorem twoPower_of_primePower_even {d : ℕ} (hp : IsPrimePow d) (hd : d%2=0) :
    twoPower d := by
  obtain ⟨p,r,hp,hr,he⟩:=(isPrimePow_nat_iff d).mp hp
  have hdiv : 2∣p^r := by rw [he]; exact Nat.dvd_of_mod_eq_zero hd
  have hdivp : 2∣p := Nat.prime_two.dvd_of_dvd_pow hdiv
  have hp2 : p=2 := by
    rcases (Nat.dvd_prime hp).mp hdivp with h | h
    · norm_num at h
    · exact h.symm
  exact ⟨r,hr,by rw [← he,hp2]⟩

/-- Exact native odd-row collapse for arbitrary prime-power-supported
complex weights. Neither phases nor the two-power tower are dropped. -/
theorem amplitude_odd_row (D : Finset ℕ) (w : ℕ → ℂ)
    (hw : ∀ d∈D,w d≠0 → IsPrimePow d) {n : ℕ} (hn : n%2=1) :
    amplitude D w n= -oddPart D w+twoTower D w n := by
  unfold amplitude oddPart twoTower
  rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hw0 : w d=0
  · simp [hw0]
  have hp:=hw d hd hw0
  by_cases hodd : d%2=1
  · have hnot : ¬twoPower d := by intro ht; have he:=twoPower_mod_two ht; omega
    simp [hodd,hnot,pairCoeff_odd_odd hn hodd]
  · have heven : d%2=0 := by have h:=Nat.mod_lt d (by norm_num : 0<2); omega
    have ht:=twoPower_of_primePower_even hp heven
    simp [hodd,ht]

/-- The two independent arrays keep their two-variable products explicit. -/
theorem polarized_odd_row (D : Finset ℕ) (w v : ℕ → ℂ)
    (hw : ∀ d∈D,w d≠0 → IsPrimePow d)
    (hv : ∀ d∈D,v d≠0 → IsPrimePow d) {n : ℕ} (hn : n%2=1) :
    polarized D w v n=oddPart D w*oddPart D v-
      oddPart D w*twoTower D v n-twoTower D w n*oddPart D v+
      twoTower D w n*twoTower D v n := by
  unfold polarized
  rw [amplitude_odd_row D w hw hn,amplitude_odd_row D v hv hn]
  ring

/-- The genuine square ledger conjugates every phase on the second leg. -/
theorem hermitian_odd_row (D : Finset ℕ) (w : ℕ → ℂ)
    (hw : ∀ d∈D,w d≠0 → IsPrimePow d) {n : ℕ} (hn : n%2=1) :
    hermitian D w n=oddPart D w*conj (oddPart D w)-
      oddPart D w*conj (twoTower D w n)-twoTower D w n*conj (oddPart D w)+
      twoTower D w n*conj (twoTower D w n) := by
  unfold hermitian
  rw [amplitude_odd_row D w hw hn]
  simp only [map_add,map_neg]
  ring

/-- Exact diagonal versus true distinct-denominator expansion, valid
before any use of primality or replacement by a mean autocorrelation. -/
theorem hermitian_eq_diagonal_add_cross (D : Finset ℕ) (w : ℕ → ℂ) (n : ℕ) :
    hermitian D w n=diagonal D w+cross D w n := by
  unfold hermitian amplitude diagonal cross
  rw [map_sum,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum,← Finset.sum_erase_add _ _ hd]
  simp only [map_mul]
  have he : (w d*pairCoeff (n+d))*(conj (w d)*conj (pairCoeff (n+d)))=
      w d*conj (w d) := by
    calc
      _ = (w d*conj (w d))*(pairCoeff (n+d)*conj (pairCoeff (n+d))) := by ring
      _ = _ := by rw [pairCoeff_mul_conj,mul_one]
  rw [he]
  ring

/-- Nonzero actual phase-weighted Mangoldt coefficients have true prime
power support, with no sign or magnitude assumption on the phase. -/
theorem mangoldtWeight_supported (phase : ℕ → ℂ) {d : ℕ}
    (hd : mangoldtWeight phase d≠0) : IsPrimePow d := by
  apply ArithmeticFunction.vonMangoldt_ne_zero_iff.mp
  intro hz
  apply hd
  simp [mangoldtWeight,hz]

/-- Every actual two-power retains the same base logarithm and its own phase. -/
theorem mangoldtWeight_twoPower (phase : ℕ → ℂ) {r : ℕ} (hr : 0<r) :
    mangoldtWeight phase (2^r)=(Real.log 2 : ℂ)*phase (2^r) := by
  simp only [mangoldtWeight,ArithmeticFunction.vonMangoldt_apply_pow hr.ne',
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- Native prime-power specialization, retaining all denominator phases. -/
theorem amplitude_mangoldt_odd_row (D : Finset ℕ) (phase : ℕ → ℂ)
    {n : ℕ} (hn : n%2=1) :
    amplitude D (mangoldtWeight phase) n=
      -oddPart D (mangoldtWeight phase)+twoTower D (mangoldtWeight phase) n :=
  amplitude_odd_row D _ (fun _ _ hd => mangoldtWeight_supported phase hd) hn

end OpenAIReview.DigitalPair

#lint+ in OpenAIReview.DigitalPair

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
  unless declarations>0 do throwError "Empty digital-pair audit."
  logInfo m!"Digital-pair audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-digital-nonlinear-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-digital-nonlinear-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual adjacent digital pair with prime-power weights inside amplitude; exact odd/two-tower and two-variable ledgers, no source theorem"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
