/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms
/-!
# Actual cyclotomic common-base CRT collapse

This isolated leaf retains the actual once-counted cyclotomic polynomial,
all residue classes and one legal common integer representative. Complete
coprime-modulus moments factor; arbitrary complex weights do not restore
a centered off-diagonal covariance. Nested divisor incidences are retained.
Local LTE counts, asymptotics, interval discrepancy and source are paper-level.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace OpenAIReview.CommonBaseCRT
/-- The actual once-counted polynomial; index one is omitted. -/
def productPolynomial (N : ℕ) : Polynomial ℤ :=
  ∏ n∈Finset.Icc 2 N, Polynomial.cyclotomic n ℤ
/-- Literal divisibility incidence, including nonunit and zero base residues. -/
def incidence (N m : ℕ) (x : ZMod m) : ℂ :=
  if (productPolynomial N).eval₂ (Int.castRingHom (ZMod m)) x=0 then 1 else 0
/-- This residue incidence is the divisibility of the actual integer value. -/
theorem incidence_integer (N m b : ℕ) :
    incidence N m (b : ZMod m)=
      if (m : ℤ)∣(productPolynomial N).eval (b : ℤ) then 1 else 0 := by
  unfold incidence
  have hc : (b : ZMod m)=(Int.castRingHom (ZMod m)) (b : ℤ) := by simp
  rw [hc,Polynomial.eval₂_at_apply]
  simp only [Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
/-- Every retained cyclotomic factor has constant coefficient one. -/
theorem product_at_zero (N : ℕ) : (productPolynomial N).eval 0=1 := by
  unfold productPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_one
  intro n hn
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact Polynomial.cyclotomic_coeff_zero ℤ (by have := (Finset.mem_Icc.mp hn).1; omega)
/-- A base prime is excluded, rather than conditioned away by unit averaging. -/
theorem incidence_zero (N m : ℕ) (hm : 1<m) : incidence N m 0=0 := by
  unfold incidence
  have he : (productPolynomial N).eval₂ (Int.castRingHom (ZMod m)) 0=1 := by
    rw [show (0 : ZMod m)=(Int.castRingHom (ZMod m)) 0 by simp,
      Polynomial.eval₂_at_apply,product_at_zero]
    simp
  rw [he]
  have : (1 : ZMod m)≠0 := by
    intro hz
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd 1 m).mp (by simpa using hz)
    have : (m : ℤ)≤1 := Int.le_of_dvd (by norm_num) hd
    omega
  simp [this]
/-- The same integer value has nested prime-power (indeed divisor) incidences. -/
theorem nested_integer_incidence (N b m n : ℕ) (hmn : m∣n) :
    incidence N m (b : ZMod m)*incidence N n (b : ZMod n)=
      incidence N n (b : ZMod n) := by
  rw [incidence_integer,incidence_integer]
  have hd : (m : ℤ)∣(n : ℤ) := by exact_mod_cast hmn
  by_cases hn : (n : ℤ)∣(productPolynomial N).eval (b : ℤ)
  · have hm := hd.trans hn
    simp [hm,hn]
  · simp [hn]
/-- A common CRT residue has a literal common integer base at least two. -/
def representative (m n : ℕ) (x : ZMod (m*n)) : ℕ := x.val+2*(m*n)
/-- The representative is a permitted base, including for zero and nonunit residues. -/
theorem representative_ge_two (m n : ℕ) [NeZero m] [NeZero n]
    (x : ZMod (m*n)) : 2≤representative m n x := by
  have hm : 0<m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hp : 0<m*n := Nat.mul_pos hm hn
  unfold representative
  omega
/-- Both CRT coordinates are reductions of the SAME permitted integer base. -/
theorem representative_coordinates (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (x : ZMod (m*n)) :
    ZMod.chineseRemainder h x=
      ((representative m n x : ZMod m),(representative m n x : ZMod n)) := by
  have hx : (x.val : ZMod (m*n))=x := ZMod.natCast_zmod_val x
  have he0 : ZMod.chineseRemainder h x=(x.val : ZMod m×ZMod n) := by
    simpa only [hx] using map_natCast (ZMod.chineseRemainder h) x.val
  have he : ZMod.chineseRemainder h x=((x.val : ZMod m),(x.val : ZMod n)) := by
    rw [he0]
    ext <;> simp
  rw [he]
  simp [representative,Nat.cast_add,Nat.cast_mul]
/-- Full-residue mean, with denominator m rather than phi(m). -/
def mean (N m : ℕ) [NeZero m] : ℂ := (∑ x : ZMod m,incidence N m x)/(m : ℂ)
/-- Center by the complete local mean, not a fitted interval mean. -/
def centered (N m : ℕ) [NeZero m] (x : ZMod m) : ℂ := incidence N m x-mean N m
/-- Centered local sum is exactly zero. -/
theorem sum_centered (N m : ℕ) [NeZero m] : ∑ x : ZMod m,centered N m x=0 := by
  have hm : (m : ℂ)≠0 := by exact_mod_cast NeZero.ne m
  simp only [centered,mean,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,ZMod.card,nsmul_eq_mul]
  field_simp [hm]
  ring
/-- CRT is a bijection of ONE complete common-base residue set. -/
theorem sum_crt_mul (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (f : ZMod m→ℂ) (g : ZMod n→ℂ) :
    (∑ x : ZMod (m*n),f (ZMod.chineseRemainder h x).1*g (ZMod.chineseRemainder h x).2)=
      (∑ a : ZMod m,f a)*(∑ b : ZMod n,g b) := by
  calc
    _=∑ y : ZMod m×ZMod n,f y.1*g y.2 :=
      (ZMod.chineseRemainder h).toEquiv.sum_comp _
    _=_ := by rw [Fintype.sum_prod_type]; simp_rw [← Finset.mul_sum]; rw [Finset.sum_mul]
/-- Exact common-base first moment, including every zero residue. -/
theorem sum_crt_left (N m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    (∑ x : ZMod (m*n),incidence N m (ZMod.chineseRemainder h x).1)=
      (n : ℂ)*(∑ a : ZMod m,incidence N m a) := by
  simpa [ZMod.card,mul_comm] using sum_crt_mul m n h (incidence N m) (fun _=>1)
/-- Actual cyclotomic incidences at coprime moduli factor exactly. -/
theorem cyclotomic_second_moment (N m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    (∑ x : ZMod (m*n),incidence N m (ZMod.chineseRemainder h x).1*
      incidence N n (ZMod.chineseRemainder h x).2)=
      (∑ a : ZMod m,incidence N m a)*(∑ b : ZMod n,incidence N n b) :=
  sum_crt_mul m n h (incidence N m) (incidence N n)
/-- Centering removes every complete off-diagonal covariance, for arbitrary complex weights. -/
theorem arbitrary_weights_covariance_zero (N m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (w v : ℂ) :
    (∑ x : ZMod (m*n),(w*centered N m (ZMod.chineseRemainder h x).1)*
      (v*centered N n (ZMod.chineseRemainder h x).2))=0 := by
  rw [sum_crt_mul m n h (fun a=>w*centered N m a) (fun b=>v*centered N n b)]
  simp_rw [← Finset.mul_sum,sum_centered,mul_zero]
end OpenAIReview.CommonBaseCRT
#lint+ in OpenAIReview.CommonBaseCRT

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
  unless declarations>0 do throwError "Empty common-base CRT audit."
  logInfo m!"Common-base CRT audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-common-base-covariance-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-common-base-covariance-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual once-counted cyclotomic incidence; all residues and one permitted common CRT integer base; complete first/second moment factorization and arbitrary-weight centered covariance zero; nested divisor incidences. Higher-depth counts, source, rates and incomplete intervals are paper-level"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr reports)]).pretty
