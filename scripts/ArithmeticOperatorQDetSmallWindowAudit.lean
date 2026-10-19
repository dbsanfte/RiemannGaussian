/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual cyclotomic product covers the small physical window

Index one is omitted. Every prime power p^r≤N with p not dividing b
still divides the actual once-counted cyclotomic product. The proof uses
geometric sums and Fermat-Euler, including p=2, without a primitive-prime
or prime-density assumption. Product packets must retain shifted depths;
this is not a theorem about a sum of row packets or physical cutoffs above N.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace OpenAIReview.QDetSmallWindow

/-- Actual positive cyclotomic integer norm. -/
def cyclotomicNorm (b n : ℕ) : ℕ := ((Polynomial.cyclotomic n ℤ).eval (b : ℤ)).natAbs

/-- Every index occurs exactly once, and index one is omitted. -/
def cyclotomicProduct (b N : ℕ) : ℕ := ∏ n∈Finset.Icc 2 N,cyclotomicNorm b n

/-- The ordinary finite geometric sum at an integer base. -/
def geometric (b m : ℕ) : ℕ := ∑ j∈Finset.range m,b^j

/-- The actual divisor product equals the geometric sum, without index one. -/
theorem divisor_product (b m : ℕ) (hm : 0<m) :
    (∏ d∈m.divisors.erase 1,cyclotomicNorm b d)=geometric b m := by
  have h:=congrArg (Polynomial.eval (b : ℤ))
    (Polynomial.prod_cyclotomic_eq_geom_sum hm ℤ)
  have hi : (∏ d∈m.divisors.erase 1,(Polynomial.cyclotomic d ℤ).eval (b : ℤ))=
      (geometric b m : ℤ) := by
    simpa [geometric,Polynomial.eval_prod] using h
  change (∏ d∈m.divisors.erase 1,Int.natAbsHom ((Polynomial.cyclotomic d ℤ).eval (b : ℤ)))=_
  rw [← map_prod]
  change (∏ d∈m.divisors.erase 1,(Polynomial.cyclotomic d ℤ).eval (b : ℤ)).natAbs=_
  rw [hi]
  simp

/-- A geometric sum at any positive index m≤N divides the native product. -/
theorem geometric_dvd_product (b N m : ℕ) (hm : 0<m) (hmN : m≤N) :
    geometric b m ∣ cyclotomicProduct b N := by
  rw [← divisor_product b m hm]
  apply Finset.prod_dvd_prod_of_subset
  intro d hd
  obtain ⟨hd1,hdm⟩:=Finset.mem_erase.mp hd
  obtain ⟨hdm',hm0⟩:=Nat.mem_divisors.mp hdm
  exact Finset.mem_Icc.mpr ⟨by have := Nat.pos_of_dvd_of_pos hdm' hm; omega,
    (Nat.le_of_dvd hm hdm').trans hmN⟩

/-- Geometric sums split into successive equal blocks at a nontrivial base. -/
theorem geometric_mul (b m n : ℕ) (hb : 2≤b) :
    geometric b (m*n)=geometric b m*geometric (b^m) n := by
  apply Nat.eq_of_mul_eq_mul_right (show 0<b-1 by omega)
  calc
    geometric b (m*n)*(b-1)=b^(m*n)-1 := geom_sum_mul_of_one_le (by omega) _
    _=(b^m)^n-1 := by rw [pow_mul]
    _=geometric (b^m) n*(b^m-1) := (geom_sum_mul_of_one_le (by have := pow_pos (show 0<b by omega) m; omega) _).symm
    _=(geometric b m*geometric (b^m) n)*(b-1) := by
      rw [← geom_sum_mul_of_one_le (show 1≤b by omega) m]
      simp only [geometric]
      ring

/-- If p divides b−1, every p-index block contributes another factor p. -/
theorem geometric_prime_blocks (b p r : ℕ) (hb : 2≤b) (hpb : p∣b-1) :
    p^r∣geometric b (p^r) := by
  have he : (b : ZMod p)=1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff b 1 p).2
      (((Nat.modEq_iff_dvd' (show 1≤b by omega)).2 hpb).symm)
  induction r with
  | zero => simp
  | succ r ih =>
    have hf : p∣geometric (b^(p^r)) p := by
      apply (ZMod.natCast_eq_zero_iff _ _).1
      simp [geometric,he]
    rw [pow_succ,geometric_mul b (p^r) p hb]
    exact mul_dvd_mul ih hf

/-- Away from b−1, Fermat-Euler supplies the required geometric-sum factor. -/
theorem geometric_totient (b p r : ℕ) (hb : 2≤b) (hp : p.Prime)
    (hpb : ¬p∣b) (hpb1 : ¬p∣b-1) :
    p^r∣geometric b (p^r).totient := by
  have hcop:=hp.coprime_pow_of_not_dvd (m:=r) hpb
  have hcop1:=hp.coprime_pow_of_not_dvd (m:=r) hpb1
  have hd : p^r∣b^((p^r).totient)-1 := (Nat.ModEq.pow_totient hcop).symm.dvd'
  rw [← geom_sum_mul_of_one_le (show 1≤b by omega)] at hd
  exact hcop1.symm.dvd_of_dvd_mul_right hd

/-- Exact native coverage of every base-coprime prime power up to N. -/
theorem prime_power_coverage (b N p r : ℕ) (hb : 2≤b) (hp : p.Prime)
    (hpb : ¬p∣b) (hcut : p^r≤N) : p^r∣cyclotomicProduct b N := by
  by_cases hpb1 : p∣b-1
  · exact (geometric_prime_blocks b p r hb hpb1).trans
      (geometric_dvd_product b N (p^r) (pow_pos hp.pos _) hcut)
  · exact (geometric_totient b p r hb hp hpb hpb1).trans
      (geometric_dvd_product b N (p^r).totient
        (Nat.totient_pos.mpr (pow_pos hp.pos _)) ((Nat.totient_le _).trans hcut))

/-- The actual product is positive at every integer base at least two. -/
theorem product_pos (b N : ℕ) (hb : 2≤b) : 0<cyclotomicProduct b N := by
  apply Finset.prod_pos
  intro n hn
  have hn1 : 1<n := by have := (Finset.mem_Icc.mp hn).1; omega
  exact lt_trans (show 0<b-1 by omega)
    (Polynomial.sub_one_lt_natAbs_cyclotomic_eval hn1 (by omega))

/-- Base primes cannot divide a positive-index actual cyclotomic value. -/
theorem base_prime_absent (b n p : ℕ) (hn : 0<n) (hp : p.Prime) (hpb : p∣b) :
    ¬p∣cyclotomicNorm b n := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  have hz : Int.castRingHom (ZMod p) ((Polynomial.cyclotomic n ℤ).eval (b : ℤ))=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (Int.natCast_dvd.mpr hd)
  have hroot : Polynomial.IsRoot (Polynomial.cyclotomic n (ZMod p))
      (Nat.castRingHom (ZMod p) b) := by
    have he:=Polynomial.cyclotomic.eval_apply (b : ℤ) n (Int.castRingHom (ZMod p))
    simpa using he.trans hz
  have hc:=Polynomial.coprime_of_root_cyclotomic hn hroot
  exact (hp.coprime_iff_not_dvd.mp hc.symm) hpb

/-- Every base prime is absent from the entire native product. -/
theorem base_prime_product_absent (b N p : ℕ) (hp : p.Prime) (hpb : p∣b) :
    ¬p∣cyclotomicProduct b N := by
  rw [cyclotomicProduct,hp.prime.dvd_finsetProd_iff]
  rintro ⟨n,hn,hd⟩
  exact base_prime_absent b n p (by have := (Finset.mem_Icc.mp hn).1; omega) hp hpb hd

/-- Inside the proved window, the product's positive prime-power support is uncoded. -/
theorem small_window_support (b N p r : ℕ) (hb : 2≤b) (hp : p.Prime)
    (hr : 0<r) (hcut : p^r≤N) :
    p^r∣cyclotomicProduct b N ↔ ¬p∣b := by
  constructor
  · intro hd hpb
    exact base_prime_product_absent b N p hp hpb
      ((dvd_pow_self p hr.ne').trans hd)
  · exact fun hpb => prime_power_coverage b N p r hb hp hpb hcut

end OpenAIReview.QDetSmallWindow

#lint+ in OpenAIReview.QDetSmallWindow

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
  unless declarations>0 do throwError "Empty small-window audit."
  logInfo m!"Small-window audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-qdet-small-window-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-qdet-small-window-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual once-counted cyclotomic product, exact base-coprime prime-power support for p^r<=N; full determinant extraction/source paper-level"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr reports)]).pretty
