/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian
import RiemannGaussian.ZetaRieszLowCountSelbergAudit
import RiemannGaussian.ZetaArithmeticBandCorrelation
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Reject automatic prime-dilation orthogonality for the balanced pair block

An optional focused audit, not another endgame carrier or a floor bound.
The actual logarithmic phase disappears from the cofactor correlation.
The balanced defect retains its literal positive factorial amplitudes, so
the entire positive overlap remains. This says nothing against cancellation
between the outer prime phases in the original signed sum.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszBalancedDilationAudit
open ZetaArithmeticBandCorrelation
open ZetaRieszLowCountSelbergAudit ZetaRieszGlobalHeadPriceAudit

/-- The actual logarithmic character. No random-phase replacement. -/
def chi (y : ℝ) (n : ℕ) : ℂ := unitPhase (-y*Real.log n)

theorem norm_chi (y : ℝ) (n : ℕ) : ‖chi y n‖=1 := norm_unitPhase _

theorem phase_cross (y : ℝ) (p q n : ℕ) (hp : p≠0) (hq : q≠0) (hn : n≠0) :
    chi y (p*n)*starRingEnd ℂ (chi y (q*n))=
      unitPhase (-y*(Real.log p-Real.log q)) := by
  rw [chi,chi,← unitPhase_sub]
  congr 1
  rw [Nat.cast_mul,Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hp) (by exact_mod_cast hn),
    Real.log_mul (by exact_mod_cast hq) (by exact_mod_cast hn)]
  ring

/-- Retain all real factorial/coefficient/support weights in the rows.
Their overlap has one constant phase, independent of the cofactor. -/
theorem weighted_cross_eq (S : Finset ℕ) (a b : ℕ→ℝ) (y : ℝ)
    (p q : ℕ) (hp : p≠0) (hq : q≠0) (hS : ∀ n∈S,n≠0) :
    (∑ n∈S,((a n : ℂ)*chi y (p*n))*
      starRingEnd ℂ ((b n : ℂ)*chi y (q*n)))=
      ((∑ n∈S,a n*b n : ℝ) : ℂ)*
        unitPhase (-y*(Real.log p-Real.log q)) := by
  rw [Complex.ofReal_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul,Complex.conj_ofReal,Complex.ofReal_mul]
  calc
    _ = (a n : ℂ)*(b n : ℂ)*
        (chi y (p*n)*starRingEnd ℂ (chi y (q*n))) := by ring
    _ = _ := by rw [phase_cross y p q n hp hq (hS n hn)]

/-- For nonnegative overlapping literal amplitudes there is no
phase saving at all in this correlation, at any fixed height. -/
theorem norm_weighted_cross_eq (S : Finset ℕ) (a b : ℕ→ℝ) (y : ℝ)
    (p q : ℕ) (hp : p≠0) (hq : q≠0) (hS : ∀ n∈S,n≠0)
    (ha : ∀ n∈S,0≤a n) (hb : ∀ n∈S,0≤b n) :
    ‖∑ n∈S,((a n : ℂ)*chi y (p*n))*
      starRingEnd ℂ ((b n : ℂ)*chi y (q*n))‖=
      ∑ n∈S,a n*b n := by
  rw [weighted_cross_eq S a b y p q hp hq hS,norm_mul,norm_unitPhase,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
  exact Finset.sum_nonneg (fun n hn => mul_nonneg (ha n hn) (hb n hn))

/-- Explicit obstruction to a strict relative saving from dilation
phases alone. This does not rule out signed amplitude cancellation. -/
theorem relative_cross_cost_ge_one (S : Finset ℕ) (a b : ℕ→ℝ) (y ε : ℝ)
    (p q : ℕ) (hp : p≠0) (hq : q≠0) (hS : ∀ n∈S,n≠0)
    (ha : ∀ n∈S,0≤a n) (hb : ∀ n∈S,0≤b n)
    (hpos : 0<∑ n∈S,a n*b n)
    (hcost : ‖∑ n∈S,((a n : ℂ)*chi y (p*n))*
      starRingEnd ℂ ((b n : ℂ)*chi y (q*n))‖≤
        ε*(∑ n∈S,a n*b n)) : 1≤ε := by
  rw [norm_weighted_cross_eq S a b y p q hp hq hS ha hb] at hcost
  nlinarith only [hcost,hpos]

/-- The plain logarithmic character violates the required small
prime-dilation correlation by the full cardinality, exactly. -/
theorem unweighted_cross_norm (X p q : ℕ) (y : ℝ) (hp : p≠0) (hq : q≠0) :
    ‖∑ n∈Finset.Icc 1 X,chi y (p*n)*starRingEnd ℂ (chi y (q*n))‖=(X : ℝ) := by
  simpa using norm_weighted_cross_eq (Finset.Icc 1 X) (fun _ => 1)
    (fun _ => 1) y p q hp hq
    (fun n hn => by have := (Finset.mem_Icc.mp hn).1; omega)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)

/-- Exactly the retained balanced defect's real factorial amplitude. -/
def amplitude (u : ℝ) (N p q : ℕ) : ℝ :=
  u^(N+1)*(selbergDefect u N (p*q)).re*
    ((Real.log (p*q : ℕ))^N/(N.factorial : ℝ)*
      Real.exp (-(3/2 : ℝ)*Real.log (p*q : ℕ)))

/-- The amplitude in the test is the literal signed pair atom, with
the original coefficient and entire factorial phase. -/
theorem literal_atom_eq (u y : ℝ) (N p q : ℕ) :
    (u : ℂ)^(N+1)*selbergDefect u N (p*q)*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q)=
        (amplitude u N p q : ℂ)*chi y (p*q) := by
  have hc : selbergDefect u N (p*q)=((selbergDefect u N (p*q)).re : ℂ) := by
    unfold selbergDefect
    rw [ZetaRieszLowCountSignedBoundary.joinedCoefficient_real]
    unfold selbergCoefficient
    simp
  rw [hc]
  unfold amplitude chi unitPhase zetaPrimeLogKernel zetaPrimeFeature
  push_cast
  simp_rw [mul_assoc]
  rw [← Complex.exp_add]
  congr 4
  ring

theorem balanced_amplitude_pos {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536≤N) (hp : p∈ZetaRieszAllowancePrimeBoxes.logPrimes N 1)
    (hq : q∈ZetaRieszAllowancePrimeBoxes.logPrimes (N+1) 1) :
    0<amplitude u N p q := by
  have he : (p,q)∈balancedPairs N := Finset.mem_product.mpr ⟨hp,hq⟩
  have hn : p*q∈balancedProducts N := Finset.mem_image.mpr ⟨(p,q),he,rfl⟩
  have hd := balanced_defect_lower hu hU hN hn
  have hpP := (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hp).1
  have hqP := (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hq).1
  have hnl : (1 : ℝ)<p*q := by exact_mod_cast (show 1<p*q by
    nlinarith only [hpP.two_le,hqP.two_le])
  have hlog : 0<Real.log (p*q : ℕ) := Real.log_pos (by exact_mod_cast hnl)
  have hd0 : 0<(selbergDefect u N (p*q)).re := by
    have hNr : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
    linarith only [hd,hNr]
  unfold amplitude
  positivity

/-- The balanced block really has the nonnegative rows required by the
correlation obstruction; no sieve, owner or factorial mask is deleted. -/
theorem balanced_cross_no_phase_saving {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p p' : ℕ}
    (hN : 65536≤N) (hp : p∈ZetaRieszAllowancePrimeBoxes.logPrimes N 1)
    (hp' : p'∈ZetaRieszAllowancePrimeBoxes.logPrimes N 1) (y : ℝ) :
    ‖∑ q∈ZetaRieszAllowancePrimeBoxes.logPrimes (N+1) 1,
      ((amplitude u N p q : ℂ)*chi y (p*q))*
        starRingEnd ℂ ((amplitude u N p' q : ℂ)*chi y (p'*q))‖=
      ∑ q∈ZetaRieszAllowancePrimeBoxes.logPrimes (N+1) 1,
        amplitude u N p q*amplitude u N p' q := by
  apply norm_weighted_cross_eq
  · exact (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hp).1.ne_zero
  · exact (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hp').1.ne_zero
  · intro q hq
    exact (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hq).1.ne_zero
  · intro q hq
    exact (balanced_amplitude_pos hu hU hN hp hq).le
  · intro q hq
    exact (balanced_amplitude_pos hu hU hN hp' hq).le

/-- No support extension: this is the correlation of the exact atoms
of the surviving balanced-pair block in `literalPairDefect`. -/
theorem balanced_literal_cross_eq {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p p' : ℕ}
    (hN : 65536≤N) (hp : p∈ZetaRieszAllowancePrimeBoxes.logPrimes N 1)
    (hp' : p'∈ZetaRieszAllowancePrimeBoxes.logPrimes N 1) (y : ℝ) :
    ‖∑ q∈ZetaRieszAllowancePrimeBoxes.logPrimes (N+1) 1,
      ((u : ℂ)^(N+1)*selbergDefect u N (p*q)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*q))*
      starRingEnd ℂ ((u : ℂ)^(N+1)*selbergDefect u N (p'*q)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p'*q))‖=
      ∑ q∈ZetaRieszAllowancePrimeBoxes.logPrimes (N+1) 1,
        amplitude u N p q*amplitude u N p' q := by
  simp_rw [literal_atom_eq]
  exact balanced_cross_no_phase_saving hu hU hN hp hp' y

end RiemannGaussian.ZetaRieszBalancedDilationAudit

#lint+ in RiemannGaussian.ZetaRieszBalancedDilationAudit
#print axioms RiemannGaussian.ZetaRieszBalancedDilationAudit.balanced_cross_no_phase_saving
#print axioms RiemannGaussian.ZetaRieszBalancedDilationAudit.relative_cross_cost_ge_one
#print axioms RiemannGaussian.ZetaRieszBalancedDilationAudit.balanced_literal_cross_eq
#print axioms RiemannGaussian.ZetaRieszBalancedDilationAudit.unweighted_cross_norm

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut checked : Array Json := #[]
  let mut declarations : Nat := 0
  for (name, ci) in env.constants.toList do
    unless name.toString.startsWith "RiemannGaussian.ZetaRieszBalancedDilationAudit." do continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {name}"
    let dependencies ← Lean.collectAxioms name
    for ax in dependencies do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {name}: {ax}"
    if ci.isTheorem then
      checked := checked.push (Json.mkObj [("theorem",toJson name.toString),
        ("axioms",toJson (dependencies.map Name.toString))])
  logInfo m!"Checked {checked.size} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/riesz-balanced-dilation-audit"
  IO.FS.writeFile ".lake/riesz-balanced-dilation-audit/axioms.json"
    (Json.mkObj [("declarations",toJson declarations),
      ("theoremsIncludingGenerated",toJson checked.size),
      ("onlyStandardAxioms",toJson true),("theoremAxioms",Json.arr checked)]).pretty
