/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.SourceLocal
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! # Native positive frequency rows under a higher-sixth restriction

This isolated source preflight joins the actual four positive native local
rows at a fixed frequency order, with their Gaussian and character phases.
The restriction keeps frequency orders divisible by `ell`. It changes the
density pole; it does not supply a new arithmetic bound or a global source
continuation below the existing native endpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.HigherSixthFrequency
open OAI OAI.SevenEighths.ProbeEuler
open OAI.ActualEisensteinCubic OAI.ConcretePrimeRowBridge

local notation "O" => OAI.ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

/-- The four actual nonzero marked rows at frequency order `n+1`, before
the independent index-zero density row is added. -/
def positiveMarkedFrequency (eta a X W : ℂ) (n : ℕ) : ℂ :=
  principalMarkedTerm p hp hg eta a X W 1 1 (2*(n+1)) 0 (n+1) +
  principalMarkedTerm p hp hg eta a X W 1 0 (2*n+2) 1 (n+1) +
  ∑ r ∈ Finset.range (n+1),
    (principalMarkedTerm p hp hg eta a X W 1 0 (2*r+2) 0 (n+1) +
      principalMarkedTerm p hp hg eta a X W 1 1 (2*r) 1 (n+1))

include hc in
theorem positiveMarkedFrequency_eq (eta a X W : ℂ) (n : ℕ) :
    positiveMarkedFrequency p hp hg eta a X W n =
      (W-eta*X)*(evenRatio (Ideal.absNorm (Ideal.span {p})) a X 1)^(n+1) +
      ((1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*
          evenRatio (Ideal.absNorm (Ideal.span {p})) a X 1 -
        eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W) *
          ∑ r ∈ Finset.range (n+1),
            (evenRatio (Ideal.absNorm (Ideal.span {p})) a X 1)^r := by
  unfold positiveMarkedFrequency
  rw [markedTerm_squarefree_boundary p hp hg hc,
    markedTerm_even_kone p hp hg hc]
  have hs :
      (∑ r ∈ Finset.range (n+1),
        (principalMarkedTerm p hp hg eta a X W 1 0 (2*r+2) 0 (n+1) +
          principalMarkedTerm p hp hg eta a X W 1 1 (2*r) 1 (n+1))) =
      ∑ r ∈ Finset.range (n+1),
        (((1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*
            evenRatio (Ideal.absNorm (Ideal.span {p})) a X 1 -
          eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W) *
            (evenRatio (Ideal.absNorm (Ideal.span {p})) a X 1)^r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrn : r≤n := by simp only [Finset.mem_range] at hr; omega
    have hn : n+1=r+1+(n-r) := by omega
    rw [hn,markedTerm_even_bulk p hp hg hc,
      markedTerm_squarefree_bulk p hp hg hc]
    simp only [one_pow]
    ring
  rw [hs,←Finset.mul_sum,pow_succ]
  ring

/-- These rows are literally sourcePrincipalTerm at cube coordinate zero;
there is no substituted random coefficient or discarded native phase. -/
def positiveSourceFrequency (eta a s w : ℂ) (n : ℕ) : ℂ :=
  sourcePrincipalTerm p hp hg eta a s w 0 1 (2*(n+1)) 0 (n+1) +
  sourcePrincipalTerm p hp hg eta a s w 0 0 (2*n+2) 1 (n+1) +
  ∑ r ∈ Finset.range (n+1),
    (sourcePrincipalTerm p hp hg eta a s w 0 0 (2*r+2) 0 (n+1) +
      sourcePrincipalTerm p hp hg eta a s w 0 1 (2*r) 1 (n+1))

theorem positiveSourceFrequency_eq_native (eta a s w : ℂ) (n : ℕ) :
    positiveSourceFrequency p hp hg eta a s w n =
      positiveMarkedFrequency p hp hg eta a
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) n := by
  unfold positiveSourceFrequency positiveMarkedFrequency
  rw [sourcePrincipalTerm_pos p hp hg eta a s w 0 1 (2*(n+1)) 0 (n+1) (by omega),
    sourcePrincipalTerm_pos p hp hg eta a s w 0 0 (2*n+2) 1 (n+1) (by omega)]
  simp only [coordV,mul_zero,Complex.cpow_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [sourcePrincipalTerm_pos p hp hg eta a s w 0 0 (2*r+2) 0 (n+1) (by omega),
    sourcePrincipalTerm_pos p hp hg eta a s w 0 1 (2*r) 1 (n+1) (by omega)]
  simp only [coordV,mul_zero,Complex.cpow_zero]

include hc in
/-- The actual ordinary target channel at frequency zero is unchanged by
every frequency-order divisibility restriction. -/
theorem actual_zero_frequency_target (eta a s w z : ℂ) :
    sourcePrincipalTerm p hp hg eta a s w z 1 0 0 0 =
      -eta*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)) := by
  rw [sourcePrincipalTerm_pos p hp hg eta a s w z 1 0 0 0 (by norm_num)]
  simpa only [Nat.mul_zero,pow_zero,one_mul] using
    markedTerm_squarefree_boundary p hp hg hc eta a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
      (coordV (Ideal.absNorm (Ideal.span {p})) z) 0

/-- Grouping `ell*n` consecutive genuine local cube-ratio powers into
blocks of size ell is exact, including the confluent ratio T=1. -/
theorem geometric_block (T : ℂ) (ell n : ℕ) :
    (∑ r ∈ Finset.range (ell*n),T^r) =
      (∑ r ∈ Finset.range ell,T^r)*
        (∑ r ∈ Finset.range n,(T^ell)^r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih,Finset.sum_range_succ]
    have hs : (∑ r ∈ Finset.range ell,T^(ell*n+r)) =
        (T^ell)^n*(∑ r ∈ Finset.range ell,T^r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [pow_add,pow_mul]
    rw [hs]
    ring

/-- The native density coordinate raised to ell is exactly Q^(-1) at the
new candidate density axis. This is a native coordinate identity, not a
global residue/annular-count theorem. -/
theorem native_density_ratio_norm {Q : ℝ} (hQ : 0<Q) (ell : ℕ) (hell : 0<ell) :
    ‖coordV Q ((1/(6*(ell:ℝ)):ℝ):ℂ)^ell‖=Q^(-1:ℝ) := by
  have hellR : (ell:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hell
  rw [norm_pow,coordV_norm Q hQ]
  simp only [Complex.ofReal_re]
  rw [←Real.rpow_natCast,←Real.rpow_mul hQ.le]
  congr 1
  field_simp

/-- The actual native angular ratio at that same density axis has the
coupled exponent 4ell-6ell*Re(s)-1. Its actual phase is not replaced. -/
theorem actual_angular_ratio_norm_le {Q : ℝ} (hQ : 0<Q)
    (eta : OAI.SevenEighths.HeckeFamily.Character) (v : O) (s : ℂ)
    (ell : ℕ) (hell : 0<ell) :
    ‖coordR Q (actualAPhase eta v) s ((1/(6*(ell:ℝ)):ℝ):ℂ)^ell‖ ≤
      Q^(4*(ell:ℝ)-6*(ell:ℝ)*s.re-1) := by
  have hellR : (ell:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hell
  rw [norm_pow]
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (coordR_norm_le Q hQ (actualAPhase eta v) s
      ((1/(6*(ell:ℝ)):ℝ):ℂ) (actualAPhase_norm_le_one eta v)) ell
  simp only [Complex.ofReal_re] at h
  apply h.trans_eq
  rw [←Real.rpow_natCast,←Real.rpow_mul hQ.le]
  congr 1
  field_simp

/-- The exact density-pole frequency ratio after keeping only multiples
of ell. Actual phases are retained; only the real exponent is displayed. -/
def restrictedAngularArgument (ell : ℝ) (sigma : ℝ) : ℝ :=
  6*ell*sigma+1-4*ell

theorem restrictedAngular_euler_gate {ell sigma : ℝ} (hell : 0<ell) :
    1<restrictedAngularArgument ell sigma ↔ 2/3<sigma := by
  unfold restrictedAngularArgument
  constructor <;> intro h <;> nlinarith

/-- A local geometric-series test is weaker than the GLOBAL angular
Euler test, but it worsens as the frequency subset gets thinner. -/
theorem restricted_local_ratio_gate {ell sigma : ℝ} (hell : 0<ell) :
    4*ell-6*ell*sigma-1<0 ↔ (4*ell-1)/(6*ell)<sigma := by
  rw [div_lt_iff₀ (by positivity : 0<6*ell)]
  constructor <;> intro h <;> linarith

theorem square_frequency_local_gate {sigma : ℝ} :
    8-12*sigma-1<0 ↔ 7/12<sigma := by
  constructor <;> intro h <;> linarith

theorem higher_frequency_local_threshold {ell : ℝ} (hell : 1<ell) :
    1/2<(4*ell-1)/(6*ell) ∧ (4*ell-1)/(6*ell)<2/3 := by
  have hpos : 0<6*ell := by positivity
  constructor
  · rw [lt_div_iff₀ hpos]
    linarith
  · rw [div_lt_iff₀ hpos]
    linarith

end OpenAIReview.HigherSixthFrequency

#lint+ in OpenAIReview.HigherSixthFrequency

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
  unless declarations>0 do throwError "Empty higher-sixth source audit."
  logInfo m!"Higher-sixth source audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/arithmetic-operator-higher-sixth-source/axioms.json"
    (Json.mkObj [("scope",toJson "native finite positive-frequency row join and exact density/angular co-movement; no restricted global source continuation or independent arithmetic estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
