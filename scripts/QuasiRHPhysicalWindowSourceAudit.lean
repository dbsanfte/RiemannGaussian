/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.PrincipalNormalizer
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Physical-window annihilation also deletes the principal source

For an arbitrary finite signed family of the actual physical windows, its
Mellin factor on the theta hyperplane is analytic for `0 < re z`. Vanishing
on the entire actual central vertical line therefore forces its value at
the source intersection `(w,z)=(1,1/6)` to vanish. The original principal
residue is precisely that value times the fixed nonzero residue factor.

This deletes the named original principal double-residue constant. It does not
prove source absence in the whole coded principal pool: single-residue/exterior
terms still need their original accounting. Nor does it rule out cancellation
against a particular arithmetic theta covariance or quantitative smallness
on a moving spectral range. No theta/source identification is assumed.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter Complex
namespace OpenAIReview.PhysicalWindowSource
open OAI OAI.SevenEighths OAI.SevenEighths.PrincipalMellinResidues
local notation "O" => OAI.SevenEighths.HeckeFamily.O

/-- The literal window factors restricted to the physical theta hyperplane. -/
def windowProfile {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (W0 W1 : ι → SchwartzMap ℝ ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ S, c i * mellin (EisensteinSchwartzPoisson.paperRadialFourier (W0 i)) z *
    mellin (W1 i) ((7/6 : ℂ) - z)

/-- No genuine divisor, calibration, or source factor has been changed. -/
theorem source_sum_eq_profile {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (W0 W1 : ι → SchwartzMap ℝ ℂ) (M : Ideal O) [NeZero M] :
    (∑ i ∈ S, c i * sourceResidueConstant (W0 i) (W1 i) M) =
      windowProfile S c W0 W1 (1/6) * fixedPrincipalResidue M ^ 2 / 6 := by
  simp only [windowProfile, sourceResidueConstant]
  norm_num only [show (7/6 : ℂ) - 1/6 = 1 by norm_num]
  simp only [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Compact positive physical support gives an entire second-window Mellin factor. -/
theorem windowProfile_analytic {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (W0 W1 : ι → SchwartzMap ℝ ℂ) (a b : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i)
    (hsupp : ∀ i ∈ S, Function.support (W1 i) ⊆ Icc (a i) (b i)) :
    AnalyticOnNhd ℂ (windowProfile S c W0 W1) {z : ℂ | 0 < z.re} := by
  intro z hz
  apply Finset.analyticAt_fun_sum
  intro i hi
  have hm := CubicReflectionKernel.compact_source_mellin_differentiable
    (W1 i) (a i) (b i) (ha i hi) (hsupp i hi) ((W1 i).smooth ⊤)
  have hcomp : AnalyticAt ℂ (fun z : ℂ => mellin (W1 i) ((7/6 : ℂ) - z)) z :=
    (hm.comp ((differentiable_const (7/6 : ℂ)).sub differentiable_id)).analyticAt z
  exact (analyticAt_const.mul
    (ProbeRadialMellin.radial_mellin_analytic (W0 i) z hz)).mul hcomp

private theorem central_line_tendsto_punctured :
    Tendsto (fun t : ℝ => (17/50 : ℂ) + t * I)
      (𝓝[≠] 0) (𝓝[≠] (17/50 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun t : ℝ => (17/50 : ℂ) + t * I) := by fun_prop
    simpa using (h.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    exact ht hi

/-- Exact annihilation on even a finite open theta segment deletes the source. -/
theorem source_sum_zero_of_segment_annihilation {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (W0 W1 : ι → SchwartzMap ℝ ℂ)
    (a b : ι → ℝ) (ha : ∀ i ∈ S, 0 < a i)
    (hsupp : ∀ i ∈ S, Function.support (W1 i) ⊆ Icc (a i) (b i))
    (M : Ideal O) [NeZero M] (H : ℝ) (hH : 0 < H)
    (hkill : ∀ t ∈ Ioo (-H) H,
      windowProfile S c W0 W1 ((17/50 : ℂ) + t * I) = 0) :
    (∑ i ∈ S, c i * sourceResidueConstant (W0 i) (W1 i) M) = 0 := by
  have han := windowProfile_analytic S c W0 W1 a b ha hsupp
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      windowProfile S c W0 W1 ((17/50 : ℂ) + t * I) = 0 := by
    filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hH) hH] with t ht
    exact hkill t ht
  have heq : EqOn (windowProfile S c W0 W1) 0 {z : ℂ | 0 < z.re} := by
    apply han.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_halfSpace_re_gt 0).isPreconnected (z₀ := (17/50 : ℂ)) (by norm_num)
    exact central_line_tendsto_punctured.frequently
      ((hnear.filter_mono nhdsWithin_le_nhds).frequently)
  rw [source_sum_eq_profile, heq (by norm_num : (1/6 : ℂ) ∈ {z : ℂ | 0 < z.re})]
  simp

/-- Cancelling the whole actual theta line cancels the original source as well. -/
theorem source_sum_zero_of_vertical_annihilation {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (W0 W1 : ι → SchwartzMap ℝ ℂ)
    (a b : ι → ℝ) (ha : ∀ i ∈ S, 0 < a i)
    (hsupp : ∀ i ∈ S, Function.support (W1 i) ⊆ Icc (a i) (b i))
    (M : Ideal O) [NeZero M]
    (hkill : ∀ t : ℝ, windowProfile S c W0 W1 ((17/50 : ℂ) + t * I) = 0) :
    (∑ i ∈ S, c i * sourceResidueConstant (W0 i) (W1 i) M) = 0 :=
  source_sum_zero_of_segment_annihilation S c W0 W1 a b ha hsupp M 1
    (by norm_num) (fun t _ => hkill t)

/-- Every source-preserving finite physical-window code leaves some theta-line value. -/
theorem exists_nonzero_theta_window_of_source_ne_zero {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (W0 W1 : ι → SchwartzMap ℝ ℂ)
    (a b : ι → ℝ) (ha : ∀ i ∈ S, 0 < a i)
    (hsupp : ∀ i ∈ S, Function.support (W1 i) ⊆ Icc (a i) (b i))
    (M : Ideal O) [NeZero M]
    (hsource : (∑ i ∈ S, c i * sourceResidueConstant (W0 i) (W1 i) M) ≠ 0) :
    ∃ t : ℝ, windowProfile S c W0 W1 ((17/50 : ℂ) + t * I) ≠ 0 := by
  by_contra h
  push Not at h
  exact hsource (source_sum_zero_of_vertical_annihilation S c W0 W1 a b ha hsupp M h)

end OpenAIReview.PhysicalWindowSource
#lint+ in OpenAIReview.PhysicalWindowSource

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
  unless declarations>0 do throwError "Empty physical-window source audit."
  logInfo m!"Physical-window source audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-physical-window-source-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-physical-window-source-gate/axioms.json"
    (Json.mkObj [("scope",toJson "Arbitrary finite signed actual physical-window family: exact theta-segment annihilation forces original principal double-residue constant to vanish. No whole-pool source absence, arithmetic covariance or quantitative smallness no-go."),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingHelpers",toJson theorems),("details",Json.arr details)]).pretty
