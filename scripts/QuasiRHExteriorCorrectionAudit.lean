/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHExteriorRegionAudit
import OAI.NumberTheory.DirichletL.Detector.SourceExclusions
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# The unchanged global correction on the actual exterior contour region

This extends the correction's own normal-product/analytic API. It neither
changes the literal carrier nor asserts the remaining physical Gauss-series
estimate or the complete source-contour transfer below the imported region.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
noncomputable section
open scoped Classical BigOperators Topology
namespace OpenAIReview.ExteriorCorrection
open OAI ActualEisensteinCubic SevenEighths SevenEighths.ProbeEuler
  SevenEighths.ProbePhysical CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- Summable envelope for the actual outer-contour prime correction. -/
def exteriorPrimeDefectBound (P : PrimeIdeal) : ℝ :=
  240*(Ideal.absNorm P.val:ℝ)^(-(73/50:ℝ))

/-- Every actual prime-ideal defect allowance is nonnegative. -/
lemma exteriorPrimeDefectBound_nonneg (P : PrimeIdeal) : 0≤exteriorPrimeDefectBound P := by
  unfold exteriorPrimeDefectBound
  positivity

/-- The new exponent is summable over the actual ideal primes unconditionally. -/
lemma exteriorPrimeDefectBound_summable : Summable exteriorPrimeDefectBound := by
  have h := (CubicEisenstein.fullIdealWeight_summable_norm ((73/50:ℝ):ℂ) (by norm_num)).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight ((73/50:ℝ):ℂ) P.val‖=exteriorPrimeDefectBound P
  unfold exteriorPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

/-- Fixed exclusions controlling the unchanged product on the larger contour region. -/
structure ExteriorTail (S : Finset Id) : Prop where
  norm_four : ∀P : PrimeIdeal,P.val∉S → 4≤Ideal.absNorm P.val
  small : (∑' P : {P : PrimeIdeal // P.val∉S},exteriorPrimeDefectBound P.val)≤1/6

/-- The exterior envelope remains summable after fixed prime exclusions. -/
lemma ExteriorTail.summable {S : Finset Id} (_h : ExteriorTail S) :
    Summable (fun P : {P : PrimeIdeal // P.val∉S}=>exteriorPrimeDefectBound P.val) :=
  exteriorPrimeDefectBound_summable.subtype _

/-- The fixed tail controls every individual prime correction. -/
lemma ExteriorTail.half {S : Finset Id} (h : ExteriorTail S)
    (P : {P : PrimeIdeal // P.val∉S}) : exteriorPrimeDefectBound P.val≤1/2 := by
  have hh := Summable.le_tsum h.summable P (fun Q _=>exteriorPrimeDefectBound_nonneg Q.val)
  linarith [h.small]

/-- Uniform enlarged-region bound for the native ideal factor. -/
lemma idealClosedCorrection_bound (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 3/4≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤exteriorPrimeDefectBound P := by
  apply OpenAIReview.ExteriorRegion.contour_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

/-- The unchanged full correction stays within one half of one on the closed box. -/
theorem globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ExteriorTail S) (x w z : ℂ)
    (hx : 3/4≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=>idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

/-- The actual full product converges in the enlarged contour region. -/
lemma globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ExteriorTail S) (x w z : ℂ)
    (hx : 3/4≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>exteriorPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

/-- The same global correction is analytic in the source variable past the old boundary. -/
theorem globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ExteriorTail S) (w z : ℂ) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x w z) {x : ℂ|3/4<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply OpenAIReview.ExteriorRegion.contour_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

/-- Analyticity in the density variable on a neighborhood of the actual exterior line. -/
theorem globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ExteriorTail S) (x z : ℂ) (hx : 3/4≤x.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun w=>globalClosedCorrection η S x w z) {w : ℂ|9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply OpenAIReview.ExteriorRegion.contour_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

/-- Analyticity in the Mellin variable on a neighborhood of the actual exterior line. -/
theorem globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ExteriorTail S) (x w : ℂ) (hx : 3/4≤x.re) (hw : 9/10≤w.re) :
    AnalyticOnNhd ℂ (fun z=>globalClosedCorrection η S x w z) {z : ℂ|4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply OpenAIReview.ExteriorRegion.contour_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

/-- One finite exclusion cutoff works for all native characters and all heights. -/
theorem exists_uniform_global_cutoff :
    ∃N : ℕ,4≤N ∧ ∀S : Finset Id,
      (∀P : PrimeIdeal,Ideal.absNorm P.val≤N → P.val∈S) → ExteriorTail S := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero exteriorPrimeDefectBound)).2 (1/6) (by norm_num)
  obtain ⟨F,hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P=>Ideal.absNorm P.val))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS
  let T := {P : PrimeIdeal // P.val∉S}
  have hnot (P : T) : P.val∉F := by
    intro hm
    exact P.property (hS P.val ((Finset.le_sup (f:=fun P : PrimeIdeal=>Ideal.absNorm P.val) hm).trans (le_max_right _ _)))
  let inc : T→{P : PrimeIdeal // P∉F} := fun P=>⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun P : {P : PrimeIdeal // P∉F}=>P.val) h)
  constructor
  · intro P hP
    have hn : ¬Ideal.absNorm P.val≤N := fun hn=>hP (hS P hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _=>exteriorPrimeDefectBound_nonneg P.val) (fun _=>le_rfl)
      (exteriorPrimeDefectBound_summable.subtype _) (exteriorPrimeDefectBound_summable.subtype _)

/-- Enlarge any prescribed exclusions while retaining the new global tail bound. -/
theorem exists_global_correction (S₀ : Finset Id) :
    ∃S : Finset Id,S₀⊆S ∧ ExteriorTail S := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_cutoff
  refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,hcut _ ?_⟩
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

/-- The wider-region envelope also dominates the old source-exclusion envelope. -/
theorem old_defect_le_exterior (P : PrimeIdeal) :
    ProbePhysical.globalPrimeDefectBound P ≤ exteriorPrimeDefectBound P := by
  unfold ProbePhysical.globalPrimeDefectBound exteriorPrimeDefectBound
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le ?_ (by norm_num)
  have hn := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  exact_mod_cast hn

/-- New exclusions preserve the repository's original correction-tail obligations. -/
theorem ExteriorTail.toCorrectionTail {S : Finset Id} (h : ExteriorTail S) :
    ProbePhysical.CorrectionTail S := by
  refine ⟨h.norm_four, le_trans ?_ h.small⟩
  exact Summable.tsum_le_tsum (fun P => old_defect_le_exterior P.val)
    (ProbePhysical.globalPrimeDefectBound_summable.subtype _) h.summable

/-- Enlarge prescribed genuine-prime exclusions without losing original source data. -/
theorem exists_exterior_source_exclusions (S₀ : Finset Id)
    (hp : ∀ P ∈ S₀, Prime P) (hbad : fixedBadPrimes ⊆ S₀) :
    ∃ S : Finset Id, S₀ ⊆ S ∧ SourceExclusions S ∧ ExteriorTail S := by
  obtain ⟨N, _hN, hcut⟩ := exists_uniform_global_cutoff
  let S := S₀ ∪ smallPrimeSet N
  have ht : ExteriorTail S := hcut S (by
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP))
  refine ⟨S, Finset.subset_union_left, ?_, ht⟩
  refine ⟨?_, hbad.trans Finset.subset_union_left, ht.toCorrectionTail⟩
  intro P hP
  rcases Finset.mem_union.mp hP with hP | hP
  · exact hp P hP
  · exact (Finset.mem_filter.mp hP).2

/-- The unchanged global correction cannot cancel a source anywhere in the closed box. -/
theorem globalClosedCorrection_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ExteriorTail S) (x w z : ℂ)
    (hx : 3/4 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    globalClosedCorrection η S x w z ≠ 0 :=
  factor_ne_zero_of_defect _ (globalClosedCorrection_bound η S hS x w z hx hw hz)

/-- Uniform reciprocal bound for the actual global correction on that same region. -/
theorem globalClosedCorrection_inverse_bound (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ExteriorTail S) (x w z : ℂ)
    (hx : 3/4 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖(globalClosedCorrection η S x w z)⁻¹‖ ≤ 2 := by
  have hb := globalClosedCorrection_bound η S hS x w z hx hw hz
  have hn := norm_sub_norm_le (1 : ℂ) (globalClosedCorrection η S x w z)
  rw [norm_one, norm_sub_rev] at hn
  have hpos : 0 < ‖globalClosedCorrection η S x w z‖ := by linarith
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ hpos).mpr (by linarith)

/-- Each literal prime factor is bounded away from zero in the enlarged contour box. -/
theorem idealClosedCorrection_lower (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ExteriorTail S) (P : PrimeIdeal) (hP : P.val ∉ S)
    (x w z : ℂ) (hx : 3/4 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    1/2 ≤ ‖idealClosedCorrection η P x w z‖ := by
  have hb := (idealClosedCorrection_bound η P (hS.norm_four P hP) x w z hx hw hz).trans
    (hS.half ⟨P,hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

/-- The first actual exterior line lies inside the proved analytic w domain. -/
theorem exterior_w_analyticAt (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ExteriorTail S) (x w z : ℂ)
    (hx : 3/4 ≤ x.re) (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    AnalyticAt ℂ (fun t => globalClosedCorrection η S x t z) w :=
  globalClosedCorrection_analytic_w η S hS x z hx (by linarith) w
    (by change (9/10:ℝ) < w.re; linarith)

/-- The second actual exterior line lies inside the proved analytic z domain. -/
theorem exterior_z_analyticAt (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ExteriorTail S) (x w z : ℂ)
    (hx : 3/4 ≤ x.re) (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    AnalyticAt ℂ (fun t => globalClosedCorrection η S x w t) z :=
  globalClosedCorrection_analytic_z η S hS x w hx (by linarith) z
    (by change (4/25:ℝ) < z.re; linarith)

end OpenAIReview.ExteriorCorrection

#lint+ in OpenAIReview.ExteriorCorrection

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty exterior correction audit."
  logInfo m!"Exterior correction audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-exterior-correction-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-exterior-correction-gate/axioms.json"
    (Json.mkObj [("scope",toJson "unchanged global correction normal product, nonvanishing and separate analyticity on x>=3/4,w>=9/10,z>=4/25 after compatible fixed exclusions; no full physical/source transfer or new zero-free result"),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
