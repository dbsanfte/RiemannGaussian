/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms
/-!
# Actual source Euler correction below the imported 7/8 cutoff

At the literal source coordinates w=1,z=1/6 the correction has normal
convergence on every closed half-plane Re(s)>=a>2/3, after increasing the
fixed exclusion set. This is a source-applicability theorem, not an
arithmetic bound on the probe or a new zero-free region. Every actual
prime-ideal factor and its angular/character phase is retained.
-/
open scoped Classical BigOperators Topology
open Filter Asymptotics
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
namespace OpenAIReview.SourceHalfplane
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeEuler
open OAI.SevenEighths.ProbePhysical OAI.ActualEisensteinCubic
open OAI.CompletedGauss

/-- Exact summable exponent supplied by the three surviving local errors. -/
def decayExponent (a:ℝ) : ℝ := min (6*a-3) (min (a+1) 2)
/-- The sextic geometric denominator controls this error exponent. -/
theorem decay_le_six (a:ℝ) : decayExponent a≤6*a-3 := min_le_left _ _
/-- The mixed prime-density term controls this error exponent. -/
theorem decay_le_one_add (a:ℝ) : decayExponent a≤a+1 :=
  (min_le_right _ _).trans (min_le_left _ _)
/-- The density-square term controls this error exponent. -/
theorem decay_le_two (a:ℝ) : decayExponent a≤2 :=
  (min_le_right _ _).trans (min_le_right _ _)
/-- All three literal error exponents are summable strictly right of2/3. -/
theorem one_lt_decay {a:ℝ} (ha:2/3<a) : 1<decayExponent a := by
  unfold decayExponent
  exact lt_min (by linarith) (lt_min (by linarith) (by norm_num))

/-- Quantitative bound for the actual continued local factor at source coordinates. -/
theorem source_local_bound (a Q:ℝ) (A eta x:ℂ) (ha:2/3<a)
    (hQ:4≤Q) (hA:‖A‖≤1) (heta:‖eta‖≤1) (hx:a≤x.re) :
    ‖unramifiedClosed Q A eta 1 x 1 (1/6)-1‖≤240*Q^(-decayExponent a) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q (1/6)
  let R := coordR Q A x (1/6)
  let W := coordW Q 1 1
  let D := coordD Q eta 1 x
  let K := coordK Q eta x 1
  have hV : ‖V‖ ≤ Q ^ ((-1:ℝ)) := by
    rw [show V = coordV Q (1/6) from rfl, coordV_norm Q hQ0]
    norm_num
  have hR : ‖R‖ ≤ Q ^ ((3-6*a)) :=
    (coordR_norm_le Q hQ0 A x (1/6) hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num at *; linarith))
  have hW : ‖W‖ ≤ Q ^ ((-1:ℝ)) :=
    (coordW_norm_le Q hQ0 1 1 (by simp)).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hD : ‖D‖ ≤ Q ^ ((-a)) :=
    (coordD_norm_le Q hQ0 eta 1 x heta (by simp)).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num at *; linarith))
  have hK : ‖K‖ ≤ Q ^ ((-a)) :=
    (coordK_norm_le Q hQ1 eta x 1 heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num at *; linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by linarith))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : (-1:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ ((-decayExponent a))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith [decay_le_six a]))
  have hprod (v₁ v₂ e₁ e₂ : ℝ) (_h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂)
      (hv₁ : v₁ ≤ Q^e₁) (hv₂ : v₂ ≤ Q^e₂)
      (he : e₁+e₂ ≤ -decayExponent a) : v₁*v₂ ≤ T := by
    calc
      v₁*v₂ ≤ Q^e₁ * Q^e₂ := mul_le_mul hv₁ hv₂ h₂ (Real.rpow_nonneg hQ0.le _)
      _ = Q^(e₁+e₂) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by linarith [decay_le_one_add a])
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by linarith [decay_le_one_add a])
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by linarith [decay_le_one_add a])
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by linarith [decay_le_two a])
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith

/-- The same literal local correction is analytic throughout the wider half-plane. -/
theorem source_local_analytic (a Q:ℝ) (A eta:ℂ) (ha:2/3<a)
    (hQ:4≤Q) (hA:‖A‖≤1) (heta:‖eta‖≤1) :
    AnalyticOnNhd ℂ (fun s=>unramifiedClosed Q A eta 1 s 1 (1/6))
      {s:ℂ | a<s.re} := by
  have hQ0:0<Q := by linarith
  have hv:1-coordV Q (1/6)≠0 := by
    apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    norm_num
  have hdif:DifferentiableOn ℂ (fun s=>unramifiedClosed Q A eta 1 s 1 (1/6))
      {s:ℂ | a<s.re} := by
    intro s hs
    apply (unramifiedClosed_differentiableAt Q hQ0 A eta 1 s 1 (1/6) ?_ hv ?_).differentiableWithinAt
    · apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
      apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
      apply rpow_le_half Q _ hQ
      norm_num
      change a<s.re at hs
      linarith
    · apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
      apply (coordD_norm_le Q hQ0 eta 1 s heta (by simp)).trans
      apply rpow_le_half Q _ hQ
      change a<s.re at hs
      linarith
  exact hdif.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- A summable uniform envelope for the genuine prime-ideal factors. -/
def sourceDefectBound (a:ℝ) (P:PrimeIdeal) : ℝ :=
  240*(Ideal.absNorm P.val:ℝ)^(-decayExponent a)

/-- Positivity of the literal prime-ideal envelope. -/
theorem sourceDefectBound_nonneg (a:ℝ) (P:PrimeIdeal) :
    0≤sourceDefectBound a P := by
  unfold sourceDefectBound
  positivity

/-- The wider local envelope sums over the actual prime ideals. -/
theorem sourceDefectBound_summable {a:ℝ} (ha:2/3<a) :
    Summable (sourceDefectBound a) := by
  have h := (CubicEisenstein.fullIdealWeight_summable_norm ((decayExponent a:ℝ):ℂ)
    (by simpa using one_lt_decay ha)).comp_injective
      (Subtype.val_injective : Function.Injective (fun P:PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight ((decayExponent a:ℝ):ℂ) P.val‖=
    sourceDefectBound a P
  unfold sourceDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

/-- This envelope bounds the repository's actual angular and character local factor. -/
theorem ideal_source_bound {a:ℝ} (ha:2/3<a) (eta:HeckeFamily.Character)
    (P:PrimeIdeal) (hP:4≤Ideal.absNorm P.val) (s:ℂ) (hs:a≤s.re) :
    ‖idealClosedCorrection eta P s 1 (1/6)-1‖≤sourceDefectBound a P := by
  exact source_local_bound a _ _ _ s ha (by exact_mod_cast hP)
    (actualAPhase_norm_le_one eta _) (HeckeFamily.idealCoeff_norm_le_one eta _) hs

/-- Analyticity is for the same genuine ideal local correction, not a model factor. -/
theorem ideal_source_analytic {a:ℝ} (ha:2/3<a) (eta:HeckeFamily.Character)
    (P:PrimeIdeal) (hP:4≤Ideal.absNorm P.val) :
    AnalyticOnNhd ℂ (fun s=>idealClosedCorrection eta P s 1 (1/6))
      {s:ℂ | a<s.re} :=
  source_local_analytic a _ _ _ ha (by exact_mod_cast hP)
    (actualAPhase_norm_le_one eta _) (HeckeFamily.idealCoeff_norm_le_one eta _)

/-- Enlarging fixed exclusions makes the actual source correction regular and
nonzero on any prescribed closed half-plane strictly right of2/3. The cutoff
may depend on that half-plane; no new probe estimate is asserted. -/
theorem exists_uniform_source_cutoff {a:ℝ} (ha:2/3<a) :
    ∃N:ℕ,4≤N ∧ ∀S:Finset (Ideal OAI.ActualEisensteinCubic.O),
      (∀P:PrimeIdeal,Ideal.absNorm P.val≤N→P.val∈S)→
      ∀eta:HeckeFamily.Character,
        AnalyticOnNhd ℂ (PrincipalSignalComparison.sourceCorrection eta S)
          {s:ℂ | a<s.re} ∧
        ∀s:ℂ,a≤s.re→‖PrincipalSignalComparison.sourceCorrection eta S s-1‖≤1/2 := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero (sourceDefectBound a))).2
    (1/6) (by norm_num)
  obtain ⟨F,hF⟩ := ht.exists
  let N:=max 4 (F.sup (fun P=>Ideal.absNorm P.val))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS eta
  let T:={P:PrimeIdeal // P.val∉S}
  have hnot (P:T):P.val∉F := by
    intro hm
    exact P.property (hS P.val
      ((Finset.le_sup (f:=fun P:PrimeIdeal=>Ideal.absNorm P.val) hm).trans (le_max_right _ _)))
  let inc:T→{P:PrimeIdeal // P∉F}:=fun P=>⟨P.val,hnot P⟩
  have hi:Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun P:{P:PrimeIdeal // P∉F}=>P.val) h)
  have hnorm (P:T):4≤Ideal.absNorm P.val.val := by
    have hn:¬Ideal.absNorm P.val.val≤N:=fun hn=>P.property (hS P.val hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  have hsum:Summable (fun P:T=>sourceDefectBound a P.val) :=
    (sourceDefectBound_summable ha).subtype _
  have hsmall:(∑' P:T,sourceDefectBound a P.val)≤1/6 := by
    apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _=>sourceDefectBound_nonneg a P.val) (fun _=>le_rfl)
      hsum ((sourceDefectBound_summable ha).subtype _)
  have hhalf (P:T):sourceDefectBound a P.val≤1/2 := by
    have hterm:=Summable.le_tsum hsum P (fun Q _=>sourceDefectBound_nonneg a Q.val)
    linarith
  constructor
  · exact normalProduct_analytic (fun (P:T) (s:ℂ)=>idealClosedCorrection eta P.val s 1 (1/6))
      (fun P:T=>sourceDefectBound a P.val) _ (isOpen_lt continuous_const Complex.continuous_re)
      hsum (fun P=>ideal_source_analytic ha eta P.val (hnorm P))
      (fun P s hs=>ideal_source_bound ha eta P.val (hnorm P) s hs.le) hhalf
  · intro s hs
    exact product_defect_le (fun P:T=>idealClosedCorrection eta P.val s 1 (1/6))
      (fun P:T=>sourceDefectBound a P.val) hsum
      (fun P=>ideal_source_bound ha eta P.val (hnorm P) s hs) hhalf hsmall

/-- Every such fixed enlarged cutoff preserves the reciprocal-L source:
the correction cannot cancel a zero through vanishing in the wider region. -/
theorem exists_source_nonvanishing_cutoff {a:ℝ} (ha:2/3<a) :
    ∃N:ℕ,4≤N ∧ ∀S:Finset (Ideal OAI.ActualEisensteinCubic.O),
      (∀P:PrimeIdeal,Ideal.absNorm P.val≤N→P.val∈S)→
      ∀eta:HeckeFamily.Character,∀s:ℂ,a≤s.re→
        PrincipalSignalComparison.sourceCorrection eta S s≠0 := by
  obtain ⟨N,hN,h⟩:=exists_uniform_source_cutoff ha
  refine ⟨N,hN,?_⟩
  intro S hS eta s hs
  exact factor_ne_zero_of_defect _ ((h S hS eta).2 s hs)

/-- Exact rational source factor before norms; the sextic denominator is retained. -/
theorem principal_rational (v R D:ℂ) (hv:1-v≠0) (hR:1-R≠0) (hD:1-D≠0) :
    ProbeLocal.continuedCorrection v v D
      (markedFactor R v v ((1-v)*D) (-D+v*R) 1)=
      (1-v^2)*(1-(1-v)*D-v*R)/((1-R)*(1-D)) := by
  unfold ProbeLocal.continuedCorrection markedFactor
  field_simp
  ring

/-- Removing the actual sextic denominator exposes the exact smaller error;
it does not assert that the corresponding auxiliary L-factor is nonzero. -/
theorem principal_extracted_defect (v R D:ℂ)
    (hv:1-v≠0) (hR:1-R≠0) (hD:1-D≠0) :
    (1-R)*ProbeLocal.continuedCorrection v v D
      (markedFactor R v v ((1-v)*D) (-D+v*R) 1)-1=
      (-v^2+(v+v^2-v^3)*D-v*(1-v^2)*R)/(1-D) := by
  rw [principal_rational v R D hv hR hD]
  field_simp
  ring

/-- The physical source fixes both elementary density coordinates to the inverse norm. -/
theorem source_density_coordinates (Q:ℝ) :
    coordV Q (1/6)=(Q:ℂ)⁻¹ ∧ coordW Q 1 1=(Q:ℂ)⁻¹ := by
  constructor
  · unfold coordV
    norm_num [Complex.cpow_neg_one]
  · simp [coordW,Complex.cpow_neg_one]

/-- The actual marked coordinate and reciprocal coordinate share the same phase. -/
theorem source_mark_coordinate {Q:ℝ} (hQ:0<Q) (eta s:ℂ) :
    coordK Q eta s 1=(1-(Q:ℂ)⁻¹)*coordD Q eta 1 s := by
  have hn:(Q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold coordK coordD
  rw [Complex.cpow_sub (-s) 1 hn,Complex.cpow_one]
  simp only [star_one,mul_one]
  field_simp

/-- Exact rational factorization of the native source correction itself. -/
theorem source_rational {Q:ℝ} (hQ:0<Q) (A eta s:ℂ)
    (hv:1-(Q:ℂ)⁻¹≠0) (hr:1-coordR Q A s (1/6)≠0)
    (hd:1-coordD Q eta 1 s≠0) :
    unramifiedClosed Q A eta 1 s 1 (1/6)=
      (1-((Q:ℂ)⁻¹)^2)*
        (1-(1-(Q:ℂ)⁻¹)*coordD Q eta 1 s-(Q:ℂ)⁻¹*coordR Q A s (1/6))/
          ((1-coordR Q A s (1/6))*(1-coordD Q eta 1 s)) := by
  unfold unramifiedClosed
  dsimp only
  rw [(source_density_coordinates Q).1,(source_density_coordinates Q).2,
    source_mark_coordinate hQ]
  exact principal_rational _ _ _ hv hr hd

end OpenAIReview.SourceHalfplane

#lint+ in OpenAIReview.SourceHalfplane

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
  unless declarations>0 do throwError "Empty source-half-plane audit."
  logInfo m!"Source half-plane audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-source-halfplane-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-source-halfplane-gate/axioms.json"
    (Json.mkObj [("scope",toJson "exact native source rational factor and unchanged global correction analytic/nonzero for any fixed half-plane a>2/3 after larger fixed exclusions; no extension of full probe/source contour or new zero-free estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr details)]).pretty
