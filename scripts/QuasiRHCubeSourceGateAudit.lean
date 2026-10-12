/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHLowerStripSlotAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Source gate of the actual cube/prime-mark commutator

Multiplying the completed index by `P^3` changes the prime mark `P ∣ A`
by its complement.  This leaf follows that EXACT local support through the
native all-power source series and its continued local Euler formula.
The result is a finite scalar multiplier of the existing source, not an
independent arithmetic estimate, a new contour, or a zero-free theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical Topology
namespace OpenAIReview.CubeSourceGate
open OAI OAI.SevenEighths OAI.CompletedGauss
open ProbePhysical ProbeEuler ProbeLocal ProbeRow PrincipalSlotEstimate HeckeFamily
open OpenAIReview.LowerStripSlot

local notation "O" => OAI.ActualEisensteinCubic.O

/-- The literal normalized prime-mark complement of the native local Euler
factor.  The actual sixth-angular and ideal-character phases remain inside. -/
def cubeMaskLocalRatio (η : Character) (P : ProbePhysical.PrimeIdeal)
    (s w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  let M := idealMarkedClosed η P s w z
  (localFactor (coordV Q z) (coordW Q 1 w) M-M)/
    localFactor (coordV Q z) (coordW Q 1 w) M

theorem cube_support_complement (e l : ℕ) :
    (1:ℂ)-(if e+3*l≠0 then 1 else 0) =
      if e=0 ∧ l=0 then 1 else 0 := by
  by_cases ht : e+3*l=0
  · have he : e=0 := by omega
    have hl : l=0 := by omega
    simp [he,hl]
  · have hn : ¬(e=0 ∧ l=0) := by omega
    simp [hn]

/-- Each actual local coefficient, including every Gaussian/character phase,
survives the commutator only at completed cube index zero. -/
theorem actual_source_complement_term (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda∉Ideal.span {p})
    (η : Character) (s w z : ℂ) (e l k m : ℕ) :
    ((1:ℂ)-(if e+3*l≠0 then 1 else 0))*
      sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) s w z e l k m =
    if e=0 ∧ l=0 then
      zeroIndexTerm p (ActualEisensteinCubic.canonicalSextic (Ideal.span {p}) hg)
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) k m
    else 0 := by
  rw [cube_support_complement]
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩
    rw [one_mul,sourcePrincipalTerm_zero]
  · rw [zero_mul]

/-- Summing the surviving native index-zero channels keeps the ordinary
two density axes; it does not supply an arithmetic cancellation inequality. -/
theorem actual_zero_index_source (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda∉Ideal.span {p})
    (η : Character) (s w z : ℂ)
    (hW : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)‖<1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1) :
    (∑' k,∑' m,sourcePrincipalTerm p hp hg (targetMonoid η p)
      (actualACube η p) s w z 0 0 k m) =
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)/
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) := by
  simp only [sourcePrincipalTerm_zero]
  exact zeroIndexSeries_eq p hp _ _ _ hW hV

/-- Exact native full-minus-marked source series on its actual convergent
Euler region.  No right-half-plane continuation is inferred. -/
theorem actual_full_sub_marked_source (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (η : Character) (s w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) s z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1) :
    sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) s w z-
      principalMarkedSeries p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) =
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)/
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) := by
  rw [sourcePrincipalSeries_eq p hp hg hc _ _ s w z hV hR hW]
  unfold principalFullSeries
  simp only [Complex.ofReal_natCast]
  ring

theorem local_factor_complement (V W M : ℂ) :
    localFactor V W M-M = 1/(1-V)+W/(1-W) := by
  unfold localFactor
  ring

/-- Native prime-ideal series and closed formulas agree in the documented
Euler half-plane, including every squarefree/cube valuation. -/
theorem actual_ideal_complement_eq (η : Character) (P : ProbePhysical.PrimeIdeal)
    (hP : CanonicalQuadraticSieve.Supported P.val) (s w z : ℂ)
    (hs : 3/2<s.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    idealHighLocalFactor η P.val s w z-idealMarkedLocalFactor η P s w z =
      1/(1-coordV (Ideal.absNorm P.val) z)+
        coordW (Ideal.absNorm P.val) 1 w/(1-coordW (Ideal.absNorm P.val) 1 w) := by
  rw [idealHighLocalFactor_eq_raw η P hP s w z hs hw hz,
    idealMarkedLocalFactor_rational η P hP s w z hs hz]
  exact local_factor_complement _ _ _

theorem actual_ideal_ratio_eq_closed (η : Character) (P : ProbePhysical.PrimeIdeal)
    (hP : CanonicalQuadraticSieve.Supported P.val) (s w z : ℂ)
    (hs : 3/2<s.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (idealHighLocalFactor η P.val s w z-idealMarkedLocalFactor η P s w z)/
      idealHighLocalFactor η P.val s w z = cubeMaskLocalRatio η P s w z := by
  unfold cubeMaskLocalRatio
  rw [idealHighLocalFactor_eq_raw η P hP s w z hs hw hz,
    idealMarkedLocalFactor_rational η P hP s w z hs hz]

theorem marked_at_principal (η : Character) (P : ProbePhysical.PrimeIdeal) (s : ℂ) :
    idealMarkedClosed η P s 1 (1/6) =
      principalMarked (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) s := rfl

theorem local_factor_principal (t R D : ℂ) (ht : 1-t≠0) (hR : 1-R≠0) :
    localFactor t t ((1+t)*(R-D)/(1-R)) =
      (1+t)*slotDenominator t R D/((1-t)*(1-R)) := by
  unfold localFactor slotDenominator
  field_simp
  ring

theorem complement_ratio_principal (t R D : ℂ) (ht : 1-t≠0)
    (hpt : 1+t≠0) (hR : 1-R≠0) (hd : slotDenominator t R D≠0) :
    (localFactor t t ((1+t)*(R-D)/(1-R))-(1+t)*(R-D)/(1-R))/
      localFactor t t ((1+t)*(R-D)/(1-R)) = (1-R)/slotDenominator t R D := by
  rw [local_factor_complement,local_factor_principal t R D ht hR]
  field_simp

/-- The exact double-principal-axis multiplier of the actual cube/prime-mark
commutator is a FINITE local ratio, with no global zero-source inference. -/
theorem actual_cube_ratio_principal {Q : ℝ} (η : Character)
    (P : ProbePhysical.PrimeIdeal) (hQ : (Ideal.absNorm P.val:ℝ)=Q) (hq : 4≤Q)
    (s : ℂ)
    (hR : ‖coordR Q (actualAPhase η (primaryGenerator P.val)) s (1/6)‖≤1/2)
    (hD : ‖coordD Q (idealCoeff η P.val) 1 s‖≤1/4) :
    cubeMaskLocalRatio η P s 1 (1/6) =
      (1-coordR Q (actualAPhase η (primaryGenerator P.val)) s (1/6))/
        slotDenominator (Q:ℂ)⁻¹
          (coordR Q (actualAPhase η (primaryGenerator P.val)) s (1/6))
          (coordD Q (idealCoeff η P.val) 1 s) := by
  have hq0 : 0<Q := by linarith
  rcases principal_slot_guards hq (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) s hR hD with ⟨ht,hpt,hr,_,hd⟩
  unfold cubeMaskLocalRatio
  rw [marked_at_principal]
  rw [hQ]
  dsimp only
  rw [principal_V,principal_W,principal_marked_exact hq0 _ _ _ ht]
  exact complement_ratio_principal _ _ _ ht hpt hr hd

theorem complement_ratio_sub_one (t R D : ℂ) (hd : slotDenominator t R D≠0) :
    (1-R)/slotDenominator t R D-1 =
      -(1-t)*(R-D)/slotDenominator t R D := by
  field_simp
  unfold slotDenominator
  ring

theorem complement_ratio_error {t : ℝ} {R D : ℂ}
    (ht0 : 0≤t) (ht : t≤1/4) (hR : ‖R‖≤1/2) (hD : ‖D‖≤1/4) :
    ‖(1-R)/slotDenominator t R D-1‖≤2*(‖R‖+‖D‖) := by
  have hdb := (small_denominator_bounds ht0 ht hR hD).1
  have hd : slotDenominator t R D≠0 := norm_pos_iff.mp (by linarith)
  have hon : ‖1-(t:ℂ)‖=1-t := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  rw [complement_ratio_sub_one _ _ _ hd,norm_div]
  apply (div_le_iff₀ (by linarith : 0<‖slotDenominator t R D‖)).mpr
  have hn : ‖-(1-(t:ℂ))*(R-D)‖≤‖R‖+‖D‖ := by
    rw [norm_mul,norm_neg,hon]
    calc
      _ ≤ 1*‖R-D‖ := by gcongr; linarith
      _ ≤ _ := by simpa only [one_mul] using norm_sub_le R D
  have hx := mul_le_mul_of_nonneg_left hdb (by positivity : 0≤‖R‖+‖D‖)
  nlinarith

theorem actual_cube_ratio_error {Q : ℝ} (η : Character)
    (P : ProbePhysical.PrimeIdeal) (hQ : (Ideal.absNorm P.val:ℝ)=Q) (hq : 4≤Q)
    (s : ℂ)
    (hR : ‖coordR Q (actualAPhase η (primaryGenerator P.val)) s (1/6)‖≤1/2)
    (hD : ‖coordD Q (idealCoeff η P.val) 1 s‖≤1/4) :
    ‖cubeMaskLocalRatio η P s 1 (1/6)-1‖≤2*(Q^(3-6*s.re)+Q^(-s.re)) := by
  have hq0 : 0<Q := by linarith
  have ht0 : 0≤Q⁻¹ := inv_nonneg.mpr hq0.le
  have ht : Q⁻¹≤1/4 := by rw [←one_div]; exact one_div_le_one_div_of_le (by norm_num) hq
  rw [actual_cube_ratio_principal η P hQ hq s hR hD]
  have hb := complement_ratio_error ht0 ht hR hD
  rw [Complex.ofReal_inv] at hb
  have hr := coordR_norm_le Q hq0 (actualAPhase η (primaryGenerator P.val)) s (1/6)
    (actualAPhase_norm_le_one η _)
  norm_num at hr
  rw [show 4-6*s.re-1=3-6*s.re by ring] at hr
  have hdd := coordD_norm_le Q hq0 (idealCoeff η P.val) 1 s
    (idealCoeff_norm_le_one η _) (by simp)
  exact hb.trans (by linarith)

/-- Large actual prime norms preserve a nonzero finite source multiplier.
This statement uses neither exposure nor a hypothetical-mode substitution. -/
theorem actual_cube_ratio_ne_zero {Q : ℝ} (η : Character)
    (P : ProbePhysical.PrimeIdeal) (hQ : (Ideal.absNorm P.val:ℝ)=Q) (hq : 4≤Q)
    (s : ℂ)
    (hR : ‖coordR Q (actualAPhase η (primaryGenerator P.val)) s (1/6)‖≤1/2)
    (hD : ‖coordD Q (idealCoeff η P.val) 1 s‖≤1/4) :
    cubeMaskLocalRatio η P s 1 (1/6)≠0 := by
  rcases principal_slot_guards hq (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) s hR hD with ⟨_,_,hr,_,hd⟩
  rw [actual_cube_ratio_principal η P hQ hq s hR hD]
  exact div_ne_zero hr hd

theorem cube_negative_power {ι : Type*} {l : Filter ι} {Q : ι → ℝ}
    (hQ : Filter.Tendsto Q l Filter.atTop) {a : ℝ} (ha : a<0) :
    Filter.Tendsto (fun n => (Q n)^a) l (𝓝 0) := by
  simpa only [neg_neg,Function.comp_def] using
    (tendsto_rpow_neg_atTop (neg_pos.mpr ha)).comp hQ

/-- The actual cube/mark complement converges to ONE on every fixed right-half
point. It supplies no strict smallness of the retained principal source. -/
theorem actual_cube_ratio_tendsto_one {ι : Type*} {l : Filter ι}
    (η : Character) (P : ι → ProbePhysical.PrimeIdeal) (s : ℂ)
    (hQ : Filter.Tendsto (fun n => (Ideal.absNorm (P n).val:ℝ)) l Filter.atTop)
    (hs : 1/2<s.re) :
    Filter.Tendsto (fun n => cubeMaskLocalRatio η (P n) s 1 (1/6)) l (𝓝 1) := by
  have hr := cube_negative_power hQ (show 3-6*s.re<0 by linarith)
  have hd := cube_negative_power hQ (show -s.re<0 by linarith)
  have hb : Filter.Tendsto
      (fun n => 2*((Ideal.absNorm (P n).val:ℝ)^(3-6*s.re)+
        (Ideal.absNorm (P n).val:ℝ)^(-s.re))) l (𝓝 0) := by
    simpa using (hr.add hd).const_mul 2
  have he : ∀ᶠ n in l,
      ‖cubeMaskLocalRatio η (P n) s 1 (1/6)-1‖≤
        2*((Ideal.absNorm (P n).val:ℝ)^(3-6*s.re)+(Ideal.absNorm (P n).val:ℝ)^(-s.re)) := by
    filter_upwards [hQ.eventually_ge_atTop 4,
      hr.eventually_le_const (by norm_num : (0:ℝ)<1/2),
      hd.eventually_le_const (by norm_num : (0:ℝ)<1/4)] with n hn hnr hnd
    have hqn : 0<(Ideal.absNorm (P n).val:ℝ) := by linarith
    have hR := coordR_norm_le (Ideal.absNorm (P n).val) hqn
      (actualAPhase η (primaryGenerator (P n).val)) s (1/6)
      (actualAPhase_norm_le_one η _)
    norm_num at hR
    rw [show 4-6*s.re-1=3-6*s.re by ring] at hR
    have hD := coordD_norm_le (Ideal.absNorm (P n).val) hqn
      (idealCoeff η (P n).val) 1 s (idealCoeff_norm_le_one η _) (by simp)
    exact actual_cube_ratio_error η (P n) rfl hn s (hR.trans hnr) (hD.trans hnd)
  have hz : Filter.Tendsto (fun n => cubeMaskLocalRatio η (P n) s 1 (1/6)-1) l (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) he hb)
  simpa using hz.add_const 1

/-- The bare cube/prime-mark commutator cannot be norm-paid as a vanishing
native principal multiplier. This is a LOCAL source-conservation no-go. -/
theorem actual_cube_ratio_not_tendsto_zero {ι : Type*} {l : Filter ι} [l.NeBot]
    (η : Character) (P : ι → ProbePhysical.PrimeIdeal) (s : ℂ)
    (hQ : Filter.Tendsto (fun n => (Ideal.absNorm (P n).val:ℝ)) l Filter.atTop)
    (hs : 1/2<s.re) :
    ¬ Filter.Tendsto (fun n => cubeMaskLocalRatio η (P n) s 1 (1/6)) l (𝓝 0) := by
  intro hz
  have he := tendsto_nhds_unique (actual_cube_ratio_tendsto_one η P s hQ hs) hz
  norm_num at he

/-- The genuine full-minus-prime-marked Euler series remains the SAME inverse
L source times the finite cube-mask ratio.  This exact identity is restricted
to the native convergent Euler half-plane. -/
theorem actual_single_complement_source_factorization
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character)
    (P : ProbePhysical.PrimeIdeal) (hP : P.val∉S) (s w z : ℂ)
    (hs : 3/2<s.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 s w z-markedIdealHighSeries S P.val η 1 s w z =
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) w/
        LFunction (η.excludePrimes S hS.prime) s*globalClosedCorrection η S s w z)*
          cubeMaskLocalRatio η P s w z := by
  have hm := markedIdealHighSeries_eq_product S hS {P}
    (by intro Q hQ; simp only [Finset.mem_singleton] at hQ; subst Q; exact hP)
    η s w z hs hw hz
  simp only [Finset.prod_singleton] at hm
  have hn := source_idealHighLocalFactor_ne_zero S hS η P hP s w z hs hw hz
  have he := actual_ideal_ratio_eq_closed η P (outside_prime_supported S hS.bad P hP)
    s w z hs hw hz
  have hratio : 1-idealMarkedLocalFactor η P s w z/idealHighLocalFactor η P.val s w z =
      cubeMaskLocalRatio η P s w z := by
    rw [←he]
    field_simp
  rw [hm,source_principalHigh_L_factorization S hS η s w z hs hw hz,←hratio]
  ring

end OpenAIReview.CubeSourceGate

#lint+ in OpenAIReview.CubeSourceGate

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
  unless declarations>0 do throwError "Empty cube-source gate audit."
  logInfo m!"Cube-source gate audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-cube-source"
  IO.FS.writeFile ".lake/arithmetic-operator-cube-source/axioms.json"
    (Json.mkObj [("scope",toJson "actual finite cube-prime-mask principal source ratio; no independent arithmetic bound, contour continuation, or hypothetical-zero residue inference"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
