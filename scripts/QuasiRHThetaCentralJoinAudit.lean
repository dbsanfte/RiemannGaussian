/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.PrimeRows.CentralCube
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Literal central kernels at the physical theta Mellin coordinate

The actual calibrated nonprincipal free-row kernel is analytic at w+z=7/6 at the actual z=17/50,
including every finite selected factor and its source weights. Finite sums
with the actual tuple weights preserve this local fact. This is not absence
of an external-Z source, an infinite-row interchange, or a theta/central
covariance estimate. A frozen sharp height mask is a constant here; no
holomorphy of its changing indicator is asserted.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.ThetaCentralJoin
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeHighRowFamily
  OAI.SevenEighths.ProbePhysical HeckeFamily HeckeInverseAmplification
local notation "O" => OAI.SevenEighths.HeckeFamily.O

/-- The literal fixed central free-row kernel is analytic on the theta half-plane. -/
theorem actual_central_kernel_analytic_w {K : ℕ}
    (e a tx tz : ℝ) (he : 0<e) (he' : e<1/1000) (ha : (51/100:ℝ)≤a)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1⊆Set.Icc a1 b1) (X Y Z : ℝ) (hY : 0<Y) :
    AnalyticOnNhd ℂ
      (fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+tx*Complex.I) w (((17/50:ℝ):ℂ)+tz*Complex.I))
      {w : ℂ | (1/2:ℝ)<w.re} := by
  have hf : FirstTail ((8*e)/2) S := by
    simpa only [show (8*e)/2=4*e by ring] using hfirst
  have hd : DifferentiableOn ℂ
      (fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+tx*Complex.I) w (((17/50:ℝ):ℂ)+tz*Complex.I))
      {w : ℂ | (1/2:ℝ)<w.re} := by
    intro w hw
    change (1/2:ℝ)<w.re at hw
    apply (continuedPhysicalRowKernel_differentiableAt_w (8*e) (by positivity)
      S hS hf hmax P hPS η u hu W0 W1 a1 b1 ha1 hW1 X Y Z hY
      (((a+16*e:ℝ):ℂ)+tx*Complex.I) w (((17/50:ℝ):ℂ)+tz*Complex.I)
      ?_ ?_ ?_ ?_).differentiableWithinAt
    all_goals try simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at *
    all_goals linarith
  exact hd.analyticOnNhd (Complex.isOpen_re_gt (1/2))

/-- No fixed nonprincipal central free-row kernel has a theta-coordinate singularity. -/
theorem actual_central_kernel_analyticAt_theta {K : ℕ}
    (e a tx tz : ℝ) (he : 0<e) (he' : e<1/1000) (ha : (51/100:ℝ)≤a)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1⊆Set.Icc a1 b1) (X Y Z : ℝ) (hY : 0<Y) :
    AnalyticAt ℂ
      (fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+tx*Complex.I) w (((17/50:ℝ):ℂ)+tz*Complex.I))
      (((62/75:ℝ):ℂ)-tz*Complex.I) := by
  apply actual_central_kernel_analytic_w e a tx tz he he' ha S hS hmax hfirst
    P hPS η u hu W0 W1 a1 b1 ha1 hW1 X Y Z hY
  norm_num

/-- The actual finite tuple-weighted central kernel sum is analytic at w+z=7/6 at the actual z=17/50. -/
theorem actual_finite_central_sum_analyticAt_theta {K : ℕ}
    (e tx tz : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character)
    (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1) (a : FreeRow→ℝ)
    (ha : ∀u∈R,(51/100:ℝ)≤a u)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1⊆Set.Icc a1 b1) (X Y Z : ℝ) (hY : 0<Y) :
    AnalyticAt ℂ
      (fun w=>∑u∈R,∑P : (∀i,T i),
        (∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
          continuedPhysicalRowKernel S hS hmax (fun i=>(P i).val)
            (fun i=>hT i _ (P i).property) η u W0 W1 X Y Z
            (((a u+16*e:ℝ):ℂ)+tx*Complex.I) w (((17/50:ℝ):ℂ)+tz*Complex.I))
      (((62/75:ℝ):ℂ)-tz*Complex.I) := by
  apply Finset.analyticAt_fun_sum
  intro u hu
  apply Finset.analyticAt_fun_sum
  intro P _
  exact analyticAt_const.mul (actual_central_kernel_analyticAt_theta e (a u) tx tz he he' (ha u hu)
    S hS hmax hfirst (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
    η u (hR u hu) W0 W1 a1 b1 ha1 hW1 X Y Z hY)

end OpenAIReview.ThetaCentralJoin
#lint+ in OpenAIReview.ThetaCentralJoin

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
  unless declarations>0 do throwError "Empty actual theta/central join audit."
  logInfo m!"Actual theta/central join audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-theta-central-join-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-theta-central-join-gate/axioms.json"
    (Json.mkObj [("scope",toJson "literal calibrated nonprincipal fixed central kernels and actual finite tuple-weighted sums analytic at physical theta Mellin coordinate w+z=7/6 at the actual z=17/50; not external-Z source absence or infinite-row/whole covariance estimate"),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingHelpers",toJson theorems),("details",Json.arr details)]).pretty
