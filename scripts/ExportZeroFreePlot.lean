import RiemannGaussian
import Lean.Util.CollectAxioms

/-!
# Checked numerical formulas for the zero-free comparison picture

The plotting program evaluates this small expression language, not a second
handwritten implementation of the bounds. The identities below check each
expression against the imported Lean definitions. Floating-point drawing is
illustrative; the nonvanishing and comparison proofs remain the authority.
-/

namespace ZeroFreePlot
open Lean Elab Command RiemannGaussian

private inductive Formula where
  | variable
  | natural (n : Nat)
  | add (a b : Formula)
  | sub (a b : Formula)
  | mul (a b : Formula)
  | div (a b : Formula)
  | power (a b : Formula)
  | log (a : Formula)
  | exp (a : Formula)
  | minimum (a b : Formula)
  | maximum (a b : Formula)

private noncomputable def Formula.real (L : ℝ) : Formula → ℝ
  | .variable => L
  | .natural n => n
  | .add a b => a.real L + b.real L
  | .sub a b => a.real L - b.real L
  | .mul a b => a.real L * b.real L
  | .div a b => a.real L / b.real L
  | .power a b => a.real L ^ b.real L
  | .log a => Real.log (a.real L)
  | .exp a => Real.exp (a.real L)
  | .minimum a b => min (a.real L) (b.real L)
  | .maximum a b => max (a.real L) (b.real L)

private def Formula.json : Formula → Json
  | .variable => toJson #[Json.str "variable"]
  | .natural n => toJson #[Json.str "natural", toJson n]
  | .add a b => toJson #[Json.str "add", a.json, b.json]
  | .sub a b => toJson #[Json.str "sub", a.json, b.json]
  | .mul a b => toJson #[Json.str "mul", a.json, b.json]
  | .div a b => toJson #[Json.str "div", a.json, b.json]
  | .power a b => toJson #[Json.str "power", a.json, b.json]
  | .log a => toJson #[Json.str "log", a.json]
  | .exp a => toJson #[Json.str "exp", a.json]
  | .minimum a b => toJson #[Json.str "minimum", a.json, b.json]
  | .maximum a b => toJson #[Json.str "maximum", a.json, b.json]

private def enlarged : Formula := .log (.add (.exp .variable) (.natural 2))

private def heightCost (a b : Nat) : Formula :=
  .add (.add enlarged (.mul (.natural a) (.log enlarged))) (.natural b)

private def gaussian : Formula := .maximum
  (.minimum (.div (.natural 1) (.natural 450000))
    (.div (.natural 221) (.mul (.natural 250) (heightCost 2052 30240))))
  (.minimum (.div (.natural 1) (.natural 40500))
    (.div (.natural 1547) (.mul (.natural 1800) (heightCost 1995 29400))))

private def reserve : Formula := .maximum
  (.div (.natural 792) (.sub (.mul (.natural 7625) enlarged) (.natural 2000)))
  (.minimum (.div (.natural 4) (.natural 39))
    (.div (.natural 4752) (.sub (.mul (.natural 45750)
      (.maximum (.div (.natural 13) (.natural 10)) enlarged)) (.natural 35725))))

private def unified : Formula := .maximum reserve gaussian

private def classical (n d : Nat) : Formula :=
  .div (.natural 1) (.mul (.div (.natural n) (.natural d)) .variable)

private def littlewood (n d : Nat) : Formula :=
  .div (.log .variable) (.mul (.div (.natural n) (.natural d)) .variable)

private def vk (n d : Nat) : Formula := .div (.natural 1)
  (.mul (.mul (.div (.natural n) (.natural d))
    (.power .variable (.div (.natural 2) (.natural 3))))
    (.power (.log .variable) (.div (.natural 1) (.natural 3))))

-- The plot begins where all selected external benchmark statements apply.
-- The current repository theorem itself has no minimum-height assumption.
private def minimumHeight : Nat := 3
private def crossoverLower : Nat := 288000
private def crossoverUpper : Nat := 289000
private def crossoverGap : Formula := .sub
  (.mul (.div (.natural 981) (.natural 50)) .variable)
  (.mul (.natural 450000) (.log .variable))
private def ceiling : Formula := .natural 480000

private theorem gaussian_correct (L : ℝ)
    (hL : 1 ≤ ZetaNearOneBudgetLimit.scale (Real.exp L)) :
    gaussian.real L = ZetaGaussianRegionUnion.width (Real.exp L) := by
  rw [ZetaGaussianRegionUnion.width_eq_max_min hL]
  simp [gaussian, heightCost, enlarged, Formula.real, ZetaGaussianRetainedRegion.heightCost,
    ZetaGaussianExpandedRegion.heightCost, ZetaNearOneBudgetLimit.scale,
    ZetaNearOneLogProfile.height,
    abs_of_pos (Real.exp_pos L)]

private theorem classical_correct (n d : Nat) (L : ℝ) :
    (classical n d).real L = ZetaGaussianBandFrontier.classicalWidth (n / d) L := by
  simp [classical, Formula.real, ZetaGaussianBandFrontier.classicalWidth]

private theorem littlewood_correct (n d : Nat) (L : ℝ) :
    (littlewood n d).real L = ZetaGaussianBandFrontier.littlewoodWidth (n / d) L := rfl

private theorem vk_correct (n d : Nat) (L : ℝ) :
    (vk n d).real L = ZetaGaussianBandFrontier.vkWidth (n / d) L := by
  simp [vk, Formula.real, ZetaGaussianBandFrontier.vkWidth]

private theorem reserve_correct (L : ℝ) :
    reserve.real L = zetaPoleReserveZeroMargin (Real.exp L) := by
  rw [zetaPoleReserveZeroMargin, zetaPoleReserveFixedMargin_eq]
  simp [reserve, Formula.real, enlarged, zetaSignedPoleZeroMargin,
    abs_of_pos (Real.exp_pos L)]

private theorem unified_correct (L : ℝ) :
    unified.real L = ZetaUnifiedZeroFree.width (Real.exp L) := by
  rw [ZetaUnifiedZeroFree.width_eq_max]
  simp [unified, reserve, gaussian, heightCost, enlarged, Formula.real,
    ZetaGaussianRetainedRegion.heightCost, ZetaGaussianExpandedRegion.heightCost,
    ZetaNearOneBudgetLimit.scale, ZetaNearOneLogProfile.height,
    abs_of_pos (Real.exp_pos L)]

private theorem allHeight_nonvanishing (s : ℂ) (hs1 : s ≠ 1)
    (hσ : 1 - ZetaUnifiedZeroFree.width s.im ≤ s.re) : riemannZeta s ≠ 0 :=
  ZetaUnifiedZeroFree.nonvanishing s hs1 hσ

private theorem crossoverGap_correct (L : ℝ) :
    crossoverGap.real L = ZetaGaussianBandFrontier.crossoverGap L := rfl

private theorem crossoverBracket_correct :
    (crossoverLower : ℝ) < ZetaGaussianBandFrontier.crossover ∧
      ZetaGaussianBandFrontier.crossover < (crossoverUpper : ℝ) :=
  ZetaGaussianBandFrontier.crossover_refined_bounds

private theorem ceiling_correct (L : ℝ) :
    ceiling.real L = 480000 := rfl

private theorem plotted_comparison (s : ℂ) {L : ℝ}
    (hL : ZetaGaussianBandFrontier.crossover < L) (hLu : L ≤ ceiling.real L)
    (ht : |s.im| = Real.exp L) (hσ : 1 - ZetaUnifiedZeroFree.width s.im ≤ s.re) :
    riemannZeta s ≠ 0 ∧ ZetaGaussianBandFrontier.benchmarkWidth L < ZetaUnifiedZeroFree.width s.im :=
  ZetaGaussianExpandedComparison.nonvanishing_and_comparison s hL hLu ht hσ

private theorem headlineEnvelope_correct (L : ℝ) :
    max ((classical 24297 5000).real L)
      (max ((littlewood 981 50).real L) ((vk 2567 50).real L)) =
      ZetaGaussianBandFrontier.benchmarkWidth L := by
  simp only [classical_correct, littlewood_correct, vk_correct]
  norm_num [ZetaGaussianBandFrontier.benchmarkWidth]

run_cmd do
  let env ← getEnv
  let mut proofs : Array Json := #[]
  for name in #[``gaussian_correct, ``reserve_correct, ``unified_correct,
      ``classical_correct, ``littlewood_correct, ``vk_correct,
      ``allHeight_nonvanishing, ``crossoverGap_correct, ``crossoverBracket_correct,
      ``ceiling_correct, ``plotted_comparison, ``headlineEnvelope_correct, ``ZetaUnifiedZeroFree.exact_strip,
      ``ZetaUnifiedZeroFree.gaussian_width_le, ``ZetaUnifiedZeroFree.reserve_width_le,
      ``ZetaGaussianExpandedComparison.nonvanishing_and_comparison] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
      throwError "nonstandard axiom in plot formula/proof: {name}: {axioms}"
    let some ci := env.find? name | throwError "missing plot proof: {name}"
    let statement ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty 110
    proofs := proofs.push (Json.mkObj [("name", toJson (privateToUserName name).toString),
      ("statement", toJson statement), ("axioms", toJson (axioms.map Name.toString))])
  let curves : Array (String × Formula) := #[
    ("gaussian", unified),
    ("classical-bty", classical 612 125),
    ("classical-candidate", classical 24297 5000),
    ("littlewood-yang", littlewood 21233 1000),
    ("littlewood-reported", littlewood 981 50),
    ("vk-bellotti-v1", vk 13501 250),
    ("vk-reported", vk 2567 50)]
  let output := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("leanVersion", toJson Lean.versionString),
    ("generator", toJson "scripts/ExportZeroFreePlot.lean"),
    ("coordinate", toJson "L = log(abs(t)); Gaussian enlarged height is log(exp(L)+2)."),
    ("minimumHeight", toJson minimumHeight),
    ("repositoryHasHeightRestriction", toJson false),
    ("curves", Json.mkObj (curves.toList.map fun (id, f) => (id, f.json))),
    ("comparison", Json.mkObj [("gap", crossoverGap.json),
      ("bracket", toJson #[crossoverLower, crossoverUpper]), ("ceiling", ceiling.json),
      ("lowerClosed", toJson false), ("upperClosed", toJson true)]),
    ("proofs", toJson proofs)]
  IO.FS.createDirAll ".lake/zero-free-regions"
  IO.FS.writeFile ".lake/zero-free-regions/formulas.json" (output.compress ++ "\n")
  logInfo "Exported checked zero-free plot formulas and transitive axiom audits."

end ZeroFreePlot
