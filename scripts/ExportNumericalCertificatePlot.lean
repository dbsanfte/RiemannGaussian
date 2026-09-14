import RiemannGaussian.External.Zeta23SevenWindowTarget
import Lean.Util.CollectAxioms

/-!
# Lean-checked coefficients for the numerical certificate comparison chart

This lightweight export uses only ordinary analytic and coefficient modules.
It does not import the exhaustive NumericalCertificate target. The separate
compiled certificate snapshot supplies the closed literal-count endpoints.
Every plotted interval below is checked against its actual Lean coefficient;
floating-point drawing is only an illustration of these rational enclosures.
-/

namespace NumericalCertificatePlot
open Lean Elab Command RiemannGaussian Zeta23InverseSampling

/-- The headline rational bound, also checked against the optional endpoint metadata. -/
private def certifiedFloor : ℚ := 6731 / 10000
/-- Lower rational enclosure of the actual pinned external coefficient. -/
private def baselineLower : ℚ := 6725007036 / 10000000000
/-- Upper rational enclosure of the actual pinned external coefficient. -/
private def baselineUpper : ℚ := 6725007037 / 10000000000
/-- Lower rational enclosure of the actual project coefficient. -/
private def improvedLower : ℚ := 6731055996 / 10000000000
/-- Upper rational enclosure of the actual project coefficient. -/
private def improvedUpper : ℚ := 6731055998 / 10000000000

/-- The plotted baseline interval encloses the exact imported Montgomery--Taylor constant. -/
private theorem baseline_bounds :
    (baselineLower : ℝ) < Zeta23.ThmD.HD 1 ∧ Zeta23.ThmD.HD 1 < (baselineUpper : ℝ) := by
  have he := MontgomeryTaylorNumericalKernel.eta_bounds
  rw [kernel_eta_eq_baseline_complement] at he
  norm_num [baselineLower, baselineUpper]
  constructor <;> linarith

/-- The plotted project interval encloses its exact coefficient, not an unchecked decimal approximation. -/
private theorem improved_bounds :
    (improvedLower : ℝ) < sevenWindowTargetCoefficient ∧
      sevenWindowTargetCoefficient < (improvedUpper : ℝ) := by
  simpa only [improvedLower, improvedUpper, Rat.cast_div, Rat.cast_ofNat] using
    sevenWindowTargetCoefficient_bounds

/-- The exact project coefficient strictly exceeds the rational eventual headline. -/
private theorem floor_below_coefficient : (certifiedFloor : ℝ) < sevenWindowTargetCoefficient := by
  simpa only [certifiedFloor, Rat.cast_div, Rat.cast_ofNat] using sevenWindowTargetCoefficient_gt_6731

/-- The displayed rational headline strictly improves two thirds. -/
private theorem floor_above_two_thirds : (2 : ℝ) / 3 < (certifiedFloor : ℝ) := by
  norm_num [certifiedFloor]

/-- Export a rational exactly as its signed numerator and positive denominator. -/
private def rationalJson (q : ℚ) : Json := toJson #[toJson q.num, toJson q.den]

run_cmd do
  let proofNames := #[``baseline_bounds, ``improved_bounds, ``floor_below_coefficient,
    ``floor_above_two_thirds, ``sevenWindowTargetCoefficient_gain]
  let mut proofs : Array Json := #[]
  for name in proofNames do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun n => n == ``propext || n == ``Classical.choice || n == ``Quot.sound) do
      throwError "nonstandard plotting theorem axioms: {name}: {axioms}"
    proofs := proofs.push (Json.mkObj [("theorem", toJson name.toString),
      ("axioms", toJson ((axioms.qsort Name.lt).map Name.toString))])
  let output := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("leanVersion", toJson Lean.versionString),
    ("generator", toJson "scripts/ExportNumericalCertificatePlot.lean"),
    ("twoThirds", rationalJson (2 / 3)), ("certifiedFloor", rationalJson certifiedFloor),
    ("baseline", toJson #[rationalJson baselineLower, rationalJson baselineUpper]),
    ("improved", toJson #[rationalJson improvedLower, rationalJson improvedUpper]),
    ("intervalConvention", toJson "strict lower and upper enclosures"),
    ("exactCoefficientTheorem", toJson (``sevenWindowTargetCoefficient_bounds).toString),
    ("proofs", toJson proofs)]
  IO.FS.createDirAll ".lake/numerical-certificate-plot"
  IO.FS.writeFile ".lake/numerical-certificate-plot/coefficients.json" (output.pretty ++ "\n")
  logInfo "Exported Lean-checked numerical certificate coefficient intervals."

end NumericalCertificatePlot
