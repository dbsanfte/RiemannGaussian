/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCardinalInputBits
import RiemannGaussian.SemiprimeAffineJetBits
import RiemannGaussian.SemiprimeNormalizedInverseBits
import RiemannGaussian.SemiprimeHermiteEvaluationBits

/-! # Executed intrinsic Hermite node on physical words
Each acquired packet and cardinal input is retained once. The normalized
inverse, quotient, evaluation and final product execute on rational words.
No decoded rational value is evaluated on this data path.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeHermiteNodeBits
open SemiprimeRationalBits SemiprimeJetBits

/-- Retained finite parameter and cached-record control allowance. This ledger
still needs a literal natural/address execution refinement. -/
def control (W Q J : ℕ) : ℕ := 20*(W+Q+J+1)^2+10

/-- One physical intrinsic Hermite summand, retaining the actual packet report. -/
def node (template : List Bool) (Q J : ℕ) (t : Fin Q) (H : JetReport) : RationalReport :=
  let inputs := SemiprimeCardinalInputBits.acquire Q J t
  let cardinal := SemiprimeAffineJetBits.build template J inputs.slopes
  let atZero := SemiprimeHermiteEvaluationBits.affineValue template inputs.x inputs.slopes
  let inverse := SemiprimeNormalizedInverseBits.build template cardinal.words J
  let quotient := multiplyBits template H.words inverse.words J
  let evaluation := SemiprimeHermiteEvaluationBits.evalPrefix template quotient.words inputs.x J
  let out := executeOperation .mul atZero.word evaluation.word template
  ⟨out.word,H.clock+inputs.clock+cardinal.clock+atZero.clock+inverse.clock+
    quotient.clock+evaluation.clock+out.clock+control template.length Q J⟩

end RiemannGaussian.SemiprimeHermiteNodeBits
