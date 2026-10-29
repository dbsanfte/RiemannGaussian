import RiemannGaussian.SemiprimeBooleanRingFactor
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  unless `OAI.Algorithms.SubexponentialSAT.GlobalPolynomial ∈ env.header.moduleNames do
    throwError "original GlobalPolynomial missing"
  for n in env.header.moduleNames do
    if n.toString.startsWith "OpenAISemiprime." then
      throwError "overlapping vendor branch imported: {n}"
  logInfo m!"ORIGINAL_ONLY no_vendor=true modules={env.header.moduleNames.size}"
