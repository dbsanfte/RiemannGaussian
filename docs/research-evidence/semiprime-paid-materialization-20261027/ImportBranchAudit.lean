import RiemannGaussian.SemiprimeTernaryPublicFactor
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for n in env.header.moduleNames do
    let s := n.toString
    if s.startsWith "OAI." || s.startsWith "OpenAISemiprime." then
      throwError "unexpected layout source branch: {n}"
  logInfo m!"NO_OAI_LAYOUT_BRANCH modules={env.header.moduleNames.size}"
