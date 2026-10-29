import RiemannGaussian
import Mathlib.Tactic.Linter

/-!
# Whole-project declaration lint gate

The silent form emits nothing when every registered declaration linter
passes and reports errors otherwise. Compiler and tactic warnings are handled
separately by the warning-as-error build.
-/

-- Literal machine-address types contain deeply nested sums. Recheck them
-- with the recursion allowance used by their source modules; keep every
-- declaration linter enabled.
set_option maxRecDepth 32768 in
#lint- in RiemannGaussian
