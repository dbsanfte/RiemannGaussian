import RiemannGaussian
import Mathlib.Tactic.Linter

/-!
# Whole-project declaration lint gate

The silent form emits nothing when every registered declaration linter
passes and reports errors otherwise. Compiler and tactic warnings are handled
separately by the warning-as-error build.
-/

#lint- in RiemannGaussian
