/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBodyBounds
/-! # Fixed semantic polynomial allowances, independent of all runtime inputs
Duplicate prepared packets are covered: generated child count can be quadratic,
unary scope output quartic, and complete per-vertex query cost ninth-degree.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryRates
namespace B
export SemiprimeD1StackChildGroupFactoryVertexBodyBounds (bodyBudget leftBudget)
end B
/-- The stopped prefix plus all generated per-vertex rows fits this uniform physical cap. -/
def master (S:Nat):Nat:=1000000000000000*(S+1)^5
/-- Real duplicate-safe row bytes fit the same fixed fifth-degree master bank. -/
theorem master_covers (S:Nat):100000000000000*(S+1)^4+S*(100*(S+1)^4)≤ master S:=by
  dsimp only [master]
  ring_nf
  omega
/-- SAME full two-source body allowance is ninth-degree, with coefficient fixed before inputs. -/
theorem bodyBudget_le (S:Nat):B.bodyBudget (master S) (master S) (S*S) S S (S*S)≤
    10^40*(S+1)^9:=by
  dsimp only [B.bodyBudget,B.leftBudget,SemiprimeD1StackChildGroupFactoryOldPortsLoopBounds.queryBudget,master]
  ring_nf
  omega
/-- The source byte cap grows only by actual row allowance during an entire marker loop. -/
theorem master_covers_remaining (S n:Nat) (hn:n≤S):
    100000000000000*(S+1)^4+n*(100*(S+1)^4)≤ master S:=
  (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _).trans (master_covers S)
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryRates
