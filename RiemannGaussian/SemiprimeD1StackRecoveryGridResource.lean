/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridWordCaps
/-! # Paid grid VALUE resource and fixed physical cache envelopes
Both true N=2^(a+1) and W cells are physically generated/acquired and are paid
by VALUE here. These are proof-only bounds, never finite-source operands.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridResource
/-- The true grid count is physically materialized by actual marker doubling. -/
def gridSize (a:Nat) :Nat:=2^(a+1)
/-- Original physical metadata/index/template bytes plus actually emitted true N cells. -/
def resource (a M u:Nat) (t width:List Bool) :Nat:=a+M+u+t.length+width.length+gridSize a+1
/-- Every signed retained index and fitted/literal rational cache has this semantic width cap. -/
def cacheWidth (a:Nat) (width:List Bool) :Nat:=a+width.length+4
/-- All foreign original, geometry, ordinal and chronological slope bytes fit this fixed cubic envelope. -/
def dataWidth (a M u:Nat) (t width:List Bool) :Nat:=10^9*(resource a M u t width)^3
/-- True N is at least two, including a0. -/
theorem gridSize_two (a:Nat) :2≤ gridSize a:=by
  have h:=Nat.pow_le_pow_right (by decide:1≤2) (show 1≤ a+1 by omega)
  change 2≤2^(a+1)
  simpa only [pow_one] using h
/-- The resource always pays positive output and input storage. -/
theorem resource_pos (a M u:Nat) (t width:List Bool) :1≤ resource a M u t width:=by unfold resource;omega
/-- Original exponent metadata is paid by its actual marker bytes. -/
theorem a_le (a M u:Nat) (t width:List Bool) :a≤ resource a M u t width:=by unfold resource;omega
/-- Original M metadata is paid by its actual marker bytes. -/
theorem M_le (a M u:Nat) (t width:List Bool) :M≤ resource a M u t width:=by unfold resource;omega
/-- Original u metadata is paid by its actual marker bytes. -/
theorem u_le (a M u:Nat) (t width:List Bool) :u≤ resource a M u t width:=by unfold resource;omega
/-- Original padded binary t remains binary and every byte is paid. -/
theorem t_le (a M u:Nat) (t width:List Bool) :t.length≤ resource a M u t width:=by unfold resource;omega
/-- The actual rational template is paid by physical W cells, not log W. -/
theorem width_le (a M u:Nat) (t width:List Bool) :width.length≤ resource a M u t width:=by unfold resource;omega
/-- The complete original grid traversal/output cost is paid by true N value. -/
theorem grid_le (a M u:Nat) (t width:List Bool) :gridSize a≤ resource a M u t width:=by unfold resource;omega
/-- Actual current-q/index-template width fits the paid resource at every iteration. -/
theorem index_le (a M u:Nat) (t width:List Bool) :a+2≤ resource a M u t width:=by
  have h:=gridSize_two a
  unfold resource
  omega
/-- Semantic signed-cache width includes raw index padding and the literal two even at W0. -/
theorem cache_le (a M u:Nat) (t width:List Bool) :cacheWidth a width≤2*resource a M u t width:=by
  have h:=gridSize_two a
  unfold resource cacheWidth
  omega
/-- Every fitted W field plus its actual sign/literal-one exception is included. -/
theorem width_cache (a:Nat) (width:List Bool) :width.length+2≤ cacheWidth a width:=by unfold cacheWidth;omega
/-- Actual unary height and every row multiplicity are paid by original physical M/u bytes. -/
theorem height_le (a M u:Nat) (t width:List Bool) :SemiprimeD1TaperedLoss.height M u≤3*resource a M u t width:=by
  have h:=SemiprimeD1StackRecoveryGridByteBounds.height_le M u
  unfold resource
  omega
/-- Actual h*u bounds every physically emitted multiplicity, including u0. -/
theorem height_product_le (a M u:Nat) (t width:List Bool) :SemiprimeD1TaperedLoss.height M u*u≤3*resource a M u t width:=by
  have h:=SemiprimeD1StackRecoveryGridByteBounds.height_product M u
  unfold resource
  omega
/-- A uniform polynomial dominates all small actual metadata/source cache bounds. -/
theorem small_le_cubic (R x:Nat) (hR:1≤ R) (hx:x≤1000000*R) :x≤10^9*R^3:=by
  have hp:R≤ R^3:=Nat.le_pow (by decide:0<3)
  norm_num1
  omega
/-- Every semantic rational cache cap fits the larger global physical-word envelope. -/
theorem cache_data (a M u:Nat) (t width:List Bool) :cacheWidth a width≤ dataWidth a M u t width:=by
  apply small_le_cubic _ _ (resource_pos a M u t width)
  have h:=cache_le a M u t width
  omega
/-- Genuine emitted N+one marker and all count-copy literals fit the global data cap. -/
theorem counts_data (a M u:Nat) (t width:List Bool) :3*resource a M u t width+2≤ dataWidth a M u t width:=by
  apply small_le_cubic _ _ (resource_pos a M u t width)
  have h:=resource_pos a M u t width
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridResource
