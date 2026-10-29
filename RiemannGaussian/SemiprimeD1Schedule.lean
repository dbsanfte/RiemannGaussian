/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PrecisionEnvelope

/-! # Literal dyadic schedule and original inherited-precision guards

Every path precision is computed by the actual D.11 update from the edge and
node history. No precision sequence is supplied. A conservative extra leaf
guard stops when fewer than minimumLevels valuation levels remain. Bounding
those leaves and the full recursive machine is a separate obligation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1Schedule
open scoped BigOperators
open SemiprimeD1ModeRate SemiprimeD1PrecisionEnvelope

/-- Fixed original D.1 epsilon denominator, before all input sizes. -/
def epsilonDenominator : ℕ := 128*1024

/-- Original dyadically decreasing retained valuation levels. -/
def levels (lam depth : ℕ) : ℕ := (lam/epsilonDenominator)/2^depth

/-- Actual cumulative exponent inherited from earlier recursion levels. -/
def previous (lam depth : ℕ) : ℕ := 2*∑ j∈Finset.range depth,levels lam j

/-- Packet exponent after adding this call's twice-taper increment. -/
def exponent (lam depth : ℕ) : ℕ := previous lam depth+2*levels lam depth

/-- Original leaf scale; a finite quotient avoids a real square-root oracle. -/
def leafSize (s lam : ℕ) : ℕ := s/(Nat.sqrt lam+1)+1

/-- The explicit active-call test; all three failing cases become leaves. -/
def Active (s lam depth M : ℕ) : Prop :=
  leafSize s lam < M ∧ minimumLevels lam ≤ levels lam depth ∧ levels lam depth ≤ M

/-- Halving is exact even across all integer floors. -/
theorem levels_succ (lam depth : ℕ) : levels lam (depth+1)=levels lam depth/2 := by
  simp only [levels,pow_succ,Nat.div_div_eq_div_mul,Nat.mul_assoc]

/-- Every actually retained level is bounded by its original input parameter. -/
theorem levels_le (lam depth : ℕ) : levels lam depth ≤ lam := by
  exact (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)

/-- The finite cumulative taper never exceeds twice its first block. -/
theorem sum_levels (lam depth : ℕ) :
    (∑ j∈Finset.range depth,levels lam j)+2*levels lam depth ≤ 2*(lam/epsilonDenominator) := by
  induction depth with
  | zero => simp [levels]
  | succ depth ih =>
    rw [Finset.sum_range_succ,levels_succ]
    have hh := Nat.div_mul_le_self (levels lam depth) 2
    omega

/-- The explicit packet exponent stays below four original epsilon blocks. -/
theorem exponent_le (lam depth : ℕ) : exponent lam depth ≤ 4*(lam/epsilonDenominator) := by
  have h := sum_levels lam (depth+1)
  rw [Finset.sum_range_succ] at h
  unfold exponent previous
  omega

/-- The conservative numeric envelope used in the inherited-precision proof. -/
theorem exponent_le_lam (lam depth : ℕ) : exponent lam depth ≤ 4*lam :=
  (exponent_le lam depth).trans (Nat.mul_le_mul_left 4 (Nat.div_le_self _ _))

/-- The next call inherits exactly the previous call's cumulative exponent. -/
theorem previous_succ (lam depth : ℕ) : previous lam (depth+1)=exponent lam depth := by
  simp only [previous,exponent,Finset.sum_range_succ,Nat.mul_add]

/-- Nonempty retained levels force a genuine logarithmic depth bound. -/
theorem depth_le (lam depth : ℕ) (hu : 0 < levels lam depth) : depth ≤ lam := by
  have hp : 0 < (2:ℕ)^depth := by positivity
  have hb : 2^depth ≤ lam/epsilonDenominator := by
    have h := (Nat.le_div_iff_mul_le hp).mp (show 1 ≤ levels lam depth by omega)
    simpa only [Nat.one_mul] using h
  have hd := depth.lt_two_pow_self
  have hl := Nat.div_le_self lam epsilonDenominator
  omega

/-- Every active node has a strictly positive actual taper. -/
theorem active_positive (s lam depth M : ℕ) (h : Active s lam depth M) : 0 < levels lam depth := by
  have hh : 8 ≤ minimumLevels lam := by unfold minimumLevels;omega
  exact lt_of_lt_of_le (by omega : 0 < minimumLevels lam) h.2.1

/-- Original active edge count pays the root-size factor in inherited precision. -/
theorem active_size (s lam depth M : ℕ) (h : Active s lam depth M) : s ≤ M*(lam+1) := by
  have hk : 0 < Nat.sqrt lam+1 := by omega
  have hq : s < (s/(Nat.sqrt lam+1)+1)*(Nat.sqrt lam+1) := by
    exact (Nat.div_lt_iff_lt_mul hk).mp (by omega)
  have hs := Nat.sqrt_le_self lam
  have hm : s/(Nat.sqrt lam+1)+1 ≤ M := by have hh := h.1;unfold leafSize at hh;omega
  have hb := Nat.mul_le_mul hm (show Nat.sqrt lam+1 ≤ lam+1 by omega)
  omega

/-- Actual precisions generated from original edge/node histories, not advice. -/
def precision (lam : ℕ) (edges node : ℕ→ℕ) (p0 : ℕ) : ℕ→ℕ
  | 0 => p0
  | depth+1 => workingPrecision (edges depth) (levels lam depth)
      (exponent lam depth) (node depth) (precision lam edges node p0 depth)

/-- Every computed precision along an admissible path satisfies the preserved envelope. -/
theorem precision_cap (s lam depth : ℕ) (edges node : ℕ→ℕ) (p0 : ℕ) (hp0 : p0 ≤ s)
    (hpath : ∀ j < depth,edges j ≤ s ∧ levels lam j ≤ edges j) :
    precision lam edges node p0 depth ≤ pathCap s lam depth (previous lam depth) := by
  induction depth with
  | zero => simpa [precision,previous,root_cap] using hp0
  | succ depth ih =>
    have hprev := ih (fun j hj => hpath j (by omega))
    have hh := hpath depth (by omega)
    rw [precision,previous_succ]
    exact update_cap s lam depth (previous lam depth) (edges depth) (levels lam depth)
      (exponent lam depth) (node depth) _ hh.1 hh.2 (exponent_le_lam lam depth)
        (by unfold exponent;omega) hprev

/-- All three mode-acquisition guards hold at every actual active path node.
The remaining graph/packing/child correctness joins do not enter this arithmetic proof. -/
theorem active_guards (s lam depth : ℕ) (edges node : ℕ→ℕ) (p0 : ℕ) (hp0 : p0 ≤ s)
    (hpath : ∀ j < depth,edges j ≤ s ∧ levels lam j ≤ edges j)
    (hactive : Active s lam depth (edges depth)) (hi : node depth < levels lam depth) :
    node depth ≤ exponent lam depth ∧
      precision lam edges node p0 depth*levels lam depth ≤ edges depth*2^(exponent lam depth-node depth) ∧
      (exponent lam depth+1)*levels lam depth ≤ 2^(exponent lam depth-node depth) := by
  have hpos := active_positive s lam depth (edges depth) hactive
  have hd := depth_le lam depth hpos
  have hpc := precision_cap s lam depth edges node p0 hp0 hpath
  have hx := exponent_le_lam lam depth
  have hstep : previous lam depth+2*levels lam depth ≤ exponent lam depth := by rfl
  refine ⟨by unfold exponent;omega,?_,?_⟩
  · exact input_guard s lam depth (previous lam depth) (edges depth) (levels lam depth)
      (exponent lam depth) (node depth) _ hpc hd (active_size _ _ _ _ hactive)
        (levels_le _ _) hactive.2.1 hstep (by omega)
  · exact evaluation_guard lam (levels lam depth) (exponent lam depth) (node depth)
      (levels_le _ _) hactive.2.1 hx (by unfold exponent;omega) (by omega)

end RiemannGaussian.SemiprimeD1Schedule
