/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WeightedPotential
import RiemannGaussian.SemiprimeD1ModeCatalog
import RiemannGaussian.SemiprimeD1EulerBound

/-! # Actual weighted-mode menu cardinality at every aspect ratio
The exponent is controlled by weighted precision, not Boolean support entropy.
Original packet construction and recursive tensor factorization remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1WeightedCardinality
open SemiprimeD1WeightedTuples
open SemiprimeD1WeightedPotential SemiprimeD1ModeCatalog
open scoped BigOperators

/-- Finite Euler bound applied to the actually enumerated positive-weight list. -/
theorem length_le_exp {ws : List ℕ} {a : ℝ} (ha : 0<a)
    (K B P : ℕ) (hpos : ∀w∈ws,0<w) (hmax : ∀w∈ws,w≤K)
    (hmult : ∀w,ws.count w≤B) :
    ((tuples ws P).length:ℝ)≤ Real.exp (a*P+2*B/a) := by
  have hc := length_le_potential ha hpos P
  rw [normalizer_exp ha hpos,←Real.exp_add] at hc
  have he := SemiprimeD1EulerBound.euler_log_sum_le a ha K
  have he' : (∑j∈Finset.range K,logFactor a (j+1))≤2/a := by
    simpa [logFactor,Nat.cast_add,Nat.cast_one] using he
  have hs := (logsum_multiplicity ha K B hmax hmult).trans
    (mul_le_mul_of_nonneg_left he' (Nat.cast_nonneg B))
  apply hc.trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ a*P+(B:ℝ)*(2/a) := add_le_add le_rfl hs
    _ = _ := by ring

/-- Optimized coloured-partition bound for all B/P, including zero cases. -/
theorem length_le_sqrt (ws : List ℕ) (K B P : ℕ)
    (hpos : ∀w∈ws,0<w) (hmax : ∀w∈ws,w≤K)
    (hmult : ∀w,ws.count w≤B) :
    ((tuples ws P).length:ℝ)≤ Real.exp (3*Real.sqrt ((B:ℝ)*P)) := by
  by_cases hP : P=0
  · subst P
    simp [tuples_zero]
  by_cases hB : B=0
  · subst B
    have hw : ws=[] := by
      cases ws with
      | nil => rfl
      | cons w ws => have hc := hmult w; simp at hc
    simp [hw,tuples]
  have hBR : (0:ℝ)<B := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hB)
  have hPR : (0:ℝ)<P := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hP)
  have ha : 0<Real.sqrt (B:ℝ)/Real.sqrt (P:ℝ) :=
    div_pos (Real.sqrt_pos.mpr hBR) (Real.sqrt_pos.mpr hPR)
  have h := length_le_exp ha K B P hpos hmax hmult
  simpa only [balance_exponent hBR hPR] using h

/-- Acquired padded D1 modes have the floor-based bound, without D≈sqrt(u).
The only packet input is its genuine packing estimate, not a mode answer. -/
theorem packet_menu_bound (packets a i M P : ℕ) (hi : i≤a)
    (hpackets : packets*2^a≤3*M) :
    ((acquireModes packets (2^(i+1)) P).values.length:ℝ)≤
      Real.exp (3*Real.sqrt (((6*M/2^(a-i):ℕ):ℝ)*P)) := by
  rw [acquireModes_values]
  exact length_le_sqrt _ P _ P (weights_positive _ _) (weights_le _ _)
    (packet_multiplicity packets a i M P · hi hpackets)

/-- Polynomial work factor for the actual catalogue and tuple traversal. -/
def modeFactor (slots P : ℕ) : ℕ := 20*(P+10)*(P*slots+1)^2

/-- Explicit acquired catalogue, weight-copy and final report overhead. -/
def modeOverhead (slots P : ℕ) : ℕ := (10*P+10+P*(10*slots+10))+10*(P*slots)+10

/-- Actual acquired native work has the same arbitrary-aspect exponential rate.
This is not an assertion that the native scalar/list report is a bit/tape clock. -/
theorem packet_work_bound (packets a i M P : ℕ) (hi : i≤a)
    (hpackets : packets*2^a≤3*M) :
    ((acquireModes packets (2^(i+1)) P).work:ℝ)≤
      (modeFactor (packets*2^(i+1)) P:ℝ)*
        Real.exp (3*Real.sqrt (((6*M/2^(a-i):ℕ):ℝ)*P))+
          (modeOverhead (packets*2^(i+1)) P:ℝ) := by
  have hn : (acquireModes packets (2^(i+1)) P).work≤
      modeFactor (packets*2^(i+1)) P*(acquireModes packets (2^(i+1)) P).values.length+
        modeOverhead (packets*2^(i+1)) P := by
    simpa only [modeFactor,modeOverhead,Nat.add_assoc] using
      acquireModes_work_le packets (2^(i+1)) P
  have hr : ((acquireModes packets (2^(i+1)) P).work:ℝ)≤
      (modeFactor (packets*2^(i+1)) P:ℝ)*
        ((acquireModes packets (2^(i+1)) P).values.length:ℝ)+
          (modeOverhead (packets*2^(i+1)) P:ℝ) := by exact_mod_cast hn
  exact hr.trans (add_le_add (mul_le_mul_of_nonneg_left
    (packet_menu_bound packets a i M P hi hpackets) (Nat.cast_nonneg _)) le_rfl)

end RiemannGaussian.SemiprimeD1WeightedCardinality
