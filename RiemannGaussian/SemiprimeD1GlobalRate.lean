/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalEnvelopeRate

/-! # Fixed polynomial slowdowns and all-input rate constants
These arithmetic endpoints preserve the requested quantitative rate and absorb
the finite initial input segment. A caller must first prove the actual machine
time or report inequality being substituted; no simulation is assumed here.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1GlobalRate
open Filter SemiprimeD1OriginalCallRate SemiprimeMacroParameters
open scoped Topology

/-- Computable finite initial-segment budget for a fixed total cost function. -/
def finiteBudget (cost : ℕ→ℕ) (cutoff : ℕ) : ℕ :=
  1+∑N∈Finset.range (2^cutoff),cost N

/-- Every actual cost in the finite binary-input segment is included. -/
theorem finiteBudget_le (cost : ℕ→ℕ) (cutoff N : ℕ) (hN:N<2^cutoff) :
    cost N  ≤  finiteBudget cost cutoff := by
  have h:=Finset.single_le_sum (fun k (_:k∈Finset.range (2^cutoff))=>Nat.zero_le (cost k))
    (Finset.mem_range.mpr hN)
  unfold finiteBudget
  omega

noncomputable section

/-- A uniform positive scale is available even for one-bit positive inputs. -/
theorem inputScale_ge_half (ell : ℕ) (hell:1  ≤  ell) : (1/2:ℝ)  ≤  inputScale ell := by
  have he:(1:ℝ)  ≤  ell:=by exact_mod_cast hell
  have hlog:0<Real.log (ell+2:ℕ):=Real.log_pos (by exact_mod_cast (by omega:1<ell+2))
  have hb:=Real.log_le_sub_one_of_pos (show (0:ℝ)<(ell+2:ℕ) by positivity)
  have hs:Real.sqrt (Real.log (ell+2:ℕ))  ≤  2*(ell:ℝ):=by
    apply (Real.sqrt_le_left (by positivity)).mpr
    push_cast at hb ⊢
    nlinarith
  unfold inputScale
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hlog)).mpr
  linarith

/-- A concrete fixed polynomial overhead changes only this exponent constant. -/
def slowdownConstant (A d C : ℕ) : ℕ := 2*A+d*(C+2)

/-- Quantitative absorption for a proved polynomial simulation inequality.
This is arithmetic, not a machine-simulation premise supplied to the algorithm. -/
theorem polynomial_slowdown (A d C work : ℕ) (B : ℝ) (hB:(1/2:ℝ)  ≤  B)
    (hwork:(work:ℝ)  ≤  (2:ℝ)^((C:ℝ)*B)) :
    (A*(work+1)^d:ℕ)  ≤  (2:ℝ)^((slowdownConstant A d C:ℝ)*B) := by
  have hpow:(1:ℝ)  ≤  (2:ℝ)^((C:ℝ)*B):=Real.one_le_rpow (by norm_num) (by positivity)
  have hplus:(work:ℝ)+1  ≤  (2:ℝ)^((C:ℝ)*B+1):=by
    rw [Real.rpow_add (by norm_num:0<(2:ℝ)),Real.rpow_one]
    linarith
  have hA:(A:ℝ)  ≤  (2:ℝ)^(A:ℝ):=by
    simpa only [Real.rpow_natCast,Nat.cast_pow,Nat.cast_ofNat] using
      (show (A:ℝ)  ≤  (2^A:ℕ) by exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n:=A))))
  have hd:=pow_le_pow_left₀ (by positivity:(0:ℝ)  ≤  (work:ℝ)+1) hplus d
  have hm:=mul_le_mul hA hd (by positivity) (by positivity)
  have hpower:((2:ℝ)^((C:ℝ)*B+1))^d=(2:ℝ)^(((C:ℝ)*B+1)*d):=
    (Real.rpow_mul_natCast (by norm_num:0  ≤  (2:ℝ)) _ _).symm
  rw [hpower,←Real.rpow_add (by norm_num:0<(2:ℝ))] at hm
  have hm':(A*(work+1)^d:ℕ)  ≤  (2:ℝ)^((A:ℝ)+((C:ℝ)*B+1)*d):=by
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hm
  apply hm'.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num:1  ≤  (2:ℝ))
  unfold slowdownConstant
  push_cast
  nlinarith [show (0:ℝ) ≤ (A:ℝ) by positivity,show (0:ℝ) ≤ (d:ℝ) by positivity]

/-- An eventual original-length bound extends to EVERY positive original input
with one constant chosen before the entire family. No empirical finite coverage
or new fallback algorithm is used; the fixed total cost itself pays the prefix. -/
theorem eventually_to_all (cost : ℕ→ℕ) (C₀ : ℕ)
    (h:∀ᶠ ell:ℕ in atTop,∀N:ℕ,0<N→bitLength N=ell→
      (cost N:ℝ)  ≤  (2:ℝ)^((C₀:ℝ)*inputScale ell)) :
    ∃C:ℕ,∀N:ℕ,0<N→(cost N:ℝ)  ≤  (2:ℝ)^((C:ℝ)*inputScale (bitLength N)) := by
  obtain ⟨L,hL⟩:=eventually_atTop.mp h
  let M:=finiteBudget cost L
  refine ⟨C₀+2*M,?_⟩
  intro N hN
  have hB:=inputScale_ge_half (bitLength N) (bitLength_pos hN)
  by_cases hell:L  ≤  bitLength N
  · apply (hL (bitLength N) hell N hN rfl).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num:1  ≤  (2:ℝ))
    push_cast
    nlinarith [show (0:ℝ) ≤ (M:ℝ) by positivity]
  · have hsize:N<2^L:=(input_lt_bitLength_power N).trans_le
      (Nat.pow_le_pow_right (by decide:0<(2:ℕ)) (by omega))
    have hcost:cost N  ≤  M:=finiteBudget_le cost L N hsize
    have hnat:cost N  ≤  2^M:=hcost.trans (Nat.le_of_lt (Nat.lt_two_pow_self (n:=M)))
    have hreal:(cost N:ℝ)  ≤  (2:ℝ)^(M:ℝ):=by
      simpa only [Real.rpow_natCast,Nat.cast_pow,Nat.cast_ofNat] using
        (show (cost N:ℝ)  ≤  (2^M:ℕ) by exact_mod_cast hnat)
    apply hreal.trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num:1  ≤  (2:ℝ))
    push_cast
    nlinarith [show (0:ℝ) ≤ (M:ℝ) by positivity,show (0:ℝ) ≤ (C₀:ℝ) by positivity]

end
end RiemannGaussian.SemiprimeD1GlobalRate
