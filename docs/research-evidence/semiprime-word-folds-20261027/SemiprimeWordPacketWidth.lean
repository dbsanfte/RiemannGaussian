/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNativeGroupBitsHeight

/-! # Polynomial-resource width for physical packet word folds
Common denominators are retained across sums. Actual head/summary/support
cardinalities enter the width polynomially, never as 2^Y or a full 2^n sweep.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeWordPacketWidth
open SemiprimeNativeGroupBitsHeight SemiprimeNativeGroupBits

/-- One common product base covering head numerators, denominators and precision. -/
def productBase (J DG BG headCap : ℕ) : ℕ := (J+1)*(DG+headCap*BG+1)

/-- Polynomial exponent of that product base, from original group input bits. -/
def productExponent (b R F s J headCap : ℕ) : ℕ :=
  J+headCap+exponent b R F s+4

/-- Actual runtime width computed from source parameters and acquired traversal cardinalities. -/
def packetWidth (b R n F s J r headCap Y Cq : ℕ) : ℕ :=
  groupWidth b R F s+n+exponent b R F s*(r+1)+
    productExponent b R F s J headCap*(2*r+4)+Y+Cq+10

/-- Original group payloads fit the larger packet template. -/
theorem groupWidth_le (b R n F s J r headCap Y Cq : ℕ) :
    groupWidth b R F s≤packetWidth b R n F s J r headCap Y Cq := by
  unfold packetWidth
  omega

/-- The actual packet width is positive even at empty products. -/
theorem positive (b R n F s J r headCap Y Cq : ℕ) :
    0<packetWidth b R n F s J r headCap Y Cq := by
  unfold packetWidth
  omega

/-- Product base covers all three original product-list guards. -/
theorem productBase_guards (J DG BG headCap : ℕ) :
    DG≤productBase J DG BG headCap ∧ headCap*BG≤productBase J DG BG headCap ∧
      J≤productBase J DG BG headCap := by
  have h := Nat.mul_le_mul_right (DG+headCap*BG+1) (show 1≤J+1 by omega)
  have h' := Nat.mul_le_mul_left (J+1) (show 1≤DG+headCap*BG+1 by omega)
  simp only [one_mul,mul_one] at h h'
  unfold productBase
  omega

/-- Head numerator additions share a denominator; only their count multiplies the numerator. -/
theorem head_dyadic (headCap BG e : ℕ) (hBG : BG≤2^e) :
    headCap*BG≤2^(headCap+e) := by
  calc
    headCap*BG≤2^headCap*2^e := Nat.mul_le_mul (Nat.le_of_lt Nat.lt_two_pow_self) hBG
    _ = _ := (pow_add _ _ _).symm

/-- The complete product base fits its explicit fixed-polynomial exponent. -/
theorem productBase_dyadic (b R F s J headCap DG BG : ℕ)
    (hDG : DG≤2^(exponent b R F s)) (hBG : BG≤2^(exponent b R F s)) :
    productBase J DG BG headCap≤2^(productExponent b R F s J headCap) := by
  let e := exponent b R F s
  have hh := head_dyadic headCap BG e hBG
  have hd := hDG.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left e headCap))
  have hone : 1≤2^(headCap+e) := Nat.one_le_pow _ _ (by decide)
  have hsum : DG+headCap*BG+1≤2^(headCap+e+2) := by
    rw [pow_add]
    norm_num
    omega
  have hj : J+1≤2^(J+1) := Nat.le_of_lt Nat.lt_two_pow_self
  have h := Nat.mul_le_mul hj hsum
  rw [← pow_add] at h
  apply h.trans
  apply Nat.pow_le_pow_right (by decide)
  unfold productExponent
  dsimp only [e]
  omega

/-- Every suffix multiplication fits the selected packet width. -/
theorem product_width (b R n F s J r headCap Y Cq : ℕ) :
    productExponent b R F s J headCap*(2*r+2)<packetWidth b R n F s J r headCap Y Cq := by
  have h := Nat.mul_le_mul_left (productExponent b R F s J headCap)
    (show 2*r+2≤2*r+4 by omega)
  unfold packetWidth
  omega

/-- The common head denominator fits the packet template strictly. -/
theorem head_denominator_lt (b R n F s J r headCap Y Cq DG : ℕ)
    (hDG : DG≤2^(exponent b R F s)) :
    DG<2^(packetWidth b R n F s J r headCap Y Cq) := by
  apply hDG.trans_lt
  apply Nat.pow_lt_pow_right (by decide)
  have h := Nat.mul_le_mul_left (exponent b R F s) (show 1≤r+1 by omega)
  simp only [mul_one] at h
  unfold packetWidth
  omega

/-- The actual head-sum numerator fits the same packet template strictly. -/
theorem head_numerator_lt (b R n F s J r headCap Y Cq BG : ℕ)
    (hBG : BG≤2^(exponent b R F s)) :
    headCap*BG<2^(packetWidth b R n F s J r headCap Y Cq) := by
  apply (head_dyadic headCap BG _ hBG).trans_lt
  apply Nat.pow_lt_pow_right (by decide)
  have hk : headCap+exponent b R F s≤productExponent b R F s J headCap := by
    unfold productExponent
    omega
  have h := Nat.mul_le_mul_left (productExponent b R F s J headCap) (show 1≤2*r+4 by omega)
  simp only [mul_one] at h
  unfold packetWidth
  omega

/-- Multiplying r group denominators does not introduce the summary count into the exponent. -/
theorem fibre_denominator_lt (b R n F s J r headCap Y Cq DG : ℕ)
    (hDG : DG≤2^(exponent b R F s)) :
    DG^r<2^(packetWidth b R n F s J r headCap Y Cq) := by
  have h := Nat.pow_le_pow_left hDG r
  rw [← pow_mul] at h
  apply h.trans_lt
  apply Nat.pow_lt_pow_right (by decide)
  have hm := Nat.mul_le_mul_left (exponent b R F s) (show r≤r+1 by omega)
  unfold packetWidth
  omega

/-- A summary prefix adds at most Y common-denominator product numerators. -/
theorem summary_numerator_lt (b R n F s J r headCap Y Cq DG BG : ℕ)
    (hDG : DG≤2^(exponent b R F s)) (hBG : BG≤2^(exponent b R F s)) :
    Y*(productBase J DG BG headCap)^(2*r)<2^(packetWidth b R n F s J r headCap Y Cq) := by
  have hp := Nat.pow_le_pow_left (productBase_dyadic b R F s J headCap DG BG hDG hBG) (2*r)
  rw [← pow_mul] at hp
  have h := Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_two_pow_self (n:=Y))) hp
  rw [← pow_add] at h
  apply h.trans_lt
  apply Nat.pow_lt_pow_right (by decide)
  have hm := Nat.mul_le_mul_left (productExponent b R F s J headCap) (show 2*r≤2*r+4 by omega)
  unfold packetWidth
  omega

/-- Signed support prefixes add at most Cq summaries, retaining the SAME fibre denominator. -/
theorem support_numerator_lt (b R n F s J r headCap Y Cq DG BG : ℕ)
    (hDG : DG≤2^(exponent b R F s)) (hBG : BG≤2^(exponent b R F s)) :
    Cq*Y*(productBase J DG BG headCap)^(2*r)<2^(packetWidth b R n F s J r headCap Y Cq) := by
  have hp := Nat.pow_le_pow_left (productBase_dyadic b R F s J headCap DG BG hDG hBG) (2*r)
  rw [← pow_mul] at hp
  have hc := Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_two_pow_self (n:=Cq)))
    (Nat.le_of_lt (Nat.lt_two_pow_self (n:=Y)))
  rw [← pow_add] at hc
  have h := Nat.mul_le_mul hc hp
  rw [← pow_add] at h
  apply h.trans_lt
  apply Nat.pow_lt_pow_right (by decide)
  have hm := Nat.mul_le_mul_left (productExponent b R F s J headCap) (show 2*r≤2*r+4 by omega)
  unfold packetWidth
  omega

end RiemannGaussian.SemiprimeWordPacketWidth
