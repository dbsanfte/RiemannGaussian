/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TaperedLoss
import RiemannGaussian.SemiprimeD1WireKernelPaper

/-! # Original tapered Hermite grid scalar acquisition and exact raw valuation
The original node factors and taper are acquired, not supplied. The exact raw
valuation sum is proved; its level regrouping is deliberately not assumed.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetRecoveryGrid
open scoped BigOperators
open SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss

/-- Original grid indices except the zero node and the node being reconstructed. -/
def others (a t : ℕ) : Finset ℕ := ((Finset.range (size a)).erase (center a)).erase t

/-- Original tapered multiplicity at the signed grid point. -/
def nodeMultiplicity (a h u q : ℕ) : ℕ := multiplicity h u (padicValInt 2 (point a q))

/-- Actual D.9 scalar E_t(0), acquired by finite rational products. -/
def Ezero (a h u t : ℕ) : ℚ :=
  ∏ q∈others a t,(-(point a q:ℚ)/((point a t:ℚ)-(point a q:ℚ)))^nodeMultiplicity a h u q

/-- Original grid points equal zero exactly at the actual center index. -/
theorem point_zero_iff (a q : ℕ) : point a q=0 ↔ q=center a := by
  unfold point
  omega

/-- Distinct grid indices give distinct original signed grid points. -/
theorem point_sub_ne_zero (a t q : ℕ) (h : q≠t) : point a t-point a q≠0 := by
  unfold point
  omega

/-- Exact rational integer-coordinate valuation, including signed grid nodes. -/
theorem int_valuation (z : ℤ) : padicValRat 2 (z:ℚ)=(padicValInt 2 z:ℤ) := by
  simp [padicValRat]

private theorem valuation_product (s : Finset ℕ) (f : ℕ→ℚ)
    (hf : ∀ q∈s,f q≠0) : padicValRat 2 (∏ q∈s,f q)=∑ q∈s,padicValRat 2 (f q) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hn : (∏ q∈s,f q)≠0 := Finset.prod_ne_zero_iff.mpr
      (fun q hq => hf q (Finset.mem_insert_of_mem hq))
    simp only [Finset.prod_insert ha,Finset.sum_insert ha,
      padicValRat.mul (hf a (by simp)) hn,ih (fun q hq => hf q (Finset.mem_insert_of_mem hq))]

/-- No original E_t0 factor vanishes; inactive nodes simply have exponent0. -/
theorem Ezero_ne_zero (a h u t : ℕ) : Ezero a h u t≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  have hqc : q≠center a := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
  have hqt : q≠t := (Finset.mem_erase.mp hq).1
  have hqz : (point a q:ℚ)≠0 := by exact_mod_cast (not_congr (point_zero_iff a q)).mpr hqc
  have hd : (point a t:ℚ)-(point a q:ℚ)≠0 := by exact_mod_cast point_sub_ne_zero a t q hqt
  exact pow_ne_zero _ (div_ne_zero (neg_ne_zero.mpr hqz) hd)

/-- Exact original-grid raw expression whose regrouping gives D.10. -/
def rawValuation (a h u t : ℕ) : ℤ :=
  ∑ q∈others a t,(nodeMultiplicity a h u q:ℤ)*
    ((padicValInt 2 (point a q):ℤ)-(padicValInt 2 (point a t-point a q):ℤ))

/-- ORIGINAL E_t0 valuation from its actual acquired finite product, not an oracle. -/
theorem Ezero_valuation (a h u t : ℕ) : padicValRat 2 (Ezero a h u t)=rawValuation a h u t := by
  unfold Ezero
  rw [valuation_product]
  · unfold rawValuation
    apply Finset.sum_congr rfl
    intro q hq
    have hqc : q≠center a := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
    have hqt : q≠t := (Finset.mem_erase.mp hq).1
    have hqz : (point a q:ℚ)≠0 := by exact_mod_cast (not_congr (point_zero_iff a q)).mpr hqc
    have hd : (point a t:ℚ)-(point a q:ℚ)≠0 := by exact_mod_cast point_sub_ne_zero a t q hqt
    rw [padicValRat.pow,padicValRat.div (neg_ne_zero.mpr hqz) hd,padicValRat.neg,int_valuation]
    have he : (point a t:ℚ)-(point a q:ℚ)=((point a t-point a q:ℤ):ℚ) := by push_cast;rfl
    rw [he,int_valuation]
  · intro q hq
    have hqc : q≠center a := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
    have hqt : q≠t := (Finset.mem_erase.mp hq).1
    have hqz : (point a q:ℚ)≠0 := by exact_mod_cast (not_congr (point_zero_iff a q)).mpr hqc
    have hd : (point a t:ℚ)-(point a q:ℚ)≠0 := by exact_mod_cast point_sub_ne_zero a t q hqt
    exact pow_ne_zero _ (div_ne_zero (neg_ne_zero.mpr hqz) hd)

/-- Actual original-schedule specialization; the still-needed finite regrouping is
rawValuation=levelValuation with n=a-i for nonzero node of valuation i. -/
theorem original_Ezero_valuation (a M u t : ℕ) :
    padicValRat 2 (Ezero a (height M u) u t)=rawValuation a (height M u) u t :=
  Ezero_valuation _ _ _ _

end RiemannGaussian.SemiprimeD1JetRecoveryGrid
