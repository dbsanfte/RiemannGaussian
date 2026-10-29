/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAffineJetBits
import RiemannGaussian.SemiprimeD1RecoveryWeightRunState

/-! # General-slope correctness of the existing physical affine-array builder
D.5 slopes can exceed one. The unit coefficient therefore requires d<=B;
original common-denominator slopes discharge this internally with B=d*N.
No frozen arithmetic runtime is replaced or altered.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryAffineBits
open SemiprimeRationalBits SemiprimeJetBits SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeHermiteArrayHeight SemiprimeAffineJetBits
open SemiprimeLocalExecutionHeight

/-- Constant-one and arbitrary bounded slope coefficients have a common representation. -/
theorem affine_representation (c : ℚ) (d B : ℕ) (hd : 0 < d) (hB : d ≤ B)
    (hc : Representation c d B) (k : ℕ) :
    Representation (coefficient (affineArray c) k) d B := by
  cases k with
  | zero =>
    simpa [coefficient,affineArray] using representation_mono (representation_one d hd) hB
  | succ k =>
    cases k with
    | zero => simpa [coefficient,affineArray] using hc
    | succ k =>
      rw [coefficient_zero (by simp [affineArray])]
      exact representation_mono (representation_zero d) (Nat.zero_le _)

/-- Every native affine-array suffix uses one product denominator and an
explicit numerator cap, allowing slopes of magnitude greater than one. -/
theorem native_representation (J d B : ℕ) (hd : 0 < d) (hB : d ≤ B) (cs : List ℚ)
    (hc : ∀c∈cs,Representation c d B) (k : ℕ) (hk : k < J) :
    Representation (coefficient (buildAffine J cs).coefficients k) (d^cs.length) ((J*B)^cs.length) := by
  induction cs generalizing k with
  | nil =>
    change Representation (coefficient #[1] k) 1 1
    cases k with
    | zero => simpa [coefficient] using representation_one 1 (by decide)
    | succ k =>
      rw [coefficient_zero (by simp)]
      exact representation_mono (representation_zero 1) (by decide)
  | cons c cs ih =>
    have hm:=multiply_representation (buildAffine J cs).coefficients (affineArray c)
      (d^cs.length) d ((J*B)^cs.length) B J
      (fun i hi => ih (fun z hz => hc z (List.mem_cons_of_mem c hz)) i hi)
      (fun i _ => affine_representation c d B hd hB (hc c List.mem_cons_self) i) k hk
    simpa only [buildAffine,List.length_cons,pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hm

/-- SAME physical affine runtime, now correct for arbitrary original bounded
slopes, with every intermediate multiplication capacity derived numerically. -/
theorem build_correct (template : List Bool) (b J d B : ℕ) (cs : List RationalWord)
    (hd : 0 < d) (hdB : d ≤ B) (hdb : d ≤ 2^b) (hBb : B ≤ 2^b) (hJb : J ≤ 2^b)
    (hwidth : width b cs.length ≤ template.length)
    (hc : ∀c∈cs,c.Valid ∧ Representation c.value d B) :
    decode (build template J cs).words=(buildAffine J (cs.map RationalWord.value)).coefficients ∧
      Valid (build template J cs).words ∧
      ArrayBound (decode (build template J cs).words) J (d^cs.length) ((J*B)^cs.length) := by
  induction cs with
  | nil =>
    refine ⟨by simp [build,decode,buildAffine],?_,?_⟩
    · intro i hi
      have hi' : i < 1 := hi
      have he : i=0 := by omega
      subst i
      exact oneWord_valid
    · intro i hi
      simpa [build,decode,buildAffine] using native_representation J d B hd hdB [] (by simp) i hi
  | cons c cs ih =>
    have hw : width b cs.length ≤ template.length := by
      unfold width at hwidth ⊢
      simp only [List.length_cons] at hwidth
      nlinarith only [hwidth]
    have hs:=ih hw (fun z hz => hc z (List.mem_cons_of_mem c hz))
    have hv:=hc c List.mem_cons_self
    have hfD:=powers_fit b J d (c::cs).length template.length hdb hJb hwidth
    have hfB:=powers_fit b J B (c::cs).length template.length hBb hJb hwidth
    have hden : d^cs.length*d < 2^template.length := by simpa only [List.length_cons,pow_succ] using hfD.1
    have hnum : J*(J*B)^cs.length*B < 2^template.length := by
      have he : J*(J*B)^cs.length*B=(J*B)^(cs.length+1) := by rw [pow_succ]; ring
      rw [he]
      exact hfB.2
    have hm:=multiplyBits_correct template (build template J cs).words (affine c)
      J (d^cs.length) d ((J*B)^cs.length) B hs.2.1 (affine_valid c hv.1)
      (pow_pos hd _) hd hden hnum hs.2.2 (by
        intro i _
        rw [affine_decode]
        exact affine_representation c.value d B hd hdB hv.2 i)
    have heq : decode (multiplyBits template (build template J cs).words (affine c) J).words=
        (multiply (decode (build template J cs).words) (decode (affine c)) J).coefficients := by
      apply SemiprimeCorrectedPortBits.array_eq_of_coeff J
      · simp only [decode_size,multiplyBits_size]
      · exact multiply_size _ _ _
      · exact hm.1
    have hout : decode (build template J (c::cs)).words=
        (buildAffine J ((c::cs).map RationalWord.value)).coefficients := by
      change decode (multiplyBits template (build template J cs).words (affine c) J).words=_
      rw [heq,hs.1,affine_decode]
      rfl
    refine ⟨hout,hm.2,?_⟩
    intro i hi
    rw [hout]
    have hr:=native_representation J d B hd hdB ((c::cs).map RationalWord.value) (by
      intro q hq
      obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hq
      exact (hc z hz).2) i hi
    simpa only [List.length_map] using hr

/-- Each actual canonical slope denominator divides the actual list product. -/
theorem denominator_dvd (cs : List ℚ) (c : ℚ) (hc : c∈cs) :
    c.den ∣ SemiprimeD1HermiteDenominatorHeight.commonDenominator cs := by
  exact List.dvd_prod (List.mem_map.mpr ⟨c,hc,rfl⟩)

/-- Actual canonical source slopes homogenize over one list denominator, without
asking for scaled numerator answers or pretending all slopes have magnitude<=1. -/
theorem slope_common_representation (cs : List ℚ) (N : ℕ) (c : ℚ) (hc : c∈cs)
    (hnum : c.num.natAbs ≤ N) :
    Representation c (SemiprimeD1HermiteDenominatorHeight.commonDenominator cs)
      (SemiprimeD1HermiteDenominatorHeight.commonDenominator cs*N) := by
  let D:=SemiprimeD1HermiteDenominatorHeight.commonDenominator cs
  have hd:=SemiprimeD1HermiteDenominatorHeight.commonDenominator_pos cs
  have hdiv : c.den ∣ D := denominator_dvd cs c hc
  have he : 0 < D/c.den := Nat.div_pos (Nat.le_of_dvd hd hdiv) c.den_pos
  have hrep : Representation c c.den N := ⟨c.num,(Rat.num_div_den c).symm,hnum⟩
  have hm:=representation_mul hrep (representation_one (D/c.den) he)
  simp only [mul_one,Nat.mul_div_cancel' hdiv] at hm
  apply representation_mono hm
  have hle : D/c.den ≤ D := Nat.div_le_self _ _
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left N hle

end RiemannGaussian.SemiprimeD1RecoveryAffineBits
