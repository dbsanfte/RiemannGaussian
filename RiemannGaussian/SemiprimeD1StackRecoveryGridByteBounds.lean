/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridEncoding
/-! # Physical-byte and multiplicity bounds for every original grid boundary
Only actual output byte widths/counts are used here. No legacy report clock is
transported. The true grid N and supplied physical W are paid by VALUE in the
whole source resource, while numerical coefficients remain binary words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridByteBounds
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridEncoding
namespace Old
export SemiprimeD1RecoveryGridBits (loop acquire copies_words)
export SemiprimeD1RecoveryPowerBits (power)
end Old
/-- Every actual original operation has precisely the physically fitted numerator/denominator widths. -/
theorem operation_lengths (op:SemiprimeRationalBits.Operation) (x y:SemiprimeRationalBits.RationalWord) (width:List Bool) :
    (SemiprimeRationalBits.executeOperation op x y width).word.numerator.magnitude.length=width.length ∧
    (SemiprimeRationalBits.executeOperation op x y width).word.denominator.length=width.length:=
  SemiprimeRationalBits.fitRationalBits_width (SemiprimeRationalBits.rawOperation op x y).word width
/-- Literal zero-exponent oneWord is charged, including the exceptional W0 case. -/
theorem power_lengths (width:List Bool) (x:SemiprimeRationalBits.RationalWord) (n:Nat) :
    (Old.power width x n).word.numerator.magnitude.length ≤ width.length+1 ∧
    (Old.power width x n).word.denominator.length ≤ width.length+1:=by
  cases n with
  | zero=>simp [Old.power,SemiprimeJetBits.oneWord]
  | succ n=>
    have h:=operation_lengths .mul (Old.power width x n).word x width
    exact ⟨h.1.le.trans (by omega),h.2.le.trans (by omega)⟩
/-- Height and all multiplicities have bounded unary VALUE, acquired from original physical metadata. -/
theorem height_product (M u:Nat) :SemiprimeD1TaperedLoss.height M u*u ≤3*M+u:=by
  have h:=Nat.div_mul_le_self (3*M+u-1) u
  unfold SemiprimeD1TaperedLoss.height
  omega
/-- Zero levels require no advised positive divisor or count; the exact original height is zero. -/
theorem height_zero (M:Nat) :SemiprimeD1TaperedLoss.height M 0=0:=by simp [SemiprimeD1TaperedLoss.height]
/-- Every actual bounded metadata quotient is at most its original paid marker numerator. -/
theorem height_le (M u:Nat) :SemiprimeD1TaperedLoss.height M u ≤3*M+u:=by
  have h:=Nat.div_le_self (3*M+u-1) u
  unfold SemiprimeD1TaperedLoss.height
  omega
/-- Exact raw grid signed products retain either literal base oneWord or physically fitted W words. -/
theorem loop_lengths (width:List Bool) (a h u t:Nat) (g:SemiprimeD1RecoveryWeightRun.Geometry)
    (center alpha node:SemiprimeRationalBits.RationalWord) (qs:List Nat) :
    (Old.loop width a h u t g center alpha node qs).numerator.numerator.magnitude.length ≤ width.length+1 ∧
    (Old.loop width a h u t g center alpha node qs).numerator.denominator.length ≤ width.length+1 ∧
    (Old.loop width a h u t g center alpha node qs).denominator.numerator.magnitude.length ≤ width.length+1 ∧
    (Old.loop width a h u t g center alpha node qs).denominator.denominator.length ≤ width.length+1 ∧
    ∀w∈(Old.loop width a h u t g center alpha node qs).slopes,
      w.numerator.magnitude.length=width.length ∧ w.denominator.length=width.length:=by
  induction qs with
  | nil=>simp [Old.loop,SemiprimeJetBits.oneWord]
  | cons q qs ih=>
    dsimp only [Old.loop]
    split
    · exact ih
    · refine ⟨?_,?_,?_,?_,?_⟩
      · exact (operation_lengths _ _ _ _).1.le.trans (by omega)
      · exact (operation_lengths _ _ _ _).2.le.trans (by omega)
      · exact (operation_lengths _ _ _ _).1.le.trans (by omega)
      · exact (operation_lengths _ _ _ _).2.le.trans (by omega)
      · intro w hw
        rw [Old.copies_words] at hw
        rcases List.mem_append.mp hw with hw|hw
        · have he: w=(SemiprimeRationalBits.executeOperation .mul alpha
              (SemiprimeRationalBits.executeOperation .inv
                (SemiprimeRationalBits.executeOperation .add node
                  (SemiprimeRationalBits.executeOperation .neg (SemiprimeD1RecoveryGridBits.index a q).word
                    (SemiprimeD1RecoveryGridBits.index a q).word width).word width).word
                (SemiprimeRationalBits.executeOperation .add node
                  (SemiprimeRationalBits.executeOperation .neg (SemiprimeD1RecoveryGridBits.index a q).word
                    (SemiprimeD1RecoveryGridBits.index a q).word width).word width).word width).word width).word:=
            (List.mem_replicate.mp hw).2
          subst w
          exact operation_lengths _ _ _ _
        · exact ih.2.2.2.2 w hw
/-- Original slope repetitions are bounded by actual visited index count times actual bounded multiplicity. -/
theorem loop_slope_count (width:List Bool) (a h u t:Nat) (g:SemiprimeD1RecoveryWeightRun.Geometry)
    (center alpha node:SemiprimeRationalBits.RationalWord) (qs:List Nat) :
    (Old.loop width a h u t g center alpha node qs).slopes.length ≤ qs.length*(h*u):=by
  induction qs with
  | nil=>simp [Old.loop]
  | cons q qs ih=>
    dsimp only [Old.loop]
    split
    · exact ih.trans (by simp only [List.length_cons];nlinarith)
    · rw [List.length_append,Old.copies_words,List.length_replicate]
      have hm:(SemiprimeD1RecoveryWeightRun.multiplicityRun g h u q).value ≤ h*u:=
        Nat.mul_le_mul_left h (Nat.sub_le _ _)
      simp only [List.length_cons]
      nlinarith
/-- Literal slope framing pays sign, every raw bit, both delimiters and vector tag. -/
theorem slopeRow_length (word:SemiprimeRationalBits.RationalWord) (tail:List Bool) :
    (slopeRow word tail).length=2*(word.numerator.magnitude.length+word.denominator.length)+5+tail.length:=by
  simp only [slopeRow,SemiprimeSourceHistogramKeyBits.frame_length,signed,List.length_cons]
  omega
/-- Whole chronological slope bytes are bounded from actual repeated field widths/counts, without copying accumulated tails. -/
theorem slopeTape_length (words:List SemiprimeRationalBits.RationalWord) (cap:Nat)
    (hw:∀w∈words,w.numerator.magnitude.length+w.denominator.length ≤ cap) :
    (slopeTape words).length ≤ words.length*(2*cap+5)+1:=by
  induction words with
  | nil=>simp [slopeTape]
  | cons w ws ih=>
    have hh:=hw w List.mem_cons_self
    have ht:=ih (fun x hx=>hw x (List.mem_cons_of_mem _ hx))
    change (slopeRow w (slopeTape ws)).length ≤_
    rw [slopeRow_length]
    simp only [List.length_cons]
    nlinarith
end RiemannGaussian.SemiprimeD1StackRecoveryGridByteBounds
