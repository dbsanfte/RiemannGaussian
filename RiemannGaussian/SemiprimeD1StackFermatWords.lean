/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroEntryExecution
import RiemannGaussian.SemiprimeSourceCompactBits

/-! # Exact public Fermat constant word specifications
The word patterns below specify the output of a physical counter-driven
producer. They do not execute native power/negation/modulo in that producer.
The legacy normalizer bridge is explicitly restricted to positive input width.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackFermatWords
open SemiprimeBitArithmetic SemiprimeSourceCompactBits
open SemiprimeMacroParameters SemiprimeMacroFermatNetwork SemiprimeMacroEntryExecution

/-- Proof-side modulus bytes, with low/high one and the actual radius gap. -/
def modulusWord (R:ℕ) : List Bool := true::(List.replicate (R-1) false++[true])
/-- Proof-side canonical inverse bytes; the physical producer consumes cached R/E markers. -/
def normalizerWord (R E:ℕ) : List Bool := true::(List.replicate (R-E-1) false++List.replicate E true)

/-- Low zero cells shift an actual little-endian magnitude. -/
theorem zeros_value (n:ℕ) (bits:List Bool) :
    bitValue (List.replicate n false++bits)=2^n*bitValue bits := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,bitValue,bitNat,Bool.false_eq_true,ite_false,
      Nat.zero_add,ih,pow_succ]
    ring

/-- All-one cells have their exact power-minus-one value, without a subtraction assumption. -/
theorem ones_value (n:ℕ) : bitValue (List.replicate n true)+1=2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,bitValue,bitNat,ite_true,pow_succ]
    omega

/-- Modulus bytes have their original Fermat value for the actual nonempty radius. -/
theorem modulus_value (R:ℕ) (hR:0<R) : bitValue (modulusWord R)=2^R+1 := by
  have hp:2^(R-1)*2=(2:ℕ)^R:=by rw [←pow_succ,Nat.sub_add_cancel hR]
  simp only [modulusWord,bitValue,bitNat,ite_true,zeros_value,Nat.mul_one,Nat.mul_zero,Nat.add_zero]
  omega

/-- Every normalizer word's raw signed cancellation is exact, not a final-value height premise. -/
theorem normalizer_sum (R E:ℕ) (hRE:E+1≤R) :
    bitValue (normalizerWord R E)+2^(R-E)=2^R+1 := by
  have ht:=ones_value E
  have hi:(R-E-1)+1+E=R:=by omega
  have hj:(R-E-1)+1=R-E:=by omega
  have hp:2*(2:ℕ)^(R-E-1)*(2:ℕ)^E=(2:ℕ)^R:=by
    rw [←pow_succ',←pow_add,hi]
  have hq:2*(2:ℕ)^(R-E-1)=(2:ℕ)^(R-E):=by rw [←pow_succ',hj]
  have hm:2*(2:ℕ)^(R-E-1)*(bitValue (List.replicate E true)+1)=(2:ℕ)^R:=by
    rw [ht]
    exact hp
  simp only [normalizerWord,bitValue,bitNat,ite_true,zeros_value]
  nlinarith [hm]

/-- The physical normalizer pattern is exactly the canonical negative dyadic residue. -/
theorem normalizer_value (R E:ℕ) (hRE:E+1≤R) :
    bitValue (normalizerWord R E)=2^R+1-2^(R-E) := by
  have h:=normalizer_sum R E hRE
  omega

/-- Nonempty compact suffix makes every actual front compact. -/
theorem compact_prefix (front tail:List Bool) (ht:Compact tail) (hne:tail≠[]) : Compact (front++tail) := by
  induction front with
  | nil => exact ht
  | cons bit front ih =>
    refine ⟨ih,?_⟩
    intro hz
    exact False.elim (hne (List.append_eq_nil_iff.mp hz).2)

/-- Actual all-one suffixes are compact, including the empty zero. -/
theorem ones_compact (E:ℕ) : Compact (List.replicate E true) := by
  induction E with
  | zero => trivial
  | succ E ih => exact ⟨ih,fun _=>rfl⟩

/-- The modulus has a literal high one; no output canonicality advice is needed. -/
theorem modulus_compact (R:ℕ) : Compact (modulusWord R) := by
  exact compact_prefix (true::List.replicate (R-1) false) [true] (by simp [Compact]) (by simp)

/-- Positive exponent gives the actual high-one suffix of the inverse. -/
theorem normalizer_compact (R E:ℕ) (hE:0<E) : Compact (normalizerWord R E) := by
  apply compact_prefix (true::List.replicate (R-E-1) false) (List.replicate E true) (ones_compact E)
  intro hz
  have h:=congrArg List.length hz
  simp only [List.length_replicate,List.length_nil] at h
  omega

/-- Original radius licenses exact output widths. -/
theorem modulus_length (R:ℕ) (hR:0<R) : (modulusWord R).length=R+1 := by
  simp only [modulusWord,List.length_cons,List.length_append,List.length_replicate,List.length_nil]
  omega

/-- Original exponent/radius relation licenses every low/high block boundary. -/
theorem normalizer_length (R E:ℕ) (hRE:E+1≤R) : (normalizerWord R E).length=R := by
  simp only [normalizerWord,List.length_cons,List.length_append,List.length_replicate]
  omega

/-- Canonical value of the original negative power, before specializing its public depth. -/
theorem negative_power_value (R E:ℕ) :
    (-(2:ZMod (2^R+1))^(R-E)).val=2^R+1-2^(R-E) := by
  let : NeZero ((2:ℕ)^R+1):=⟨Nat.succ_ne_zero _⟩
  have hpow:(2:ℕ)^(R-E)<2^R+1:=lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le R E)) (by omega)
  have hv:(((2:ℕ)^(R-E):ℕ):ZMod (2^R+1)).val=(2:ℕ)^(R-E):=ZMod.val_natCast_of_lt hpow
  have hn:((((2:ℕ)^(R-E):ℕ):ZMod (2^R+1)))≠0:=by
    intro h
    have he:=congrArg ZMod.val h
    rw [hv,ZMod.val_zero] at he
    have hp:0<(2:ℕ)^(R-E):=pow_pos (by decide) _
    omega
  have he:(2:ZMod (2^R+1))^(R-E)=(((2:ℕ)^(R-E):ℕ):ZMod (2^R+1)):=by simp
  rw [he,ZMod.neg_val,ite_eq_right hn,hv]

/-- Positive original width identifies the SAME legacy normalizer and ring.
At ell=0, depth=0 has macroLength2 whereas the metadata radius is1; no equality is claimed there. -/
theorem original_normalizer (ell:ℕ) (hL:0<ell) :
    bitValue (normalizerWord (transformLength ell) (transformExponent ell))=
      (explicitNormalizer (macroDepth ell)).val := by
  have hE:1≤transformExponent ell:=by have h:=transformExponent_ge_two hL;omega
  have hR:transformExponent ell+1≤transformLength ell:=by
    exact Nat.succ_le_of_lt (Nat.lt_two_pow_self)
  have hd:macroDepth ell+1=transformExponent ell:=by
    simp only [macroDepth]
    omega
  rw [normalizer_value _ _ hR]
  change _ = (-(2:ZMod (2^(macroLength (macroDepth ell))+1))^
    (macroLength (macroDepth ell)-(macroDepth ell+1))).val
  rw [←transform_eq_macroLength hL,hd,negative_power_value]
end RiemannGaussian.SemiprimeD1StackFermatWords
