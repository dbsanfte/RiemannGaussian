/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceOffsetInputsCore

/-! # Original-dimension scale construction by actual addressed word operations
The literal program takes only original natural words, never x/y advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceOffsetInputsScales
open SemiprimeRationalBits SemiprimeBitArithmetic SemiprimeSourceProgramBits
open SemiprimeJetArrayHeight

/-- Literal four-bit addresses used by this initializer program and its seven reads. -/
def addr : ℕ → List Bool
  | 0 => [false,false,false,false]
  | 1 => [true,false,false,false]
  | 2 => [false,true,false,false]
  | 3 => [true,true,false,false]
  | 4 => [false,false,true,false]
  | 7 => [true,true,true,false]
  | 8 => [false,false,false,true]
  | 9 => [true,false,false,true]
  | 10 => [false,true,false,true]
  | 11 => [true,true,false,true]
  | 13 => [true,false,true,true]
  | _ => [false,false,false,false]

/-- Eight actual operations compute eps*M/U and n/(2r) from natural inputs. -/
def code : List Instruction :=
  [⟨.mul,addr 2,addr 4⟩,⟨.inv,addr 0,addr 0⟩,⟨.mul,addr 0,addr 2⟩,
   ⟨.inv,addr 8,addr 8⟩,⟨.mul,addr 1,addr 0⟩,⟨.add,addr 7,addr 7⟩,
   ⟨.inv,addr 0,addr 0⟩,⟨.mul,addr 8,addr 0⟩]

/-- Original integer values, not supplied scales. -/
def inputValues (M n r Q lam U : ℕ) : List ℚ := [M,n,r,Q,lam,U]

/-- The literal desired output register indices, all paid by the caller's scans. -/
def selection : List ℕ := [3,0,8,9,10,11,13]

/-- Exact semantic selection after the SAME physical initializer instructions. -/
theorem evaluate_values (M n r Q lam U : ℕ) :
    selection.map (fun i => ((evaluate code (inputValues M n r Q lam U))[i]?).getD 0)=
      [(1/((r*lam:ℕ):ℚ))*(M:ℚ)/(U:ℚ),(n:ℚ)/(2*(r:ℚ)),M,n,r,Q,U] := by
  simp [selection,evaluate,code,Instruction.value,Operation.value,addr,inputValues,bitValue,bitNat,
    div_eq_mul_inv,Nat.cast_mul,two_mul]

/-- Original dimensions bound all scale-construction numerators and denominators. -/
def parameterSum (M n r Q lam U : ℕ) : ℕ := M+n+r+Q+lam+U+r*lam+2*r+2

/-- A positive common working template, larger than the final offset template. -/
def workingWidth (M n r Q lam U finalWidth : ℕ) : ℕ :=
  finalWidth+(parameterSum M n r Q lam U)^2+parameterSum M n r Q lam U+3

/-- All eight actual instruction fits follow from ORIGINAL integer dimensions. -/
theorem code_safe (M n r Q lam U W0 : ℕ) (hr : 0<r) (hlam : 0<lam) (hU : 0<U) :
    Safe (workingWidth M n r Q lam U W0) code (inputValues M n r Q lam U) := by
  let P := parameterSum M n r Q lam U
  let C := P^2+P+1
  let W := workingWidth M n r Q lam U W0
  have hP : 1≤P := by dsimp [P,parameterSum];omega
  have hM : M≤P := by dsimp [P,parameterSum];omega
  have hn : n≤P := by dsimp [P,parameterSum];omega
  have hrl : r*lam≤P := by dsimp [P,parameterSum];omega
  have hu : U≤P := by dsimp [P,parameterSum];omega
  have h2r : 2*r≤P := by dsimp [P,parameterSum];omega
  have hpc : P≤C := by dsimp [C];omega
  have hone : 1≤C := hP.trans hpc
  have hcap : C<2^W := by
    have hc : C<W := by dsimp [P,C,W,workingWidth];omega
    exact hc.trans (Nat.lt_two_pow_self)
  have fit {q : ℚ} {d B : ℕ} (hd : 0<d) (hq : Representation q d B)
      (hdc : d≤C) (hbc : B≤C) : Fits q W :=
    fits_of_representation hd hq (hbc.trans_lt hcap) (hdc.trans_lt hcap)
  have natrep (c : ℕ) : Representation (c:ℚ) 1 c := ⟨(c:ℤ),by simp,by simp⟩
  have invrep (c : ℕ) : Representation ((c:ℚ)⁻¹) c 1 := ⟨1,by simp,by simp⟩
  have hfirst : Fits ((r:ℚ)*(lam:ℚ)) W := by
    simpa only [Nat.cast_mul] using fit (by decide) (natrep (r*lam)) hone (hrl.trans hpc)
  have heps : Fits (((r:ℚ)*(lam:ℚ))⁻¹) W := by
    simpa only [Nat.cast_mul] using fit (Nat.mul_pos hr hlam) (invrep (r*lam)) (hrl.trans hpc) hone
  have hmrep : Representation (((r*lam:ℕ):ℚ)⁻¹*(M:ℚ)) (r*lam) M := by
    simpa only [Nat.mul_one,Nat.one_mul] using representation_mul (invrep (r*lam)) (natrep M)
  have hscaled : Fits ((((r:ℚ)*(lam:ℚ))⁻¹)*(M:ℚ)) W := by
    simpa only [Nat.cast_mul] using fit (Nat.mul_pos hr hlam) hmrep (hrl.trans hpc) (hM.trans hpc)
  have hinvu : Fits ((U:ℚ)⁻¹) W := fit hU (invrep U) (hu.trans hpc) hone
  have hxrep := representation_mul hmrep (invrep U)
  have hdenx : (r*lam)*U≤C := by
    have hm := Nat.mul_le_mul hrl hu
    dsimp [C]
    nlinarith
  have hx : Fits (((r:ℚ)*(lam:ℚ))⁻¹*(M:ℚ)*(U:ℚ)⁻¹) W := by
    have hh := fit (Nat.mul_pos (Nat.mul_pos hr hlam) hU) hxrep hdenx (by simpa using hM.trans hpc)
    simpa only [Nat.cast_mul] using hh
  have htwo : Fits ((r:ℚ)+(r:ℚ)) W := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,two_mul,Nat.cast_add] using fit (by decide) (natrep (2*r)) hone (h2r.trans hpc)
  have hinvtwo : Fits (((r:ℚ)+(r:ℚ))⁻¹) W := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,two_mul,Nat.cast_add] using fit (Nat.mul_pos (by decide) hr)
      (invrep (2*r)) (h2r.trans hpc) hone
  have hyrep : Representation ((n:ℚ)/(2*(r:ℚ))) (2*r) n := ⟨(n:ℤ),by simp,by simp⟩
  have hy : Fits ((n:ℚ)*((r:ℚ)+(r:ℚ))⁻¹) W := by
    simpa only [div_eq_mul_inv,two_mul] using fit (Nat.mul_pos (by decide) hr) hyrep (h2r.trans hpc) (hn.trans hpc)
  change Safe W code (inputValues M n r Q lam U)
  simp only [code,Safe,Instruction.value,Operation.value,addr,inputValues,bitValue,bitNat,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Bool.false_eq_true,ite_false,ite_true,
    Nat.zero_add,Nat.mul_zero,Nat.mul_one,Nat.add_zero,Nat.reduceAdd,Nat.reduceMul]
  exact ⟨hfirst,heps,hscaled,hinvu,hx,htwo,hinvtwo,hy,trivial⟩

end RiemannGaussian.SemiprimeSourceOffsetInputsScales
