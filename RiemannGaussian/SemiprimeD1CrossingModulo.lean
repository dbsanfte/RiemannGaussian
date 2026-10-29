/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1CrossingResidue

/-! # Actual scalar finite D.12 expansion modulo 2^p
The proof clears only odd denominators. Auxiliary fraction sums are proof
witnesses, not a proposed runtime denominator-product algorithm.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1CrossingModulo
open scoped BigOperators
open SemiprimeD1WireKernelFactors SemiprimeD1WireKernelEntry
  SemiprimeD1WireKernelOriginal SemiprimeD1CrossingCoefficient
  SemiprimeD1CrossingExpansion SemiprimeD1CrossingOriginal SemiprimeD1CrossingResidue

/-- Integer-fraction addition used to witness a finite odd-localized sum. -/
def fractionAdd (a b : Coefficient) : Coefficient :=
  ⟨a.numerator*b.denominator+b.numerator*a.denominator,a.denominator*b.denominator⟩

/-- Addition of acquired odd fractions agrees with rational addition. -/
theorem fractionAdd_value (a b : Coefficient) (ha : Odd a.denominator)
    (hb : Odd b.denominator) : value (fractionAdd a b)=value a+value b := by
  have han : a.denominator≠0 := by intro h;rw [h] at ha;simp at ha
  have hbn : b.denominator≠0 := by intro h;rw [h] at hb;simp at hb
  have haq : (a.denominator:ℚ)≠0 := by exact_mod_cast han
  have hbq : (b.denominator:ℚ)≠0 := by exact_mod_cast hbn
  unfold value fractionAdd
  simp only [Int.cast_add,Int.cast_mul]
  field_simp

/-- Exact finite odd-fraction addition respects actual unit-inverse residues. -/
theorem fractionAdd_residue (p : ℕ) (a b : Coefficient)
    (ha : Odd a.denominator) (hb : Odd b.denominator) :
    residue p (fractionAdd a b)=residue p a+residue p b := by
  apply (odd_unit _ (ha.mul hb) p).mul_left_cancel
  change ((fractionAdd a b).denominator:ZMod (2^p))*_= _
  rw [residue_denominator p (fractionAdd a b) (ha.mul hb)]
  simp only [fractionAdd,Int.cast_add,Int.cast_mul]
  calc
    _ = (b.denominator:ZMod (2^p))*((a.denominator:ZMod (2^p))*residue p a)+
      (a.denominator:ZMod (2^p))*((b.denominator:ZMod (2^p))*residue p b) := by
        rw [residue_denominator p a ha,residue_denominator p b hb]
        ring
    _ = _ := by ring

/-- Finite odd-localized rational sums have consistent actual modular evaluations. -/
theorem finite_sum_witness {ι : Type*} (s : Finset ι) (f : ι → Coefficient)
    (p : ℕ) (hf : ∀ b∈s,Odd (f b).denominator) :
    ∃ c : Coefficient,Odd c.denominator ∧ value c=(∑ b∈s,value (f b)) ∧
      residue p c=∑ b∈s,residue p (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⟨0,1⟩,by decide,by simp [value],by simp [residue]⟩
  | @insert a s ha ih =>
    obtain ⟨c,hc,hv,hr⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    refine ⟨fractionAdd (f a) c,(hf a (by simp)).mul hc,?_,?_⟩
    · rw [fractionAdd_value (f a) c (hf a (by simp)) hc,hv,Finset.sum_insert ha]
    · rw [fractionAdd_residue p (f a) c (hf a (by simp)) hc,hr,Finset.sum_insert ha]

/-- Multiplying an acquired fraction by an integer retains the same odd denominator. -/
def fractionScale (a : Coefficient) (j : ℤ) : Coefficient := ⟨a.numerator*j,a.denominator⟩

/-- Scaling consistency is an exact identity over the odd-localized rationals. -/
theorem fractionScale_value (a : Coefficient) (j : ℤ) :
    value (fractionScale a j)=value a*(j:ℚ) := by
  simp only [value,fractionScale,Int.cast_mul]
  ring

/-- Scaling consistency uses actual integer cast and actual unit inverse modulo 2^p. -/
theorem fractionScale_residue (p : ℕ) (a : Coefficient) (j : ℤ) :
    residue p (fractionScale a j)=residue p a*(j:ZMod (2^p)) := by
  simp only [residue,fractionScale,Int.cast_mul]
  ring

/-- ORIGINAL scalar kernel D.12, with exactly b+1<p and positive tile powers.
Every mode and inverse is acquired from the original grid data. -/
theorem original_modulo (k center i j d tile p : ℕ) (z : ℤ)
    (hc : center<2^k) (hj : j<2^k) (hd : d<2^k) (htile : d+2^(i+1)*tile<2^k)
    (hi : i<k) (hne : d≠j) (hv : padicValInt 2 (difference j d)≤ i) (hp : 0<p) :
    evaluate p (SemiprimeD1WireKernelEntry.acquire k center j (d+2^(i+1)*tile)) (z:ZMod (2^p))=
      ∑ b∈Finset.range (p-1),
        residue p (SemiprimeD1CrossingCoefficient.acquire k center i j d b z)*
          (tile:ZMod (2^p))^b := by
  let f := fun b => fractionScale (SemiprimeD1CrossingCoefficient.acquire k center i j d b z) ((tile:ℤ)^b)
  obtain ⟨c,hco,hcv,hcr⟩ := finite_sum_witness (Finset.range (p-1)) f p
    (fun b _ => acquire_odd k center i j d b z hc hj hd hne)
  have he := expansion k center i j d (p-1) z tile hc hj hd hne hv
  have hfo : Odd (remainder k center i j d (p-1) z tile).denominator :=
    (target_remainder_odd k center i j d (p-1) z tile hc hj hd hne hv).2
  have heq : value (target k center i j d z tile)=
      value (fractionAdd c (remainder k center i j d (p-1) z tile)) := by
    rw [fractionAdd_value c _ hco hfo,hcv]
    simpa only [f,fractionScale_value,Int.cast_pow,Int.cast_natCast] using he
  have hz := residue_eq_of_value_eq p (target k center i j d z tile)
    (fractionAdd c (remainder k center i j d (p-1) z tile))
    (target_remainder_odd k center i j d (p-1) z tile hc hj hd hne hv).1 (hco.mul hfo) heq
  rw [fractionAdd_residue p c _ hco hfo,
    (strict_remainder_zero k center i j d tile p z hc hj hd hi hne hv hp).2,
    add_zero,hcr] at hz
  rw [← target_residue_original k center i j d tile p z hc hj hd htile hne hv,hz]
  apply Finset.sum_congr rfl
  intro b _
  simp only [f,fractionScale_residue,Int.cast_pow,Int.cast_natCast]

end RiemannGaussian.SemiprimeD1CrossingModulo
