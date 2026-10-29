/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryResidue

/-! # Original local cardinal common denominators and actual inverse heights
The denominator is the product of ACTUAL canonical slope denominators. Variable
factor denominators are multiplied once, rather than an exponentially iterated
recurrence-height estimate. Native rational metadata/cost lowering is separate.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HermiteDenominatorHeight
open scoped BigOperators
open SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeHermiteArrayHeight
  SemiprimeD1JetRecoveryWeights SemiprimeD1JetRecoveryGrid SemiprimeD1TaperedLoss
  SemiprimeD1WireKernelOriginal SemiprimeD1WireKernelFactors

/-- Actual common denominator of a finite slope list, acquired from canonical rational data. -/
def commonDenominator (cs : List ℚ) : ℕ := (cs.map Rat.den).prod

/-- The actual acquired denominator is strictly positive. -/
theorem commonDenominator_pos (cs : List ℚ) : 0<commonDenominator cs := by
  induction cs with
  | nil => simp [commonDenominator]
  | cons c cs ih => simpa only [commonDenominator,List.map_cons,List.prod_cons] using Nat.mul_pos c.den_pos ih

/-- Literal raw signed integer ratio has a positive-denominator representation
before any rational gcd normalization. -/
theorem int_ratio_representation (n d : ℤ) :
    Representation ((n:ℚ)/(d:ℚ)) d.natAbs n.natAbs := by
  by_cases hs : 0≤d
  · have he : (d.natAbs:ℤ)=d := by rw [Int.natCast_natAbs,abs_of_nonneg hs]
    have heq : (d.natAbs:ℚ)=(d:ℚ) := by
      simpa only [Int.cast_natCast] using congrArg (fun x:ℤ => (x:ℚ)) he
    exact ⟨n,by rw [heq],le_rfl⟩
  · have he : (d.natAbs:ℤ)=-d := by rw [Int.natCast_natAbs,abs_of_neg (by omega)]
    have heq : (d.natAbs:ℚ)=-(d:ℚ) := by
      simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun x:ℤ => (x:ℚ)) he
    refine ⟨-n,?_,by simpa only [Int.natAbs_neg] using (le_rfl : n.natAbs≤n.natAbs)⟩
    simp only [Int.cast_neg,heq,neg_div_neg_eq]

/-- One actual slope array has its own canonical denominator and an original numerator cap. -/
theorem affine_representation (c : ℚ) (N : ℕ) (hden : c.den≤N) (hnum : c.num.natAbs≤N) (k : ℕ) :
    Representation (coefficient (affineArray c) k) c.den N := by
  cases k with
  | zero =>
    apply representation_mono (by simpa [coefficient,affineArray] using representation_one c.den c.den_pos)
    exact hden
  | succ k =>
    cases k with
    | zero =>
      refine ⟨c.num,?_,hnum⟩
      simpa [coefficient,affineArray] using (Rat.num_div_den c).symm
    | succ k =>
      rw [coefficient_zero (by simp [affineArray])]
      exact representation_mono (representation_zero c.den) (Nat.zero_le _)

/-- ACTUAL affine builder output uses ONE product denominator and an explicit
power numerator cap, with no source coefficient answer. -/
theorem buildAffine_common_representation (J N : ℕ) (cs : List ℚ)
    (hc : ∀c∈cs,c.den≤N ∧ c.num.natAbs≤N) (k : ℕ) (hk : k<J) :
    Representation (coefficient (buildAffine J cs).coefficients k)
      (commonDenominator cs) ((J*N)^cs.length) := by
  induction cs generalizing k with
  | nil =>
    change Representation (coefficient #[1] k) 1 1
    cases k with
    | zero => simpa [coefficient] using representation_one 1 (by decide)
    | succ k =>
      rw [coefficient_zero (by simp)]
      exact representation_mono (representation_zero 1) (by decide)
  | cons c cs ih =>
    have hm := multiply_representation (buildAffine J cs).coefficients (affineArray c)
      (commonDenominator cs) c.den ((J*N)^cs.length) N J
      (fun i hi => ih (fun q hq => hc q (List.mem_cons_of_mem c hq)) i hi)
      (fun i _ => affine_representation c N (hc c List.mem_cons_self).1 (hc c List.mem_cons_self).2 i) k hk
    simpa only [buildAffine,commonDenominator,List.map_cons,List.prod_cons,List.length_cons,pow_succ,
      Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hm

/-- Actual common denominator magnitude is bounded by original finite-list dimensions. -/
theorem commonDenominator_le (N : ℕ) (cs : List ℚ) (hc : ∀c∈cs,c.den≤N) :
    commonDenominator cs≤N^cs.length := by
  induction cs with
  | nil => simp [commonDenominator]
  | cons c cs ih =>
    simp only [commonDenominator,List.map_cons,List.prod_cons,List.length_cons,pow_succ]
    calc
      _ ≤ N*N^cs.length := Nat.mul_le_mul (hc c List.mem_cons_self)
        (ih (fun q hq => hc q (List.mem_cons_of_mem c hq)))
      _ = _ := by ring

/-- EVERY actual original slope has canonical numerator and denominator at most2L. -/
theorem original_slope_bounds (a h u : ℕ) (t : Fin (size a)) (c : ℚ)
    (hc : c∈slopes a h u t.val) : c.den≤ size a ∧ c.num.natAbs≤ size a := by
  obtain ⟨q,hqr,hc⟩ := List.mem_flatMap.mp hc
  have hq : q<size a := List.mem_range.mp hqr
  by_cases hex : q=center a ∨ q=t.val
  · simp only [hex,ite_true,List.not_mem_nil] at hc
  · simp only [hex,ite_false,List.mem_replicate] at hc
    obtain ⟨_,rfl⟩ := hc
    have hqt : q≠t.val := fun he => hex (Or.inr he)
    have hd : point a t.val-point a q≠0 := point_sub_ne_zero a t.val q hqt
    have hrep := int_ratio_representation ((2:ℤ)^(a+1)) (point a t.val-point a q)
    have hdp : 0<(point a t.val-point a q).natAbs := Int.natAbs_pos.mpr hd
    have hb := representation_reduced_bound hdp hrep
    have he : point a t.val-point a q=difference t.val q := by unfold point difference;ring
    have hbound := (difference_abs_lt (size a) t.val q t.isLt hq).le
    have hn : ((2:ℤ)^(a+1)).natAbs=size a := by norm_num [Int.natAbs_pow,SemiprimeD1WireKernelOriginal.size]
    have hdq : ((point a t.val-point a q:ℤ):ℚ)=(point a t.val:ℚ)-(point a q:ℚ) := by
      simp only [Int.cast_sub]
    rw [hdq] at hb
    simp only [Int.cast_pow,Int.cast_ofNat] at hb
    have hds : (point a t.val-point a q).natAbs≤ size a := by rw [he];exact hbound
    exact ⟨hb.1.trans hds,hb.2.trans hn.le⟩

/-- The ACTUAL source factor-list length has an original finite-grid bound. -/
theorem original_slopes_length (a h u t : ℕ) : (slopes a h u t).length≤ size a*h*u := by
  have hlist (ls : List ℕ) :
      (ls.flatMap (fun q => if q=center a ∨ q=t then [] else
        List.replicate (nodeMultiplicity a h u q)
          (((2:ℤ)^(a+1):ℚ)/((point a t:ℚ)-(point a q:ℚ))))).length≤ls.length*(h*u) := by
    induction ls with
    | nil => simp
    | cons q qs ih =>
      have hmult : nodeMultiplicity a h u q≤h*u := Nat.mul_le_mul_left h (Nat.sub_le _ _)
      by_cases he : q=center a ∨ q=t
      · simp only [List.flatMap_cons,he,ite_true,List.nil_append,List.length_cons]
        nlinarith
      · simp only [List.flatMap_cons,he,ite_false,List.length_append,List.length_replicate,List.length_cons]
        nlinarith
  simpa only [slopes,List.length_range,Nat.mul_assoc] using hlist (List.range (size a))

/-- Original actual local denominator and original fixed numerator cap. -/
def sourceDenominator (a h u t : ℕ) : ℕ := commonDenominator (slopes a h u t)

/-- Literal retained numerator bound from original list size, no height oracle. -/
def sourceNumerator (a h u t : ℕ) : ℕ :=
  (nodeMultiplicity a h u t*size a)^(slopes a h u t).length

/-- Common-denominator representation of EVERY ACTUAL acquired local cardinal coefficient. -/
theorem original_denominator_representation (a h u : ℕ) (t : Fin (size a)) (k : ℕ)
    (hk : k<nodeMultiplicity a h u t.val) :
    Representation (coefficient (acquire a h u t.val).denominator.coefficients k)
      (sourceDenominator a h u t.val) (sourceNumerator a h u t.val) :=
  buildAffine_common_representation _ _ _ (fun c hc => original_slope_bounds a h u t c hc) k hk

/-- Source denominator positivity is derived from actual canonical scalar denominators. -/
theorem sourceDenominator_pos (a h u t : ℕ) : 0<sourceDenominator a h u t := commonDenominator_pos _

/-- EVERY ACTUAL cached inverse coefficient has ONE denominator D^q and an explicit
power numerator bound. There is no exponential recurrence-height hypothesis. -/
theorem original_inverse_representation (a h u : ℕ) (t : Fin (size a))
    (hq : 0<nodeMultiplicity a h u t.val) (k : ℕ) (hk : k<nodeMultiplicity a h u t.val) :
    Representation (coefficient (acquire a h u t.val).inverse.coefficients k)
      ((sourceDenominator a h u t.val)^nodeMultiplicity a h u t.val)
      ((inverseBase (nodeMultiplicity a h u t.val) (sourceDenominator a h u t.val)
        (sourceNumerator a h u t.val))^nodeMultiplicity a h u t.val) :=
  cached_inverse_common_representation _ _ _ _ (sourceDenominator_pos _ _ _ _)
    (acquire_denominator_constant a h u t.val hq)
    (fun i hi => original_denominator_representation a h u t i hi) k hk

/-- EVERY actual recursive affine suffix array retains a single acquired product denominator. -/
theorem original_denominator_suffix_representation (a h u : ℕ) (t : Fin (size a)) (s k : ℕ)
    (hk : k<nodeMultiplicity a h u t.val) :
    Representation (coefficient (buildAffine (nodeMultiplicity a h u t.val)
        ((slopes a h u t.val).drop s)).coefficients k)
      (commonDenominator ((slopes a h u t.val).drop s))
      ((nodeMultiplicity a h u t.val*size a)^((slopes a h u t.val).drop s).length) := by
  refine buildAffine_common_representation _ _ _ ?_ k hk
  intro c hc
  exact original_slope_bounds a h u t c (List.mem_of_mem_drop hc)

/-- EVERY actual partial scalar accumulator of the normalized inverse recurrence
has original-derived canonical numerator/denominator bounds. -/
theorem original_inverse_dot_heights (a h u : ℕ) (t : Fin (size a)) (n len : ℕ)
    (hn : n+1<nodeMultiplicity a h u t.val) (hlen : len≤n+1) :
    (dotPrefix (acquire a h u t.val).denominator.coefficients
      (SemiprimeJetArray.inverse (acquire a h u t.val).denominator.coefficients (n+1)).coefficients
      n len).value.den≤(sourceDenominator a h u t.val)^(n+1) ∧
    (dotPrefix (acquire a h u t.val).denominator.coefficients
      (SemiprimeJetArray.inverse (acquire a h u t.val).denominator.coefficients (n+1)).coefficients
      n len).value.num.natAbs≤
        (inverseBase (nodeMultiplicity a h u t.val) (sourceDenominator a h u t.val)
          (sourceNumerator a h u t.val))^(n+1) := by
  exact cached_dotPrefix_heights _ _ _ _ n len (sourceDenominator_pos _ _ _ _)
    (acquire_denominator_constant a h u t.val (by omega))
    (fun i hi => original_denominator_representation a h u t i hi) hn hlen

/-- Every actual affine-convolution dot prefix has one variable-denominator product,
with numerator padded only by its actual finite length, not repeated denominator squaring. -/
theorem buildAffine_dot_representation (J N : ℕ) (cs : List ℚ) (c : ℚ)
    (hcs : ∀x∈cs,x.den≤N ∧ x.num.natAbs≤N) (hc : c.den≤N ∧ c.num.natAbs≤N)
    (n len : ℕ) (hn : n<J) (hlen : len≤n) :
    Representation (dotPrefix (buildAffine J cs).coefficients (affineArray c) (n-1) len).value
      (commonDenominator (c::cs)) ((J*N)^(cs.length+1)) := by
  have hh := dotPrefix_common_representation (buildAffine J cs).coefficients (affineArray c)
    (commonDenominator cs) c.den ((J*N)^cs.length) N (n-1) len
    (fun i hi => buildAffine_common_representation J N cs hcs (i+1) (by omega))
    (fun i _ => affine_representation c N hc.1 hc.2 (n-1-i))
  have hb : len*(J*N)^cs.length*N≤(J*N)^(cs.length+1) := by
    rw [pow_succ]
    calc
      _ ≤ J*(J*N)^cs.length*N := Nat.mul_le_mul_right N (Nat.mul_le_mul_right _ (by omega))
      _ = _ := by ring
  have hm := representation_mono hh hb
  simpa only [commonDenominator,List.map_cons,List.prod_cons,Nat.mul_comm] using hm

/-- Original source specialization covers the ACTUAL affine-builder scalar dot
accumulator at every literal list position and retained coefficient prefix. -/
theorem original_affine_dot_representation (a h u : ℕ) (t : Fin (size a))
    (s : Fin (slopes a h u t.val).length) (n len : ℕ)
    (hn : n<nodeMultiplicity a h u t.val) (hlen : len≤n) :
    Representation
      (dotPrefix (buildAffine (nodeMultiplicity a h u t.val)
        ((slopes a h u t.val).drop (s.val+1))).coefficients
        (affineArray ((slopes a h u t.val)[s.val])) (n-1) len).value
      (commonDenominator (((slopes a h u t.val)[s.val])::
        ((slopes a h u t.val).drop (s.val+1))))
      ((nodeMultiplicity a h u t.val*size a)^(((slopes a h u t.val).drop (s.val+1)).length+1)) := by
  apply buildAffine_dot_representation
  · intro c hc
    exact original_slope_bounds a h u t c (List.mem_of_mem_drop hc)
  · exact original_slope_bounds a h u t _ (List.getElem_mem s.isLt)
  · exact hn
  · exact hlen

end RiemannGaussian.SemiprimeD1HermiteDenominatorHeight
