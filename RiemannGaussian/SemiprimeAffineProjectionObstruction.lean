/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLiteralQuadraticRoots
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Prime.Infinite

/-!
# A generic obstruction to bounded affine projections

This module concerns arbitrary affine points, not the public Euclidean
packet source. For every coefficient height, three points have a proper
semiprime area while the pooled signed values of all nonzero integer linear
forms of that height are separated in both prime fields, including dilated
directions. A proof specific to the arithmetic row source, or a different
incidence extractor, is still
required. This is not a factoring lower bound or a coverage theorem.
-/

namespace RiemannGaussian.SemiprimeAffineProjectionObstruction

open SemiprimeAffinePointAreas SemiprimeCompanionCoverage SemiprimeRowDerivative
open SemiprimeReflectedCompanions

/-- The point spacing exceeds every permitted coefficient. -/
def projectionDilation (h : ℤ) : ℤ := h+1

/-- A positional base larger than all coefficient differences used below. -/
def projectionBase (h : ℤ) : ℤ := h*(projectionDilation h+1)+1

/-- The integer bound for a form evaluated at the middle point. -/
def projectionHeight (h : ℤ) : ℤ := h*(projectionBase h+1)

/-- All nonzero bounded integer forms, including signs and dilated directions. -/
noncomputable def boundedForms (h : ℤ) : Finset (ℤ×ℤ) :=
  ((Finset.Icc (-h) h)×ˢ(Finset.Icc (-h) h)).filter
    fun z => z≠(0,0)

theorem boundedForms_mem {h : ℤ} {z : ℤ×ℤ} :
    z∈boundedForms h ↔ |z.1|≤h ∧ |z.2|≤h ∧ z≠(0,0) := by
  rw [boundedForms,Finset.mem_filter,Finset.mem_product]
  simp only [Finset.mem_Icc,abs_le]
  tauto

/-- Evaluation at the middle point `(B,1)`. -/
def firstValue (h : ℤ) (z : ℤ×ℤ) : ℤ := z.1*projectionBase h+z.2

/-- Evaluation at the final point `(lambda*B,lambda+p)`. -/
def secondValue (p : ℕ) (h : ℤ) (z : ℤ×ℤ) : ℤ :=
  projectionDilation h*firstValue h z+z.2*p

/-- Evaluation at either nonzero constructed point, with its point label retained. -/
def projectedValue (p : ℕ) (h : ℤ) (side : Bool) (z : ℤ×ℤ) : ℤ :=
  if side then secondValue p h z else firstValue h z

/-- The part of a projection that remains after reduction modulo `p`. -/
def scaledFirst (h : ℤ) (side : Bool) (z : ℤ×ℤ) : ℤ :=
  if side then projectionDilation h*firstValue h z else firstValue h z

theorem projectionDilation_pos {h : ℤ} (hh : 1≤h) : 0<projectionDilation h := by
  unfold projectionDilation
  omega

theorem projectionBase_pos {h : ℤ} (hh : 1≤h) : 0<projectionBase h := by
  unfold projectionBase projectionDilation
  positivity

theorem projectionHeight_pos {h : ℤ} (hh : 1≤h) : 0<projectionHeight h := by
  have hb := projectionBase_pos hh
  unfold projectionHeight
  positivity

theorem firstValue_abs_le {h : ℤ} (hh : 1≤h) {z : ℤ×ℤ}
    (hz : z∈boundedForms h) : |firstValue h z|≤projectionHeight h := by
  obtain ⟨hx,hy,_⟩ := boundedForms_mem.mp hz
  have hb := (projectionBase_pos hh).le
  have ha := abs_add_le (z.1*projectionBase h) z.2
  rw [abs_mul,abs_of_nonneg hb] at ha
  have hm := mul_le_mul_of_nonneg_right hx hb
  unfold firstValue projectionHeight
  nlinarith

/-- A small residual cannot cancel a nonzero multiple of the positional base. -/
theorem base_equation_zero {h r s : ℤ} (hh : 1≤h)
    (hs : |s|<projectionBase h) (he : r*projectionBase h+s=0) : r=0 ∧ s=0 := by
  by_cases hr : r=0
  · simp only [hr,zero_mul,zero_add] at he
    exact ⟨hr,he⟩
  · have hb := projectionBase_pos hh
    have hrabs : 1≤|r| := by have := abs_pos.mpr hr; omega
    have hm := mul_le_mul_of_nonneg_right hrabs hb.le
    have ha : |r| * projectionBase h=|s| := by
      calc
        _ = |r*projectionBase h| := by rw [abs_mul,abs_of_pos hb]
        _ = |-s| := congrArg abs (by omega)
        _ = |s| := abs_neg _
    nlinarith

theorem firstValue_injective {h : ℤ} (hh : 1≤h) {z w : ℤ×ℤ}
    (hz : z∈boundedForms h) (hw : w∈boundedForms h)
    (he : firstValue h z=firstValue h w) : z=w := by
  have hz' := boundedForms_mem.mp hz
  have hw' := boundedForms_mem.mp hw
  have hs := abs_sub_le z.2 0 w.2
  simp only [sub_zero,zero_sub,abs_neg] at hs
  have hs' : |z.2-w.2|<projectionBase h := by
    unfold projectionBase projectionDilation
    nlinarith [hz'.2.1,hw'.2.1]
  have he' : (z.1-w.1)*projectionBase h+(z.2-w.2)=0 := by
    unfold firstValue at he
    linear_combination he
  obtain ⟨hx,hy⟩ := base_equation_zero hh hs' he'
  exact Prod.ext (by omega) (by omega)

theorem firstValue_ne_zero {h : ℤ} (hh : 1≤h) {z : ℤ×ℤ}
    (hz : z∈boundedForms h) : firstValue h z≠0 := by
  intro he
  obtain ⟨_,hs,hne⟩ := boundedForms_mem.mp hz
  have hs' : |z.2|<projectionBase h := by
    unfold projectionBase projectionDilation
    nlinarith
  obtain ⟨hx,hy⟩ := base_equation_zero hh hs' he
  exact hne (Prod.ext hx hy)

/-- A nonzero coefficient cannot be scaled by more than the permitted height. -/
theorem bounded_scaled_zero {h a b : ℤ} (hh : 1≤h) (ha : |a|≤h)
    (he : a=projectionDilation h*b) : b=0 := by
  by_contra hb
  have hl := projectionDilation_pos hh
  have hb' : 1≤|b| := by have := abs_pos.mpr hb; omega
  have hm := mul_le_mul_of_nonneg_left hb' hl.le
  rw [he,abs_mul,abs_of_pos hl] at ha
  unfold projectionDilation at ha hm
  nlinarith

/-- No two bounded nonzero directions differ by the chosen point spacing. -/
theorem firstValue_ne_scale {h : ℤ} (hh : 1≤h) {z w : ℤ×ℤ}
    (hz : z∈boundedForms h) (hw : w∈boundedForms h) :
    firstValue h z≠projectionDilation h*firstValue h w := by
  intro he
  have hz' := boundedForms_mem.mp hz
  have hw' := boundedForms_mem.mp hw
  have hl := projectionDilation_pos hh
  have hs := abs_sub_le z.2 0 (projectionDilation h*w.2)
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_pos hl] at hs
  have hm := mul_le_mul_of_nonneg_left hw'.2.1 hl.le
  have hs' : |z.2-projectionDilation h*w.2|<projectionBase h := by
    unfold projectionBase
    nlinarith [hz'.2.1]
  have he' : (z.1-projectionDilation h*w.1)*projectionBase h+
      (z.2-projectionDilation h*w.2)=0 := by
    unfold firstValue at he
    linear_combination he
  obtain ⟨hx,hy⟩ := base_equation_zero hh hs' he'
  have hwx := bounded_scaled_zero hh hz'.1 (sub_eq_zero.mp hx)
  have hwy := bounded_scaled_zero hh hz'.2.1 (sub_eq_zero.mp hy)
  exact hw'.2.2 (Prod.ext hwx hwy)

theorem scaledFirst_abs_le {h : ℤ} (hh : 1≤h) {z : ℤ×ℤ}
    (hz : z∈boundedForms h) (side : Bool) :
    |scaledFirst h side z|≤projectionDilation h*projectionHeight h := by
  have ha := firstValue_abs_le hh hz
  have hp := (projectionHeight_pos hh).le
  have hl := projectionDilation_pos hh
  have hm := mul_le_mul_of_nonneg_left ha hl.le
  have hl' : 1≤projectionDilation h := by unfold projectionDilation; omega
  have hH := mul_le_mul_of_nonneg_right hl' hp
  cases side
  · simpa only [scaledFirst,Bool.false_eq_true,if_false] using
      ha.trans (by simpa only [one_mul] using hH)
  · simpa only [scaledFirst,if_true,abs_mul,abs_of_pos hl] using hm

theorem scaledFirst_ne_zero {h : ℤ} (hh : 1≤h) {z : ℤ×ℤ}
    (hz : z∈boundedForms h) (side : Bool) : scaledFirst h side z≠0 := by
  have ha := firstValue_ne_zero hh hz
  have hl := (projectionDilation_pos hh).ne'
  cases side <;> simp [scaledFirst,ha,hl]

theorem scaledFirst_injective {h : ℤ} (hh : 1≤h) {z w : ℤ×ℤ}
    (hz : z∈boundedForms h) (hw : w∈boundedForms h) {us ws : Bool}
    (he : scaledFirst h us z=scaledFirst h ws w) : us=ws ∧ z=w := by
  cases us <;> cases ws <;> simp only [scaledFirst,Bool.false_eq_true,
    ↓reduceIte] at he
  · exact ⟨rfl,firstValue_injective hh hz hw he⟩
  · exact (firstValue_ne_scale hh hz hw he).elim
  · exact (firstValue_ne_scale hh hw hz he.symm).elim
  · exact ⟨rfl,firstValue_injective hh hz hw
      (mul_left_cancel₀ (projectionDilation_pos hh).ne' he)⟩

/-- Integer equality follows from a congruence whose difference is below the modulus. -/
theorem small_cast_eq {p : ℕ} {a b : ℤ} (hb : |b-a|<(p : ℤ))
    (he : (a : ZMod p)=(b : ZMod p)) : a=b := by
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mp he
  have hn : (b-a).natAbs<p := by
    rw [←Int.natCast_natAbs] at hb
    exact_mod_cast hb
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    (by simpa only [Int.natAbs_natCast] using hn)
  omega

theorem projectedValue_cast_p (p : ℕ) (h : ℤ) (side : Bool) (z : ℤ×ℤ) :
    (projectedValue p h side z : ZMod p)=(scaledFirst h side z : ZMod p) := by
  cases side <;> simp [projectedValue,secondValue,scaledFirst]

/-- The first prime image retains every projection label, including the chosen point. -/
theorem projectedValue_prime_injective {p : ℕ} {h : ℤ} (hh : 1≤h)
    (hp : 2*projectionDilation h*projectionHeight h<(p : ℤ)) {z w : ℤ×ℤ}
    (hz : z∈boundedForms h) (hw : w∈boundedForms h) {us ws : Bool}
    (he : (projectedValue p h us z : ZMod p)=(projectedValue p h ws w : ZMod p)) :
    us=ws ∧ z=w := by
  rw [projectedValue_cast_p,projectedValue_cast_p] at he
  have ha := scaledFirst_abs_le hh hz us
  have hb := scaledFirst_abs_le hh hw ws
  have hd := abs_sub_le (scaledFirst h ws w) 0 (scaledFirst h us z)
  simp only [sub_zero,zero_sub,abs_neg] at hd
  exact scaledFirst_injective hh hz hw (small_cast_eq (by linarith) he)

theorem projectedValue_prime_ne_zero {p : ℕ} {h : ℤ} (hh : 1≤h)
    (hp : 2*projectionDilation h*projectionHeight h<(p : ℤ)) {z : ℤ×ℤ}
    (hz : z∈boundedForms h) (side : Bool) :
    (projectedValue p h side z : ZMod p)≠0 := by
  rw [projectedValue_cast_p]
  intro he
  have ha := scaledFirst_abs_le hh hz side
  have hn := (projectionHeight_pos hh).le
  have hz' : scaledFirst h side z=0 := small_cast_eq (by simpa using (by
    linarith : |scaledFirst h side z|<(p : ℤ))) (by simpa using he)
  exact scaledFirst_ne_zero hh hz side hz'

/-- All evaluations from both nonzero points, pooled with the zero point. -/
noncomputable def integerRoots (p : ℕ) (h : ℤ) : Finset ℤ :=
  insert 0 ((boundedForms h).image (firstValue h) ∪
    (boundedForms h).image (secondValue p h))

theorem integerRoots_mem {p : ℕ} {h a : ℤ} :
    a∈integerRoots p h ↔ a=0 ∨
      ∃ z∈boundedForms h, ∃ side : Bool, projectedValue p h side z=a := by
  classical
  simp only [integerRoots,Finset.mem_insert,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro (ha|⟨z,hz,he⟩|⟨z,hz,he⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨z,hz,false,he⟩
    · exact Or.inr ⟨z,hz,true,he⟩
  · rintro (ha|⟨z,hz,side,he⟩)
    · exact Or.inl ha
    · cases side
      · exact Or.inr (Or.inl ⟨z,hz,he⟩)
      · exact Or.inr (Or.inr ⟨z,hz,he⟩)

theorem integerRoots_prime_injective {p : ℕ} {h : ℤ} (hh : 1≤h)
    (hp : 2*projectionDilation h*projectionHeight h<(p : ℤ)) {a b : ℤ}
    (ha : a∈integerRoots p h) (hb : b∈integerRoots p h)
    (he : (a : ZMod p)=(b : ZMod p)) : a=b := by
  rcases integerRoots_mem.mp ha with rfl|⟨z,hz,us,rfl⟩
  · rcases integerRoots_mem.mp hb with rfl|⟨w,hw,ws,rfl⟩
    · rfl
    · exact (projectedValue_prime_ne_zero hh hp hw ws (by simpa using he.symm)).elim
  · rcases integerRoots_mem.mp hb with rfl|⟨w,hw,ws,rfl⟩
    · exact (projectedValue_prime_ne_zero hh hp hz us (by simpa using he)).elim
    · obtain ⟨rfl,rfl⟩ := projectedValue_prime_injective hh hp hz hw he
      rfl

theorem projectedValue_abs_le {p : ℕ} {h : ℤ} (hh : 1≤h) {z : ℤ×ℤ}
    (hz : z∈boundedForms h) (side : Bool) :
    |projectedValue p h side z|≤projectionDilation h*projectionHeight h+h*p := by
  have ha := firstValue_abs_le hh hz
  have hs := (boundedForms_mem.mp hz).2.1
  have hm := mul_le_mul_of_nonneg_right hs (Int.natCast_nonneg p)
  have hh' := (projectionHeight_pos hh).le
  have hl := projectionDilation_pos hh
  have ha' := mul_le_mul_of_nonneg_left ha hl.le
  have hl' : 1≤projectionDilation h := by unfold projectionDilation; omega
  have hH := mul_le_mul_of_nonneg_right hl' hh'
  have hp' : 0≤h*(p : ℤ) := mul_nonneg (by omega) (Int.natCast_nonneg p)
  cases side
  · change |firstValue h z|≤_
    linarith
  · have hb := abs_add_le (projectionDilation h*firstValue h z) (z.2*p)
    simp only [abs_mul,abs_of_pos hl,abs_of_nonneg (Int.natCast_nonneg p)] at hb
    unfold projectedValue secondValue
    simp only [if_true]
    nlinarith

theorem integerRoots_abs_le {p : ℕ} {h : ℤ} (hh : 1≤h) {a : ℤ}
    (ha : a∈integerRoots p h) : |a|≤projectionDilation h*projectionHeight h+h*p := by
  rcases integerRoots_mem.mp ha with rfl|⟨z,hz,side,rfl⟩
  · have hH := (projectionHeight_pos hh).le
    have hl := (projectionDilation_pos hh).le
    have hm := mul_nonneg hl hH
    have hp' : 0≤h*(p : ℤ) := mul_nonneg (by omega) (Int.natCast_nonneg p)
    norm_num only [abs_zero]
    linarith
  · exact projectedValue_abs_le hh hz side

/-- The second prime image is injective by an ordinary integer difference bound. -/
theorem integerRoots_other_prime_injective {p q : ℕ} {h : ℤ} (hh : 1≤h)
    (hq : 2*projectionDilation h*projectionHeight h+2*h*p<(q : ℤ)) {a b : ℤ}
    (ha : a∈integerRoots p h) (hb : b∈integerRoots p h)
    (he : (a : ZMod q)=(b : ZMod q)) : a=b := by
  have ha' := integerRoots_abs_le hh ha
  have hb' := integerRoots_abs_le hh hb
  have hd := abs_sub_le b 0 a
  simp only [sub_zero,zero_sub,abs_neg] at hd
  exact small_cast_eq (by linarith) he

theorem boundedForms_neg {h : ℤ} {z : ℤ×ℤ} (hz : z∈boundedForms h) :
    (-z.1,-z.2)∈boundedForms h := by
  rcases z with ⟨r,s⟩
  rw [boundedForms_mem] at hz ⊢
  refine ⟨by simpa only [abs_neg] using hz.1,
    by simpa only [abs_neg] using hz.2.1,?_⟩
  intro he
  have hr : -r=0 := congrArg Prod.fst he
  have hs : -s=0 := congrArg Prod.snd he
  exact hz.2.2 (Prod.ext (neg_eq_zero.mp hr) (neg_eq_zero.mp hs))

theorem projectedValue_neg (p : ℕ) (h : ℤ) (side : Bool) (z : ℤ×ℤ) :
    projectedValue p h side (-z.1,-z.2) = -projectedValue p h side z := by
  cases side <;> simp [projectedValue,secondValue,firstValue] <;> ring

theorem integerRoots_neg {p : ℕ} {h a : ℤ} (ha : a∈integerRoots p h) :
    -a∈integerRoots p h := by
  rcases integerRoots_mem.mp ha with rfl|⟨z,hz,side,rfl⟩
  · apply integerRoots_mem.mpr
    exact Or.inl (neg_zero)
  · apply integerRoots_mem.mpr
    exact Or.inr ⟨(-z.1,-z.2),boundedForms_neg hz,side,projectedValue_neg p h side z⟩

/-- This is the complete pooled scalar family for the three constructed points. -/
noncomputable def projectionRoots (p q : ℕ) (h : ℤ) : Finset (ZMod (p*q)) :=
  (integerRoots p h).image fun a : ℤ => (a : ZMod (p*q))

theorem projectionRoots_mem {p q : ℕ} {h : ℤ} {x : ZMod (p*q)} :
    x∈projectionRoots p q h ↔ ∃ a∈integerRoots p h, (a : ZMod (p*q))=x := by
  classical
  simp only [projectionRoots,Finset.mem_image]

theorem projectionRoots_zero (p q : ℕ) (h : ℤ) :
    (0 : ZMod (p*q))∈projectionRoots p q h := by
  apply projectionRoots_mem.mpr
  exact ⟨0,integerRoots_mem.mpr (Or.inl rfl),Int.cast_zero⟩

theorem projectionRoots_neg {p q : ℕ} {h : ℤ} {x : ZMod (p*q)}
    (hx : x∈projectionRoots p q h) : -x∈projectionRoots p q h := by
  obtain ⟨a,ha,rfl⟩ := projectionRoots_mem.mp hx
  exact projectionRoots_mem.mpr ⟨-a,integerRoots_neg ha,Int.cast_neg a⟩

theorem projectionRoots_signed (p q : ℕ) (h : ℤ) :
    signedRoots (projectionRoots p q h)=projectionRoots p q h := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [signedRoots,anchoredRoots,Finset.mem_insert,Finset.mem_union,
      Finset.mem_image] at hx
    rcases hx with rfl|hx|⟨a,ha,rfl⟩
    · exact projectionRoots_zero p q h
    · exact hx
    · exact projectionRoots_neg ha
  · intro x hx
    exact signedRoots_mem hx

/-- Every pairwise and reflected scalar GCD is uninformative in this entire family. -/
theorem projectionRoots_recover_none {p q : ℕ} {h : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hh : 1≤h)
    (hlargeP : 2*projectionDilation h*projectionHeight h<(p : ℤ))
    (hlargeQ : 2*projectionDilation h*projectionHeight h+2*h*p<(q : ℤ)) :
    recoverRows (projectionRoots p q h)=none ∧
      recoverReflectedRows (projectionRoots p q h)=none := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hn : recoverRows (projectionRoots p q h)=none := by
    apply (recoverRows_none_iff_prime_separation hp hq _).mpr
    intro t ht x hx hne
    obtain ⟨a,ha,rfl⟩ := projectionRoots_mem.mp ht
    obtain ⟨b,hb,rfl⟩ := projectionRoots_mem.mp hx
    constructor
    · intro he
      simp only [map_intCast] at he
      exact hne (congrArg (fun k : ℤ => (k : ZMod (p*q)))
        (integerRoots_prime_injective hh hlargeP ha hb he).symm)
    · intro he
      simp only [map_intCast] at he
      exact hne (congrArg (fun k : ℤ => (k : ZMod (p*q)))
        (integerRoots_other_prime_injective hh hlargeQ ha hb he).symm)
  refine ⟨hn,?_⟩
  rw [recoverReflectedRows_none_iff_signed,projectionRoots_signed]
  exact hn

/-- An integer linear form evaluated on an affine point. -/
def linearProjection {N : ℕ} (z : ℤ×ℤ) (u : ZMod N×ZMod N) : ZMod N :=
  (z.1 : ZMod N)*u.1+(z.2 : ZMod N)*u.2

/-- The middle point provides a positional encoding of every bounded direction. -/
def middlePoint (N : ℕ) (h : ℤ) : ZMod N×ZMod N := (projectionBase h,1)

/-- The final point is a large dilation with a vertical first-prime displacement. -/
def lastPoint (N p : ℕ) (h : ℤ) : ZMod N×ZMod N :=
  ((projectionDilation h : ZMod N)*projectionBase h,(projectionDilation h : ZMod N)+p)

theorem firstValue_projection (N : ℕ) (h : ℤ) (z : ℤ×ℤ) :
    (firstValue h z : ZMod N)=linearProjection z (middlePoint N h) := by
  simp [firstValue,linearProjection,middlePoint]

theorem secondValue_projection (N p : ℕ) (h : ℤ) (z : ℤ×ℤ) :
    (secondValue p h z : ZMod N)=linearProjection z (lastPoint N p h) := by
  simp [secondValue,firstValue,linearProjection,lastPoint]
  ring

theorem constructed_area (N p : ℕ) (h : ℤ) :
    affineArea (0,0) (middlePoint N h) (lastPoint N p h)=
      (projectionBase h : ZMod N)*(p : ZMod N) := by
  simp [affineArea,middlePoint,lastPoint,Matrix.det_fin_three]
  ring

theorem projectionBase_le_height {h : ℤ} (hh : 1≤h) :
    projectionBase h≤projectionHeight h := by
  have hb := projectionBase_pos hh
  have hm := mul_le_mul_of_nonneg_right hh (show 0≤projectionBase h+1 by omega)
  unfold projectionHeight
  linarith

/-- The area vanishes only in the first prime field, despite all scalar separation. -/
theorem constructed_area_gcd {p q : ℕ} {h : ℤ} (hp : p.Prime) (hq : q.Prime)
    (hh : 1≤h) (hlargeQ : 2*projectionDilation h*projectionHeight h+2*h*p<(q : ℤ)) :
    (p*q).gcd (affineArea (0,0) (middlePoint (p*q) h)
      (lastPoint (p*q) p h)).val=p := by
  let : Fact q.Prime := ⟨hq⟩
  have hH := projectionHeight_pos hh
  have hL := projectionDilation_pos hh
  have hB := projectionBase_pos hh
  have hBH := projectionBase_le_height hh
  have hp' : 0<(p : ℤ) := by exact_mod_cast hp.pos
  have hqB : projectionBase h<(q : ℤ) := by nlinarith
  have hpq : (p : ℤ)<(q : ℤ) := by nlinarith
  have hbq : (projectionBase h : ZMod q)≠0 := by
    intro he
    have hzero : projectionBase h=0 := small_cast_eq
      (by simpa only [zero_sub,abs_neg,abs_of_pos hB] using hqB) (by simpa using he)
    omega
  have hpq' : (p : ZMod q)≠0 := by
    intro he
    have hzero : (p : ℤ)=0 := small_cast_eq
      (by simpa only [zero_sub,abs_neg,abs_of_pos hp'] using hpq) (by simpa using he)
    omega
  rw [constructed_area]
  apply SemiprimeCentreFreeCover.separating_residue_gcd hp hq
  · simp only [map_mul,map_intCast,map_natCast,ZMod.natCast_self,mul_zero]
  · simpa only [map_mul,map_intCast,map_natCast] using mul_ne_zero hbq hpq'

/-- The complete projection detector fails while one constant-size area gives a factor.
This concerns the constructed points, not membership in the Euclidean packet family. -/
theorem projection_obstruction {p q : ℕ} {h : ℤ} (hp : p.Prime) (hq : q.Prime)
    (hh : 1≤h) (hlargeP : 2*projectionDilation h*projectionHeight h<(p : ℤ))
    (hlargeQ : 2*projectionDilation h*projectionHeight h+2*h*p<(q : ℤ)) :
    recoverRows (projectionRoots p q h)=none ∧
      recoverReflectedRows (projectionRoots p q h)=none ∧
      SemiprimeGroupSelection.ProperDivisor (p*q)
        ((p*q).gcd (affineArea (0,0) (middlePoint (p*q) h)
          (lastPoint (p*q) p h)).val) := by
  obtain ⟨hn,hr⟩ := projectionRoots_recover_none hp hq hh hlargeP hlargeQ
  refine ⟨hn,hr,?_⟩
  rw [constructed_area_gcd hp hq hh hlargeQ]
  refine ⟨hp.one_lt,?_,dvd_mul_right p q⟩
  have hm := Nat.mul_le_mul_left p hq.two_le
  nlinarith [hp.pos]

/-- Such prime pairs exist for every positive coefficient height.
No canonical modulus, public packet membership, or factoring price is asserted. -/
theorem exists_projection_obstruction (h : ℤ) (hh : 1≤h) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
      recoverRows (projectionRoots p q h)=none ∧
      recoverReflectedRows (projectionRoots p q h)=none ∧
      SemiprimeGroupSelection.ProperDivisor (p*q)
        ((p*q).gcd (affineArea (0,0) (middlePoint (p*q) h)
          (lastPoint (p*q) p h)).val) := by
  have hH := (projectionHeight_pos hh).le
  have hL := (projectionDilation_pos hh).le
  have hbound : 0≤2*projectionDilation h*projectionHeight h := by positivity
  obtain ⟨p,hpbound,hp⟩ := Nat.exists_infinite_primes (2*projectionDilation h*projectionHeight h).toNat.succ
  have hlargeP : 2*projectionDilation h*projectionHeight h<(p : ℤ) := by
    have he := Int.toNat_of_nonneg hbound
    omega
  have hnonneg : 0≤2*projectionDilation h*projectionHeight h+2*h*p := by positivity
  obtain ⟨q,hqbound,hq⟩ :=
    Nat.exists_infinite_primes (2*projectionDilation h*projectionHeight h+2*h*p).toNat.succ
  have hlargeQ : 2*projectionDilation h*projectionHeight h+2*h*p<(q : ℤ) := by
    have he := Int.toNat_of_nonneg hnonneg
    omega
  exact ⟨p,q,hp,hq,projection_obstruction hp hq hh hlargeP hlargeQ⟩

end RiemannGaussian.SemiprimeAffineProjectionObstruction
