/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitInverse
import Mathlib.Data.Int.Interval

/-!
# Arithmetic separation for a mixed short CRT index

The retained marked index has two distinct, bounded local roots. Their
sum and product satisfy one affine lattice congruence. A homogeneous
relation cannot be too short: it would lift to an integer equality at
the larger prime and contradict the distinct root at the smaller prime.

This is arithmetic over the original index, with no local root supplied
to the public relation construction. Native integer operations below
are specifications, not a complete Boolean bit-cost certificate.
-/

namespace RiemannGaussian.SemiprimeIndexLattice

open SemiprimeIntervalJet
open scoped BigOperators

/-- The homogeneous lattice associated with a public modular index. -/
def indexRelation {N : ℕ} (s : ZMod N) (u v : ℤ) : Prop :=
  (u : ZMod N)*s=(v : ZMod N)

/-- A coefficient pair in the original bounded sum/product rectangle. -/
def coefficientCandidate {N : ℕ} (s : ZMod N) (L : ℕ) (a b : ℤ) : Prop :=
  0≤a ∧ a<2*(L : ℤ) ∧ 0≤b ∧ b<(L : ℤ)^2 ∧
    s^2-(a : ZMod N)*s+(b : ZMod N)=0

/-- A divisible integer strictly smaller in magnitude than its modulus
must vanish; negative relations are retained. -/
theorem integer_zero_of_dvd_abs_lt {n : ℕ} {z : ℤ}
    (hd : (n : ℤ) ∣ z) (hz : |z|<(n : ℤ)) : z=0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
  simp only [Int.natAbs_natCast]
  rw [← Int.natCast_natAbs] at hz
  exact_mod_cast hz

/-- Two distinct short local roots force the original symmetric
coefficient congruence, including a zero local index. -/
theorem mixed_index_coefficient_candidate {p q L k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hk : k<L) (hl : l<L)
    (s : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) s=(k : ZMod p))
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) s=(l : ZMod q)) :
    coefficientCandidate s L ((k : ℤ)+l) ((k : ℤ)*l) := by
  refine ⟨by positivity, by exact_mod_cast (show k+l<2*L by omega),
    by positivity, ?_, ?_⟩
  · have hkn : (k : ℤ)<L := by exact_mod_cast hk
    have hln : (l : ℤ)<L := by exact_mod_cast hl
    have hkp : (0 : ℤ)≤k := by positivity
    have hlp : (0 : ℤ)≤l := by positivity
    nlinarith
  · apply zero_of_prime_reductions hp hq hpq
    · simp only [map_add, map_sub, map_mul, map_pow, map_intCast]
      push_cast
      rw [hP]
      ring
    · simp only [map_add, map_sub, map_mul, map_pow, map_intCast]
      push_cast
      rw [hQ]
      ring

/-- The arithmetic reason a homogeneous mixed-index relation cannot
be tiny. The larger-prime congruence lifts to v=u*l; the smaller-prime
congruence then contradicts k≠l unless both coordinates are zero. -/
theorem mixed_index_no_short_relation {p q L k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLp : L≤p) (hkl : k≠l) (s : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) s=(k : ZMod p))
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) s=(l : ZMod q))
    (u v : ℤ) (hrel : indexRelation s u v)
    (hu : |u|<(p : ℤ)) (hsize : |u| * (L : ℤ)+|v|<(q : ℤ)) :
    u=0 ∧ v=0 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hqzero : ((u*(l : ℤ)-v : ℤ) : ZMod q)=0 := by
    have hh := congrArg (ZMod.castHom (dvd_mul_left q p) (ZMod q)) hrel
    simp only [map_mul, map_intCast, hQ] at hh
    push_cast
    exact sub_eq_zero.mpr hh
  have hsmall : |u*(l : ℤ)-v|<(q : ℤ) := by
    have hln : (l : ℤ)≤L := by exact_mod_cast hl.le
    calc
      |u*(l : ℤ)-v| ≤ |u*(l : ℤ)|+|v| := abs_sub _ _
      _ = |u| * (l : ℤ)+|v| := by rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg l)]
      _ ≤ |u| * (L : ℤ)+|v| := by nlinarith [abs_nonneg u]
      _ < (q : ℤ) := hsize
  have heq : u*(l : ℤ)=v := sub_eq_zero.mp
    (integer_zero_of_dvd_abs_lt
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hqzero) hsmall)
  have hpzero : (u : ZMod p)*((k : ZMod p)-(l : ZMod p))=0 := by
    have hh := congrArg (ZMod.castHom (dvd_mul_right p q) (ZMod p)) hrel
    simp only [map_mul, map_intCast, hP] at hh
    have hv := congrArg (fun z : ℤ => (z : ZMod p)) heq
    push_cast at hv
    linear_combination hh-hv
  have hdiff : (k : ZMod p)-(l : ZMod p)≠0 := by
    intro hh
    have hv := congrArg ZMod.val (sub_eq_zero.mp hh)
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (hk.trans_le hLp),
      Nat.mod_eq_of_lt (hl.trans_le hLp)] at hv
    exact hkl hv
  have huz : (u : ZMod p)=0 := (mul_eq_zero.mp hpzero).resolve_right hdiff
  have hu0 := integer_zero_of_dvd_abs_lt
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp huz) hu
  exact ⟨hu0, by simpa [hu0] using heq.symm⟩

/-- A nonzero relation pays at least one of the two arithmetic
separations. This holds for every relation, without a generic-position
or random-index assumption. -/
theorem mixed_index_relation_separation {p q L k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLp : L≤p) (hkl : k≠l) (s : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) s=(k : ZMod p))
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) s=(l : ZMod q))
    (u v : ℤ) (hrel : indexRelation s u v) (hne : u≠0 ∨ v≠0) :
    (p : ℤ)≤|u| ∨ (q : ℤ)≤|u| * (L : ℤ)+|v| := by
  by_contra hh
  push Not at hh
  obtain ⟨hu,hv⟩ := mixed_index_no_short_relation hp hq hk hl hLp hkl s hP hQ
    u v hrel hh.1 hh.2
  rcases hne with hne | hne
  · exact hne hu
  · exact hne hv

/-- Subtracting two coefficient candidates gives a homogeneous relation
in the original public index lattice. -/
theorem coefficientCandidate_difference {N L : ℕ} (s : ZMod N)
    {a b c d : ℤ} (hfirst : coefficientCandidate s L a b)
    (hsecond : coefficientCandidate s L c d) :
    indexRelation s (a-c) (b-d) := by
  unfold indexRelation
  push_cast
  linear_combination hsecond.2.2.2.2-hfirst.2.2.2.2

/-- Early Euclid returns an unsigned coefficient and its retained sign. -/
structure ShortRelationReport where
  /-- The unsigned coefficient of the current remainder. -/
  coefficient : ℕ
  /-- The current remainder, at or below the public stopping threshold. -/
  remainder : ℕ
  /-- The unsigned coefficient of the actual preceding remainder. -/
  previousCoefficient : ℕ
  /-- The actual preceding remainder; it completes the public basis. -/
  previousRemainder : ℕ
  /-- The sign of the current coefficient and retained second coordinate. -/
  negative : Bool
  /-- Native Euclidean divisions before reaching the threshold. -/
  steps : ℕ

/-- The integer second coordinate; sign is essential to the relation. -/
def ShortRelationReport.second (report : ShortRelationReport) : ℤ :=
  if report.negative then -(report.remainder : ℤ) else report.remainder

/-- The companion coordinate has the opposite retained sign. -/
def ShortRelationReport.companionSecond (report : ShortRelationReport) : ℤ :=
  if report.negative then (report.previousRemainder : ℤ) else -report.previousRemainder

/-- Euclid stops at the public threshold instead of computing an inverse.
Unsigned alternating coefficients grow by addition and multiplication. -/
def shortRelationLoop (T r0 r1 c0 c1 : ℕ) (negative : Bool) : ShortRelationReport :=
  if _hs : r1≤T then
    ⟨c1,r1,c0,r0,negative,0⟩
  else
    let tail := shortRelationLoop T r1 (r0%r1) c1 (c0+(r0/r1)*c1) (!negative)
    { tail with steps := tail.steps+1 }
termination_by r1
decreasing_by exact Nat.mod_lt _ (by omega)

/-- Construct a public short homogeneous relation. This executable
integer specification has no prime, local root, or supplied basis input. -/
def shortRelation (N s A : ℕ) : ShortRelationReport :=
  shortRelationLoop (N/(A+1)) N (s%N) 0 1 false

/-- The sum determinant is conserved by every unsigned Euclidean step. -/
theorem shortRelation_step_determinant (r0 r1 c0 c1 : ℕ) :
    r1*(c0+(r0/r1)*c1)+(r0%r1)*c1=r0*c1+r1*c0 := by
  have hd := Nat.mod_add_div r0 r1
  nlinarith

/-- Every actual early-Euclid output reaches the threshold and retains
a positive first coefficient, with its predecessor above threshold. -/
theorem shortRelationLoop_bounds {N A T r0 r1 c0 c1 : ℕ}
    (hT : T=N/(A+1)) (hdet : r0*c1+r1*c0=N)
    (hprev : T<r0) (hc : 0<c1) (horder : r1<r0) (negative : Bool) :
    let out := shortRelationLoop T r0 r1 c0 c1 negative
    0<out.coefficient ∧ out.coefficient≤A ∧ out.remainder≤T := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 negative with
  | h r1 ih =>
    dsimp only
    by_cases hs : r1≤T
    · rw [shortRelationLoop, dif_pos hs]
      dsimp only
      refine ⟨hc, ?_, hs⟩
      have hdiv := Nat.mod_lt N (show 0<A+1 by omega)
      have hsum := Nat.mod_add_div N (A+1)
      subst T
      nlinarith
    · rw [shortRelationLoop, dif_neg hs]
      dsimp only
      apply ih _ (Nat.mod_lt _ (by omega))
      · exact shortRelation_step_determinant _ _ _ _ |>.trans hdet
      · omega
      · have hquot : 0<r0/r1 := (Nat.div_pos (by omega) (by omega))
        nlinarith
      · exact Nat.mod_lt _ (by omega)

/-- Alternating coefficient congruences are maintained without reducing
or losing their sign. -/
theorem shortRelationLoop_correct {N : ℕ} (s : ZMod N)
    (T r0 r1 c0 c1 : ℕ) (negative : Bool)
    (hc0 : (c0 : ZMod N)*s=if negative then (r0 : ZMod N) else -(r0 : ZMod N))
    (hc1 : (c1 : ZMod N)*s=if negative then -(r1 : ZMod N) else (r1 : ZMod N)) :
    indexRelation s (shortRelationLoop T r0 r1 c0 c1 negative).coefficient
      (shortRelationLoop T r0 r1 c0 c1 negative).second := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 negative with
  | h r1 ih =>
    by_cases hs : r1≤T
    · rw [shortRelationLoop, dif_pos hs]
      cases negative <;> simpa [indexRelation, ShortRelationReport.second] using hc1
    · rw [shortRelationLoop, dif_neg hs]
      dsimp only [indexRelation, ShortRelationReport.second]
      apply ih _ (Nat.mod_lt _ (by omega))
      · cases negative <;> simpa only [Bool.not_false, Bool.not_true,
          Bool.false_eq_true, reduceIte] using hc1
      · have hd := congrArg (fun n : ℕ => (n : ZMod N)) (Nat.mod_add_div r0 r1)
        push_cast at hd
        cases negative
        · simp only [Bool.not_false, Bool.false_eq_true, reduceIte] at hc0 hc1 ⊢
          push_cast
          linear_combination hc0+(r0/r1 : ZMod N)*hc1+hd
        · simp only [Bool.not_true, reduceIte] at hc0 hc1 ⊢
          push_cast
          linear_combination hc0+(r0/r1 : ZMod N)*hc1-hd

/-- The actual early-Euclid construction provides the required bounded
nonzero relation for every positive modulus and positive width. -/
theorem shortRelation_correct {N A : ℕ} (hN : 0<N) (hA : 0<A) (s : ℕ) :
    let out := shortRelation N s A
    indexRelation (s : ZMod N) out.coefficient out.second ∧
      0<out.coefficient ∧ out.coefficient≤A ∧ |out.second|≤(N/(A+1) : ℕ) := by
  have hprev : N/(A+1)<N := Nat.div_lt_self hN (by omega)
  have hb := shortRelationLoop_bounds rfl
    (show N*1+(s%N)*0=N by omega) hprev (by omega) (Nat.mod_lt s hN) false
  have hc := shortRelationLoop_correct (s : ZMod N) (N/(A+1)) N (s%N) 0 1 false
    (by simp) (by simp)
  dsimp only [shortRelation] at hc ⊢
  refine ⟨hc, hb.1, hb.2.1, ?_⟩
  dsimp only [ShortRelationReport.second]
  split <;> simpa only [abs_neg, abs_of_nonneg (Int.natCast_nonneg _)] using
    (show ((shortRelationLoop (N/(A+1)) N (s%N) 0 1 false).remainder : ℤ)≤
      (N/(A+1) : ℕ) by exact_mod_cast hb.2.2)

/-- Early stopping never uses more Euclidean divisions than the frozen
full inverse specification, regardless of coefficient sizes. -/
theorem shortRelationLoop_steps (T N r0 r1 c0 c1 : ℕ) (negative : Bool) :
    (shortRelationLoop T r0 r1 c0 c1 negative).steps≤
      (SemiprimeWindowInverse.euclidLoop N r0 r1 0 0).steps := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 negative with
  | h r1 ih =>
    by_cases hs : r1≤T
    · rw [shortRelationLoop, dif_pos hs]
      exact Nat.zero_le _
    · have hr : r1≠0 := by omega
      rw [shortRelationLoop, dif_neg hs, SemiprimeWindowInverse.euclidLoop, dif_neg hr]
      dsimp only [SemiprimeWindowInverse.makeFrame]
      have ht := ih (r0%r1) (Nat.mod_lt r0 (by omega)) r1 c1 (c0+(r0/r1)*c1) (!negative)
      have he : ((0+N-(r0/r1*0)%N)%N)=0 := by simp
      simp only [he]
      omega

/-- The public native specification takes at most twice the input's
binary length in Euclidean divisions. This is not a Boolean clock. -/
theorem shortRelation_steps (N s A : ℕ) :
    (shortRelation N s A).steps≤2*Nat.clog 2 (s%N+1) := by
  exact (shortRelationLoop_steps (N/(A+1)) N N (s%N) 0 1 false).trans
    (SemiprimeWindowInverse.euclidLoop_steps N N (s%N) 0 0)

/-- The actual predecessor completes the short vector to a full basis;
its determinant is the original modulus, with its orientation retained. -/
theorem shortRelationLoop_determinant {N : ℕ}
    (T r0 r1 c0 c1 : ℕ) (negative : Bool) (hdet : r0*c1+r1*c0=N) :
    let out := shortRelationLoop T r0 r1 c0 c1 negative
    (out.coefficient : ℤ)*out.companionSecond-
      out.second*out.previousCoefficient=(if out.negative then (N : ℤ) else -N) := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 negative with
  | h r1 ih =>
    dsimp only
    by_cases hs : r1≤T
    · rw [shortRelationLoop, dif_pos hs]
      have hd : (r0 : ℤ)*c1+(r1 : ℤ)*c0=N := by exact_mod_cast hdet
      cases negative <;> simp only [ShortRelationReport.second,
        ShortRelationReport.companionSecond, Bool.false_eq_true, reduceIte] <;>
        nlinarith
    · rw [shortRelationLoop, dif_neg hs]
      dsimp only
      exact ih (r0%r1) (Nat.mod_lt r0 (by omega)) r1 c1 (c0+(r0/r1)*c1)
        (!negative) ((shortRelation_step_determinant _ _ _ _).trans hdet)

/-- The actual predecessor is a homogeneous relation as well. -/
theorem shortRelationLoop_companion {N : ℕ} (s : ZMod N)
    (T r0 r1 c0 c1 : ℕ) (negative : Bool)
    (hc0 : (c0 : ZMod N)*s=if negative then (r0 : ZMod N) else -(r0 : ZMod N))
    (hc1 : (c1 : ZMod N)*s=if negative then -(r1 : ZMod N) else (r1 : ZMod N)) :
    indexRelation s (shortRelationLoop T r0 r1 c0 c1 negative).previousCoefficient
      (shortRelationLoop T r0 r1 c0 c1 negative).companionSecond := by
  induction r1 using Nat.strong_induction_on generalizing r0 c0 c1 negative with
  | h r1 ih =>
    by_cases hs : r1≤T
    · rw [shortRelationLoop, dif_pos hs]
      cases negative <;> simpa [indexRelation, ShortRelationReport.companionSecond] using hc0
    · rw [shortRelationLoop, dif_neg hs]
      dsimp only [indexRelation, ShortRelationReport.companionSecond]
      apply ih (r0%r1) (Nat.mod_lt r0 (by omega))
      · cases negative <;> simpa only [Bool.not_false, Bool.not_true,
          Bool.false_eq_true, reduceIte] using hc1
      · have hd := congrArg (fun n : ℕ => (n : ZMod N)) (Nat.mod_add_div r0 r1)
        push_cast at hd
        cases negative
        · simp only [Bool.not_false, Bool.false_eq_true, reduceIte] at hc0 hc1 ⊢
          push_cast
          linear_combination hc0+(r0/r1 : ZMod N)*hc1+hd
        · simp only [Bool.not_true, reduceIte] at hc0 hc1 ⊢
          push_cast
          linear_combination hc0+(r0/r1 : ZMod N)*hc1-hd

/-- Both vectors and their full determinant come from the one actual
public early-Euclid run; no primitive-vector or basis oracle is supplied. -/
theorem shortRelation_basis {N A : ℕ} (hN : 0<N) (hA : 0<A) (s : ℕ) :
    let out := shortRelation N s A
    indexRelation (s : ZMod N) out.coefficient out.second ∧
      indexRelation (s : ZMod N) out.previousCoefficient out.companionSecond ∧
      0<out.coefficient ∧ out.coefficient≤A ∧ |out.second|≤(N/(A+1) : ℕ) ∧
      ((out.coefficient : ℤ)*out.companionSecond-out.second*out.previousCoefficient=N ∨
        (out.coefficient : ℤ)*out.companionSecond-out.second*out.previousCoefficient= -N) := by
  have hc := shortRelation_correct hN hA s
  have hp := shortRelationLoop_companion (s : ZMod N) (N/(A+1)) N (s%N) 0 1 false
    (by simp) (by simp)
  have hd := shortRelationLoop_determinant (N/(A+1)) N (s%N) 0 1 false
    (show N*1+(s%N)*0=N by omega)
  dsimp only [shortRelation] at hc ⊢
  refine ⟨hc.1,hp,hc.2.1,hc.2.2.1,hc.2.2.2,?_⟩
  dsimp only at hd
  split at hd
  · exact Or.inl hd
  · exact Or.inr hd

/-- Determinants of two homogeneous relations are exact multiples of
the original modulus, even for nonunit coordinates. -/
theorem indexRelation_determinant_dvd {N : ℕ} (s : ZMod N)
    {u v a b : ℤ} (huv : indexRelation s u v) (hab : indexRelation s a b) :
    (N : ℤ) ∣ u*b-v*a := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  unfold indexRelation at huv hab
  linear_combination (a : ZMod N)*huv-(u : ZMod N)*hab

/-- A pair of public relations with determinant ±N represents EVERY
other homogeneous relation by integer coordinates. -/
theorem indexRelation_basis_coordinates {N : ℕ} (hN : 0<N) (s : ZMod N)
    {u v c d a b : ℤ} (huv : indexRelation s u v) (hcd : indexRelation s c d)
    (hdet : u*d-v*c=(N : ℤ) ∨ u*d-v*c= -(N : ℤ))
    (hab : indexRelation s a b) :
    ∃ i j : ℤ, a=i*u+j*c ∧ b=i*v+j*d := by
  have hda := indexRelation_determinant_dvd s hab hcd
  have hdb := indexRelation_determinant_dvd s huv hab
  have hd0 : u*d-v*c≠0 := by
    have hn : (N : ℤ)≠0 := by exact_mod_cast hN.ne'
    rcases hdet with hd | hd
    · rw [hd]
      exact hn
    · rw [hd]
      exact neg_ne_zero.mpr hn
  have hia : u*d-v*c ∣ a*d-b*c := by
    rcases hdet with hd | hd <;> simpa only [hd, neg_dvd] using hda
  have hjb : u*d-v*c ∣ u*b-v*a := by
    rcases hdet with hd | hd <;> simpa only [hd, neg_dvd] using hdb
  obtain ⟨i,hi⟩ := hia
  obtain ⟨j,hj⟩ := hjb
  refine ⟨i,j,?_,?_⟩
  · apply mul_right_cancel₀ hd0
    linear_combination u*hi+c*hj
  · apply mul_right_cancel₀ hd0
    linear_combination v*hi+d*hj

/-- Integer rectangle bounds are retained before any counting view. -/
def inCoefficientRectangle (L : ℕ) (a b : ℤ) : Prop :=
  0≤a ∧ a<2*(L : ℤ) ∧ 0≤b ∧ b<(L : ℤ)^2

/-- Any two original coefficient points have bounded coordinate
differences, independent of their congruence. -/
theorem coefficientRectangle_difference {L : ℕ} {a b a' b' : ℤ}
    (ha : inCoefficientRectangle L a b) (hb : inCoefficientRectangle L a' b') :
    |a-a'|≤2*(L : ℤ) ∧ |b-b'|≤(L : ℤ)^2 := by
  constructor <;> apply abs_le.mpr <;> constructor <;>
    rcases ha with ⟨ha0,ha1,hb0,hb1⟩ <;>
    rcases hb with ⟨ha'0,ha'1,hb'0,hb'1⟩ <;> omega

/-- In a public basis of determinant ±N, the coefficient rectangle
occupies only a bounded span of second basis coordinates. -/
theorem coefficientRectangle_band_span {N L C : ℕ} (hN : 0<N)
    {u v c d a0 b0 i j i' j' : ℤ}
    (hu : 0≤u) (hub : u≤2*(L : ℤ)) (hvb : |v| * (2*(L : ℤ))≤N)
    (hdet : u*d-v*c=(N : ℤ) ∨ u*d-v*c= -(N : ℤ))
    (hvolume : L^3≤C*N)
    (hfirst : inCoefficientRectangle L (a0+i*u+j*c) (b0+i*v+j*d))
    (hsecond : inCoefficientRectangle L (a0+i'*u+j'*c) (b0+i'*v+j'*d)) :
    |j-j'|≤(2*C+1 : ℕ) := by
  have hr := coefficientRectangle_difference hfirst hsecond
  have he : (j-j')*(u*d-v*c)=
      u*((b0+i*v+j*d)-(b0+i'*v+j'*d))-
        v*((a0+i*u+j*c)-(a0+i'*u+j'*c)) := by ring
  have hn : (0 : ℤ)<N := by exact_mod_cast hN
  have hvol : (L : ℤ)^3≤(C : ℤ)*N := by exact_mod_cast hvolume
  have habs : |u*d-v*c|=(N : ℤ) := by
    rcases hdet with hd | hd <;> rw [hd] <;>
      simp only [abs_neg, abs_of_nonneg hn.le]
  have hbound : |j-j'| * (N : ℤ)≤(2*C+1 : ℕ)*(N : ℤ) := by
    calc
      |j-j'| * (N : ℤ) = |(j-j')*(u*d-v*c)| := by rw [abs_mul, habs]
      _ = |u*((b0+i*v+j*d)-(b0+i'*v+j'*d))-
          v*((a0+i*u+j*c)-(a0+i'*u+j'*c))| := by rw [he]
      _ ≤ |u*((b0+i*v+j*d)-(b0+i'*v+j'*d))|+
          |v*((a0+i*u+j*c)-(a0+i'*u+j'*c))| := abs_sub _ _
      _ = u*|(b0+i*v+j*d)-(b0+i'*v+j'*d)|+
          |v| * |(a0+i*u+j*c)-(a0+i'*u+j'*c)| := by rw [abs_mul, abs_mul, abs_of_nonneg hu]
      _ ≤ u*(L : ℤ)^2+|v| * (2*(L : ℤ)) := by nlinarith [abs_nonneg v]
      _ ≤ 2*(L : ℤ)^3+(N : ℤ) := by nlinarith [sq_nonneg (L : ℤ)]
      _ ≤ (2*C+1 : ℕ)*(N : ℤ) := by push_cast; nlinarith
  nlinarith

/-- On one basis line, mixed-index arithmetic bounds the span of the
first integer coordinate. This is the missing spacing information that
a determinant or volume bound alone would not provide. -/
theorem mixed_index_line_span {p q L k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLp : L≤p) (hkl : k≠l) (s : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) s=(k : ZMod p))
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) s=(l : ZMod q))
    {u v a0 b0 i i' : ℤ} (hu : 0<u) (hrel : indexRelation s u v)
    (hfirst : inCoefficientRectangle L (a0+i*u) (b0+i*v))
    (hsecond : inCoefficientRectangle L (a0+i'*u) (b0+i'*v)) :
    |i-i'|≤(2+3*L^2/q : ℕ) := by
  have hr := coefficientRectangle_difference hfirst hsecond
  have hda : |i-i'| * u≤2*(L : ℤ) := by
    have he : (a0+i*u)-(a0+i'*u)=(i-i')*u := by ring
    rw [he, abs_mul, abs_of_nonneg hu.le] at hr
    exact hr.1
  have hdb : |i-i'| * |v|≤(L : ℤ)^2 := by
    have he : (b0+i*v)-(b0+i'*v)=(i-i')*v := by ring
    rw [he, abs_mul] at hr
    exact hr.2
  have hs := mixed_index_relation_separation hp hq hk hl hLp hkl s hP hQ u v hrel
    (Or.inl hu.ne')
  rw [abs_of_nonneg hu.le] at hs
  rcases hs with hs | hs
  · have hln : (L : ℤ)≤p := by exact_mod_cast hLp
    have hpn : (0 : ℤ)<p := by exact_mod_cast hp.pos
    have hi : |i-i'|≤2 := by nlinarith [abs_nonneg (i-i')]
    have hmore : (2 : ℤ)≤(2+3*L^2/q : ℕ) := by exact_mod_cast (Nat.le_add_right 2 _)
    exact hi.trans hmore
  · have hw : |i-i'| * (q : ℤ)≤3*(L : ℤ)^2 := by
      nlinarith [abs_nonneg (i-i'), Int.natCast_nonneg L]
    rw [← Int.natCast_natAbs] at hw
    have hwn : (i-i').natAbs*q≤3*L^2 := by exact_mod_cast hw
    have hi := (Nat.le_div_iff_mul_le hq.pos).mpr hwn
    rw [← Int.natCast_natAbs]
    exact_mod_cast hi.trans (Nat.le_add_left _ _)

/-- A finite injective integer view with bounded pairwise span has a
uniform cardinal bound. It does not charge construction of the view. -/
theorem card_le_of_integer_span {α : Type*}
    (xs : Finset α) (f : α → ℤ) (H : ℕ)
    (hinj : Set.InjOn f xs)
    (hspan : ∀ x∈xs, ∀ y∈xs, |f x-f y|≤(H : ℤ)) :
    xs.card≤2*H+1 := by
  by_cases hx : xs.Nonempty
  · obtain ⟨x0,hx0⟩ := hx
    have hcard : (Finset.Icc (f x0-(H : ℤ)) (f x0+H)).card=2*H+1 := by
      rw [Int.card_Icc]
      omega
    rw [← hcard]
    apply Finset.card_le_card_of_injOn f ?_ hinj
    intro x hx
    have hh := (abs_le.mp (hspan x hx x0 hx0))
    exact Finset.mem_Icc.mpr (by omega)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hx, Finset.card_empty]
    omega

/-- Arithmetic line spacing and determinant-band spacing give a
universal finite parameter count. All signs and local indices remain
in the source hypotheses; no random or generic lattice assumption enters. -/
theorem mixed_index_parameter_count {p q L C k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLp : L≤p) (hkl : k≠l) (s : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) s=(k : ZMod p))
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) s=(l : ZMod q))
    {u v c d a0 b0 : ℤ} (hu : 0<u) (hub : u≤2*(L : ℤ))
    (hvb : |v| * (2*(L : ℤ))≤p*q) (hrel : indexRelation s u v)
    (hdet : u*d-v*c=(p*q : ℕ) ∨ u*d-v*c= -(p*q : ℕ))
    (hvolume : L^3≤C*(p*q)) (xs : Finset (ℤ×ℤ))
    (hxs : ∀ t∈xs, inCoefficientRectangle L
      (a0+t.1*u+t.2*c) (b0+t.1*v+t.2*d)) :
    xs.card≤(4*C+3)*(5+2*(3*L^2/q)) := by
  let bands := xs.image Prod.snd
  have hbands : bands.card≤4*C+3 := by
    have hb := card_le_of_integer_span bands id (2*C+1) (by intro x _ y _ h; exact h)
      (by
        intro j hj j' hj'
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hj
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hj'
        exact coefficientRectangle_band_span (Nat.mul_pos hp.pos hq.pos)
          hu.le hub hvb hdet hvolume (hxs x hx) (hxs y hy))
    omega
  have hfibers : ∀ j∈bands, (xs.filter (fun t => t.2=j)).card≤5+2*(3*L^2/q) := by
    intro j _
    have hf := card_le_of_integer_span (xs.filter (fun t => t.2=j)) Prod.fst
      (2+3*L^2/q) (by
        intro x hx y hy he
        have hxj := (Finset.mem_filter.mp hx).2
        have hyj := (Finset.mem_filter.mp hy).2
        exact Prod.ext he (hxj.trans hyj.symm)) (by
        intro x hx y hy
        obtain ⟨hx,hxj⟩ := Finset.mem_filter.mp hx
        obtain ⟨hy,hyj⟩ := Finset.mem_filter.mp hy
        have hfx := hxs x hx
        have hfy := hxs y hy
        rw [hxj] at hfx
        rw [hyj] at hfy
        apply mixed_index_line_span hp hq hk hl hLp hkl s hP hQ
          (a0:=a0+j*c) (b0:=b0+j*d) (i:=x.1) (i':=y.1) hu hrel
        · convert hfx using 1 <;> ring
        · convert hfy using 1 <;> ring)
    omega
  calc
    xs.card = ∑ j ∈ bands, (xs.filter (fun t => t.2=j)).card :=
      Finset.card_eq_sum_card_image Prod.snd xs
    _ ≤ ∑ _j ∈ bands, (5+2*(3*L^2/q)) := Finset.sum_le_sum hfibers
    _ = bands.card*(5+2*(3*L^2/q)) := by simp
    _ ≤ (4*C+3)*(5+2*(3*L^2/q)) := Nat.mul_le_mul_right _ hbands

/-- Native Cramer coordinates for a retained integer basis. -/
def basisCoordinates (u v c d a b : ℤ) : ℤ×ℤ :=
  ((a*d-b*c)/(u*d-v*c), (u*b-v*a)/(u*d-v*c))

/-- The concrete quotient formula represents every relation exactly;
neither divisibility nor correct coordinates are supplied as advice. -/
theorem basisCoordinates_exact {N : ℕ} (hN : 0<N) (s : ZMod N)
    {u v c d a b : ℤ} (huv : indexRelation s u v) (hcd : indexRelation s c d)
    (hdet : u*d-v*c=(N : ℤ) ∨ u*d-v*c= -(N : ℤ))
    (hab : indexRelation s a b) :
    let t := basisCoordinates u v c d a b
    a=t.1*u+t.2*c ∧ b=t.1*v+t.2*d := by
  obtain ⟨i,j,ha,hb⟩ := indexRelation_basis_coordinates hN s huv hcd hdet hab
  have hd0 : u*d-v*c≠0 := by
    have hn : (N : ℤ)≠0 := by exact_mod_cast hN.ne'
    rcases hdet with hd | hd
    · rw [hd]; exact hn
    · rw [hd]; exact neg_ne_zero.mpr hn
  have hi : (a*d-b*c)/(u*d-v*c)=i := by
    apply Int.ediv_eq_of_eq_mul_right hd0
    rw [ha,hb]
    ring
  have hj : (u*b-v*a)/(u*d-v*c)=j := by
    apply Int.ediv_eq_of_eq_mul_right hd0
    rw [ha,hb]
    ring
  dsimp only [basisCoordinates]
  rw [hi,hj]
  exact ⟨ha,hb⟩

/-- Public integer coordinates for a symmetric coefficient candidate.
The affine origin is (0,-s²); all basis data come from early Euclid. -/
def publicCoefficientCoordinates (N s L : ℕ) (point : ℤ×ℤ) : ℤ×ℤ :=
  let out := shortRelation N s (2*L)
  basisCoordinates out.coefficient out.second out.previousCoefficient out.companionSecond
    point.1 (point.2+(s : ℤ)^2)

/-- The actual public coordinate formula preserves every candidate
exactly, with the affine origin and both basis signs intact. -/
theorem publicCoefficientCoordinates_exact {N L : ℕ} (hN : 0<N) (hL : 0<L)
    (s : ℕ) (point : ℤ×ℤ) (hpoint : coefficientCandidate (s : ZMod N) L point.1 point.2) :
    let out := shortRelation N s (2*L)
    let t := publicCoefficientCoordinates N s L point
    point.1=t.1*(out.coefficient : ℤ)+t.2*out.previousCoefficient ∧
      point.2= -(s : ℤ)^2+t.1*out.second+t.2*out.companionSecond := by
  have hb := shortRelation_basis hN (show 0<2*L by omega) s
  have hrel : indexRelation (s : ZMod N) point.1 (point.2+(s : ℤ)^2) := by
    unfold indexRelation
    push_cast
    linear_combination -hpoint.2.2.2.2
  have he := basisCoordinates_exact hN (s : ZMod N) hb.1 hb.2.1 hb.2.2.2.2.2 hrel
  dsimp only [publicCoefficientCoordinates]
  dsimp only at he
  exact ⟨he.1, by linear_combination he.2⟩

/-- All bounded symmetric coefficient candidates. This rectangle filter
is a specification for a set, not the proposed efficient enumerator. -/
noncomputable def coefficientCandidates (N s L : ℕ) : Finset (ℤ×ℤ) :=
  ((Finset.Ico (0 : ℤ) (2*(L : ℤ))).product (Finset.Ico (0 : ℤ) ((L : ℤ)^2))).filter
    (fun t => (s : ZMod N)^2-(t.1 : ZMod N)*(s : ZMod N)+(t.2 : ZMod N)=0)

/-- The set specification retains exactly the original rectangle and
affine congruence. -/
theorem mem_coefficientCandidates (N s L : ℕ) (point : ℤ×ℤ) :
    point∈coefficientCandidates N s L ↔ coefficientCandidate (s : ZMod N) L point.1 point.2 := by
  rcases point with ⟨a,b⟩
  constructor
  · intro h
    obtain ⟨hmem,he⟩ := Finset.mem_filter.mp h
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hmem
    obtain ⟨ha0,ha1⟩ := Finset.mem_Ico.mp ha
    obtain ⟨hb0,hb1⟩ := Finset.mem_Ico.mp hb
    exact ⟨ha0,ha1,hb0,hb1,he⟩
  · rintro ⟨ha0,ha1,hb0,hb1,he⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr ⟨ha0,ha1⟩,Finset.mem_Ico.mpr ⟨hb0,hb1⟩⟩,he⟩

/-- The actual original mixed indices supply a candidate, including
either zero root. No finite successful-example premise is used. -/
theorem mixed_index_candidate_mem {p q L k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hk : k<L) (hl : l<L)
    (s : ℕ)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) :
    ((k : ℤ)+l,(k : ℤ)*l)∈coefficientCandidates (p*q) s L := by
  apply (mem_coefficientCandidates _ _ _ _).mpr
  exact mixed_index_coefficient_candidate hp hq hpq hk hl (s : ZMod (p*q))
    (by simpa only [map_natCast] using hP) (by simpa only [map_natCast] using hQ)

/-- The concrete coefficient set has a universal arithmetic cardinal
bound. This proves the output count, not a bit price for its rectangle
filter; a basis-line enumerator is required to spend the bound. -/
theorem mixed_index_coefficient_count {p q L C k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hk : k<L) (hl : l<L)
    (hLp : L≤p) (hkl : k≠l) (s : ℕ)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q))
    (hvolume : L^3≤C*(p*q)) :
    (coefficientCandidates (p*q) s L).card≤(4*C+3)*(5+2*(3*L^2/q)) := by
  have hN := Nat.mul_pos hp.pos hq.pos
  have hL : 0<L := by omega
  let out := shortRelation (p*q) s (2*L)
  let points := coefficientCandidates (p*q) s L
  let coords := publicCoefficientCoordinates (p*q) s L
  have hb := shortRelation_basis hN (show 0<2*L by omega) s
  have hcoords : ∀ point∈points,
      point.1=(coords point).1*(out.coefficient : ℤ)+(coords point).2*out.previousCoefficient ∧
      point.2= -(s : ℤ)^2+(coords point).1*out.second+(coords point).2*out.companionSecond := by
    intro point hpoint
    exact publicCoefficientCoordinates_exact hN hL s point
      ((mem_coefficientCandidates _ _ _ _).mp hpoint)
  have hinj : Set.InjOn coords points := by
    intro x hx y hy he
    obtain ⟨hxa,hxb⟩ := hcoords x hx
    obtain ⟨hya,hyb⟩ := hcoords y hy
    rw [he] at hxa hxb
    exact Prod.ext (hxa.trans hya.symm) (hxb.trans hyb.symm)
  have hdiv := Nat.div_mul_le_self (p*q) (2*L+1)
  have hvc : |out.second| * (2*(L : ℤ))≤(p*q : ℕ) := by
    have ht : (((p*q)/(2*L+1) : ℕ) : ℤ)*(2*(L : ℤ))≤(p*q : ℕ) := by exact_mod_cast
      ((Nat.mul_le_mul_left ((p*q)/(2*L+1)) (show 2*L≤2*L+1 by omega)).trans
        (by simpa only [Nat.mul_comm] using hdiv))
    have hv := hb.2.2.2.2.1
    change |out.second|≤((p*q)/(2*L+1) : ℕ) at hv
    nlinarith [Int.natCast_nonneg L]
  have hcount := mixed_index_parameter_count hp hq hk hl hLp hkl (s : ZMod (p*q))
    (by simpa only [map_natCast] using hP) (by simpa only [map_natCast] using hQ)
    (a0:=0) (b0:= -(s : ℤ)^2) (c:=out.previousCoefficient) (d:=out.companionSecond)
    (by exact_mod_cast hb.2.2.1) (by exact_mod_cast hb.2.2.2.1) hvc hb.1 hb.2.2.2.2.2
    hvolume (points.image coords) (by
      intro t ht
      obtain ⟨point,hpoint,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨ha,hb'⟩ := hcoords point hpoint
      have hp' := (mem_coefficientCandidates _ _ _ _).mp hpoint
      change 0≤_ ∧ _<2*(L : ℤ) ∧ 0≤_ ∧ _<(L : ℤ)^2
      simp only [zero_add]
      rw [← ha,← hb']
      exact ⟨hp'.1,hp'.2.1,hp'.2.2.1,hp'.2.2.2.1⟩)
  rw [Finset.card_image_of_injOn hinj] at hcount
  exact hcount

/-- The actual public matched modulus is bounded by four times the
predecessor of the ceiling sixth root. -/
theorem public_modulus_predecessor_bound {N : ℕ} (hN : 0<N)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth N) :
    SemiprimeEuclidRowBudget.publicRowModulus N≤
      4*(SemiprimeLehmanCoverage.sixthWidth N-1) := by
  have hm := (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).2
  omega

/-- The coefficient-volume assumption is discharged at the ACTUAL
public matched width and original padded seed interval. -/
theorem public_seed_coefficient_volume {N : ℕ} (hN : 0<N)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth N) :
    (SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus N))^3≤262144*N := by
  let m := SemiprimeEuclidRowBudget.publicRowModulus N
  let t := SemiprimeLehmanCoverage.sixthWidth N-1
  have hm : 4≤m := hB.trans (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).1
  have hmt : m≤4*t := public_modulus_predecessor_bound hN hB
  have ht6 : t^6≤N := (SemiprimeLehmanCoverage.sixthWidth_lower hN).le
  have hm6 : m^6≤4096*N := by
    calc
      m^6≤(4*t)^6 := Nat.pow_le_pow_left hmt 6
      _ = 4096*t^6 := by ring
      _ ≤ 4096*N := Nat.mul_le_mul_left _ ht6
  calc
    (SemiprimeSeedSumAcquisition.seedLength m)^3≤(4*m^2)^3 :=
      Nat.pow_le_pow_left (SemiprimeSeedSumAcquisition.seedLength_bounds hm).2 3
    _ = 64*m^6 := by ring
    _ ≤ 64*(4096*N) := Nat.mul_le_mul_left _ hm6
    _ = 262144*N := by ring

/-- The larger factor is automatically large enough to turn the
arithmetic line-spacing bound into a linear matched-width count. -/
theorem public_seed_line_quotient {p q : ℕ} (hp : 0<p) (hq : 0<q) (hpq : p≤q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q)) :
    3*(SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))^2/q≤
        3072*SemiprimeEuclidRowBudget.publicRowModulus (p*q) := by
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let t := SemiprimeLehmanCoverage.sixthWidth (p*q)-1
  have hN := Nat.mul_pos hp hq
  have hm : 4≤m := hB.trans (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).1
  have hmt : m≤4*t := public_modulus_predecessor_bound hN hB
  have ht6 : t^6<p*q := SemiprimeLehmanCoverage.sixthWidth_lower hN
  have hNq : p*q≤q^2 := by nlinarith
  have ht3 : t^3≤q := by
    by_contra h
    have hqt : q<t^3 := by omega
    have hh : q^2<(t^3)^2 := Nat.pow_lt_pow_left hqt (by decide)
    have he : (t^3)^2=t^6 := by ring
    rw [he] at hh
    omega
  have hm3 : m^3≤64*q := by
    calc
      m^3≤(4*t)^3 := Nat.pow_le_pow_left hmt 3
      _ = 64*t^3 := by ring
      _ ≤ 64*q := Nat.mul_le_mul_left _ ht3
  have hnum : 3*(SemiprimeSeedSumAcquisition.seedLength m)^2≤3072*m*q := by
    calc
      3*(SemiprimeSeedSumAcquisition.seedLength m)^2≤3*(4*m^2)^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
          (SemiprimeSeedSumAcquisition.seedLength_bounds hm).2 2)
      _ = (48*m)*m^3 := by ring
      _ ≤ (48*m)*(64*q) := Nat.mul_le_mul_left _ hm3
      _ = 3072*m*q := by ring
  have hd := Nat.div_le_div_right (c:=q) hnum
  simpa only [Nat.mul_div_cancel _ hq] using hd

/-- At the public matched width the entire mixed-index symmetric
coefficient set has O(ceiling(N^(1/6))) cardinality. This is an arithmetic
search-space theorem, not an acquisition, enumeration or bit-clock claim. -/
theorem public_mixed_index_coefficient_count {p q k l : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hk : k<SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hl : l<SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hLp : SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))≤p)
    (hkl : k≠l) (s : ℕ)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q)) :
    (coefficientCandidates (p*q) s (SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))).card≤
        1048579*(5+12288*SemiprimeLehmanCoverage.sixthWidth (p*q)) := by
  have hN := Nat.mul_pos hp.pos hq.pos
  have hc := mixed_index_coefficient_count hp hq hk hl hLp hkl s hP hQ
    (public_seed_coefficient_volume hN hB)
  have hqbound := public_seed_line_quotient hp.pos hq.pos hpq hB
  have hmbound := (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).2
  norm_num only at hc
  calc
    _ ≤ 1048579*(5+2*(3*(SemiprimeSeedSumAcquisition.seedLength
        (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))^2/q)) := hc
    _ ≤ 1048579*(5+2*(3072*SemiprimeEuclidRowBudget.publicRowModulus (p*q))) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hqbound) _)
    _ ≤ 1048579*(5+12288*SemiprimeLehmanCoverage.sixthWidth (p*q)) := by nlinarith

/-- A quadratic with two short integer roots has no other short root
in a prime field. -/
theorem short_quadratic_root {p L k i j : ℕ} (hp : p.Prime)
    (hLp : L≤p) (hk : k<L) (hi : i<L) (hj : j<L)
    (he : (k : ZMod p)^2-((i : ZMod p)+j)*(k : ZMod p)+(i : ZMod p)*j=0) :
    k=i ∨ k=j := by
  let : Fact p.Prime := ⟨hp⟩
  have hmul : ((k : ZMod p)-i)*((k : ZMod p)-j)=0 := by linear_combination he
  have hinj : ∀ n<L, ∀ n'<L, (n : ZMod p)=(n' : ZMod p) → n=n' := by
    intro n hn n' hn' hh
    have hv := congrArg ZMod.val hh
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hn.trans_le hLp),
      Nat.mod_eq_of_lt (hn'.trans_le hLp)] using hv
  rcases mul_eq_zero.mp hmul with hh | hh
  · exact Or.inl (hinj k hk i hi (sub_eq_zero.mp hh))
  · exact Or.inr (hinj k hk j hj (sub_eq_zero.mp hh))

/-- Any candidate that splits into two short integer roots is exactly
the original local-root pair, up to the retained prime orientation. -/
theorem mixed_index_root_pair_unique {p q L k l i j : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hLp : L≤p) (hLq : L≤q)
    (hk : k<L) (hl : l<L) (hi : i<L) (hj : j<L) (hkl : k≠l)
    (s : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) s=(k : ZMod p))
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) s=(l : ZMod q))
    (he : coefficientCandidate s L ((i : ℤ)+j) ((i : ℤ)*j)) :
    (k=i ∧ l=j) ∨ (k=j ∧ l=i) := by
  have hpr := congrArg (ZMod.castHom (dvd_mul_right p q) (ZMod p)) he.2.2.2.2
  have hqr := congrArg (ZMod.castHom (dvd_mul_left q p) (ZMod q)) he.2.2.2.2
  simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero, hP] at hpr
  simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero, hQ] at hqr
  push_cast at hpr hqr
  have hkp := short_quadratic_root hp hLp hk hi hj hpr
  have hlq := short_quadratic_root hq hLq hl hi hj hqr
  omega

/-- Testing the two actual integer roots of a splitting candidate
recovers the smaller prime in one of the two original GCDs. -/
theorem mixed_index_splitting_candidate_recovers {p q L k l i j : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hLp : L≤p) (hLq : L≤q)
    (hk : k<L) (hl : l<L) (hi : i<L) (hj : j<L) (hkl : k≠l)
    (s : ZMod (p*q))
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) s=(k : ZMod p))
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) s=(l : ZMod q))
    (he : coefficientCandidate s L ((i : ℤ)+j) ((i : ℤ)*j)) :
    (p*q).gcd (s-(i : ZMod (p*q))).val=p ∨
      (p*q).gcd (s-(j : ZMod (p*q))).val=p := by
  have hpair := mixed_index_root_pair_unique hp hq hLp hLq hk hl hi hj hkl s hP hQ he
  have hg := distinct_index_gcd hp hq hk hl hLq hkl s hP hQ
  rcases hpair with hpair | hpair
  · exact Or.inl (hpair.1 ▸ hg)
  · exact Or.inr (hpair.1 ▸ hg)

/-- The original marked decoder on the ACTUAL matched-width long
route produces a nonempty, linearly bounded symmetric candidate set for
every mixed original root pair. The hidden indices certify the result
and are not executable inputs to the public basis or coordinate formula. -/
theorem actual_public_route_mixed_index_candidates {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : SemiprimeWrapIndexRecovery.routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let g := ZMod.unitOfCoprime a hc
      let alpha := SemiprimeSeedSumAcquisition.seedBase
        (SemiprimeCentreFreeCover.projectedUnit g m) m
      let L := SemiprimeSeedSumAcquisition.seedLength m
      ∀ (x : ZMod (p*q)) (denom : (ZMod (p*q))ˣ),
        (denom : ZMod (p*q))=x*targetDerivative (alpha : ZMod (p*q)) x L →
        ∀ k l : ℕ, k<L → l<L → k≠l →
        ZMod.castHom (dvd_mul_right p q) (ZMod p) x=
          (ZMod.castHom (dvd_mul_right p q) (ZMod p) (alpha : ZMod (p*q)))^k →
        ZMod.castHom (dvd_mul_left q p) (ZMod q) x=
          (ZMod.castHom (dvd_mul_left q p) (ZMod q) (alpha : ZMod (p*q)))^l →
        let s := decodedIndex (alpha : ZMod (p*q)) x L denom
        ((k : ℤ)+l,(k : ℤ)*l)∈coefficientCandidates (p*q) s.val L ∧
          (coefficientCandidates (p*q) s.val L).card≤
            1048579*(5+12288*SemiprimeLehmanCoverage.sixthWidth (p*q)) := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  have hdata := SemiprimeWrapIndexRecovery.routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hdata
  obtain ⟨hc,hlong⟩ := hdata
  have hN := Nat.mul_pos hp.pos hq.pos
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  let alpha := SemiprimeSeedSumAcquisition.seedBase
    (SemiprimeCentreFreeCover.projectedUnit g m) m
  let L := SemiprimeSeedSumAcquisition.seedLength m
  have hm : 4≤m := hB.trans (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).1
  have hperiods := SemiprimeSeedSumAcquisition.long_seed_interval_periods hm g hlong
  have hLp : L≤p := hperiods.1.trans
    (local_unit_period_lt_prime hp (dvd_mul_right p q) alpha).le
  refine ⟨hc,?_⟩
  dsimp only
  intro x denom hdenom k l hk hl hkl hP hQ
  let s := decodedIndex (alpha : ZMod (p*q)) x L denom
  have hpr := decodedIndex_map_root (ZMod.castHom (dvd_mul_right p q) (ZMod p))
    (alpha : ZMod (p*q)) x L denom hdenom hk hP
  have hqr := decodedIndex_map_root (ZMod.castHom (dvd_mul_left q p) (ZMod q))
    (alpha : ZMod (p*q)) x L denom hdenom hl hQ
  have hsP : (s.val : ZMod p)=(k : ZMod p) := by
    rw [SemiprimeCentreFreeCover.castHom_val (dvd_mul_right p q)]
    exact hpr
  have hsQ : (s.val : ZMod q)=(l : ZMod q) := by
    rw [SemiprimeCentreFreeCover.castHom_val (dvd_mul_left q p)]
    exact hqr
  exact ⟨mixed_index_candidate_mem hp hq hpq.ne hk hl s.val hsP hsQ,
    public_mixed_index_coefficient_count hp hq hpq.le hB hk hl hLp hkl s.val hsP hsQ⟩

end RiemannGaussian.SemiprimeIndexLattice
