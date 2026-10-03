/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeGuardedTrace

/-!
# Weighted cancellation of retained quadratic rows

Cancelling the common N-times-denominator term factors the quadratic
through the public linear direction. Exact centering errors show what
remains in its physical index. Adjacent original rows, with all four
public center combinations, form an N-only candidate family. Its guarded
trace detector recovers a new literal control. These are construction,
information and recovery theorems, not universal coverage or bit bounds.
-/

namespace RiemannGaussian.SemiprimeWeightedRows

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily

/-- Every emitted Euclidean denominator is at most the public modulus.
The invariant is preserved through all intermediate and recursive rows. -/
theorem euclidPairs_denominator_le {m r₀ r₁ x y : ℕ} {negative : Bool}
    (horder : r₁<r₀) (hy : 0<y) (hdet : r₀*y+r₁*x=m)
    {z : ℤ×ℕ} (hz : z∈euclidPairs r₀ r₁ x y negative) : z.2≤m := by
  rw [euclidPairs] at hz
  split_ifs at hz with hr
  · simp only [List.not_mem_nil] at hz
  · have hrpos : 0<r₁ := by omega
    simp only [List.mem_cons,List.mem_append,List.mem_map] at hz
    rcases hz with hcur | hmid | htail
    · subst z
      have hmul := Nat.le_mul_of_pos_left y (show 0<r₀ by omega)
      omega
    · obtain ⟨k,hk,rfl⟩ := hmid
      have hquot : k+1<r₀/r₁ := by
        have := List.mem_range.mp hk
        omega
      have hmul : (k+1)*r₁≤r₀ :=
        (Nat.mul_le_mul_right r₁ hquot.le).trans (Nat.div_mul_le_self _ _)
      have hprod : r₁*(x+(k+1)*y)≤m := by
        calc
          _ = r₁*x+((k+1)*r₁)*y := by ring
          _ ≤ r₁*x+r₀*y := Nat.add_le_add_left (Nat.mul_le_mul_right y hmul) _
          _ = m := by omega
      exact (Nat.le_mul_of_pos_left _ hrpos).trans hprod
    · have hquot : 0<r₀/r₁ := Nat.div_pos horder.le hrpos
      have hnew : r₁*(x+r₀/r₁*y)+(r₀%r₁)*y=m := by
        rw [←euclid_determinant_step,hdet]
      exact euclidPairs_denominator_le (Nat.mod_lt _ hrpos) (by positivity) hnew htail
termination_by r₁
decreasing_by exact Nat.mod_lt _ (by omega)

/-- The actual N-only coordinate constructor has public-size weights. -/
theorem publicPairs_denominator_le {N m j : ℕ} (hm : 0<m) {z : ℤ×ℕ}
    (hz : z∈publicPairs N m j) : z.2≤m :=
  euclidPairs_denominator_le (Nat.mod_lt _ hm) (by decide) (by simp) hz

/-- Signed determinant of the retained quotient coordinates. -/
def rowDet (left right : QuotientRow) : ℤ := right.t*left.a-left.t*right.a

/-- Cancel the common N term, keeping both source rows separately upstream. -/
def weightedRow (left right : QuotientRow) : QuotientRow :=
  ⟨rowDet left right, right.t*left.b-left.t*right.b,
    right.t*left.c-left.t*right.c, 0, left.divisions+right.divisions⟩

/-- This cancellation is exact over integers, before any modular map. -/
theorem weightedRow_relation {N m j : ℤ} {left right : QuotientRow}
    (hl : quotientRelation N m j left.a left.b left.c left.t)
    (hr : quotientRelation N m j right.a right.b right.c right.t) :
    quotientRelation N m j (weightedRow left right).a (weightedRow left right).b
      (weightedRow left right).c 0 := by
  unfold quotientRelation at hl hr ⊢
  unfold weightedRow rowDet
  linear_combination right.t*hl-left.t*hr

/-- Every same-residue cancellation has the common public factor mX+j. -/
theorem weighted_scaled_factorization {N m j : ℤ} {left right : QuotientRow}
    (hl : quotientRelation N m j left.a left.b left.c left.t)
    (hr : quotientRelation N m j right.a right.b right.c right.t) (X : ℤ) :
    m^2*(right.t*quadratic left.a left.b left.c X-
        left.t*quadratic right.a right.b right.c X)=
      (m*X+j)*(rowDet left right*(m*X-j)+m*(weightedRow left right).b) := by
  unfold quotientRelation at hl hr
  unfold quadratic weightedRow rowDet
  linear_combination right.t*hl-left.t*hr

/-- Primitive determinant coordinates give an integral linear companion.
No hidden factor is used to obtain this public factorization. -/
theorem weighted_factorization {N m j d h : ℤ} {left right : QuotientRow}
    (hm : m≠0)
    (hl : quotientRelation N m j left.a left.b left.c left.t)
    (hr : quotientRelation N m j right.a right.b right.c right.t)
    (hdet : rowDet left right=m*d)
    (hb : (weightedRow left right).b=j*d+m*h) (X : ℤ) :
    right.t*quadratic left.a left.b left.c X-
        left.t*quadratic right.a right.b right.c X=(m*X+j)*(d*X+h) := by
  apply mul_left_cancel₀ (pow_ne_zero 2 hm)
  calc
    _ = (m*X+j)*(rowDet left right*(m*X-j)+m*(weightedRow left right).b) :=
      weighted_scaled_factorization hl hr X
    _ = _ := by rw [hdet,hb]; ring

/-- The companion's integrality follows from the original quotient class
and the public coprimality condition, rather than a division oracle. -/
theorem weighted_integral_companion {N m j d : ℤ} {left right : QuotientRow}
    (hm : m≠0) (hj : IsCoprime m j)
    (hl : quotientRelation N m j left.a left.b left.c left.t)
    (hr : quotientRelation N m j right.a right.b right.c right.t)
    (hdet : rowDet left right=m*d) :
    ∃ h : ℤ, (weightedRow left right).b=j*d+m*h ∧
      ∀ X : ℤ, right.t*quadratic left.a left.b left.c X-
        left.t*quadratic right.a right.b right.c X=(m*X+j)*(d*X+h) := by
  have hw := weightedRow_relation hl hr
  change m^2*(weightedRow left right).c-j*m*(weightedRow left right).b+
    j^2*rowDet left right=N*0 at hw
  rw [hdet] at hw
  have hz : m*(m*(weightedRow left right).c-j*((weightedRow left right).b-j*d))=0 := by
    linear_combination hw
  have he : m*(weightedRow left right).c=j*((weightedRow left right).b-j*d) := by
    have := (mul_eq_zero.mp hz).resolve_left hm
    linarith only [this]
  have hd : m ∣ j*((weightedRow left right).b-j*d) := by
    rw [←he]
    exact dvd_mul_right _ _
  obtain ⟨h,hh⟩ := hj.dvd_of_dvd_mul_left hd
  have hb : (weightedRow left right).b=j*d+m*h := by linarith only [hh]
  exact ⟨h,hb,weighted_factorization hm hl hr hdet hb⟩

/-- The remaining exponent is a public linear-direction exponent. -/
theorem weighted_giant_exponent {N m j : ℤ} {left right : QuotientRow}
    (hl : quotientRelation N m j left.a left.b left.c left.t)
    (hr : quotientRelation N m j right.a right.b right.c right.t) :
    right.t*giantExponent m j left.a left.b left.c-
      left.t*giantExponent m j right.a right.b right.c=
        rowDet left right*(1-2*j)+m*(weightedRow left right).b := by
  rw [giantExponent_eq hl,giantExponent_eq hr]
  unfold rowDet weightedRow
  ring

/-- Integer weights act on already retained group values without a matrix. -/
theorem weighted_power {G : Type*} [CommGroup G] (g : G) (e₁ e₂ t₁ t₂ : ℤ) :
    g^(t₂*e₁-t₁*e₂)=(g^e₁)^t₂*(g^e₂)^(-t₁) := by
  rw [zpow_sub,zpow_mul,zpow_mul,zpow_neg]
  simp only [←zpow_mul,mul_comm]

/-- Public unrounded midpoint with the complete offset retained. -/
def centerNumerator (m j A B : ℤ) (z : QuotientRow) : ℤ :=
  z.a*A+z.t*B+2*(z.b*m-2*z.a*j)

/-- Literal nearest integer m-squared phase used by both public centers. -/
def roundedShift (m H : ℤ) : ℤ := (H+m^2)/(2*m^2)

/-- Exact signed rounding error, retained before applying its envelope. -/
def roundingError (m H : ℤ) : ℤ := 2*m^2*roundedShift m H-H

theorem publicShift_midpoint (N m j : ℕ) (z : QuotientRow) :
    publicShift N m j z.a z.b z.t=roundedShift m
      (centerNumerator m j ((N/2).sqrt+N.sqrt) (N.sqrt+(2*N).sqrt) z) := by
  unfold publicShift lowerSum upperSum roundedShift centerNumerator
  congr 1
  split_ifs <;> ring

theorem reflectedShift_midpoint (N m j : ℕ) (z : QuotientRow) :
    reflectedShift N m j z.a z.b z.t=roundedShift m
      (centerNumerator m j (N.sqrt+(2*N).sqrt) ((N/2).sqrt+N.sqrt) z) := by
  unfold reflectedShift roundedShift centerNumerator
  dsimp only
  congr 1
  split_ifs <;> ring

/-- Both signs and the exact tie convention are covered. -/
theorem roundingError_abs_le {m H : ℤ} (hm : 0<m) : |roundingError m H|≤m^2 := by
  have hpos : 0<2*m^2 := by positivity
  have hmod := Int.emod_nonneg (H+m^2) (ne_of_gt hpos)
  have hlt := Int.emod_lt_of_pos (H+m^2) hpos
  have he := Int.emod_add_mul_ediv (H+m^2) (2*m^2)
  unfold roundingError roundedShift
  apply abs_le.mpr
  constructor <;> nlinarith only [he,hmod,hlt]

/-- Exact physical index after arbitrary two public centers. The q term
cancels, but the center difference and signed rounding errors survive. -/
theorem weighted_centered_index {m j p q A₁ B₁ A₂ B₂ i₁ i₂ : ℤ}
    {left right : QuotientRow}
    (hl : m^2*i₁=left.a*p+left.t*q+left.b*m-2*left.a*j)
    (hr : m^2*i₂=right.a*p+right.t*q+right.b*m-2*right.a*j) :
    2*m^2*(right.t*(i₁-roundedShift m (centerNumerator m j A₁ B₁ left))-
      left.t*(i₂-roundedShift m (centerNumerator m j A₂ B₂ right)))=
      rowDet left right*(2*p-A₁)+left.t*right.a*(A₂-A₁)+left.t*right.t*(B₂-B₁)-
        (right.t*roundingError m (centerNumerator m j A₁ B₁ left)-
          left.t*roundingError m (centerNumerator m j A₂ B₂ right)) := by
  unfold roundingError centerNumerator rowDet
  linear_combination 2*right.t*hl-2*left.t*hr

/-- Same-center cancellation leaves the factor's distance from that
center, with only the explicit denominator-weighted rounding correction. -/
theorem same_center_index_deviation {m p q A B j i₁ i₂ : ℤ}
    {left right : QuotientRow} (hm : 0<m) (ht₁ : 0≤left.t) (ht₂ : 0≤right.t)
    (hdet : |rowDet left right|=m)
    (hl : m^2*i₁=left.a*p+left.t*q+left.b*m-2*left.a*j)
    (hr : m^2*i₂=right.a*p+right.t*q+right.b*m-2*right.a*j) :
    |2*p-A|≤2*m*|right.t*(i₁-roundedShift m (centerNumerator m j A B left))-
      left.t*(i₂-roundedShift m (centerNumerator m j A B right))|+
        m*(left.t+right.t) := by
  let I := right.t*(i₁-roundedShift m (centerNumerator m j A B left))-
    left.t*(i₂-roundedShift m (centerNumerator m j A B right))
  let ε₁ := roundingError m (centerNumerator m j A B left)
  let ε₂ := roundingError m (centerNumerator m j A B right)
  have he : rowDet left right*(2*p-A)=2*m^2*I+(right.t*ε₁-left.t*ε₂) := by
    have h := weighted_centered_index (A₁:=A) (B₁:=B) (A₂:=A) (B₂:=B) hl hr
    dsimp [I,ε₁,ε₂]
    linarith only [h]
  have hε₁ : |ε₁|≤m^2 := roundingError_abs_le hm
  have hε₂ : |ε₂|≤m^2 := roundingError_abs_le hm
  have hb : |right.t*ε₁-left.t*ε₂|≤(left.t+right.t)*m^2 := by
    calc
      _ ≤ |right.t*ε₁|+|left.t*ε₂| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (right.t*ε₁) (-(left.t*ε₂))
      _ = right.t*|ε₁|+left.t*|ε₂| := by rw [abs_mul,abs_mul,abs_of_nonneg ht₁,abs_of_nonneg ht₂]
      _ ≤ (left.t+right.t)*m^2 := by
        nlinarith only [mul_le_mul_of_nonneg_left hε₁ ht₂,mul_le_mul_of_nonneg_left hε₂ ht₁]
  have hn : m*|2*p-A|≤2*m^2*|I|+(left.t+right.t)*m^2 := by
    calc
      _ = |rowDet left right*(2*p-A)| := by rw [abs_mul,hdet]
      _ = |2*m^2*I+(right.t*ε₁-left.t*ε₂)| := by rw [he]
      _ ≤ |2*m^2*I|+|right.t*ε₁-left.t*ε₂| := abs_add_le _ _
      _ ≤ 2*m^2*|I|+(left.t+right.t)*m^2 := by
        rw [abs_mul,abs_of_nonneg (show 0≤2*m^2 by positivity)]
        exact add_le_add (le_refl _) hb
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    m*|2*p-A| ≤ 2*m^2*|I|+(left.t+right.t)*m^2 := hn
    _ = m*(2*m*|I|+m*(left.t+right.t)) := by ring

/-- The index cannot fit the proposed window if this actual public
center is too far from the factor. This is not a lower bound on factoring. -/
theorem same_center_window_obstruction {m p q A B j i₁ i₂ M : ℤ}
    {left right : QuotientRow} (hm : 0<m) (ht₁ : 0≤left.t) (ht₂ : 0≤right.t)
    (hdet : |rowDet left right|=m)
    (hl : m^2*i₁=left.a*p+left.t*q+left.b*m-2*left.a*j)
    (hr : m^2*i₂=right.a*p+right.t*q+right.b*m-2*right.a*j)
    (hfar : m*(2*M+left.t+right.t) < |2*p-A|) :
    M < |right.t*(i₁-roundedShift m (centerNumerator m j A B left))-
      left.t*(i₂-roundedShift m (centerNumerator m j A B right))| := by
  have hd := same_center_index_deviation (A:=A) (B:=B) hm ht₁ ht₂ hdet hl hr
  by_contra hn
  have hb := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (show 0≤2*m by positivity)
  nlinarith only [hd,hb,hfar]

/-- Both original rows and their individual public centers are retained. -/
structure WeightedPacket where
  /-- The original left row and its public center. -/
  left : FamilyPacket
  /-- The original right row and its public center. -/
  right : FamilyPacket
deriving Repr

/-- Exact exponent from the two original centered packet exponents. -/
def weightedPacketExponent (m : ℕ) (w : WeightedPacket) : ℤ :=
  w.right.original.t*packetExponent m w.left-w.left.original.t*packetExponent m w.right

theorem weightedPacket_power_reuse {G : Type*} [CommGroup G] (g : G)
    (m : ℕ) (w : WeightedPacket) :
    g^weightedPacketExponent m w=
      (g^packetExponent m w.left)^w.right.original.t*
        (g^packetExponent m w.right)^(-w.left.original.t) :=
  weighted_power g _ _ _ _

/-- All four center combinations for one adjacent original pair. -/
def pairPackets (N m j : ℕ) (left right : QuotientRow) : List WeightedPacket :=
  let ls := FamilyPacket.mk j left (publicShift N m j left.a left.b left.t)
  let ll := FamilyPacket.mk j left (reflectedShift N m j left.a left.b left.t)
  let rs := FamilyPacket.mk j right (publicShift N m j right.a right.b right.t)
  let rl := FamilyPacket.mk j right (reflectedShift N m j right.a right.b right.t)
  [⟨ls,rs⟩,⟨ls,rl⟩,⟨ll,rs⟩,⟨ll,rl⟩]

/-- Adjacent original quadratics are paired before projecting their powers. -/
def weightedResiduePackets (N m j : ℕ) : List WeightedPacket :=
  let rows := (publicPairs N m j).map fun v => liftRow N m j (publicInverse m j) v.1 v.2
  (rows.zip rows.tail).flatMap fun v => pairPackets N m j v.1 v.2

/-- The constructor enumerates all unit residues from public inputs. -/
def publicWeightedPackets (N m : ℕ) : List WeightedPacket :=
  (List.range m).flatMap fun j => if j.Coprime m then weightedResiduePackets N m j else []

/-- Project the public candidate family while retaining its packets upstream. -/
def publicWeightedExponents (N m : ℕ) : List ℤ :=
  (publicWeightedPackets N m).map (weightedPacketExponent m)

private theorem length_flatMap_const {α β : Type*} (f : α → List β) (k : ℕ)
    (hf : ∀ x, (f x).length=k) (xs : List α) : (xs.flatMap f).length=k*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [hf,ih,Nat.mul_add,Nat.add_comm]

private theorem length_flatMap_le {α β γ : Type*} (f : α → List β) (g : α → List γ)
    (k : ℕ) (hf : ∀ x, (f x).length≤k*(g x).length) (xs : List α) :
    (xs.flatMap f).length≤k*(xs.flatMap g).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa only [List.flatMap_cons,List.length_append,Nat.mul_add] using add_le_add (hf x) ih

/-- Four center combinations per adjacent original pair give at most
twice the original two-center packet count. This is a count, not a bit price. -/
theorem weightedResiduePackets_length_le (N m j : ℕ) :
    (weightedResiduePackets N m j).length≤2*(residuePackets N m j).length := by
  have hbase : (residuePackets N m j).length=2*(publicPairs N m j).length := by
    exact length_flatMap_const _ 2 (by intro v; rfl) _
  unfold weightedResiduePackets
  rw [length_flatMap_const _ 4 (by intro v; rfl),List.length_zip,List.length_map,hbase]
  have h := Nat.min_le_left (publicPairs N m j).length
    (((publicPairs N m j).map fun v => liftRow N m j (publicInverse m j) v.1 v.2).tail.length)
  omega

theorem publicWeightedPackets_length_le (N m : ℕ) :
    (publicWeightedPackets N m).length≤2*(publicPackets N m).length := by
  apply length_flatMap_le _ _ 2
  intro j
  split_ifs
  · exact weightedResiduePackets_length_le N m j
  · simp

/-- Original weighted units precede every inverse-orbit trace compression. -/
def weightedUnitRows {N : ℕ} (m : ℕ) (g : (ZMod N)ˣ) : List (ZMod N)ˣ :=
  (publicWeightedExponents N m).map fun e => g^e

/-- Complete guarded trace extraction on the new N-only candidate family. -/
noncomputable def recoverWeightedRows {N : ℕ} (m : ℕ) (g : (ZMod N)ˣ) : Option ℕ :=
  SemiprimeGuardedTrace.guardedTraceRows (weightedUnitRows m g)

theorem recoverWeightedRows_sound {N m d : ℕ} {g : (ZMod N)ˣ}
    (hd : recoverWeightedRows m g=some d) : SemiprimeGroupSelection.ProperDivisor N d :=
  SemiprimeGuardedTrace.guardedTraceRows_sound _ hd

theorem recoverWeightedRows_gcd_bound {N m : ℕ} (g : (ZMod N)ˣ) :
    SemiprimeGuardedTrace.guardedTraceGcdCount (weightedUnitRows m g)≤
      5*(publicWeightedPackets N m).length := by
  simpa [weightedUnitRows,publicWeightedExponents] using
    SemiprimeGuardedTrace.guardedTraceGcdCount_le (weightedUnitRows m g)

/-- All guards and recovery GCDs fit ten per original public packet.
Construction, group powers and polynomial bit costs remain separate. -/
theorem recoverWeightedRows_original_gcd_bound {N m : ℕ} (g : (ZMod N)ˣ) :
    SemiprimeGuardedTrace.guardedTraceGcdCount (weightedUnitRows m g)≤
      10*(publicPackets N m).length := by
  have hg := recoverWeightedRows_gcd_bound (m:=m) g
  have hp := Nat.mul_le_mul_left 5 (publicWeightedPackets_length_le N m)
  omega

theorem publicWeightedExponent_mem_of_residue {N m j : ℕ} (hj : j<m) (hc : j.Coprime m)
    {e : ℤ} (he : e∈(weightedResiduePackets N m j).map (weightedPacketExponent m)) :
    e∈publicWeightedExponents N m := by
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp he
  apply List.mem_map.mpr
  refine ⟨w,?_,rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨j,List.mem_range.mpr hj,?_⟩
  change w∈(if j.Coprime m then weightedResiduePackets N m j else [])
  rwa [if_pos hc]

theorem recoverWeightedRows_succeeds_of_pair {N m : ℕ} [NeZero N]
    (g : (ZMod N)ˣ) {e f : ℤ}
    (he : e∈publicWeightedExponents N m) (hf : f∈publicWeightedExponents N m)
    (hp : SemiprimeGroupSelection.ProperDivisor N
        (N.gcd (((g^e : (ZMod N)ˣ) : ZMod N)-((g^f : (ZMod N)ˣ) : ZMod N)).val) ∨
      SemiprimeGroupSelection.ProperDivisor N
        (N.gcd (((g^e : (ZMod N)ˣ) : ZMod N)*((g^f : (ZMod N)ˣ) : ZMod N)-1).val)) :
    ∃ d, recoverWeightedRows m g=some d := by
  apply SemiprimeGuardedTrace.guardedTraceRows_succeeds_of_pair (weightedUnitRows m g)
    (List.mem_map.mpr ⟨e,he,rfl⟩) (List.mem_map.mpr ⟨f,hf,rfl⟩) hp

/-- Literal public base; no factor or private order is supplied. -/
def controlBase : (ZMod 788096216222522769981991129)ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 788096216222522769981991129)

set_option maxRecDepth 32768 in
/-- These two cancellations belong to the complete N-only adjacent family. -/
theorem control_weighted_exponents :
    (966926180542225069170 : ℤ)∈publicWeightedExponents 788096216222522769981991129 30403 ∧
    (5440830797789338080020 : ℤ)∈publicWeightedExponents 788096216222522769981991129 30403 := by
  constructor
  · apply publicWeightedExponent_mem_of_residue (j:=7483) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel
  · apply publicWeightedExponent_mem_of_residue (j:=11359) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel

theorem control_weighted_values :
    ((controlBase^(966926180542225069170 : ℤ) : (ZMod 788096216222522769981991129)ˣ) :
      ZMod 788096216222522769981991129)=339724066659803716926062920 ∧
    ((controlBase^(5440830797789338080020 : ℤ) : (ZMod 788096216222522769981991129)ˣ) :
      ZMod 788096216222522769981991129)=406912301288304218152558959 := by
  norm_num only [controlBase,zpow_ofNat,Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime]
  constructor <;> reduce_mod_char

theorem control_weighted_product :
    SemiprimeGroupSelection.ProperDivisor 788096216222522769981991129
      ((788096216222522769981991129 : ℕ).gcd
        ((339724066659803716926062920*406912301288304218152558959-1 :
          ZMod 788096216222522769981991129)).val) := by
  norm_num [SemiprimeGroupSelection.ProperDivisor,ZMod.val_ofNat]

/-- The complete guarded procedure recovers on the original 90-bit native
failure input. The proving pair and the factor are not algorithm inputs. -/
theorem control_public_weighted_recovers :
    ∃ d, recoverWeightedRows 30403 controlBase=some d ∧
      SemiprimeGroupSelection.ProperDivisor 788096216222522769981991129 d := by
  have hp : SemiprimeGroupSelection.ProperDivisor 788096216222522769981991129
      ((788096216222522769981991129 : ℕ).gcd
        (((controlBase^(966926180542225069170 : ℤ) : (ZMod 788096216222522769981991129)ˣ) :
          ZMod 788096216222522769981991129)*
          ((controlBase^(5440830797789338080020 : ℤ) : (ZMod 788096216222522769981991129)ˣ) :
            ZMod 788096216222522769981991129)-1).val) := by
    rw [control_weighted_values.1,control_weighted_values.2]
    exact control_weighted_product
  obtain ⟨d,hd⟩ := recoverWeightedRows_succeeds_of_pair controlBase
    control_weighted_exponents.1 control_weighted_exponents.2 (Or.inr hp)
  exact ⟨d,hd,recoverWeightedRows_sound hd⟩

end RiemannGaussian.SemiprimeWeightedRows
