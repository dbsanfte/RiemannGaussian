/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeQuotientRows
import Mathlib.Data.Finset.Card

/-!
# Arithmetic forcing by differences of dense quotient rows

The public source keeps both numerator representatives for every positive
denominator below m. At the true factor residue, m proof-side representatives
have integral indices in one bounded interval. Pigeonhole forces a short
difference index; re-lifting the difference changes that index by at most
three. This establishes actual emitted-row coverage, rather than assuming a
hidden short vector. The source has quadratic size in m: it does not establish
the requested sixth-root construction or full bit-operation bound.
-/

namespace RiemannGaussian.SemiprimeDenseRowCoverage

open SemiprimeQuotientRows

/-- A public representative of the modular numerator for denominator t. -/
def representative (N m j t : ℕ) : ℕ := (quotientSlope N m j*t)%m

/-- Both possible differences of canonical numerators are emitted. -/
def denseRow (N m j t : ℕ) (negative : Bool) : QuotientRow :=
  liftRow N m j (publicInverse m j)
    ((representative N m j t : ℤ)-(if negative then (m : ℤ) else 0)) t

/-- The executable N-only stream emits two rows at each residue/denominator
pair. A nonunit residue can be handled by the public gcd prefix separately. -/
def denseRows (N m : ℕ) : List (ℕ×QuotientRow) :=
  (List.range (m-1)).flatMap fun r =>
    (List.range (m-1)).flatMap fun s =>
      [(r+1,denseRow N m (r+1) (s+1) false),
       (r+1,denseRow N m (r+1) (s+1) true)]

/-- Each canonical representative has the exact public quotient congruence. -/
theorem representative_congruence {N m j t : ℕ} (hm : 0<m) :
    (representative N m j t : ℤ) ≡
      (N : ℤ)*(publicInverse m j)^2*(t : ℤ) [ZMOD m] := by
  have hr : (representative N m j t : ℤ) ≡
      (quotientSlope N m j : ℤ)*(t : ℤ) [ZMOD m] := by
    simpa only [representative,Int.natCast_mod,Nat.cast_mul] using
      Int.mod_modEq ((quotientSlope N m j : ℤ)*(t : ℤ)) (m : ℤ)
  exact hr.trans ((quotientSlope_modEq hm).mul_right (t : ℤ))

/-- Subtracting one modulus retains that congruence and both original
quadratic coefficients after the exact lift. -/
theorem denseRow_relation {N m j t : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (negative : Bool) :
    let z := denseRow N m j t negative
    quotientRelation N m j z.a z.b z.c z.t := by
  apply liftRow_correct (publicInverse_correct hj)
  cases negative with
  | false => simpa using representative_congruence (N:=N) (j:=j) (t:=t) hm
  | true =>
    have hz : (m : ℤ) ≡ 0 [ZMOD m] :=
      Int.modEq_zero_iff_dvd.mpr (dvd_refl _)
    simpa using (representative_congruence (N:=N) (j:=j) (t:=t) hm).sub hz

/-- A generous uniform bound on the actual centered coefficient, including
the proof-side t=0 representative. -/
theorem denseRow_b_bound {N m j t : ℕ} (hm : 1<m) (negative : Bool) :
    |(denseRow N m j t negative).b|≤(m : ℤ) := by
  have hb := centered_natAbs_le (by omega : 0<m)
    (-(publicInverse m j)*(((N : ℤ)*t-(j : ℤ)^2*
      ((representative N m j t : ℤ)-(if negative then (m : ℤ) else 0)))/(m : ℤ)))
  have hh : m/2+1≤m := by omega
  have h : ((centered m (-(publicInverse m j)*
      (((N : ℤ)*t-(j : ℤ)^2*((representative N m j t : ℤ)-
        (if negative then (m : ℤ) else 0)))/(m : ℤ)))).natAbs : ℤ)≤m := by
    exact_mod_cast hb.trans hh
  simpa only [Int.natCast_natAbs,denseRow,liftRow] using h

/-- Coprimality of the slope excludes the zero numerator for every emitted
positive denominator, in either numerator orientation. -/
theorem denseRow_a_ne_zero {N m j t : ℕ} (hm : 1<m)
    (hN : m.Coprime N) (hj : j.Coprime m) (ht : 0<t) (htm : t<m)
    (negative : Bool) : (denseRow N m j t negative).a≠0 := by
  have hc := quotientSlope_coprime (by omega : 0<m) hN hj
  have hr : representative N m j t≠0 := by
    intro hz
    have hd : m∣quotientSlope N m j*t := by
      apply Nat.dvd_of_mod_eq_zero
      exact hz
    have hdt := hc.dvd_of_dvd_mul_left hd
    exact (not_le_of_gt htm) (Nat.le_of_dvd ht hdt)
  have hb : representative N m j t<m := Nat.mod_lt _ (by omega)
  cases negative <;> simp only [denseRow,liftRow,Bool.false_eq_true,if_false,
    if_true,sub_zero]
  · exact_mod_cast hr
  · omega

/-- Every integral factor pair has a literal quadratic index in its correct
residue. This is used for arbitrary dense rows, rather than original packets. -/
theorem row_index_exists {p q m : ℕ} (hp : 0<p)
    (hN : m.Coprime (p*q)) {z : QuotientRow}
    (hz : quotientRelation (p*q) m ((p%m : ℕ) : ℤ) z.a z.b z.c z.t) :
    ∃ i : ℤ, (m : ℤ)^2*i=z.a*p+z.b*m-2*z.a*(p%m : ℕ)+z.t*q ∧
      quadratic z.a z.b z.c (p/m : ℕ)=(p : ℤ)*i := by
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hd := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hc : IsCoprime (p : ℤ) (m : ℤ) := by
    have hn := hN.isCoprime
    rw [Nat.cast_mul] at hn
    exact hn.of_mul_right_left.symm
  have hrel : quotientRelation ((p : ℤ)*q) m ((p%m : ℕ) : ℤ) z.a z.b z.c z.t := by
    simpa only [Nat.cast_mul] using hz
  obtain ⟨i,hi⟩ := quotient_row_integer_index hcoord hrel hc
  refine ⟨i,?_,hi⟩
  have he := scaled_quadratic_factor_sum hcoord hrel
  rw [hi] at he
  apply mul_left_cancel₀ (by exact_mod_cast hp.ne' : (p : ℤ)≠0)
  linear_combination he

/-- Positive canonical numerators and denominators give a single interval
for all m proof-side indices, before taking any pairwise differences. -/
theorem representative_index_interval {p q m t : ℕ} (hm : 1<m)
    (ht : t<m) {i : ℤ}
    (hi : (m : ℤ)^2*i=
        (denseRow (p*q) m (p%m) t false).a*p+
        (denseRow (p*q) m (p%m) t false).b*m-
          2*(denseRow (p*q) m (p%m) t false).a*(p%m : ℕ)+
            (denseRow (p*q) m (p%m) t false).t*q) :
    (0 : ℤ) ≤ i + 3 ∧ (m : ℤ)*(i + 3)≤p+q+4*m := by
  let a : ℤ := representative (p*q) m (p%m) t
  let b : ℤ := (denseRow (p*q) m (p%m) t false).b
  have ha₀ : 0≤a := by positivity
  have ham : a≤m := by
    change (((quotientSlope (p*q) m (p%m)*t)%m : ℕ) : ℤ)≤m
    exact_mod_cast (Nat.mod_lt _ (by omega : 0<m)).le
  have hb := abs_le.mp (denseRow_b_bound (N:=p*q) (j:=p%m) (t:=t) hm false)
  have hmz : (0 : ℤ)<m := by exact_mod_cast (by omega : 0<m)
  have htm : (t : ℤ)≤m := by exact_mod_cast ht.le
  have hjm : ((p%m : ℕ) : ℤ)≤m := by
    exact_mod_cast (Nat.mod_lt p (by omega : 0<m)).le
  change (m : ℤ)^2*i=a*p+b*m-2*a*(p%m : ℕ)+(t : ℤ)*q at hi
  have hbm₀ := mul_le_mul_of_nonneg_right hb.1 hmz.le
  have hbm₁ := mul_le_mul_of_nonneg_right hb.2 hmz.le
  have haj := mul_le_mul ham hjm (by positivity : (0 : ℤ)≤(p%m : ℕ))
    (by positivity : (0 : ℤ)≤m)
  have hap := mul_le_mul_of_nonneg_right ham (by positivity : (0 : ℤ)≤p)
  have htq := mul_le_mul_of_nonneg_right htm (by positivity : (0 : ℤ)≤q)
  have hp₀ : (0 : ℤ)≤a*p := mul_nonneg ha₀ (by positivity)
  have hq₀ : (0 : ℤ)≤(t : ℤ)*q := by positivity
  have hj₀ : (0 : ℤ)≤a*(p%m : ℕ) := by positivity
  constructor
  · nlinarith only [hi,hbm₀,haj,hp₀,hq₀,hmz,sq_pos_of_pos hmz]
  · nlinarith only [hi,hbm₁,hap,htq,hj₀,hmz]

/-- Binning m integral indices into m-1 intervals forces a close pair.
Neither sorting nor the unknown index function is an algorithmic oracle. -/
theorem index_pigeonhole {m K p q : ℕ} (hm : 1<m) (hK : 0<K)
    (hwidth : p+q+4*m<m*(m-1)*K) (f : ℕ→ℤ)
    (hf : ∀ t<m, 0≤f t+3 ∧ (m : ℤ)*(f t+3)≤p+q+4*m) :
    ∃ s t : ℕ, s<t ∧ t<m ∧ |f t-f s|<(K : ℤ) := by
  classical
  let bin (t : ℕ) : ℕ := (f t+3).toNat/K
  have hmap : Set.MapsTo bin (Finset.range m) (Finset.range (m-1)) := by
    intro t ht
    have ht' : t<m := Finset.mem_range.mp ht
    have hb := hf t ht'
    have hcast : ((f t+3).toNat : ℤ)=f t+3 := Int.toNat_of_nonneg hb.1
    have hn : (f t+3).toNat<(m-1)*K := by
      have hw : (p : ℤ)+q+4*m<(m : ℤ)*((m-1 : ℕ) : ℤ)*K := by
        exact_mod_cast hwidth
      have hmz : (0 : ℤ)<m := by exact_mod_cast (by omega : 0<m)
      have hi : f t+3<((m-1 : ℕ) : ℤ)*K := by nlinarith only [hb.2,hw,hmz]
      have hi' : ((f t+3).toNat : ℤ)<((m-1 : ℕ) : ℤ)*K := by
        simpa only [hcast] using hi
      exact_mod_cast hi'
    apply Finset.mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hK).mpr (by simpa [Nat.mul_comm] using hn)
  obtain ⟨s,hs,t,ht,hne,he⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s:=Finset.range m) (t:=Finset.range (m-1)) (by simp; omega) hmap
  have hclose : |f t-f s|<(K : ℤ) := by
    have hbs := hf s (Finset.mem_range.mp hs)
    have hbt := hf t (Finset.mem_range.mp ht)
    have hcs := Int.toNat_of_nonneg hbs.1
    have hct := Int.toNat_of_nonneg hbt.1
    have hds := Nat.mod_add_div (f s+3).toNat K
    have hdt := Nat.mod_add_div (f t+3).toNat K
    have hrs := Nat.mod_lt (f s+3).toNat hK
    have hrt := Nat.mod_lt (f t+3).toNat hK
    change (f s+3).toNat/K=(f t+3).toNat/K at he
    rw [←he] at hdt
    exact abs_lt.mpr (by omega)
  rcases lt_or_gt_of_ne hne with hst|hts
  · exact ⟨s,t,hst,Finset.mem_range.mp ht,hclose⟩
  · refine ⟨t,s,hts,Finset.mem_range.mp hs,?_⟩
    simpa only [abs_sub_comm] using hclose

/-- The public stream contains each requested signed numerator row. -/
theorem denseRow_mem {N m j t : ℕ} (hj : 0<j) (hjm : j<m)
    (ht : 0<t) (htm : t<m) (negative : Bool) :
    (j,denseRow N m j t negative)∈denseRows N m := by
  apply List.mem_flatMap.mpr
  refine ⟨j-1,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨t-1,List.mem_range.mpr (by omega),?_⟩
  have hj' : j-1+1=j := by omega
  have ht' : t-1+1=t := by omega
  rw [hj',ht']
  cases negative <;> simp

/-- Exact construction size, before any collision search or bit backend. -/
theorem denseRows_length (N m : ℕ) : (denseRows N m).length=2*(m-1)^2 := by
  simp [denseRows,List.length_flatMap,pow_two]
  ring

/-- A difference of canonical numerators has one of the two emitted forms.
There is no enumeration of all pairs in the actual row constructor. -/
theorem representative_difference {N m j s t : ℕ} (hm : 0<m)
    (hst : s<t) :
    ∃ negative : Bool,
      (denseRow N m j (t-s) negative).a=
        (denseRow N m j t false).a-(denseRow N m j s false).a := by
  let A : ℤ := (representative N m j t : ℤ)-representative N m j s
  let R : ℤ := representative N m j (t-s)
  have htr : (t : ℤ)-(s : ℤ)=(t-s : ℕ) := by omega
  have hc := (representative_congruence (N:=N) (j:=j) (t:=t) hm).sub
    (representative_congruence (N:=N) (j:=j) (t:=s) hm)
  have he : (N : ℤ)*(publicInverse m j)^2*t-
      (N : ℤ)*(publicInverse m j)^2*s=
        (N : ℤ)*(publicInverse m j)^2*(t-s : ℕ) := by
    rw [←htr]
    ring
  rw [he] at hc
  have hcong : A ≡ R [ZMOD m] :=
    hc.trans (representative_congruence (N:=N) (j:=j) (t:=t-s) hm).symm
  obtain ⟨k,hk⟩ := hcong.dvd
  have ht₀ : (0 : ℤ)≤representative N m j t := by positivity
  have hs₀ : (0 : ℤ)≤representative N m j s := by positivity
  have hr₀ : 0≤R := by positivity
  have ht₁ : (representative N m j t : ℤ)<m := by
    exact_mod_cast Nat.mod_lt _ hm
  have hs₁ : (representative N m j s : ℤ)<m := by
    exact_mod_cast Nat.mod_lt _ hm
  have hr₁ : R<m := by
    change (((quotientSlope N m j*(t-s))%m : ℕ) : ℤ)<m
    exact_mod_cast Nat.mod_lt _ hm
  have hmz : (0 : ℤ)<m := by exact_mod_cast hm
  have ha₀ : -(m : ℤ)<A := by dsimp only [A]; omega
  have ha₁ : A<m := by dsimp only [A]; omega
  have hk₀ : 0≤k := by
    by_contra! hn
    have hn' : k≤-1 := by omega
    nlinarith only [hk,hr₀,ha₁,hmz,hn']
  have hk₁ : k≤1 := by
    by_contra! hn
    have hn' : 2≤k := by omega
    nlinarith only [hk,hr₁,ha₀,hmz,hn']
  by_cases hz : k=0
  · refine ⟨false,?_⟩
    simp only [denseRow,liftRow,Bool.false_eq_true,if_false,sub_zero]
    dsimp only [A,R] at hk
    rw [hz] at hk
    linarith only [hk]
  · have ho : k=1 := by omega
    refine ⟨true,?_⟩
    simp only [denseRow,liftRow,if_true,Bool.false_eq_true,if_false,sub_zero]
    dsimp only [A,R] at hk
    rw [ho] at hk
    linarith only [hk]

/-- Re-lifting a difference changes its factor index by at most three.
All b coefficients are the actual centered coefficients; no unknown center
or supplied short-vector assumption is present. -/
theorem difference_relift_index {p q m j : ℕ} (hm : 0<m)
    {u v w : QuotientRow} {i k l : ℤ}
    (ha : w.a=v.a-u.a) (ht : w.t=v.t-u.t)
    (hu : |u.b|≤(m : ℤ)) (hv : |v.b|≤(m : ℤ)) (hw : |w.b|≤(m : ℤ))
    (hi : (m : ℤ)^2*i=u.a*p+u.b*m-2*u.a*j+u.t*q)
    (hk : (m : ℤ)^2*k=v.a*p+v.b*m-2*v.a*j+v.t*q)
    (hl : (m : ℤ)^2*l=w.a*p+w.b*m-2*w.a*j+w.t*q) :
    |l-(k-i)|≤3 := by
  have hmz : (0 : ℤ)<m := by exact_mod_cast hm
  have he : (m : ℤ)*(m*(l-(k-i)))=(m : ℤ)*(w.b-v.b+u.b) := by
    rw [ha,ht] at hl
    linear_combination hl-hk+hi
  have he' := mul_left_cancel₀ hmz.ne' he
  have hbu := abs_le.mp hu
  have hbv := abs_le.mp hv
  have hbw := abs_le.mp hw
  apply abs_le.mpr
  constructor <;> nlinarith only [he',hbu.1,hbu.2,hbv.1,hbv.2,hbw.1,hbw.2,hmz]

/-- The correct public residue has an emitted informative quadratic whose
literal factor index lies in the pigeonhole radius plus the centering cost.
Factors occur solely as coverage witnesses for the N-only row stream. -/
theorem denseRows_index_coverage {p q m K : ℕ} (hm : 1<m) (hp : 0<p)
    (hN : m.Coprime (p*q)) (hK : 0<K)
    (hwidth : p+q+4*m<m*(m-1)*K) :
    ∃ (t : ℕ) (negative : Bool) (i : ℤ),
      (p%m,denseRow (p*q) m (p%m) t negative)∈denseRows (p*q) m ∧
      (denseRow (p*q) m (p%m) t negative).a≠0 ∧
      0<t ∧ t<m ∧ |i|≤(K : ℤ)+3 ∧
      (m : ℤ)^2*i=(denseRow (p*q) m (p%m) t negative).a*p+
        (denseRow (p*q) m (p%m) t negative).b*m-
          2*(denseRow (p*q) m (p%m) t negative).a*(p%m : ℕ)+
            (denseRow (p*q) m (p%m) t negative).t*q ∧
      quadratic (denseRow (p*q) m (p%m) t negative).a
        (denseRow (p*q) m (p%m) t negative).b
          (denseRow (p*q) m (p%m) t negative).c (p/m : ℕ)=(p : ℤ)*i := by
  have hm₀ : 0<m := by omega
  have hpcop : p.Coprime m := by
    apply Nat.isCoprime_iff_coprime.mp
    have hn := hN.isCoprime
    rw [Nat.cast_mul] at hn
    exact hn.of_mul_right_left.symm
  have hjcop : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hpcop.symm
  have hj : 0<p%m := by
    by_contra! hz
    have he : p%m=0 := by omega
    simp only [he,Nat.coprime_zero_left] at hjcop
    omega
  have hindices : ∀ t : ℕ, ∃ i : ℤ,
      (m : ℤ)^2*i=(denseRow (p*q) m (p%m) t false).a*p+
        (denseRow (p*q) m (p%m) t false).b*m-
          2*(denseRow (p*q) m (p%m) t false).a*(p%m : ℕ)+
            (denseRow (p*q) m (p%m) t false).t*q ∧
      quadratic (denseRow (p*q) m (p%m) t false).a
        (denseRow (p*q) m (p%m) t false).b
          (denseRow (p*q) m (p%m) t false).c (p/m : ℕ)=(p : ℤ)*i :=
    fun t => row_index_exists hp hN (denseRow_relation hm₀ hjcop false)
  choose f hf using hindices
  obtain ⟨s,t,hst,htm,hclose⟩ := index_pigeonhole hm hK hwidth f
    (fun t ht => representative_index_interval hm ht (hf t).1)
  obtain ⟨negative,ha⟩ := representative_difference (N:=p*q) (j:=p%m) hm₀ hst
  have hT : 0<t-s := by omega
  have hTm : t-s<m := by omega
  obtain ⟨i,hi,hquad⟩ := row_index_exists hp hN
    (denseRow_relation (N:=p*q) (t:=t-s) hm₀ hjcop negative)
  have hden : (denseRow (p*q) m (p%m) (t-s) negative).t=
      (denseRow (p*q) m (p%m) t false).t-
        (denseRow (p*q) m (p%m) s false).t := by
    change ((t-s : ℕ) : ℤ)=(t : ℤ)-(s : ℤ)
    omega
  have hshift := difference_relift_index hm₀ ha hden
    (denseRow_b_bound hm false) (denseRow_b_bound hm false)
    (denseRow_b_bound hm negative) (hf s).1 (hf t).1 hi
  have hiBound : |i|≤(K : ℤ)+3 := by
    have he : i=(i-(f t-f s))+(f t-f s) := by ring
    have hb := abs_add_le (i-(f t-f s)) (f t-f s)
    rw [←he] at hb
    linarith only [hb,hshift,hclose]
  exact ⟨t-s,negative,i,
    denseRow_mem hj (Nat.mod_lt p hm₀) hT hTm negative,
    denseRow_a_ne_zero hm hN hjcop hT hTm negative,hT,hTm,hiBound,hi,hquad⟩

/-- Coverage reaches actual prime-field powers and the informative integer
recovery quadratic. Fermat supplies the period for every chosen unit; no
high-order or successful-collision hypothesis is assumed. -/
theorem denseRows_prime_collision_coverage {p q m K : ℕ} (hm : 1<m)
    (hp : p.Prime) (hN : m.Coprime (p*q)) (hK : 0<K)
    (hwidth : p+q+4*m<m*(m-1)*K) (g : (ZMod p)ˣ) :
    ∃ (z : QuotientRow) (i : ℤ),
      (p%m,z)∈denseRows (p*q) m ∧ z.a≠0 ∧ i.natAbs≤K+3 ∧
      g^giantExponent m (p%m : ℕ) z.a z.b z.c=g^((m : ℤ)^2*i) ∧
      (p : ℤ)∈integerRoots z.a
        (z.b*m-2*z.a*(p%m : ℕ)-(m : ℤ)^2*i) (z.t*(p*q : ℕ)) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t,negative,i,hmem,ha,_ht,_htm,hbound,_hsum,hi⟩ :=
    denseRows_index_coverage hm hp.pos hN hK hwidth
  let z := denseRow (p*q) m (p%m) t negative
  have hmp : m.Coprime p := hN.of_dvd_right (dvd_mul_right p q)
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hmp
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ) z.a z.b z.c z.t := by
    simpa only [Nat.cast_mul] using
      denseRow_relation (N:=p*q) (t:=t) (by omega : 0<m) hj negative
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hd := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hperiod : g^((p : ℤ)-1)=1 := by
    have h := ZMod.units_pow_card_sub_one_eq_one p g
    have hz : g^((p-1 : ℕ) : ℤ)=1 := by simpa only [zpow_natCast] using h
    simpa only [Nat.cast_sub hp.one_le,Nat.cast_one] using hz
  have hindex : i.natAbs≤K+3 := by
    have h : (i.natAbs : ℤ)≤(K+3 : ℕ) := by
      simpa only [Int.natCast_natAbs,Nat.cast_add,Nat.cast_ofNat] using hbound
    exact_mod_cast h
  have hroot := quotient_row_recovery_equation hcoord hrel hi
  exact ⟨z,i,hmem,ha,hindex,
    quotient_row_power_hit g hcoord hrel hi (by exact_mod_cast hp.ne_zero) hperiod,
    integerRoots_complete ha hroot⟩

/-- Balanced factors and the public sixth-root ceiling discharge the
pigeonhole width with an explicit linear radius. This permits prime squares. -/
theorem balanced_pigeonhole_width {p q m : ℕ} (hm : 1<m)
    (hpq : p≤q) (hq : q≤2*p) (hsize : p*q≤m^6) :
    p+q+4*m<m*(m-1)*(3*m+11) := by
  have hp_square : p^2≤(m^3)^2 := by
    calc
      p^2≤p*q := by nlinarith only [Nat.mul_le_mul_left p hpq]
      _≤m^6 := hsize
      _=(m^3)^2 := by ring
  have hp_cube : p≤m^3 := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp hp_square
  have hsum : p+q≤3*m^3 := by omega
  have hsumz : (p : ℤ)+q≤3*(m : ℤ)^3 := by exact_mod_cast hsum
  have hmz : (2 : ℤ)≤m := by exact_mod_cast (by omega : 2≤m)
  have hprod := mul_nonneg (by omega : (0 : ℤ)≤m) (by omega : (0 : ℤ)≤m-2)
  have hw : (p : ℤ)+q+4*m<(m : ℤ)*((m : ℤ)-1)*(3*m+11) := by
    nlinarith only [hsumz,hmz,hprod]
  have he : (m : ℤ)-1=(m-1 : ℕ) := by omega
  rw [he] at hw
  exact_mod_cast hw

/-- A genuine arithmetic reason for a linear signed baby window at the
sixth-root scale, for this explicitly quadratic-size public row family. -/
theorem denseRows_balanced_collision_coverage {p q m : ℕ} (hm : 1<m)
    (hp : p.Prime) (hpq : p≤q) (hq : q≤2*p) (hN : m.Coprime (p*q))
    (hsize : p*q≤m^6) (g : (ZMod p)ˣ) :
    ∃ (z : QuotientRow) (i : ℤ),
      (p%m,z)∈denseRows (p*q) m ∧ z.a≠0 ∧ i.natAbs≤3*m+14 ∧
      g^giantExponent m (p%m : ℕ) z.a z.b z.c=g^((m : ℤ)^2*i) ∧
      (p : ℤ)∈integerRoots z.a
        (z.b*m-2*z.a*(p%m : ℕ)-(m : ℤ)^2*i) (z.t*(p*q : ℕ)) := by
  simpa only [Nat.add_assoc] using
    denseRows_prime_collision_coverage hm hp hN (by omega : 0<3*m+11)
      (balanced_pigeonhole_width hm hpq hq hsize) g

/-- Merely producing the explicit source already has quadratic output
size. No faster compressed constructor or bit-machine lower bound is asserted. -/
theorem denseRows_output_lower_bound (N m : ℕ) (hm : 1<m) :
    m^2≤2*(denseRows N m).length := by
  have he : m≤2*(m-1) := by omega
  have hs := Nat.pow_le_pow_left he 2
  rw [denseRows_length]
  nlinarith only [hs]

end RiemannGaussian.SemiprimeDenseRowCoverage
