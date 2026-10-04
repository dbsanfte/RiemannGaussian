/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeForcedRowSeparation

/-!
# Exact cancellation of all common global row hits

Cross-multiplying two verified global hits cancels the large N term.
The routed global order exceeds the entire remaining integer interval,
so the congruence is an exact phase identity. At the prime row modulus
its residue support has degree at most two. This classifies common global
hits; acquiring a first hit and the complete bit budget remain separate.
-/

namespace RiemannGaussian.SemiprimeGlobalPhaseCancellation

open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open SemiprimeMergedIndexAcquisition SemiprimeForcedRowSeparation
open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeWrapIndexRecovery
open SemiprimeCentreFreeCover SemiprimeWideWrapCoverage
open Polynomial

/-- The small part of a seed exponent, computed from its cached data. -/
def cachedOffset {G : Type*} (m : ℕ) (s : ProgressionSeed G) : ℤ :=
  (s.slope : ℤ)+(m : ℤ)*s.linear-2*(s.slope : ℤ)*s.residue

/-- Public denominator-one offset, independent of any group or factor. -/
def seedOffset (N m j : ℕ) : ℤ :=
  (representative N m j 1 : ℤ)+(m : ℤ)*(seedRow N m j).b-
    2*(representative N m j 1 : ℤ)*j

/-- Cached and public offsets are literally the same integer. -/
theorem cachedOffset_seed {G : Type*} [CommGroup G] (g : G) (N m j : ℕ) :
    cachedOffset m (progressionSeed g N m j)=seedOffset N m j := rfl

/-- All original positive-residue seed offsets lie in one short interval. -/
theorem seedOffset_bounds {N m j : ℕ} (hm : 1<m) (hj : 1≤j) (hjm : j<m) :
    -3*(m : ℤ)^2≤seedOffset N m j ∧ seedOffset N m j≤(m : ℤ)^2 := by
  have hA : (0 : ℤ)≤representative N m j 1 := by positivity
  have hAm : (representative N m j 1 : ℤ)≤m := by
    exact_mod_cast (Nat.mod_lt (quotientSlope N m j*1) (by omega : 0<m)).le
  have hjz : (1 : ℤ)≤j := by exact_mod_cast hj
  have hjmz : (j : ℤ)≤m := by exact_mod_cast hjm.le
  have hmz : (0 : ℤ)≤m := by positivity
  have hb := abs_le.mp (denseRow_b_bound (N:=N) (j:=j) (t:=1) hm false)
  change -(m : ℤ)≤(seedRow N m j).b ∧ (seedRow N m j).b≤m at hb
  have hbm0 := mul_le_mul_of_nonneg_left hb.1 hmz
  have hbm1 := mul_le_mul_of_nonneg_left hb.2 hmz
  have hprod := mul_le_mul hAm hjmz (by positivity : (0 : ℤ)≤j) hmz
  have hprod0 := mul_nonneg hA (by omega : (0 : ℤ)≤2*(j : ℤ)-1)
  unfold seedOffset
  constructor <;> nlinarith only [hA,hbm0,hbm1,hprod,hprod0]

/-- A literal public seed step has exponent N plus its short offset. -/
theorem seed_step_offset {G : Type*} [CommGroup G] (g : G) {N m j : ℕ}
    (hm : 0<m) (hj : j.Coprime m) :
    (progressionSeed g N m j).step=g^((N : ℤ)+seedOffset N m j) := by
  have hr := denseRow_relation (N:=N) (j:=j) (t:=1) hm hj false
  change quotientRelation N m j (seedRow N m j).a (seedRow N m j).b
    (seedRow N m j).c (seedRow N m j).t at hr
  have hden : (seedRow N m j).t=(1 : ℤ) := rfl
  rw [hden] at hr
  have he := giantExponent_eq hr
  simp only [one_mul] at he
  change g^giantExponent m j (seedRow N m j).a (seedRow N m j).b
    (seedRow N m j).c=_
  rw [he]
  congr 1
  have ha : (seedRow N m j).a=(representative N m j 1 : ℤ) := rfl
  rw [ha]
  unfold seedOffset
  ring

/-- A verified common global row hit has this integer order residual. -/
theorem hit_residual_iff {G : Type*} [CommGroup G] (g : G) {N m j t : ℕ}
    (hm : 0<m) (hj : j.Coprime m) (z : ℤ) :
    (progressionSeed g N m j).step^t=(commonStep g m)^z ↔
      (orderOf g : ℤ)∣(t : ℤ)*((N : ℤ)+seedOffset N m j)-(m : ℤ)*z := by
  rw [seed_step_offset g hm hj]
  simp only [commonStep,←zpow_natCast,←zpow_mul]
  rw [←orderOf_dvd_sub_iff_zpow_eq_zpow]
  rw [mul_comm ((N : ℤ)+seedOffset N m j) (t : ℤ)]

/-- The CRT order is a product, large enough to forbid wraparound after
cancelling the common N term between any two original global hits. -/
theorem long_global_order_bound {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    16*m^4<orderOf (projectedUnit g m) := by
  rw [global_order_eq_lcm hp hq hpq,(hlong.2.2.2.2.1).lcm_eq_mul]
  have hP : 4*m^2<orderOf (leftUnit (projectedUnit g m)) := by
    have hh := hlong.2.2.2.1.1
    nlinarith only [hh]
  have hQ : 4*m^2<orderOf (rightUnit (projectedUnit g m)) := by
    have hh := hlong.2.2.2.1.2
    nlinarith only [hh]
  have hmul₀ := mul_le_mul_of_nonneg_left hQ.le (Nat.zero_le (4*m^2))
  have hmul₁ := mul_lt_mul_of_pos_right hP
    (by omega : 0<orderOf (rightUnit (projectedUnit g m)))
  nlinarith only [hmul₀,hmul₁]

/-- Every cross residual, including those from false global row tags,
fits strictly inside the routed global-order interval. -/
theorem cross_residual_bound {m t t₀ : ℕ} {δ δ₀ z z₀ : ℤ}
    (ht : t≤m) (ht₀ : t₀≤m)
    (hδ : -3*(m : ℤ)^2≤δ ∧ δ≤(m : ℤ)^2)
    (hδ₀ : -3*(m : ℤ)^2≤δ₀ ∧ δ₀≤(m : ℤ)^2)
    (hz : -4*(m : ℤ)^2≤z ∧ z≤2*(m : ℤ)^2)
    (hz₀ : -4*(m : ℤ)^2≤z₀ ∧ z₀≤2*(m : ℤ)^2) :
    |(t : ℤ)*t₀*(δ-δ₀)-(m : ℤ)*((t₀ : ℤ)*z-(t : ℤ)*z₀)|≤
      12*(m : ℤ)^4 := by
  have htZ : (t : ℤ)≤m := by exact_mod_cast ht
  have ht₀Z : (t₀ : ℤ)≤m := by exact_mod_cast ht₀
  have hd : |δ-δ₀|≤4*(m : ℤ)^2 := abs_le.mpr (by constructor <;> omega)
  have hzA : |z|≤4*(m : ℤ)^2 := abs_le.mpr (by constructor <;> nlinarith only [hz.1,hz.2,sq_nonneg (m : ℤ)])
  have hz₀A : |z₀|≤4*(m : ℤ)^2 := abs_le.mpr (by constructor <;> nlinarith only [hz₀.1,hz₀.2,sq_nonneg (m : ℤ)])
  have htt := mul_le_mul htZ ht₀Z (by positivity : (0 : ℤ)≤t₀) (by positivity : (0 : ℤ)≤m)
  have hterm := mul_le_mul htt hd (abs_nonneg _) (by positivity : (0 : ℤ)≤(m : ℤ)*m)
  have htZz := mul_le_mul ht₀Z hzA (abs_nonneg _) (by positivity : (0 : ℤ)≤m)
  have htZz₀ := mul_le_mul htZ hz₀A (abs_nonneg _) (by positivity : (0 : ℤ)≤m)
  have hinner : |(t₀ : ℤ)*z-(t : ℤ)*z₀|≤8*(m : ℤ)^3 := by
    have hh := abs_sub ((t₀ : ℤ)*z) ((t : ℤ)*z₀)
    simp only [abs_mul,abs_of_nonneg (by positivity : (0 : ℤ)≤t),
      abs_of_nonneg (by positivity : (0 : ℤ)≤t₀)] at hh
    nlinarith only [hh,htZz,htZz₀]
  have houter := mul_le_mul_of_nonneg_left hinner (by positivity : (0 : ℤ)≤m)
  have hh := abs_sub ((t : ℤ)*t₀*(δ-δ₀)) ((m : ℤ)*((t₀ : ℤ)*z-(t : ℤ)*z₀))
  simp only [abs_mul,abs_of_nonneg (by positivity : (0 : ℤ)≤t),
    abs_of_nonneg (by positivity : (0 : ℤ)≤t₀),
    abs_of_nonneg (by positivity : (0 : ℤ)≤m)] at hh
  nlinarith only [hh,hterm,houter]

/-- Removing N from two global-hit congruences gives an exact integer
identity whenever the global order has the routed lower bound. -/
theorem global_phase_identity {G : Type*} [CommGroup G] (g : G)
    {N m j j₀ t t₀ : ℕ} {z z₀ : ℤ}
    (hm : 1<m) (hj : 1≤j) (hjm : j<m) (hj₀ : 1≤j₀) (hj₀m : j₀<m)
    (hcop : j.Coprime m) (hcop₀ : j₀.Coprime m)
    (ht : t<m) (ht₀ : t₀<m)
    (hz : -4*(m : ℤ)^2≤z ∧ z<2*(m : ℤ)^2)
    (hz₀ : -4*(m : ℤ)^2≤z₀ ∧ z₀<2*(m : ℤ)^2)
    (horder : 16*m^4<orderOf g)
    (hhit : (progressionSeed g N m j).step^t=(commonStep g m)^z)
    (hhit₀ : (progressionSeed g N m j₀).step^t₀=(commonStep g m)^z₀) :
    (t : ℤ)*t₀*(seedOffset N m j-seedOffset N m j₀)=
      (m : ℤ)*((t₀ : ℤ)*z-(t : ℤ)*z₀) := by
  have hdiv := (hit_residual_iff g (by omega) hcop z).mp hhit
  have hdiv₀ := (hit_residual_iff g (by omega) hcop₀ z₀).mp hhit₀
  have he : (t₀ : ℤ)*((t : ℤ)*((N : ℤ)+seedOffset N m j)-(m : ℤ)*z)-
      (t : ℤ)*((t₀ : ℤ)*((N : ℤ)+seedOffset N m j₀)-(m : ℤ)*z₀)=
      (t : ℤ)*t₀*(seedOffset N m j-seedOffset N m j₀)-
        (m : ℤ)*((t₀ : ℤ)*z-(t : ℤ)*z₀) := by ring
  have hd := (dvd_mul_of_dvd_right hdiv (t₀ : ℤ)).sub
    (dvd_mul_of_dvd_right hdiv₀ (t : ℤ))
  rw [he] at hd
  have hb := cross_residual_bound ht.le ht₀.le
    (seedOffset_bounds (N:=N) hm hj hjm) (seedOffset_bounds (N:=N) hm hj₀ hj₀m)
    ⟨hz.1,hz.2.le⟩ ⟨hz₀.1,hz₀.2.le⟩
  have ho : 12*(m : ℤ)^4<(orderOf g : ℤ) := by
    have hh : 12*m^4<orderOf g := by nlinarith only [horder]
    exact_mod_cast hh
  have hab := hb.trans_lt ho
  rw [←Int.natCast_natAbs] at hab
  have habN : ((t : ℤ)*t₀*(seedOffset N m j-seedOffset N m j₀)-
      (m : ℤ)*((t₀ : ℤ)*z-(t : ℤ)*z₀)).natAbs<(orderOf g : ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using (show _<orderOf g by exact_mod_cast hab)
  have heq := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd habN
  linarith only [heq]

/-- A verified original global tag includes its public source bounds. -/
def GlobalHit {G : Type*} [CommGroup G] (g : G) (N m j t : ℕ) (z : ℤ) : Prop :=
  0<t ∧ t<m ∧ 1≤j ∧ j<m ∧ -4*(m : ℤ)^2≤z ∧ z<2*(m : ℤ)^2 ∧
    (progressionSeed g N m j).step^t=(commonStep g m)^z

/-- A prime row modulus cancels both short positive denominators from
the exact phase identity, leaving equality of the offset residue classes. -/
theorem phase_offset_divisible {m t t₀ : ℕ} {δ δ₀ z z₀ : ℤ}
    (hm : m.Prime) (ht : 0<t) (htm : t<m) (ht₀ : 0<t₀) (ht₀m : t₀<m)
    (he : (t : ℤ)*t₀*(δ-δ₀)=(m : ℤ)*((t₀ : ℤ)*z-(t : ℤ)*z₀)) :
    (m : ℤ)∣δ-δ₀ := by
  have hc : t.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ht htm)).symm
  have hc₀ : t₀.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ht₀ ht₀m)).symm
  have hd : (m : ℤ)∣(t : ℤ)*t₀*(δ-δ₀) := by
    rw [he]
    exact dvd_mul_right _ _
  rw [mul_assoc] at hd
  exact hc₀.isCoprime.symm.dvd_of_dvd_mul_left
    (hc.isCoprime.symm.dvd_of_dvd_mul_left hd)

/-- All verified global tags of the actual long base share one exact
phase. No tag is assumed to be the private factor witness. -/
theorem long_global_phase {p q m j j₀ t t₀ : ℕ} {z z₀ : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hhit : GlobalHit (projectedUnit g m) (p*q) m j t z)
    (hhit₀ : GlobalHit (projectedUnit g m) (p*q) m j₀ t₀ z₀) :
    (t : ℤ)*t₀*(seedOffset (p*q) m j-seedOffset (p*q) m j₀)=
      (m : ℤ)*((t₀ : ℤ)*z-(t : ℤ)*z₀) := by
  rcases hhit with ⟨_,ht,hj,hjm,hz,hzm,he⟩
  rcases hhit₀ with ⟨_,ht₀,hj₀,hj₀m,hz₀,hz₀m,he₀⟩
  have hc : j.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hc₀ : j₀.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hj₀m)).symm
  exact global_phase_identity (projectedUnit g m) hm.one_lt hj hjm hj₀ hj₀m
    hc hc₀ ht ht₀ ⟨hz,hzm⟩ ⟨hz₀,hz₀m⟩ (long_global_order_bound hp hq hpq g hlong) he he₀

/-- The quotient slope multiplied by the original residue square is N. -/
theorem slope_square_residue {N m j : ℕ} (hm : 0<m) (hj : j.Coprime m) :
    (representative N m j 1 : ZMod m)*(j : ZMod m)^2=(N : ZMod m) := by
  have hr := representative_congruence (N:=N) (j:=j) (t:=1) hm
  simp only [Nat.cast_one,mul_one] at hr
  have hi := ((publicInverse_correct hj).pow 2).mul_left (N : ℤ)
  have hcross : (j : ℤ)^2*((N : ℤ)*(publicInverse m j)^2) ≡ (N : ℤ) [ZMOD m] := by
    convert hi using 1 <;> first | rfl | ring
  have hs := (hr.mul_left ((j : ℤ)^2)).trans hcross
  have hz := (ZMod.intCast_eq_intCast_iff _ _ m).mpr hs
  simpa only [Int.cast_mul,Int.cast_pow,Int.cast_natCast,mul_comm] using hz

/-- The offset residue has a quadratic relation in the original public
residue. Centering disappears modulo m without discarding its integer carry. -/
theorem offset_square_residue {N m j : ℕ} (hm : 0<m) (hj : j.Coprime m) :
    (seedOffset N m j : ZMod m)*(j : ZMod m)^2=
      (N : ZMod m)*(1-2*(j : ZMod m)) := by
  have hs := slope_square_residue (N:=N) hm hj
  unfold seedOffset
  push_cast
  simp only [ZMod.natCast_self,zero_mul,add_zero]
  calc
    ((representative N m j 1 : ZMod m)-2*(representative N m j 1 : ZMod m)*j)*j^2=
        ((representative N m j 1 : ZMod m)*j^2)*(1-2*(j : ZMod m)) := by ring
    _=(N : ZMod m)*(1-2*(j : ZMod m)) := by rw [hs]

/-- A phase class is a degree-at-most-two polynomial over the public
prime row field. Its constant term is nonzero after the public prefix. -/
noncomputable def phasePolynomial (N m : ℕ) (δ : ℤ) : (ZMod m)[X] :=
  C (δ : ZMod m)*X^2+C (2*(N : ZMod m))*X-C (N : ZMod m)

/-- Public coprimality excludes the zero phase polynomial. -/
theorem phasePolynomial_ne_zero {N m : ℕ} (hm : m.Prime) (hN : m.Coprime N)
    (δ : ℤ) : phasePolynomial N m δ≠0 := by
  intro he
  have hc := congrArg (fun P : (ZMod m)[X] => P.coeff 0) he
  simp only [phasePolynomial,coeff_sub,coeff_add,coeff_C_mul_X_pow,
    coeff_C_mul_X,coeff_C_zero,coeff_zero,show (0 : ℕ)≠2 by decide,
    show (0 : ℕ)≠1 by decide,if_false,zero_add,zero_sub,neg_eq_zero] at hc
  have hd := (ZMod.natCast_eq_zero_iff N m).mp hc
  have hdiv : m∣1 := by
    simpa only [hN.gcd_eq_one] using Nat.dvd_gcd (dvd_refl m) hd
  have hm1 := Nat.le_of_dvd (by decide : 0<1) hdiv
  have hm2 := hm.two_le
  omega

/-- Every phase polynomial has degree at most two, even when its leading
coefficient vanishes. -/
theorem phasePolynomial_degree (N m : ℕ) (δ : ℤ) :
    (phasePolynomial N m δ).natDegree≤2 := by
  have ha : (C (δ : ZMod m)*X^2 : (ZMod m)[X]).natDegree≤2 :=
    natDegree_mul_le.trans (add_le_add (le_of_eq (natDegree_C _)) (natDegree_X_pow_le 2))
  have hb : (C (2*(N : ZMod m))*X : (ZMod m)[X]).natDegree≤1 :=
    natDegree_mul_le.trans (add_le_add (le_of_eq (natDegree_C _)) natDegree_X_le)
  have hab := (natDegree_add_le _ _).trans (max_le ha (hb.trans (by decide : 1≤2)))
  exact (natDegree_sub_le _ _).trans
    (max_le hab ((le_of_eq (natDegree_C _)).trans (by decide : 0≤2)))

/-- A residue whose cached offset is in the phase class is a root of
the same public quadratic. -/
theorem phasePolynomial_root {N m j : ℕ} {δ : ℤ} (hm : 0<m)
    (hj : j.Coprime m) (hd : (m : ℤ)∣seedOffset N m j-δ) :
    (phasePolynomial N m δ).IsRoot (j : ZMod m) := by
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr hd
  simp only [Int.cast_sub,sub_eq_zero] at he
  have hs := offset_square_residue (N:=N) hm hj
  rw [he] at hs
  change (phasePolynomial N m δ).eval (j : ZMod m)=0
  simp only [phasePolynomial,eval_sub,eval_add,eval_mul,eval_C,eval_pow,eval_X]
  linear_combination hs

/-- Public cached descriptors in one offset residue class. This does not
query either hidden local order or either prime factor. -/
def phaseSeeds {G : Type*} [CommGroup G] (g : G) (N m j₀ : ℕ) :
    List (ProgressionSeed G) :=
  (progressionSeeds g N m).filter fun s =>
    (cachedOffset m s-seedOffset N m j₀)%(m : ℤ)==0

/-- The phase menu contains at most TWO literal cached descriptors. -/
theorem phaseSeeds_length_le_two {G : Type*} [CommGroup G]
    (g : G) {N m : ℕ} (hm : m.Prime) (hN : m.Coprime N) (j₀ : ℕ) :
    (phaseSeeds g N m j₀).length≤2 := by
  classical
  let : Fact m.Prime := ⟨hm⟩
  let : NeZero m := ⟨hm.ne_zero⟩
  let indices := (List.range (m-1)).filter fun r =>
    (seedOffset N m (r+1)-seedOffset N m j₀)%(m : ℤ)==0
  have hb {r : ℕ} (hr : r∈indices.toFinset) :
      r+1<m ∧ (m : ℤ)∣seedOffset N m (r+1)-seedOffset N m j₀ := by
    have hh := List.mem_filter.mp (List.mem_toFinset.mp hr)
    have hbr := List.mem_range.mp hh.1
    exact ⟨by omega,Int.dvd_of_emod_eq_zero (by simpa only [beq_iff_eq] using hh.2)⟩
  have hlength : (phaseSeeds g N m j₀).length=indices.length := by
    simp only [phaseSeeds,progressionSeeds,List.filter_map,List.length_map]
    rfl
  rw [hlength]
  let P := phasePolynomial N m (seedOffset N m j₀)
  have hP : P≠0 := phasePolynomial_ne_zero hm hN _
  have hmapping : Set.MapsTo (fun r : ℕ => ((r+1 : ℕ) : ZMod m))
      indices.toFinset P.roots.toFinset := by
    intro r hr
    have hbr := hb hr
    have hcop : (r+1).Coprime m :=
      (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hbr.1)).symm
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr
      (phasePolynomial_root hm.pos hcop hbr.2))
  have hinj : (indices.toFinset : Set ℕ).InjOn
      (fun r : ℕ => ((r+1 : ℕ) : ZMod m)) := by
    intro r hr s hs he
    have hv := congrArg ZMod.val he
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt (hb hr).1,
      Nat.mod_eq_of_lt (hb hs).1] at hv
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmapping hinj
  have hroots := Multiset.toFinset_card_le P.roots
  have hdegree := (Polynomial.card_roots' P).trans (phasePolynomial_degree N m _)
  have hnodup : indices.Nodup := (List.nodup_range (n:=m-1)).filter _
  rw [List.toFinset_card_of_nodup hnodup] at hcard
  omega

/-- Exact signed index predicted from one verified phase anchor. Both
divisions have explicit integrality checks in the public tag emitter. -/
def phaseIndex (m t t₀ : ℕ) (δ δ₀ z₀ : ℤ) : ℤ :=
  ((t : ℤ)*z₀)/(t₀ : ℤ)+(t : ℤ)*((δ-δ₀)/(m : ℤ))

/-- The exact phase identity forces BOTH divisions used by the public
predictor to be integral and gives the original signed index exactly. -/
theorem phase_index_exact {m t t₀ : ℕ} {δ δ₀ z z₀ : ℤ}
    (hm : m.Prime) (ht : 0<t) (htm : t<m) (ht₀ : 0<t₀) (ht₀m : t₀<m)
    (he : (t : ℤ)*t₀*(δ-δ₀)=(m : ℤ)*((t₀ : ℤ)*z-(t : ℤ)*z₀)) :
    (m : ℤ)∣δ-δ₀ ∧ (t₀ : ℤ)∣(t : ℤ)*z₀ ∧ z=phaseIndex m t t₀ δ δ₀ z₀ := by
  have hd := phase_offset_divisible hm ht htm ht₀ ht₀m he
  have hm0 : (m : ℤ)≠0 := by exact_mod_cast hm.ne_zero
  have ht₀0 : (t₀ : ℤ)≠0 := by exact_mod_cast ht₀.ne'
  have hδ := Int.ediv_mul_cancel hd
  rw [←hδ] at he
  have hlinear : (t₀ : ℤ)*z-(t : ℤ)*z₀=
      (t : ℤ)*t₀*((δ-δ₀)/(m : ℤ)) := by
    apply mul_left_cancel₀ hm0
    nlinarith only [he]
  have hz : (t₀ : ℤ)∣(t : ℤ)*z₀ := by
    refine ⟨z-(t : ℤ)*((δ-δ₀)/(m : ℤ)),?_⟩
    nlinarith only [hlinear]
  refine ⟨hd,hz,?_⟩
  have hdivide := Int.ediv_mul_cancel hz
  apply mul_left_cancel₀ ht₀0
  unfold phaseIndex
  nlinarith only [hlinear,hdivide]

/-- Conversely, integral phase predictions preserve a verified global
order residual. Roughness permits cancelling the anchor denominator. -/
theorem phase_prediction_residual {D m t t₀ N : ℕ} {δ δ₀ z₀ : ℤ}
    (hc : D.Coprime t₀) (hd : (m : ℤ)∣δ-δ₀) (hz : (t₀ : ℤ)∣(t : ℤ)*z₀)
    (hanchor : (D : ℤ)∣(t₀ : ℤ)*((N : ℤ)+δ₀)-(m : ℤ)*z₀) :
    (D : ℤ)∣(t : ℤ)*((N : ℤ)+δ)-(m : ℤ)*phaseIndex m t t₀ δ δ₀ z₀ := by
  have hδ := Int.ediv_mul_cancel hd
  have hz₀ := Int.ediv_mul_cancel hz
  have he : (t₀ : ℤ)*((t : ℤ)*((N : ℤ)+δ)-(m : ℤ)*phaseIndex m t t₀ δ δ₀ z₀)=
      (t : ℤ)*((t₀ : ℤ)*((N : ℤ)+δ₀)-(m : ℤ)*z₀) := by
    unfold phaseIndex
    linear_combination -(t : ℤ)*t₀*hδ-(m : ℤ)*hz₀
  apply hc.isCoprime.dvd_of_dvd_mul_left
  rw [he]
  exact dvd_mul_of_dvd_right hanchor (t : ℤ)

/-- Every short positive denominator is coprime to the actual global
order. This is proof-side cancellation, with no order query in the mask. -/
theorem long_global_coprime_small {p q m a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (ha : 0<a) (ham : a≤m) :
    (orderOf (projectedUnit g m)).Coprime a := by
  rw [global_order_eq_lcm hp hq hpq,(hlong.2.2.2.2.1).lcm_eq_mul]
  exact (rough_coprime_small ha ham hlong.2.2.2.2.2.1).mul_left
    (rough_coprime_small ha ham hlong.2.2.2.2.2.2)

/-- Membership in a cached phase menu keeps the original source residue
and the exact offset divisibility checked by the emitter. -/
theorem phaseSeeds_mem_iff {G : Type*} [CommGroup G] (g : G) (N m j₀ : ℕ)
    (s : ProgressionSeed G) : s∈phaseSeeds g N m j₀ ↔
      s∈progressionSeeds g N m ∧ (m : ℤ)∣cachedOffset m s-seedOffset N m j₀ := by
  simp only [phaseSeeds,List.mem_filter,beq_iff_eq]
  exact and_congr_right (fun _ => Int.dvd_iff_emod_eq_zero.symm)

/-- The original residue of any cached public descriptor is canonical,
and the whole descriptor is exactly the source seed at that residue. -/
theorem cached_seed_source {G : Type*} [CommGroup G] {g : G} {N m : ℕ}
    {s : ProgressionSeed G} (hs : s∈progressionSeeds g N m) :
    1≤s.residue ∧ s.residue<m ∧ s=progressionSeed g N m s.residue := by
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hs
  have hb := List.mem_range.mp hr
  subst s
  exact ⟨by change 1≤r+1; omega,by change r+1<m; omega,rfl⟩

/-- The arithmetic-only tag emitter checks integral phase and signed
range membership, without evaluating any further group powers. -/
def predictedTag {G : Type*} (m t₀ : ℕ) (δ₀ z₀ : ℤ)
    (s : ProgressionSeed G) (r : ℕ) : Option (ℕ×ℕ×ℤ) :=
  let t := r+1
  let z := phaseIndex m t t₀ (cachedOffset m s) δ₀ z₀
  if (t₀ : ℤ)∣(t : ℤ)*z₀ ∧ -4*(m : ℤ)^2≤z ∧ z<2*(m : ℤ)^2
    then some (s.residue,t,z) else none

/-- After one verified anchor, all predicted global tags are obtained
from at most two cached seeds and one linear denominator stream. -/
def predictedGlobalTags {G : Type*} [CommGroup G] (g : G)
    (N m j₀ t₀ : ℕ) (z₀ : ℤ) : List (ℕ×ℕ×ℤ) :=
  (phaseSeeds g N m j₀).flatMap fun s =>
    (List.range (m-1)).filterMap (predictedTag m t₀ (seedOffset N m j₀) z₀ s)

/-- Exact arithmetic characterization of an emitted tag. -/
theorem predictedTag_eq_some_iff {G : Type*} (m t₀ : ℕ) (δ₀ z₀ : ℤ)
    (s : ProgressionSeed G) (r j t : ℕ) (z : ℤ) :
    predictedTag m t₀ δ₀ z₀ s r=some (j,t,z) ↔
      j=s.residue ∧ t=r+1 ∧ z=phaseIndex m t t₀ (cachedOffset m s) δ₀ z₀ ∧
      (t₀ : ℤ)∣(t : ℤ)*z₀ ∧ -4*(m : ℤ)^2≤z ∧ z<2*(m : ℤ)^2 := by
  unfold predictedTag
  dsimp only
  split_ifs with h
  · constructor
    · intro he
      have hp := Option.some.inj he
      have hj := congrArg Prod.fst hp
      have ht := congrArg (fun c : ℕ×ℕ×ℤ => c.2.1) hp
      have hz := congrArg (fun c : ℕ×ℕ×ℤ => c.2.2) hp
      dsimp only at hj ht hz
      subst j
      subst t
      subst z
      exact ⟨rfl,rfl,rfl,h.1,h.2⟩
    · rintro ⟨rfl,rfl,rfl,_,_,_⟩
      rfl
  · constructor
    · intro he
      cases he
    · rintro ⟨_,rfl,rfl,hd,hz,hzm⟩
      exact False.elim (h ⟨hd,hz,hzm⟩)

/-- The entire arithmetic mask has at most 2*(m-1) tags. This is an
input-count statement; it does not price anchor acquisition or bit costs. -/
theorem predictedGlobalTags_length_le {G : Type*} [CommGroup G] (g : G)
    {N m : ℕ} (hm : m.Prime) (hN : m.Coprime N) (j₀ t₀ : ℕ) (z₀ : ℤ) :
    (predictedGlobalTags g N m j₀ t₀ z₀).length≤2*(m-1) := by
  have hmenu := phaseSeeds_length_le_two g hm hN j₀
  unfold predictedGlobalTags
  rw [List.length_flatMap]
  have hbound : ∀ s∈phaseSeeds g N m j₀,
      ((List.range (m-1)).filterMap
        (predictedTag m t₀ (seedOffset N m j₀) z₀ s)).length≤m-1 := by
    intro s _
    simpa only [List.length_range] using List.length_filterMap_le _ (List.range (m-1))
  have hh := List.sum_le_card_nsmul
    ((phaseSeeds g N m j₀).map fun s =>
      ((List.range (m-1)).filterMap
        (predictedTag m t₀ (seedOffset N m j₀) z₀ s)).length) (m-1)
    (by intro n hn; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hn; exact hbound s hs)
  simp only [List.length_map,smul_eq_mul] at hh
  exact
    hh.trans (Nat.mul_le_mul_right (m-1) hmenu)

/-- Every arithmetic prediction is a genuine global hit for the routed
base. Soundness uses the verified anchor and rough-order cancellation. -/
theorem predictedGlobalTags_sound {p q m j₀ t₀ j t : ℕ} {z₀ z : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hanchor : GlobalHit (projectedUnit g m) (p*q) m j₀ t₀ z₀)
    (hmem : (j,t,z)∈predictedGlobalTags (projectedUnit g m) (p*q) m j₀ t₀ z₀) :
    GlobalHit (projectedUnit g m) (p*q) m j t z := by
  obtain ⟨s,hs,htarget⟩ := List.mem_flatMap.mp hmem
  obtain ⟨r,hr,he⟩ := List.mem_filterMap.mp htarget
  have hrm := List.mem_range.mp hr
  obtain ⟨hjs,htr,hindex,htz,hz,hzm⟩ :=
    (predictedTag_eq_some_iff _ _ _ _ _ _ _ _ _).mp he
  have hmenu := (phaseSeeds_mem_iff _ _ _ _ _).mp hs
  obtain ⟨hsmin,hsm,hseed⟩ := cached_seed_source hmenu.1
  have hoff : cachedOffset m s=seedOffset (p*q) m j := by
    rw [hseed,←hjs,cachedOffset_seed]
  rw [hoff] at hindex
  have hdiv : (m : ℤ)∣seedOffset (p*q) m j-seedOffset (p*q) m j₀ := by
    simpa only [hoff] using hmenu.2
  rcases hanchor with ⟨ht₀,ht₀m,hj₀,hj₀m,_,_,hglobal₀⟩
  have hc : j.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt
      (by omega) (by omega : j<m))).symm
  have hc₀ : j₀.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hj₀m)).symm
  have hcop := long_global_coprime_small hp hq hpq g hlong ht₀ ht₀m.le
  have hres := phase_prediction_residual hcop hdiv htz
    ((hit_residual_iff (projectedUnit g m) hm.pos hc₀ z₀).mp hglobal₀)
  rw [←hindex] at hres
  exact ⟨by omega,by omega,by omega,by omega,hz,hzm,
    (hit_residual_iff (projectedUnit g m) hm.pos hc z).mpr hres⟩

/-- Every verified global hit occurs in the arithmetic mask. This uses
the exact short cross residual, including arbitrary false factor-row tags. -/
theorem predictedGlobalTags_complete {p q m j₀ t₀ j t : ℕ} {z₀ z : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hanchor : GlobalHit (projectedUnit g m) (p*q) m j₀ t₀ z₀)
    (hhit : GlobalHit (projectedUnit g m) (p*q) m j t z) :
    (j,t,z)∈predictedGlobalTags (projectedUnit g m) (p*q) m j₀ t₀ z₀ := by
  have hphase := long_global_phase hp hq hpq hm g hlong hhit hanchor
  rcases hanchor with ⟨ht₀,ht₀m,_,_,_,_,_⟩
  rcases hhit with ⟨ht,htm,hj,hjm,hz,hzm,_⟩
  obtain ⟨hdiv,htz,hindex⟩ := phase_index_exact hm ht htm ht₀ ht₀m hphase
  let s := progressionSeed (projectedUnit g m) (p*q) m j
  have hs : s∈phaseSeeds (projectedUnit g m) (p*q) m j₀ :=
    (phaseSeeds_mem_iff _ _ _ _ _).mpr
      ⟨progressionSeed_mem _ (by omega) hjm,by simpa only [s,cachedOffset_seed] using hdiv⟩
  apply List.mem_flatMap.mpr
  refine ⟨s,hs,List.mem_filterMap.mpr ⟨t-1,List.mem_range.mpr (by omega),?_⟩⟩
  apply (predictedTag_eq_some_iff _ _ _ _ _ _ _ _ _).mpr
  exact ⟨rfl,by omega,by simpa only [s,cachedOffset_seed] using hindex,htz,hz,hzm⟩

/-- One verified public global tag determines exactly the entire common
global-hit set. The two seed descriptors suffice; expansion is only linear. -/
theorem predictedGlobalTags_exact {p q m j₀ t₀ j t : ℕ} {z₀ z : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hanchor : GlobalHit (projectedUnit g m) (p*q) m j₀ t₀ z₀) :
    (j,t,z)∈predictedGlobalTags (projectedUnit g m) (p*q) m j₀ t₀ z₀ ↔
      GlobalHit (projectedUnit g m) (p*q) m j t z :=
  ⟨predictedGlobalTags_sound hp hq hpq hm g hlong hanchor,
    predictedGlobalTags_complete hp hq hpq hm g hlong hanchor⟩

/-- A common index returned by the original public interval reader
supplies a verified phase anchor, with its exact original signed bounds. -/
theorem merged_reader_global_tag {N m j t r : ℕ} (g : (ZMod N)ˣ)
    (upper : Bool) (ht : 0<t) (htm : t<m) (hj : 1≤j) (hjm : j<m)
    (hread : recoverTaggedInterval (commonStep g m)
      (mergedTarget g m t (progressionSeed g N m j) upper)
      (mergedLength m) (2*m)=some (Sum.inr r)) :
    GlobalHit g N m j t (mergedStart m upper+r) := by
  obtain ⟨hr,hvalue⟩ := recoverTaggedInterval_index_sound _ _ hread
  have hrZ : (r : ℤ)<3*(m : ℤ)^2 := by
    exact_mod_cast hr
  have hr₀ : (0 : ℤ)≤r := by positivity
  have hx : mergedTarget g m t (progressionSeed g N m j) upper=(commonStep g m)^r := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val] using hvalue
  have hglobal : (progressionSeed g N m j).step^t=
      (commonStep g m)^(mergedStart m upper+r) := by
    calc
      (progressionSeed g N m j).step^t=
          mergedTarget g m t (progressionSeed g N m j) upper*
            (commonStep g m)^mergedStart m upper := by
        simp only [mergedTarget,mul_assoc,←zpow_add,neg_add_cancel,zpow_zero,mul_one]
      _=(commonStep g m)^r*(commonStep g m)^mergedStart m upper := by rw [hx]
      _=(commonStep g m)^(mergedStart m upper+r) := by
        rw [←zpow_natCast,←zpow_add]
        congr 1
        omega
  refine ⟨ht,htm,hj,hjm,?_,?_,hglobal⟩
  · cases upper <;> simp only [mergedStart,Bool.false_eq_true,if_false,if_true] <;>
      nlinarith only [hr₀,sq_nonneg (m : ℤ)]
  · cases upper <;> simp only [mergedStart,Bool.false_eq_true,if_false,if_true] <;>
      nlinarith only [hrZ,sq_nonneg (m : ℤ)]

/-- On the actual N-only matched-width long route, a public common index
from the unchanged reader determines the exact linear arithmetic mask.
Neither numerical local order nor a private factor-row tag is an input. -/
theorem long_public_route_reader_mask {p q a j₀ t₀ r₀ : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) (hc : a.Coprime (p*q))
    (upper₀ : Bool)
    (ht₀ : 0<t₀) (ht₀m : t₀<SemiprimeEuclidRowBudget.publicRowModulus (p*q))
    (hj₀ : 1≤j₀) (hj₀m : j₀<SemiprimeEuclidRowBudget.publicRowModulus (p*q))
    (hread : let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      recoverTaggedInterval (commonStep h m)
        (mergedTarget h m t₀ (progressionSeed h (p*q) m j₀) upper₀)
        (mergedLength m) (2*m)=some (Sum.inr r₀)) :
    let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
    let h := projectedUnit (ZMod.unitOfCoprime a hc) m
    let z₀ := mergedStart m upper₀+r₀
    (∀ (j t : ℕ) (z : ℤ), (j,t,z)∈predictedGlobalTags h (p*q) m j₀ t₀ z₀ ↔
      GlobalHit h (p*q) m j t z) ∧
      (predictedGlobalTags h (p*q) m j₀ t₀ z₀).length≤2*(m-1) := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨_,hlong⟩ := hd
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  have hm := SemiprimeEuclidRowBudget.publicRowModulus_prime (p*q)
  have hcover := public_modulus_prefix_below_input (Nat.mul_pos hp.pos hq.pos) hB
  have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer hcover hnone hm.pos
    (by have hh := hm.two_le; nlinarith only [hh] : m≤m^2)
  have hanchor := merged_reader_global_tag (projectedUnit g m) upper₀
    ht₀ ht₀m hj₀ hj₀m hread
  constructor
  · intro j t z
    exact predictedGlobalTags_exact hp hq hpq.ne hm g hlong hanchor
  · exact predictedGlobalTags_length_le _ hm hcop.symm _ _ _

end RiemannGaussian.SemiprimeGlobalPhaseCancellation
