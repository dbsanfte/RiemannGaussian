/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNormCancellationObstruction
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Multiset.Dedup

/-!
# The second carry separates the residue polynomial's paired roots

For each fixed lower input digit, distinct original row tags can have equal
exact integer offsets at only one second carry. Summing the whole original
family over all carries gives a linear duplicate-pair mass bound.

The literal exponential target carrier preserves exact offset surplus on
LongData. Thus its monic squared divisors cannot recover the large square
factor of the lower-digit residue polynomial on the classical counterfamily
recorded in the investigation journal. Published analytic density, infinite
families and asymptotic counting are not additional Lean axioms here.
-/

namespace RiemannGaussian.SemiprimeOffsetCarryObstruction

open scoped BigOperators
open Polynomial SemiprimeQuotientRows SemiprimeDenseRowCoverage
open SemiprimeDenseRowCarries SemiprimeGlobalPhaseCancellation
open SemiprimeSeedDetectorResidueObstruction SemiprimeScatteredColumnObstruction
open SemiprimeCauchyAcquisitionObstruction SemiprimeLocalOrderRouting
open SemiprimeCentreFreeCover SemiprimeSeedHermiteQuotient
open SemiprimeSeedPointRigidity

/-- The original centered carry satisfies this exact second-digit identity. -/
theorem offset_lift_balance {N m j : ℕ} (hm : 0<m) (hj : j.Coprime m) :
    (N : ℤ)+j*seedOffset N m j=
      (representative N m j 1 : ℤ)*j*(1-j)+(m : ℤ)^2*(seedRow N m j).c := by
  have hr := denseRow_relation (N:=N) (j:=j) (t:=1) hm hj false
  change quotientRelation N m j (representative N m j 1)
    (seedRow N m j).b (seedRow N m j).c 1 at hr
  unfold quotientRelation at hr
  unfold seedOffset
  linear_combination -hr

/-- The full offset determines the input modulo m squared once its leading residue is fixed. -/
theorem offset_lift_modEq {N m j : ℕ} (hm : 0<m) (hj : j.Coprime m) :
    (j : ℤ)*seedOffset N m j ≡
      (representative N m j 1 : ℤ)*j*(1-j)-N [ZMOD (m : ℤ)^2] := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(seedRow N m j).c,?_⟩
  linear_combination -(offset_lift_balance (N:=N) hm hj)

/-- Equal lower input digits leave a linear second-carry difference. -/
theorem offset_difference_modEq {N N₀ m j : ℕ} (hm : 0<m) (hj : j.Coprime m)
    (hclass : (N : ℤ) ≡ (N₀ : ℤ) [ZMOD m]) :
    (j : ℤ)*(seedOffset N m j-seedOffset N₀ m j) ≡
      -((N : ℤ)-N₀) [ZMOD (m : ℤ)^2] := by
  have ha := representative_eq_of_cofactor_modEq (p:=1) hm hj hclass
  simp only [one_mul] at ha
  have h := (offset_lift_modEq (N:=N) hm hj).sub (offset_lift_modEq (N:=N₀) hm hj)
  rw [ha] at h
  convert h using 1 <;> ring

/-- All m second carries share the same lower input digit. -/
theorem carry_class {s m u v : ℕ} :
    ((s+m*u : ℕ) : ℤ) ≡ ((s+m*v : ℕ) : ℤ) [ZMOD m] := by
  apply Int.modEq_iff_dvd.mpr
  exact ⟨(v : ℤ)-u,by push_cast; ring⟩

/-- Two bounded second carries cannot represent the same input modulo m squared. -/
theorem equal_input_carry {s m u v : ℕ} (hm : 0<m) (hu : u<m) (hv : v<m)
    (h : ((s+m*u : ℕ) : ℤ) ≡ ((s+m*v : ℕ) : ℤ) [ZMOD (m : ℤ)^2]) : u=v := by
  have h' : (m : ℤ)*u ≡ (m : ℤ)*v [ZMOD (m : ℤ)*(m : ℤ)] := by
    have h₀ : (s : ℤ)+(m : ℤ)*u ≡ (s : ℤ)+(m : ℤ)*v
        [ZMOD (m : ℤ)*(m : ℤ)] := by
      simpa only [Nat.cast_add,Nat.cast_mul,pow_two] using h
    exact h₀.add_left_cancel' s
  have h'' : (u : ℤ) ≡ (v : ℤ) [ZMOD m] :=
    h'.mul_left_cancel' (by exact_mod_cast hm.ne')
  have hn := Int.natCast_modEq_iff.mp h''
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt hu,Nat.mod_eq_of_lt hv] using hn

/-- Every fixed literal row retains all m different second carries in its exact integer offset. -/
theorem offset_carry_injective {s m j : ℕ} (hm : 0<m) (hj : j.Coprime m) :
    Function.Injective (fun u : Fin m => seedOffset (s+m*u.val) m j) := by
  intro u v he
  change seedOffset (s+m*u.val) m j=seedOffset (s+m*v.val) m j at he
  have h := offset_difference_modEq hm hj (carry_class (s:=s) (u:=u.val) (v:=v.val))
  rw [he,sub_self,mul_zero] at h
  have h' : ((s+m*u.val : ℕ) : ℤ) ≡ ((s+m*v.val : ℕ) : ℤ) [ZMOD (m : ℤ)^2] := by
    apply Int.modEq_iff_dvd.mpr
    simpa only [sub_zero,neg_sub] using h.dvd
  exact Fin.ext (equal_input_carry hm u.isLt v.isLt h')

/-- A nonzero element modulo a prime also permits integer cancellation modulo its square. -/
theorem integer_coprime_square {m : ℕ} (hm : m.Prime) (a : ℤ)
    (ha : (a : ZMod m)≠0) : IsCoprime ((m : ℤ)^2) a := by
  apply IsCoprime.pow_left
  apply Int.isCoprime_iff_nat_coprime.mpr
  rw [Int.natAbs_natCast]
  apply hm.coprime_iff_not_dvd.mpr
  intro hd
  exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr (Int.natCast_dvd.mpr hd))

/-- Two distinct original tags can have equal exact offsets at only one second carry. -/
theorem duplicate_pair_unique_carry {s m j k u v : ℕ} (hm : m.Prime)
    (hj : 1≤j) (hjm : j<m) (hk : 1≤k) (hkm : k<m) (hjk : j≠k)
    (hu : u<m) (hv : v<m)
    (he : seedOffset (s+m*u) m j=seedOffset (s+m*u) m k)
    (he₀ : seedOffset (s+m*v) m j=seedOffset (s+m*v) m k) : u=v := by
  have hjcop : j.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hkcop : k.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hkm)).symm
  let D := seedOffset (s+m*u) m j-seedOffset (s+m*v) m j
  have hJ := offset_difference_modEq hm.pos hjcop (carry_class (s:=s) (u:=u) (v:=v))
  have hK := offset_difference_modEq hm.pos hkcop (carry_class (s:=s) (u:=u) (v:=v))
  rw [←he,←he₀] at hK
  change (j : ℤ)*D ≡ -(((s+m*u : ℕ) : ℤ)-(s+m*v : ℕ)) [ZMOD (m : ℤ)^2] at hJ
  change (k : ℤ)*D ≡ -(((s+m*u : ℕ) : ℤ)-(s+m*v : ℕ)) [ZMOD (m : ℤ)^2] at hK
  have hd : (m : ℤ)^2∣((j : ℤ)-k)*D := by
    have h := (hJ.sub hK).symm.dvd
    convert h using 1
    ring
  have hdiff : (((j : ℤ)-k : ℤ) : ZMod m)≠0 := by
    intro heq
    have heq' : (j : ZMod m)=(k : ZMod m) := by
      simpa only [Int.cast_sub,Int.cast_natCast,sub_eq_zero] using heq
    have hv' := congrArg ZMod.val heq'
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hjm,Nat.mod_eq_of_lt hkm] at hv'
    exact hjk hv'
  have hD := (integer_coprime_square hm ((j : ℤ)-k) hdiff).dvd_of_dvd_mul_left hd
  have hDmod : D ≡ 0 [ZMOD (m : ℤ)^2] := Int.modEq_iff_dvd.mpr (by simpa using hD.neg_right)
  have hN := (hDmod.mul_left (j : ℤ)).symm.trans hJ
  have hclass : ((s+m*u : ℕ) : ℤ) ≡ ((s+m*v : ℕ) : ℤ) [ZMOD (m : ℤ)^2] := by
    apply Int.modEq_iff_dvd.mpr
    simpa only [mul_zero,sub_zero,neg_sub] using hN.dvd
  exact equal_input_carry hm.pos hu hv hclass

/-- The lower offset residue depends only on the lower input digit. -/
theorem offset_residue_of_input_modEq {N N₀ m j : ℕ} (hm : 0<m) (hj : j.Coprime m)
    (hclass : (N : ℤ) ≡ (N₀ : ℤ) [ZMOD m]) :
    seedOffset N m j ≡ seedOffset N₀ m j [ZMOD m] := by
  have ha := representative_eq_of_cofactor_modEq (p:=1) hm hj hclass
  simp only [one_mul] at ha
  apply Int.modEq_iff_dvd.mpr
  refine ⟨(seedRow N₀ m j).b-(seedRow N m j).b,?_⟩
  unfold seedOffset
  rw [ha]
  ring

/-- Each nonzero original tag has at most one distinct partner in its lower offset class. -/
theorem residue_partner_unique {N m j k l : ℕ} (hm : m.Prime) (hN : m.Coprime N)
    (hj : 1≤j) (hjm : j<m) (hk : 1≤k) (hkm : k<m) (hl : 1≤l) (hlm : l<m)
    (hjk : j≠k) (hjl : j≠l)
    (hek : (seedOffset N m j : ZMod m)=(seedOffset N m k : ZMod m))
    (hel : (seedOffset N m j : ZMod m)=(seedOffset N m l : ZMod m)) : k=l := by
  let : Fact m.Prime := ⟨hm⟩
  have hdk : (m : ℤ)∣seedOffset N m j-seedOffset N m k :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp (by simpa using sub_eq_zero.mpr hek)
  have hdl : (m : ℤ)∣seedOffset N m j-seedOffset N m l :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp (by simpa using sub_eq_zero.mpr hel)
  have hpk := (offset_class_partner_relation hm hN hj hjm hk hkm hdk).resolve_left hjk
  have hpl := (offset_class_partner_relation hm hN hj hjm hl hlm hdl).resolve_left hjl
  have hjzero : (j : ZMod m)≠0 := by
    apply (ZMod.isUnit_iff_coprime j m).mpr ?_ |>.ne_zero
    exact (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hc : 2*(j : ZMod m)-1≠0 := by
    intro hz
    apply hjzero
    linear_combination hpk+(k : ZMod m)*hz
  have hprod : (2*(j : ZMod m)-1)*((k : ZMod m)-l)=0 := by
    linear_combination -hpk+hpl
  have hkl := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hc)
  have hv := congrArg ZMod.val hkl
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hkm,Nat.mod_eq_of_lt hlm] using hv

/-- Unordered pairs of distinct literal original row labels. -/
noncomputable def rowPairs (m : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.range (m-1))×ˢ(Finset.range (m-1))).filter fun jk => jk.1<jk.2

/-- Row pairs with equal lower-digit offset residues at the supplied input. -/
noncomputable def aliasPairs (s m : ℕ) : Finset (ℕ×ℕ) :=
  (rowPairs m).filter fun jk =>
    (seedOffset s m (jk.1+1) : ZMod m)=(seedOffset s m (jk.2+1) : ZMod m)

/-- Row pairs with equal full integer offsets, including the centered carry. -/
noncomputable def duplicatePairs (N m : ℕ) : Finset (ℕ×ℕ) :=
  (rowPairs m).filter fun jk => seedOffset N m (jk.1+1)=seedOffset N m (jk.2+1)

/-- An unordered pair retains two literal positive row tags and their original bounds. -/
theorem rowPairs_mem {m j k : ℕ} : (j,k)∈rowPairs m ↔ j+1<m ∧ k+1<m ∧ j<k := by
  simp only [rowPairs,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
  omega

/-- A linear bound for all lower-digit alias pairs; no prime progression distribution is assumed. -/
theorem aliasPairs_card_le {s m : ℕ} (hm : m.Prime) (hs : m.Coprime s) :
    (aliasPairs s m).card≤m-1 := by
  have hmaps : Set.MapsTo Prod.fst (aliasPairs s m : Set (ℕ×ℕ))
      (Finset.range (m-1) : Set ℕ) := by
    intro jk hjk
    have h := (rowPairs_mem.mp (Finset.mem_filter.mp hjk).1).1
    exact Finset.mem_range.mpr (by omega)
  have hinj : Set.InjOn Prod.fst (aliasPairs s m : Set (ℕ×ℕ)) := by
    intro jk hjk jl hjl he
    have h₁ := rowPairs_mem.mp (Finset.mem_filter.mp hjk).1
    have h₂ := rowPairs_mem.mp (Finset.mem_filter.mp hjl).1
    have hsecond : jk.2+1=jl.2+1 := by
      apply residue_partner_unique hm hs (by omega) h₁.1 (by omega) h₁.2.1
        (by omega) h₂.2.1 (by omega) (by omega)
      · exact (Finset.mem_filter.mp hjk).2
      · simpa only [he] using (Finset.mem_filter.mp hjl).2
    exact Prod.ext he (by omega)
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmaps hinj

/-- Every exact duplicate is already a lower-digit alias, with no change of row labels. -/
theorem duplicatePairs_eq_alias_filter {s m u : ℕ} (hm : m.Prime) :
    duplicatePairs (s+m*u) m=(aliasPairs s m).filter fun jk =>
      seedOffset (s+m*u) m (jk.1+1)=seedOffset (s+m*u) m (jk.2+1) := by
  ext jk
  simp only [duplicatePairs,aliasPairs,Finset.mem_filter]
  constructor
  · rintro ⟨hr,he⟩
    refine ⟨⟨hr,?_⟩,he⟩
    have hb := rowPairs_mem.mp hr
    have hj : (jk.1+1).Coprime m :=
      (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hb.1)).symm
    have hk : (jk.2+1).Coprime m :=
      (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hb.2.1)).symm
    have hJ := offset_residue_of_input_modEq hm.pos hj (carry_class (s:=s) (u:=u) (v:=0))
    have hK := offset_residue_of_input_modEq hm.pos hk (carry_class (s:=s) (u:=u) (v:=0))
    simp only [mul_zero,add_zero] at hJ hK
    have hclass := hJ.symm.trans (by simpa only [he] using hK)
    exact (ZMod.intCast_eq_intCast_iff _ _ m).mpr hclass
  · exact fun h => ⟨h.1.1,h.2⟩

/-- The whole-family duplicate-pair mass, summed across all second carries, is at most linear. -/
theorem duplicate_carry_mass_le {s m : ℕ} (hm : m.Prime) (hs : m.Coprime s) :
    ∑ u∈Finset.range m,(duplicatePairs (s+m*u) m).card≤m-1 := by
  classical
  have hrewrite : (∑ u∈Finset.range m,(duplicatePairs (s+m*u) m).card)=
      ∑ jk∈aliasPairs s m,((Finset.range m).filter fun u =>
        seedOffset (s+m*u) m (jk.1+1)=seedOffset (s+m*u) m (jk.2+1)).card := by
    simp_rw [duplicatePairs_eq_alias_filter hm,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  rw [hrewrite]
  calc
    _≤∑ _jk∈aliasPairs s m,1 := by
      apply Finset.sum_le_sum
      intro jk hjk
      apply Finset.card_le_one.mpr
      intro u hu v hv
      have hb := rowPairs_mem.mp (Finset.mem_filter.mp hjk).1
      exact duplicate_pair_unique_carry hm (by omega) hb.1 (by omega) hb.2.1
        (by omega) (Finset.mem_range.mp (Finset.mem_filter.mp hu).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hv).1)
        (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2
    _=(aliasPairs s m).card := by simp
    _≤m-1 := aliasPairs_card_le hm hs

/-- An exact finite Markov bound for second carries with many duplicate original targets. -/
theorem duplicate_carry_threshold_bound {s m B : ℕ} (hm : m.Prime)
    (hs : m.Coprime s) :
    B*((Finset.range m).filter fun u => B≤(duplicatePairs (s+m*u) m).card).card≤m-1 := by
  classical
  let bad := (Finset.range m).filter fun u => B≤(duplicatePairs (s+m*u) m).card
  calc
    B*bad.card=∑ _u∈bad,B := by simp only [Finset.sum_const,smul_eq_mul,mul_comm]
    _≤∑ u∈bad,(duplicatePairs (s+m*u) m).card := by
      apply Finset.sum_le_sum
      exact fun _ hu => (Finset.mem_filter.mp hu).2
    _≤∑ u∈Finset.range m,(duplicatePairs (s+m*u) m).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
    _≤m-1 := duplicate_carry_mass_le hm hs

/-- An exponent unit of order greater than m cannot be an additive character of ZMod m. -/
theorem no_residue_exponent_hom {G : Type*} [Group G] (g : G) {m : ℕ}
    (hm : 0<m) (horder : m<orderOf g) :
    ¬∃ f : ZMod m→+Additive G,f 1=Additive.ofMul g := by
  rintro ⟨f,hf⟩
  have hmzero : m • (1 : ZMod m)=0 := by simp only [nsmul_eq_mul,ZMod.natCast_self,mul_one]
  have he := congrArg f hmzero
  rw [map_nsmul,hf,map_zero] at he
  have hg : g^m=1 := by
    exact congrArg Additive.toMul he
  exact (not_le_of_gt horder) (orderOf_le_of_pow_eq_one hm hg)


/-- A squared monic divisor is bounded by the surplus of exact root occurrences. -/
theorem multiset_square_divisor_natDegree_le_surplus
    {K : Type*} [Field K] [DecidableEq K] (s : Multiset K) {A : K[X]}
    (hA : A.Monic) (hdvd : A^2 ∣ (s.map fun x => X-C x).prod) :
    A.natDegree ≤ (s-s.dedup).card := by
  classical
  have hP : (s.map fun x => X-C x).prod.Monic := monic_multisetProd_X_sub_C s
  have hsplits : ((s.map fun x => X-C x).prod).Splits := by
    apply splits_iff_card_roots.mpr
    rw [roots_multiset_prod_X_sub_C,natDegree_multiset_prod_X_sub_C_eq_card]
  have hAdvd : A ∣ (s.map fun x => X-C x).prod :=
    dvd_trans ⟨A,by rw [pow_two]⟩ hdvd
  have hsplitA := hsplits.of_dvd hP.ne_zero hAdvd
  have hpow : (A^2).roots=A.roots+A.roots := by
    rw [pow_two,roots_mul (mul_ne_zero hA.ne_zero hA.ne_zero)]
  have hle : A.roots+A.roots ≤ s := by
    simpa only [hpow,roots_multiset_prod_X_sub_C] using
      (Polynomial.roots.le_of_dvd hP.ne_zero hdvd)
  have hrootle : A.roots ≤ s-s.dedup := by
    apply Multiset.le_iff_count.mpr
    intro x
    have hc := Multiset.le_iff_count.mp hle x
    simp only [Multiset.count_add] at hc
    rw [Multiset.count_sub,Multiset.count_dedup]
    by_cases hx : x∈s
    · simp only [hx, ↓reduceIte]
      have hpos := Multiset.count_pos.mpr hx
      omega
    · simp only [hx, ↓reduceIte]
      have hz := Multiset.count_eq_zero.mpr hx
      omega
  rw [hsplitA.natDegree_eq_card_roots]
  exact Multiset.card_le_card hrootle

/-- Restricted injectivity preserves the surplus exactly, including all
original repeated occurrences. Global injectivity is not required. -/
theorem mapped_surplus_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Multiset α) (f : α→β) (hinj : Set.InjOn f s.toFinset) :
    (s.map f-(s.map f).dedup).card=(s-s.dedup).card := by
  rw [Multiset.card_sub (Multiset.dedup_le _),Multiset.card_map,
    Multiset.card_sub (Multiset.dedup_le _)]
  congr 1
  rw [←Multiset.card_toFinset,Multiset.toFinset_map,
    Finset.card_image_of_injOn hinj,Multiset.card_toFinset]

/-- A field root map injective on the supplied integer offsets preserves
the original offset-surplus bound for every squared monic divisor. -/
theorem list_square_divisor_natDegree_le_offset_surplus
    {K : Type*} [Field K] (ds : List ℤ) (f : ℤ→K)
    (hinj : Set.InjOn f ds.toFinset) {A : K[X]} (hA : A.Monic)
    (hdvd : A^2 ∣ ((ds.map f).map fun x => X-C x).prod) :
    A.natDegree≤((ds : Multiset ℤ)-(ds : Multiset ℤ).dedup).card := by
  classical
  have hdvd' : A^2 ∣ (((ds : Multiset ℤ).map f).map fun x => X-C x).prod := by
    simpa using hdvd
  have h := multiset_square_divisor_natDegree_le_surplus
    ((ds : Multiset ℤ).map f) hA hdvd'
  rw [mapped_surplus_eq (ds : Multiset ℤ) f (by simpa using hinj)] at h
  exact h

/-- The actual short offset window embeds into exponent targets whenever
the local order exceeds its width. The additive N phase cancels. -/
theorem exponent_targets_injOn_of_short_offsets
    {R : Type*} [CommRing R] (u : Rˣ) (N m : ℕ) (ds : List ℤ)
    (horder : 4*m^2<orderOf u)
    (hbound : ∀ d∈ds,-3*(m : ℤ)^2≤d ∧ d≤(m : ℤ)^2) :
    Set.InjOn (fun d : ℤ => ((u^((N : ℤ)+d) : Rˣ) : R)) ds.toFinset := by
  intro a ha b hb he
  have hba := hbound a (List.mem_toFinset.mp ha)
  have hbb := hbound b (List.mem_toFinset.mp hb)
  by_contra hab
  have hexp : (N : ℤ)+a≠(N : ℤ)+b := by omega
  have hgap : (((N : ℤ)+a)-((N : ℤ)+b)).natAbs≤4*m^2 := by
    have h : |((N : ℤ)+a)-((N : ℤ)+b)|≤4*(m : ℤ)^2 := by
      rw [abs_le]
      constructor <;> omega
    rw [←Int.natCast_natAbs] at h
    exact_mod_cast h
  have hnonzero := zpow_short_gap_ne_zero u ((N : ℤ)+a) ((N : ℤ)+b)
    hexp (hgap.trans_lt horder)
  exact hnonzero (sub_eq_zero.mpr he)

/-- One hidden prime-field specialization of the exact offset count. -/
theorem long_left_exponent_square_divisor_le_offset_surplus
    {p q m : ℕ} (hp : p.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (ds : List ℤ)
    (hbound : ∀ d∈ds,-3*(m : ℤ)^2≤d ∧ d≤(m : ℤ)^2)
    {A : (ZMod p)[X]} (hA : A.Monic)
    (hdvd : A^2 ∣ ((ds.map fun d =>
      (((leftUnit (projectedUnit g m))^(((p*q : ℕ) : ℤ)+d) : (ZMod p)ˣ) : ZMod p)).map
        fun x => X-C x).prod) :
    A.natDegree≤((ds : Multiset ℤ)-(ds : Multiset ℤ).dedup).card := by
  let : Fact p.Prime := ⟨hp⟩
  apply list_square_divisor_natDegree_le_offset_surplus ds _ _ hA hdvd
  apply exponent_targets_injOn_of_short_offsets
    (leftUnit (projectedUnit g m)) (p*q) m ds _ hbound
  have h := hlong.2.2.2.1.1
  nlinarith only [h]

/-- Original row labels, with their integer offsets left untouched in
the surplus on the right. No deduplication of the source list is made. -/
theorem long_left_tag_square_divisor_le_offset_surplus
    {p q m : ℕ} (hp : p.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (tags : List ℕ) (htags : ∀ j∈tags,1≤j ∧ j<m)
    {A : (ZMod p)[X]} (hA : A.Monic)
    (hdvd : A^2 ∣ (tags.map fun j => X-C
      (((leftUnit (projectedUnit g m))^(((p*q : ℕ) : ℤ)+seedOffset (p*q) m j) :
        (ZMod p)ˣ) : ZMod p)).prod) :
    A.natDegree≤
      ((tags.map (seedOffset (p*q) m) : Multiset ℤ)-
        (tags.map (seedOffset (p*q) m) : Multiset ℤ).dedup).card := by
  apply long_left_exponent_square_divisor_le_offset_surplus hp g hlong
    (tags.map (seedOffset (p*q) m)) _ hA
      (by simpa only [List.map_map,Function.comp_def] using hdvd)
  intro d hd
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd
  exact seedOffset_bounds (by omega : 1<m) (htags j hj).1 (htags j hj).2

/-- The ORIGINAL modulus-N carrier, transported to one hidden field.
Its degree and literal offset multiplicities are preserved; the field
projection is proof-side only. -/
theorem original_square_divisor_natDegree_le_offset_surplus
    {p q m : ℕ} (hp : p.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    {A : (ZMod (p*q))[X]} (hA : A.Monic)
    (hdvd : A^2 ∣ targetPolynomial (seedTargets (projectedUnit g m) m)) :
    A.natDegree≤
      (((List.range (m-1)).map fun r => seedOffset (p*q) m (r+1) : Multiset ℤ)-
        ((List.range (m-1)).map fun r => seedOffset (p*q) m (r+1) :
          Multiset ℤ).dedup).card := by
  let : Fact p.Prime := ⟨hp⟩
  let f := ZMod.castHom (dvd_mul_right p q) (ZMod p)
  let h := projectedUnit g m
  let ds := (List.range (m-1)).map fun r => seedOffset (p*q) m (r+1)
  have hbound : ∀ d∈ds,-3*(m : ℤ)^2≤d ∧ d≤(m : ℤ)^2 := by
    intro d hd
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hd
    have hr' := List.mem_range.mp hr
    exact seedOffset_bounds (by omega : 1<m) (by omega) (by omega)
  have hstep (r : ℕ) (hr : r∈List.range (m-1)) :
      f (((progressionSeed h (p*q) m (r+1)).step : (ZMod (p*q))ˣ) : ZMod (p*q))=
        (((leftUnit h)^(((p*q : ℕ) : ℤ)+seedOffset (p*q) m (r+1)) :
          (ZMod p)ˣ) : ZMod p) := by
    have hr' := List.mem_range.mp hr
    have hjcop : (r+1).Coprime m :=
      (hmprime.coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
    change (leftUnit ((progressionSeed h (p*q) m (r+1)).step) : ZMod p)=_
    rw [seed_step_offset _ hmprime.pos hjcop]
    simp only [leftUnit,map_zpow]
  have hpoly : (targetPolynomial (seedTargets h m)).map f=
      ((ds.map fun d =>
        (((leftUnit h)^(((p*q : ℕ) : ℤ)+d) : (ZMod p)ˣ) : ZMod p)).map
          fun x => X-C x).prod := by
    unfold targetPolynomial seedTargets progressionSeeds
    rw [Polynomial.map_list_prod]
    simp only [ds,List.map_map,Function.comp_def,Polynomial.map_sub,
      Polynomial.map_X,Polynomial.map_C]
    congr 1
    apply List.map_congr_left
    intro r hr
    rw [hstep r hr]
  have hmapdvd : (A.map f)^2 ∣ (targetPolynomial (seedTargets h m)).map f := by
    simpa only [Polynomial.map_pow] using Polynomial.map_dvd f hdvd
  rw [hpoly] at hmapdvd
  have hdegree := long_left_exponent_square_divisor_le_offset_surplus hp g hlong
    ds hbound (hA.map f) hmapdvd
  rw [hA.natDegree_map f] at hdegree
  exact hdegree


section PairCount

variable {α : Type*} [DecidableEq α]

/-- Equal-root pairs with increasing source indices. -/
noncomputable def indexedEqualPairs (f : ℕ→α) (n : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.range n)×ˢ(Finset.range n)).filter fun ij =>
    ij.1 < ij.2 ∧ f ij.1=f ij.2

/-- Each surplus occurrence contributes at least one pair with an earlier equal value. -/
theorem range_surplus_le_equal_pairs (f : ℕ→α) (n : ℕ) :
    n-((Finset.range n).image f).card≤(indexedEqualPairs f n).card := by
  induction n with
  | zero => simp [indexedEqualPairs]
  | succ n ih =>
    have hsubset : indexedEqualPairs f n⊆indexedEqualPairs f (n+1) := by
      intro ij hij
      simp only [indexedEqualPairs,Finset.mem_filter,Finset.mem_product,
        Finset.mem_range] at hij ⊢
      exact ⟨⟨by omega,by omega⟩,hij.2⟩
    have hcard := Finset.card_le_card hsubset
    have himage : ((Finset.range n).image f).card≤n := by
      exact (Finset.card_image_le).trans (by simp)
    by_cases hmem : f n∈(Finset.range n).image f
    · obtain ⟨i,hi,hfi⟩ := Finset.mem_image.mp hmem
      have hinew : (i,n)∈indexedEqualPairs f (n+1) := by
        simp only [indexedEqualPairs,Finset.mem_filter,Finset.mem_product,
          Finset.mem_range]
        have hilt := Finset.mem_range.mp hi
        exact ⟨⟨by omega,by omega⟩,hilt,hfi⟩
      have hinot : (i,n)∉indexedEqualPairs f n := by
        simp only [indexedEqualPairs,Finset.mem_filter,Finset.mem_product,
          Finset.mem_range]
        omega
      have hinsert : insert (i,n) (indexedEqualPairs f n)⊆indexedEqualPairs f (n+1) :=
        Finset.insert_subset_iff.mpr ⟨hinew,hsubset⟩
      have hinc : (indexedEqualPairs f n).card+1≤(indexedEqualPairs f (n+1)).card := by
        simpa only [Finset.card_insert_of_notMem hinot] using Finset.card_le_card hinsert
      rw [Finset.range_add_one,Finset.image_insert,Finset.insert_eq_of_mem hmem]
      omega
    · rw [Finset.range_add_one,Finset.image_insert,Finset.card_insert_of_notMem hmem]
      omega

/-- Multiset form: no bound on individual fibers is required. -/
theorem indexed_multiset_surplus_le_equal_pairs (f : ℕ→α) (n : ℕ) :
    ((Finset.range n).val.map f-((Finset.range n).val.map f).dedup).card≤
      (indexedEqualPairs f n).card := by
  rw [Multiset.card_sub (Multiset.dedup_le _),Multiset.card_map,
    ←Multiset.card_toFinset]
  simpa only [Finset.card_range,Finset.range_val,Multiset.card_range,Multiset.toFinset_map,
    Multiset.toFinset_range] using range_surplus_le_equal_pairs f n

/-- List-of-range form matching the original offset list. -/
theorem range_list_surplus_le_equal_pairs (f : ℕ→α) (n : ℕ) :
    (((List.range n).map f : Multiset α)-
      ((List.range n).map f : Multiset α).dedup).card≤
      (indexedEqualPairs f n).card := by
  simpa only [Finset.range_val,←Multiset.coe_range,Multiset.map_coe] using
    indexed_multiset_surplus_le_equal_pairs f n


end PairCount

/-- A squared monic divisor of the literal whole-family carrier is bounded
by the unordered exact duplicate-pair count, with all row labels retained. -/
theorem original_square_divisor_natDegree_le_duplicatePairs
    {p q m : ℕ} (hp : p.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    {A : (ZMod (p*q))[X]} (hA : A.Monic)
    (hdvd : A^2 ∣ targetPolynomial (seedTargets (projectedUnit g m) m)) :
    A.natDegree≤(duplicatePairs (p*q) m).card := by
  have hsurplus := range_list_surplus_le_equal_pairs
    (fun r => seedOffset (p*q) m (r+1)) (m-1)
  have hpairs : indexedEqualPairs (fun r => seedOffset (p*q) m (r+1)) (m-1)=
      duplicatePairs (p*q) m := by
    ext jk
    simp only [indexedEqualPairs,duplicatePairs,rowPairs,Finset.mem_filter,and_assoc]
  rw [hpairs] at hsurplus
  exact (original_square_divisor_natDegree_le_offset_surplus hp hm hmprime g hlong hA hdvd).trans
    hsurplus

end RiemannGaussian.SemiprimeOffsetCarryObstruction
