import RiemannGaussian.SemiprimeMaskAcquisitionObstruction

/-!
# Original partner-template obstruction and same-tag recovery

The exact original lower offset and public partner involution give a
monic quartic. Every product-template fiber has at most four tags once
the actual integer offset sum lifts below the supplied local order.
Consequently complete-input and hidden-field advice do not organize
the original partners into a sublinear catalog of reciprocal centers.
This does not lower-bound arbitrary implicit scalar evaluation.

When the factor tags coincide, the literal original representative is
one. Balanced gates then give an exact factor-sum index below 4m.
An executable public fixedpoint scan is sound, complete on that branch,
and has at most 8m candidate trials. Every partner-orbit cover is
saturated on that branch. Distinct formal tags leave every sum carry
attainable from a fixed two-digit product state.

The journal supplies a fresh actual infinite same-tag family, a classical
unbalanced progression-product recovery, and an all-phase honest Gauss
double-puncture counterfamily. Analytic density, cyclotomic norm
construction, full bit costs and the general one-sixth coverage theorem
are not supplied as native axioms or claimed by this finite leaf.
-/

namespace RiemannGaussian.SemiprimePartnerAcquisitionObstruction

open Polynomial
open SemiprimeMaskAcquisitionObstruction SemiprimeGlobalPhaseCancellation
open SemiprimeDenseRowCarries SemiprimeSeedEnergyAcquisitionObstruction

/-- The exact original offset after projection to the public row field. -/
def lowerPhase {K : Type*} [Field K] (s j : K) : K :=
  s*(j⁻¹)^2-2*s*j⁻¹

/-- The monic quartic controlling affine phase relations between partners. -/
noncomputable def partnerPolynomial {K : Type*} [CommRing K] (s e D : K) : K[X] :=
  X^4-C (2*s)*X^3-C (D*s)*X^2+C (2*e*s^2)*X-C (e*s^2)

theorem partnerPolynomial_coeff_four {K : Type*} [CommRing K] (s e D : K) :
    (partnerPolynomial s e D).coeff 4=1 := by
  simp only [partnerPolynomial,coeff_sub,coeff_add,coeff_C_mul,coeff_X_pow,
    coeff_X,coeff_C]
  norm_num

theorem partnerPolynomial_ne_zero {K : Type*} [CommRing K] [Nontrivial K]
    (s e D : K) : partnerPolynomial s e D ≠ 0 := by
  intro he
  have hc := congrArg (fun P : K[X] => P.coeff 4) he
  rw [partnerPolynomial_coeff_four,coeff_zero] at hc
  exact one_ne_zero hc

theorem partnerPolynomial_degree_le {K : Type*} [CommRing K] (s e D : K) :
    (partnerPolynomial s e D).natDegree ≤ 4 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp only [partnerPolynomial,coeff_sub,coeff_add,coeff_C_mul,coeff_X_pow,
    coeff_X,coeff_C]
  split_ifs <;> first | omega | ring

theorem partnerPhase_quartic_root {K : Type*} [Field K] (s e D j : K)
    (hs : s ≠ 0) (hj : j ≠ 0)
    (hphase : lowerPhase s (rowPartner s j)-e*lowerPhase s j=D) :
    (partnerPolynomial s e D).eval j=0 := by
  simp only [lowerPhase,rowPartner] at hphase
  simp only [partnerPolynomial,eval_sub,eval_add,eval_mul,eval_pow,eval_X,eval_C]
  field_simp at hphase
  linear_combination hphase

theorem partnerPhase_fiber_card_le_four {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (s e D : K) (hs : s ≠ 0) :
    (Finset.univ.filter fun j : K => j ≠ 0 ∧
      lowerPhase s (rowPartner s j)-e*lowerPhase s j=D).card ≤ 4 := by
  classical
  let T := Finset.univ.filter fun j : K => j ≠ 0 ∧
    lowerPhase s (rowPartner s j)-e*lowerPhase s j=D
  have hsub : T ⊆ (partnerPolynomial s e D).roots.toFinset := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots (partnerPolynomial_ne_zero s e D)).mpr
    exact partnerPhase_quartic_root s e D j hs h.1 h.2
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (partnerPolynomial_degree_le s e D)))

/-- The rational lower phase is exactly the literal original integer
offset projected to the public row field. -/
theorem original_offset_lowerPhase {N m j : ℕ} [Fact m.Prime]
    (hj : 1 ≤ j) (hjm : j < m) :
    (seedOffset N m j : ZMod m)=lowerPhase (N : ZMod m) (j : ZMod m) := by
  have hm : m.Prime := Fact.out
  have hcop : j.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hj0 : (j : ZMod m) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff j m).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) hjm)
  have hs := offset_square_residue (N:=N) hm.pos hcop
  apply (mul_right_cancel₀ (pow_ne_zero 2 hj0))
  rw [hs]
  simp only [lowerPhase]
  field_simp

/-- The finite quartic count applies to the actual original offsets and
the canonical complementary tags, with no carry equidistribution premise. -/
theorem original_partner_phase_fiber_card_le_four {N m : ℕ} [Fact m.Prime]
    (hN : m.Coprime N) (e D : ZMod m) :
    ((Finset.univ.erase 0).filter fun j : ZMod m =>
      (seedOffset N m (rowPartner (N : ZMod m) j).val : ZMod m)-
        e*(seedOffset N m j.val : ZMod m)=D).card ≤ 4 := by
  classical
  have hm : m.Prime := Fact.out
  have hs : (N : ZMod m) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff N m).not.mpr (hm.coprime_iff_not_dvd.mp hN)
  have hsub : ((Finset.univ.erase 0).filter fun j : ZMod m =>
      (seedOffset N m (rowPartner (N : ZMod m) j).val : ZMod m)-
        e*(seedOffset N m j.val : ZMod m)=D) ⊆
      (Finset.univ.filter fun j : ZMod m => j ≠ 0 ∧
        lowerPhase (N : ZMod m) (rowPartner (N : ZMod m) j)-
          e*lowerPhase (N : ZMod m) j=D) := by
    intro j hj
    have hj0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
    have hk0 := rowPartner_ne_zero hs hj0
    have hphase := (Finset.mem_filter.mp hj).2
    rw [original_offset_lowerPhase (by exact ZMod.val_pos.mpr hk0) (ZMod.val_lt _),
      original_offset_lowerPhase (by exact ZMod.val_pos.mpr hj0) (ZMod.val_lt _)] at hphase
    simp only [ZMod.natCast_zmod_val] at hphase
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj0,hphase⟩
  exact (Finset.card_le_card hsub).trans (partnerPhase_fiber_card_le_four (N : ZMod m) e D hs)

/-- The product of the two ACTUAL original source targets in a public
complementary-tag orbit. -/
def partnerTargetProduct {G : Type*} [CommGroup G] (g : G) (N m : ℕ)
    (j : ZMod m) : G :=
  (progressionSeed g N m j.val).step *
    (progressionSeed g N m (rowPartner (N : ZMod m) j).val).step

/-- Even a completely advised reciprocal center can match at most four
original partner tags once the original integer sums lift below the
actual local order. This is pointwise, not an asymptotic count. -/
theorem original_partner_product_fiber_card_le_four
    {G : Type*} [CommGroup G] [DecidableEq G] {N m : ℕ} [Fact m.Prime]
    (g : G) (hN : m.Coprime N) (horder : 8*m^2 < orderOf g) (C : G) :
    ((Finset.univ.erase 0).filter fun j : ZMod m =>
      partnerTargetProduct g N m j=C).card ≤ 4 := by
  classical
  let T := (Finset.univ.erase 0).filter fun j : ZMod m =>
    partnerTargetProduct g N m j=C
  have hm : m.Prime := Fact.out
  have hs : (N : ZMod m) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff N m).not.mpr (hm.coprime_iff_not_dvd.mp hN)
  by_cases hT : T.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hT
    let D : ℤ := seedOffset N m j₀.val+
      seedOffset N m (rowPartner (N : ZMod m) j₀).val
    have hsub : T ⊆ ((Finset.univ.erase 0).filter fun j : ZMod m =>
        (seedOffset N m (rowPartner (N : ZMod m) j).val : ZMod m)-
          (-1)*(seedOffset N m j.val : ZMod m)=(D : ZMod m)) := by
      intro j hj
      have hjne := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
      have hj₀ne := (Finset.mem_erase.mp (Finset.mem_filter.mp hj₀).1).1
      have hkne := rowPartner_ne_zero hs hjne
      have hk₀ne := rowPartner_ne_zero hs hj₀ne
      have he : partnerTargetProduct g N m j=partnerTargetProduct g N m j₀ :=
        (Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hj₀).2.symm
      have hsum := (original_pair_product_eq_iff_offset_sum g hm
        (ZMod.val_pos.mpr hjne) (ZMod.val_lt _)
        (ZMod.val_pos.mpr hkne) (ZMod.val_lt _)
        (ZMod.val_pos.mpr hj₀ne) (ZMod.val_lt _)
        (ZMod.val_pos.mpr hk₀ne) (ZMod.val_lt _) horder).mp he
      apply Finset.mem_filter.mpr
      refine ⟨(Finset.mem_filter.mp hj).1,?_⟩
      have hcast := congrArg (fun z : ℤ => (z : ZMod m)) hsum
      simp only [Int.cast_add] at hcast
      dsimp only [D]
      push_cast
      linear_combination hcast
    exact (Finset.card_le_card hsub).trans
      (original_partner_phase_fiber_card_le_four hN (-1) (D : ZMod m))
  · have hz : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    change T.card ≤ 4
    rw [hz,Finset.card_empty]
    omega

/-- The actual reciprocal centers already have linear cardinality before
any chosen compressed representation or query algorithm is considered. -/
theorem original_partner_product_centers_card_bound
    {G : Type*} [CommGroup G] [DecidableEq G] {N m : ℕ} [Fact m.Prime]
    (g : G) (hN : m.Coprime N) (horder : 8*m^2 < orderOf g) :
    m-1 ≤ 4*((Finset.univ.erase 0).image (partnerTargetProduct g N m)).card := by
  classical
  have h := card_le_fiber_bound_mul_image (Finset.univ.erase (0 : ZMod m))
    (partnerTargetProduct g N m) 4
    (fun C _ => original_partner_product_fiber_card_le_four g hN horder C)
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod m)),
    Finset.card_univ,ZMod.card] using h

open Polynomial
open SemiprimeMaskAcquisitionObstruction SemiprimeGlobalPhaseCancellation
open SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open SemiprimeBalancedAcquisitionObstruction SemiprimeSeedSumAcquisition
open SemiprimePhaseSumRecovery SemiprimeGroupSelection

/-- The literal original row has slope exactly one when both factor tags
coincide. This recovers the integer representative, not just its residue. -/
theorem same_tag_representative_one {p q m : ℕ} (hm : m.Prime)
    (hN : m.Coprime (p*q)) (hsame : p%m=q%m) :
    representative (p*q) m (p%m) 1=1 := by
  let : Fact m.Prime := ⟨hm⟩
  have hcop : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hj0 : (p : ZMod m) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff p m).not.mpr
      (hm.coprime_iff_not_dvd.mp (hN.of_dvd_right (dvd_mul_right p q)))
  have hpq : (p : ZMod m)=(q : ZMod m) := by
    simpa only [ZMod.natCast_mod] using congrArg (fun n : ℕ => (n : ZMod m)) hsame
  have hr := slope_square_residue (N:=p*q) hm.pos hcop
  simp only [ZMod.natCast_mod,Nat.cast_mul] at hr
  have ha : (representative (p*q) m (p%m) 1 : ZMod m)=1 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hj0)
    rw [hr,hpq,pow_two,one_mul]
  have hav := congrArg ZMod.val ha
  have ham : representative (p*q) m (p%m) 1 < m :=
    Nat.mod_lt _ hm.pos
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt ham,ZMod.val_one] using hav

/-- Same tags reduce the exact original forced index to an unweighted
factor sum, and the balanced upper gates bound it by a linear scan. -/
theorem same_tag_balanced_sum_index {p q m : ℕ} (hp : 0<p) (hm : 4≤m)
    (hmprime : m.Prime) (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3)
    (hN : m.Coprime (p*q)) (hsame : p%m=q%m) :
    ∃ r : ℕ, r<4*m ∧
      ((p : ℤ)+q)=(m : ℤ)^2*r+1-seedOffset (p*q) m (p%m) := by
  have ha := same_tag_representative_one hmprime hN hsame
  obtain ⟨r,_,_,he⟩ := balanced_forced_seed_arithmetic hp hm hprefixp hprefixq
    hpupper hqupper hN
  rw [ha] at he
  have hsum : ((p : ℤ)+q)=(m : ℤ)^2*r+1-seedOffset (p*q) m (p%m) := by
    push_cast at he
    nlinarith only [he]
  have hb := abs_le.mp (denseRow_b_bound (N:=p*q) (m:=m) (j:=p%m) (t:=1) (by omega) false)
  change -(m : ℤ) ≤ (seedRow (p*q) m (p%m)).b ∧
    (seedRow (p*q) m (p%m)).b ≤ m at hb
  have hupperp : 2*(p : ℤ)≤3*(m : ℤ)^3 := by exact_mod_cast hpupper
  have hupperq : 2*(q : ℤ)≤3*(m : ℤ)^3 := by exact_mod_cast hqupper
  have hindex : (m : ℤ)^2*r=(p : ℤ)+q+
      (m : ℤ)*(seedRow (p*q) m (p%m)).b-2*(p%m : ℕ) := by
    unfold seedOffset at hsum
    rw [ha] at hsum
    simp only [Nat.cast_one,mul_one] at hsum
    linarith only [hsum]
  have hmsq : (0 : ℤ)<(m : ℤ)^2 := by positivity
  have hbound : (r : ℤ)≤3*(m : ℤ)+1 := by
    have hmb := mul_le_mul_of_nonneg_left hb.2 (by positivity : (0 : ℤ)≤m)
    have hmul : (m : ℤ)^2*r≤(m : ℤ)^2*(3*(m : ℤ)+1) := by
      nlinarith only [hindex,hmb,hupperp,hupperq,
        show (0 : ℤ)≤(p%m : ℕ) by positivity]
    exact le_of_mul_le_mul_left hmul hmsq
  refine ⟨r,?_,hsum⟩
  have hboundn : r≤3*m+1 := by exact_mod_cast hbound
  omega

/-- Candidate checks use the exact original row offset. -/
def sameTagProbe (N m j r : ℕ) : Option ℕ :=
  checkedSignal N (factorSumCandidate N ((m : ℤ)^2*r+1-seedOffset N m j))

/-- Public fixedpoint tags, stored as the original tag minus one. -/
def fixedPointRows (N m : ℕ) : List ℕ :=
  (List.range (m-1)).filter fun j => (j+1)^2%m=N%m

/-- Original fixedpoint tags paired with every index below the linear bound. -/
def sameTagMenu (N m : ℕ) : List (ℕ × ℕ) :=
  (fixedPointRows N m).flatMap fun j => (List.range (4*m)).map fun r => (j+1,r)

/-- Search the public menu and return only independently checked divisors. -/
def recoverSameTagSum (N m : ℕ) : Option Selection :=
  search (sameTagProbe N m) (sameTagMenu N m)

/-- The scanner retains at most the two public fixedpoint rows; the
bound concerns the literal finite list that drives its candidate menu. -/
theorem fixedPointRows_length_le_two (N : ℕ) {m : ℕ} (hm : m.Prime) :
    (fixedPointRows N m).length ≤ 2 := by
  classical
  let : Fact m.Prime := ⟨hm⟩
  let P : (ZMod m)[X] := X^2-C (N : ZMod m)
  have hP : P≠0 := X_pow_sub_C_ne_zero (by decide : 0<2) (N : ZMod m)
  have hnodup : (fixedPointRows N m).Nodup := (List.nodup_range).filter _
  rw [←List.toFinset_card_of_nodup hnodup]
  have hmaps : Set.MapsTo (fun r : ℕ => ((r+1 : ℕ) : ZMod m))
      ((fixedPointRows N m).toFinset : Set ℕ) P.roots.toFinset := by
    intro r hr
    have h := List.mem_filter.mp (List.mem_toFinset.mp hr)
    have he : ((r+1 : ℕ) : ZMod m)^2=(N : ZMod m) := by
      have hcast := congrArg (fun n : ℕ => (n : ZMod m)) (of_decide_eq_true h.2)
      simpa only [ZMod.natCast_mod,Nat.cast_pow] using hcast
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hP).mpr
    change P.eval ((r+1 : ℕ) : ZMod m)=0
    simp only [P,eval_sub,eval_pow,eval_X,eval_C,he,sub_self]
  have hinj : Set.InjOn (fun r : ℕ => ((r+1 : ℕ) : ZMod m))
      ((fixedPointRows N m).toFinset : Set ℕ) := by
    intro r hr t ht he
    have hrm : r+1<m := by
      have h := List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hr)).1
      omega
    have htm : t+1<m := by
      have h := List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp ht)).1
      omega
    have hv := congrArg ZMod.val he
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hrm,Nat.mod_eq_of_lt htm] at hv
    omega
  exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans
    ((Multiset.toFinset_card_le P.roots).trans
      (Polynomial.card_roots_X_pow_sub_C (by decide : 0<2) (N : ZMod m)))

theorem sameTagMenu_length_le_linear (N : ℕ) {m : ℕ} (hm : m.Prime) :
    (sameTagMenu N m).length ≤ 8*m := by
  have hlength : (sameTagMenu N m).length=(fixedPointRows N m).length*(4*m) := by
    simp only [sameTagMenu,List.length_flatMap,List.length_map,List.length_range]
    simp
  rw [hlength]
  have h := fixedPointRows_length_le_two N hm
  nlinarith only [Nat.mul_le_mul_right (4*m) h]

theorem recoverSameTagSum_sound {N m : ℕ} {result : Selection}
    (h : recoverSameTagSum N m=some result) : ProperDivisor N result.factor :=
  search_sound (sameTagProbe N m) (fun _ _ _ he => checkedSignal_sound he) h

theorem recoverSameTagSum_complete {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q) (hm : 4≤m) (hmprime : m.Prime)
    (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3)
    (hN : m.Coprime (p*q)) (hsame : p%m=q%m) :
    ∃ result, recoverSameTagSum (p*q) m=some result := by
  obtain ⟨r,hr,hsum⟩ := same_tag_balanced_sum_index hp.pos hm hmprime
    hprefixp hprefixq hpupper hqupper hN hsame
  have hjpos : 0<p%m := by
    have hjcop : (p%m).Coprime m := by
      change Nat.gcd (p%m) m=1
      rw [←Nat.gcd_rec]
      exact hN.of_dvd_right (dvd_mul_right p q)
    by_contra! hn
    have hz : p%m=0 := by omega
    simp only [hz,Nat.coprime_zero_left] at hjcop
    omega
  have hjm : p%m<m := Nat.mod_lt p (by omega)
  have htag : p%m-1 ∈ fixedPointRows (p*q) m := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (by omega),?_⟩
    rw [show p%m-1+1=p%m by omega]
    simp [pow_two,Nat.mul_mod,hsame]
  have hmenu : (p%m,r) ∈ sameTagMenu (p*q) m := by
    apply List.mem_flatMap.mpr
    refine ⟨p%m-1,htag,?_⟩
    apply List.mem_map.mpr
    refine ⟨r,List.mem_range.mpr hr,?_⟩
    simp only [show p%m-1+1=p%m by omega]
  have hprobe : sameTagProbe (p*q) m (p%m) r=some p := by
    unfold sameTagProbe
    rw [←hsum,factorSumCandidate_exact hpq.le,checkedSignal,
      Nat.gcd_eq_right (dvd_mul_right p q),ite_eq_left]
    exact ⟨hp.one_lt,by nlinarith only [hp.pos,hq.one_lt]⟩
  exact search_succeeds_of_menu_hit (sameTagProbe (p*q) m) hmenu hprobe

/-- Expanding the actual two factor lifts and cancelling one public
modulus gives exactly the stated two-digit carry equation. -/
theorem product_two_digit_carry_iff {m : ℕ} (hm : 0<m) (j k u v C : ℤ) :
    (j+(m : ℤ)*u)*(k+(m : ℤ)*v) ≡ j*k+(m : ℤ)*C [ZMOD (m : ℤ)^2] ↔
      j*v+k*u ≡ C [ZMOD (m : ℤ)] := by
  have hmz : (m : ℤ)≠0 := by exact_mod_cast hm.ne'
  have hex : (j+(m : ℤ)*u)*(k+(m : ℤ)*v) ≡
      j*k+(m : ℤ)*(j*v+k*u) [ZMOD (m : ℤ)^2] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(u*v),?_⟩
    ring
  constructor
  · intro hstate
    have hc := Int.ModEq.add_left_cancel' (j*k) (hex.symm.trans hstate)
    have hc' : (m : ℤ)*(j*v+k*u) ≡ (m : ℤ)*C [ZMOD (m : ℤ)*(m : ℤ)] := by
      simpa only [pow_two] using hc
    exact Int.ModEq.mul_left_cancel' hmz hc'
  · intro hc
    have hc' : (m : ℤ)*(j*v+k*u) ≡ (m : ℤ)*C [ZMOD (m : ℤ)*(m : ℤ)] := hc.mul_left'
    have hstate : j*k+(m : ℤ)*(j*v+k*u) ≡ j*k+(m : ℤ)*C [ZMOD (m : ℤ)^2] := by
      simpa only [pow_two] using hc'.add_left (j*k)
    exact hex.trans hstate

/-- Equal factor tags fix their sum carry from the two-digit product state. -/
theorem equal_tag_carry_sum {K : Type*} [Field K] (j C u v : K) (hj : j≠0)
    (hstate : j*v+j*u=C) : u+v=C/j := by
  apply (eq_div_iff hj).mpr
  linear_combination hstate

/-- Distinct paired tags leave every sum carry attainable, with exactly
one pair of formal carries for each requested sum. -/
theorem distinct_tag_carries_all_sums {K : Type*} [Field K]
    (j k C w : K) (hjk : j≠k) :
    ∃! uv : K × K, j*uv.2+k*uv.1=C ∧ uv.1+uv.2=w := by
  have hkj : k-j≠0 := sub_ne_zero.mpr hjk.symm
  let u := (C-j*w)/(k-j)
  have hu : (k-j)*u=C-j*w := by
    dsimp only [u]
    field_simp
  refine ⟨(u,w-u),⟨?_,by ring⟩,?_⟩
  · change j*(w-u)+k*u=C
    linear_combination hu
  · intro uv huv
    have hu' : (k-j)*uv.1=C-j*w := by
      linear_combination huv.1-j*huv.2
    have hueq : uv.1=u := mul_left_cancel₀ hkj (hu'.trans hu.symm)
    apply Prod.ext hueq
    dsimp only
    linear_combination huv.2-hueq

open SemiprimeIntervalJet

/-- Every public partner-orbit cover is saturated when the two hidden
factor tags coincide, including all false hits in its original rows. -/
theorem balanced_same_tag_cover_norm_zero {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime)
    (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3)
    (hN : m.Coprime (p*q)) (hsame : p%m=q%m) (g : (ZMod (p*q))ˣ)
    (S : Finset (ZMod m))
    (hcover : ∀ j : ZMod m, j ≠ 0 →
      j ∈ S ∨ rowPartner (p*q : ZMod m) j ∈ S) :
    rowMaskNorm g m S=0 := by
  let : Fact m.Prime := ⟨hmprime⟩
  have hp0 : (p : ZMod m) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff p m).not.mpr
      (hmprime.coprime_iff_not_dvd.mp (hN.of_dvd_right (dvd_mul_right p q)))
  have htags := orbit_cover_pair S hp0 (show (p : ZMod m)*(q : ZMod m)=p*q by rfl) hcover
  have he : (p : ZMod m)=(q : ZMod m) := by
    simpa only [ZMod.natCast_mod] using congrArg (fun n : ℕ => (n : ZMod m)) hsame
  have htagp : (p : ZMod m) ∈ S := by
    obtain h | h := htags
    · exact h
    · rwa [he]
  have htagq : (q : ZMod m) ∈ S := he ▸ htagp
  apply zero_of_prime_reductions hp hq hpq
  · exact retained_factor_row_norm_zero hp hm hprefixp hprefixq hpupper hqupper
      rfl hN g S htagp (dvd_mul_right p q)
  · exact retained_factor_row_norm_zero hq hm hprefixq hprefixp hqupper hpupper
      (Nat.mul_comm p q) hN g S htagq (dvd_mul_left q p)

/-- Saturation is an exact scalar-gcd statement, rather than just
failure to prove that the mask norm is a unit. -/
theorem balanced_same_tag_cover_gcd_modulus {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime)
    (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3)
    (hN : m.Coprime (p*q)) (hsame : p%m=q%m) (g : (ZMod (p*q))ˣ)
    (S : Finset (ZMod m))
    (hcover : ∀ j : ZMod m, j ≠ 0 →
      j ∈ S ∨ rowPartner (p*q : ZMod m) j ∈ S) :
    (p*q).gcd (rowMaskNorm g m S).val=p*q := by
  rw [balanced_same_tag_cover_norm_zero hp hq hpq hm hmprime hprefixp hprefixq
    hpupper hqupper hN hsame g S hcover]
  simp only [ZMod.val_zero,Nat.gcd_zero_right]

end RiemannGaussian.SemiprimePartnerAcquisitionObstruction
