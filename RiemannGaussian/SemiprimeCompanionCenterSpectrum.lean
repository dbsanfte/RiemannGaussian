/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCompanionRows
import RiemannGaussian.SemiprimeEuclidRowBudget
import Mathlib.NumberTheory.LucasPrimality

/-!
# Exact public center spectrum before companion projection

Keep the actual primitive packet, both center choices and both signed
rounding errors. Same-center companions occupy a public interval, whereas
mixed centers retain an additional arithmetic direction. These identities
do not assume or prove universal useful-hit coverage.
-/

namespace RiemannGaussian.SemiprimeCompanionCenterSpectrum

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
open SemiprimeWeightedRows SemiprimeCompanionRows

/-- The first midpoint coordinate, with the public orientation retained. -/
def centerA (N : ℕ) (large : Bool) : ℤ :=
  if large then (N.sqrt : ℤ)+(2*N).sqrt else ((N/2).sqrt : ℤ)+N.sqrt

/-- The other midpoint coordinate uses the opposite public orientation. -/
def centerB (N : ℕ) (large : Bool) : ℤ := centerA N (!large)

/-- An actual packet shift has the stated public midpoint orientation. -/
def CenterChoice (N m : ℕ) (w : FamilyPacket) (large : Bool) : Prop :=
  w.shift=roundedShift m (centerNumerator m w.residue (centerA N large) (centerB N large) w.original)

/-- Signed error before any interval or modular projection. -/
def packetCenterError (N m : ℕ) (w : FamilyPacket) (large : Bool) : ℤ :=
  roundingError m (centerNumerator m w.residue (centerA N large) (centerB N large) w.original)

/-- Every literal residue-family packet has one of the four public choices. -/
theorem weightedResiduePacket_center_choices {N m j : ℕ} {w : WeightedPacket}
    (hw : w∈weightedResiduePackets N m j) :
    ∃ ls rs : Bool, CenterChoice N m w.left ls ∧ CenterChoice N m w.right rs := by
  unfold weightedResiduePackets at hw
  obtain ⟨⟨left,right⟩,_,hw⟩ := List.mem_flatMap.mp hw
  simp only [pairPackets,List.mem_cons,List.not_mem_nil,or_false] at hw
  have hsmall (z : QuotientRow) :
      CenterChoice N m ⟨j,z,publicShift N m j z.a z.b z.t⟩ false := by
    simpa only [CenterChoice,centerA,centerB,Bool.not_false,Bool.false_eq_true,
      if_false,if_true] using publicShift_midpoint N m j z
  have hlarge (z : QuotientRow) :
      CenterChoice N m ⟨j,z,reflectedShift N m j z.a z.b z.t⟩ true := by
    simpa only [CenterChoice,centerA,centerB,Bool.not_true,Bool.false_eq_true,
      if_false,if_true] using reflectedShift_midpoint N m j z
  rcases hw with rfl|rfl|rfl|rfl
  · exact ⟨false,false,hsmall left,hsmall right⟩
  · exact ⟨false,true,hsmall left,hlarge right⟩
  · exact ⟨true,false,hlarge left,hsmall right⟩
  · exact ⟨true,true,hlarge left,hlarge right⟩

/-- Public-family membership supplies the two orientations without advice. -/
theorem publicPacket_center_choices {N m : ℕ} {w : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) :
    ∃ ls rs : Bool, CenterChoice N m w.left ls ∧ CenterChoice N m w.right rs := by
  obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
  split_ifs at hw
  · exact weightedResiduePacket_center_choices hw
  · simp only [List.not_mem_nil] at hw

/-- Exact companion identity for two independently chosen midpoints.
The signed errors and center differences remain separate terms. -/
theorem centered_coefficient_spectrum (m j d A₁ B₁ A₂ B₂ : ℤ)
    (left right : QuotientRow) (hdet : rowDet left right=m*d) (hd : d^2=1) :
    2*m*coefficientCompanion j d
        (right.t*(left.b-m*roundedShift m (centerNumerator m j A₁ B₁ left))-
          left.t*(right.b-m*roundedShift m (centerNumerator m j A₂ B₂ right)))=
      m*A₁+d*(right.t*roundingError m (centerNumerator m j A₁ B₁ left)-
        left.t*roundingError m (centerNumerator m j A₂ B₂ right)-
        left.t*right.a*(A₂-A₁)-left.t*right.t*(B₂-B₁)) := by
  unfold coefficientCompanion roundingError centerNumerator
  unfold rowDet at hdet
  linear_combination (d*(A₁-4*j))*hdet+(m*(A₁-4*j))*hd

/-- The spectrum applies to the actual complete primitive public source. -/
theorem publicPacket_center_spectrum {N m : ℕ} {w : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) (hp : PrimitivePacket m w)
    {ls rs : Bool} (hl : CenterChoice N m w.left ls) (hr : CenterChoice N m w.right rs) :
    2*(m : ℤ)*packetCompanion m w=(m : ℤ)*centerA N ls+
      packetOrientation m w*(w.right.original.t*packetCenterError N m w.left ls-
        w.left.original.t*packetCenterError N m w.right rs-
        w.left.original.t*w.right.original.a*(centerA N rs-centerA N ls)-
        w.left.original.t*w.right.original.t*(centerB N rs-centerB N ls)) := by
  have hs : w.right.residue=w.left.residue := by
    obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
    split_ifs at hw with hj
    · have h := weightedResiduePacket_relations hp.1 hj hw
      exact h.2.1.trans h.1.symm
    · simp only [List.not_mem_nil] at hw
  have hd : (packetOrientation m w)^2=1 := by
    rcases primitivePacket_orientation hp with h|h <;> rw [h] <;> norm_num
  have hmD : (m : ℤ)∣rowDet w.left.original w.right.original := by
    rw [←dvd_abs,hp.2.1]
  have hdet : rowDet w.left.original w.right.original=(m : ℤ)*packetOrientation m w :=
    (Int.mul_ediv_cancel' hmD).symm
  rw [publicPacketCompanion_eq_coefficient hw hp]
  have h := centered_coefficient_spectrum (m : ℤ) w.left.residue (packetOrientation m w)
    (centerA N ls) (centerB N ls) (centerA N rs) (centerB N rs)
    w.left.original w.right.original hdet hd
  change w.left.shift=_ at hl
  change w.right.shift=_ at hr
  simpa only [packetLinearCoefficient,weightedRow,centeredPacketRow,shiftRow,
    packetCenterError,hl,hr,hs,mul_comm] using h

/-- Each retained public error has its original exact rounding envelope. -/
theorem packetCenterError_abs_le {N m : ℕ} (hm : 0<m) (w : FamilyPacket) (side : Bool) :
    |packetCenterError N m w side|≤(m : ℤ)^2 :=
  roundingError_abs_le (by exact_mod_cast hm)

/-- Both actual original denominators retain their positive public bounds. -/
theorem weightedResiduePacket_denominators {N m j : ℕ} (hm : 0<m) {w : WeightedPacket}
    (hw : w∈weightedResiduePackets N m j) :
    0≤w.left.original.t ∧ w.left.original.t≤m ∧
      0≤w.right.original.t ∧ w.right.original.t≤m := by
  unfold weightedResiduePackets at hw
  obtain ⟨⟨left,right⟩,hz,hw⟩ := List.mem_flatMap.mp hw
  have hrows := List.of_mem_zip hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hrows.1
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp (List.mem_of_mem_tail hrows.2)
  have hvb := publicPairs_denominator_le hm hv
  have hub := publicPairs_denominator_le hm hu
  simp only [pairPackets,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl
  all_goals
    change 0≤(v.2 : ℤ) ∧ (v.2 : ℤ)≤m ∧ 0≤(u.2 : ℤ) ∧ (u.2 : ℤ)≤m
    exact ⟨by positivity,by exact_mod_cast hvb,by positivity,by exact_mod_cast hub⟩

theorem publicPacket_denominators {N m : ℕ} (hm : 0<m) {w : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) :
    0≤w.left.original.t ∧ w.left.original.t≤m ∧
      0≤w.right.original.t ∧ w.right.original.t≤m := by
  obtain ⟨j,_,hw⟩ := List.mem_flatMap.mp hw
  split_ifs at hw
  · exact weightedResiduePacket_denominators hm hw
  · simp only [List.not_mem_nil] at hw

/-- Swapping the two public centers reverses the other midpoint difference. -/
theorem center_complement_difference (N : ℕ) (ls rs : Bool) :
    centerB N rs-centerB N ls=-(centerA N rs-centerA N ls) := by
  cases ls <;> cases rs <;> simp only [centerA,centerB,Bool.not_true,Bool.not_false,
    Bool.false_eq_true,if_false,if_true] <;> ring

/-- The mixed-center contribution is one retained arithmetic direction. -/
theorem publicPacket_center_spectrum_rankOne {N m : ℕ} {w : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) (hp : PrimitivePacket m w)
    {ls rs : Bool} (hl : CenterChoice N m w.left ls) (hr : CenterChoice N m w.right rs) :
    2*(m : ℤ)*packetCompanion m w=(m : ℤ)*centerA N ls+
      packetOrientation m w*(w.right.original.t*packetCenterError N m w.left ls-
        w.left.original.t*packetCenterError N m w.right rs-
        w.left.original.t*(w.right.original.a-w.right.original.t)*(centerA N rs-centerA N ls)) := by
  have h := publicPacket_center_spectrum hw hp hl hr
  rw [center_complement_difference] at h
  linear_combination h

/-- The signed error pair is bounded only after retaining its cancellation. -/
theorem publicPacket_weighted_error_bound {N m : ℕ} {w : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) (hm : 0<m) (ls rs : Bool) :
    |w.right.original.t*packetCenterError N m w.left ls-
      w.left.original.t*packetCenterError N m w.right rs|≤
        (m : ℤ)^2*(w.left.original.t+w.right.original.t) := by
  have ht := publicPacket_denominators hm hw
  have hl := packetCenterError_abs_le (N:=N) hm w.left ls
  have hr := packetCenterError_abs_le (N:=N) hm w.right rs
  calc
    _ ≤ |w.right.original.t*packetCenterError N m w.left ls|+
        |w.left.original.t*packetCenterError N m w.right rs| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le
        (w.right.original.t*packetCenterError N m w.left ls) 0
        (w.left.original.t*packetCenterError N m w.right rs)
    _ = w.right.original.t*|packetCenterError N m w.left ls|+
        w.left.original.t*|packetCenterError N m w.right rs| := by
      rw [abs_mul,abs_mul,abs_of_nonneg ht.1,abs_of_nonneg ht.2.2.1]
    _ ≤ w.right.original.t*(m : ℤ)^2+w.left.original.t*(m : ℤ)^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hl ht.2.2.1)
        (mul_le_mul_of_nonneg_left hr ht.1)
    _ = _ := by ring

/-- Equal center choices remove the mixed direction exactly; each actual
companion remains in a public interval whose doubled radius is at most 2m². -/
theorem publicPacket_same_center_interval {N m : ℕ} {w : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) (hp : PrimitivePacket m w)
    (side : Bool) (hl : CenterChoice N m w.left side) (hr : CenterChoice N m w.right side) :
    |2*packetCompanion m w-centerA N side|≤
      (m : ℤ)*(w.left.original.t+w.right.original.t) ∧
    |2*packetCompanion m w-centerA N side|≤2*(m : ℤ)^2 := by
  have hm : (0 : ℤ)<m := by exact_mod_cast hp.1
  have he : (m : ℤ)*(2*packetCompanion m w-centerA N side)=
      packetOrientation m w*(w.right.original.t*packetCenterError N m w.left side-
        w.left.original.t*packetCenterError N m w.right side) := by
    have h := publicPacket_center_spectrum_rankOne hw hp hl hr
    simp only [sub_self,mul_zero,sub_zero] at h
    linear_combination h
  have hd : |packetOrientation m w|=1 := by
    rcases primitivePacket_orientation hp with h|h <;> rw [h] <;> norm_num
  have habs := congrArg abs he
  rw [abs_mul,abs_mul,abs_of_pos hm,hd,one_mul] at habs
  have herror := publicPacket_weighted_error_bound hw hp.1 side side
  have hsum := publicPacket_denominators hp.1 hw
  have hbound : |2*packetCompanion m w-centerA N side|≤
      (m : ℤ)*(w.left.original.t+w.right.original.t) := by
    nlinarith only [habs,herror,hm]
  exact ⟨hbound,hbound.trans (by nlinarith only [hm,hsum.2.1,hsum.2.2.2])⟩

/-- Two same-center companions differ by at most 2m² before modular reduction. -/
theorem publicPacket_same_center_difference {N m : ℕ} {w v : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) (hv : v∈publicWeightedPackets N m)
    (hpw : PrimitivePacket m w) (hpv : PrimitivePacket m v) (side : Bool)
    (hwl : CenterChoice N m w.left side) (hwr : CenterChoice N m w.right side)
    (hvl : CenterChoice N m v.left side) (hvr : CenterChoice N m v.right side) :
    |packetCompanion m w-packetCompanion m v|≤2*(m : ℤ)^2 := by
  have hwc := (publicPacket_same_center_interval hw hpw side hwl hwr).2
  have hvc := (publicPacket_same_center_interval hv hpv side hvl hvr).2
  have h := abs_sub_le (2*packetCompanion m w-centerA N side) 0
    (2*packetCompanion m v-centerA N side)
  simp only [sub_zero,zero_sub,abs_neg] at h
  have he : 2*|packetCompanion m w-packetCompanion m v|=
      |(2*packetCompanion m w-centerA N side)-(2*packetCompanion m v-centerA N side)| := by
    rw [←abs_of_nonneg (by decide : (0 : ℤ)≤2),←abs_mul]
    congr 1
    ring
  nlinarith only [hwc,hvc,h,he]

/-- Above the interval width, local equality of same-center companions is
already literal integer equality. Thus this channel creates no distinct
local difference collision in any modulus greater than 2m². -/
theorem publicPacket_same_center_modular_injective {N m p : ℕ} {w v : WeightedPacket}
    (hw : w∈publicWeightedPackets N m) (hv : v∈publicWeightedPackets N m)
    (hpw : PrimitivePacket m w) (hpv : PrimitivePacket m v) (side : Bool)
    (hwl : CenterChoice N m w.left side) (hwr : CenterChoice N m w.right side)
    (hvl : CenterChoice N m v.left side) (hvr : CenterChoice N m v.right side)
    (hlarge : 2*(m : ℤ)^2<p)
    (he : (packetCompanion m w : ZMod p)=(packetCompanion m v : ZMod p)) :
    packetCompanion m w=packetCompanion m v := by
  have hbound := publicPacket_same_center_difference hv hw hpv hpw side hvl hvr hwl hwr
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mp he
  have hsmall : (packetCompanion m v-packetCompanion m w).natAbs<p := by
    have h := hbound.trans_lt hlarge
    rw [←Int.natCast_natAbs] at h
    exact_mod_cast h
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    (by simpa only [Int.natAbs_natCast] using hsmall)
  exact (sub_eq_zero.mp hz).symm

/-- Lucas certificate for the only large predecessor prime in the control. -/
theorem frontier_predecessor_prime : Nat.Prime 54018370951 := by
  apply lucas_primality 54018370951 (17 : ZMod 54018370951)
  · reduce_mod_char
  · intro q hq hd
    have he : (54018370951 : ℕ)-1=2*3*5*5*15359*23447 := by norm_num
    rw [he] at hd
    simp only [Nat.Prime.dvd_mul hq,
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 15359),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23447),or_assoc] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> reduce_mod_char <;> decide

/-- Kernel-checked primality of the smaller factor in the native frontier miss. -/
theorem frontier_p_prime : Nat.Prime 2245327606949267 := by
  apply lucas_primality 2245327606949267 (2 : ZMod 2245327606949267)
  · reduce_mod_char
  · intro q hq hd
    have he : (2245327606949267 : ℕ)-1=2*7*2969*54018370951 := by norm_num
    rw [he] at hd
    simp only [Nat.Prime.dvd_mul hq,
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2969),
      Nat.prime_dvd_prime_iff_eq hq frontier_predecessor_prime,or_assoc] at hd
    rcases hd with rfl|rfl|rfl|rfl <;> reduce_mod_char <;> decide

/-- Kernel-checked primality of the larger factor in the native frontier miss. -/
theorem frontier_q_prime : Nat.Prime 3027647967431443 := by
  apply lucas_primality 3027647967431443 (3 : ZMod 3027647967431443)
  · reduce_mod_char
  · intro q hq hd
    have he : (3027647967431443 : ℕ)-1=2*3*463*577*153953*12269 := by norm_num
    rw [he] at hd
    simp only [Nat.Prime.dvd_mul hq,
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 463),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 577),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 153953),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 12269),or_assoc] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> reduce_mod_char <;> decide

/-- Arithmetic scope of the miss input is certified separately from its
native full-root injection test, which is not a kernel exhaustion proof. -/
theorem frontier_control_arithmetic :
    Nat.Prime 2245327606949267 ∧ Nat.Prime 3027647967431443 ∧ Nat.Prime 137639 ∧
      2245327606949267*3027647967431443=6798061565397654183415201602281 ∧
      2245327606949267<3027647967431443 ∧ 3027647967431443≤2*2245327606949267 ∧
      2*(137639 : ℕ)^2<2245327606949267 ∧
      (137635 : ℕ)^6<6798061565397654183415201602281 ∧
      6798061565397654183415201602281≤(137636 : ℕ)^6 ∧
      ¬Nat.Prime 137636 ∧ ¬Nat.Prime 137637 ∧ ¬Nat.Prime 137638 := by
  refine ⟨frontier_p_prime,frontier_q_prime,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> norm_num

/-- The native miss uses the literal N-only ceiling sixth root. -/
theorem frontier_control_sixthWidth :
    SemiprimeLehmanCoverage.sixthWidth 6798061565397654183415201602281=137636 := by
  unfold SemiprimeLehmanCoverage.sixthWidth
  apply (Nat.find_eq_iff _).mpr
  constructor
  · norm_num
  · intro k hk hkn
    have hle : k≤137635 := by omega
    have hp := Nat.pow_le_pow_left hle 6
    have hl : (137635 : ℕ)^6<6798061565397654183415201602281 := by norm_num
    omega

/-- The actual least public prime selector equals the audited modulus.
No field factors enter this selector or its evaluation. -/
theorem frontier_control_public_modulus :
    SemiprimeEuclidRowBudget.publicRowModulus 6798061565397654183415201602281=137639 := by
  simp only [SemiprimeEuclidRowBudget.publicRowModulus,frontier_control_sixthWidth,
    show max 1 137636=137636 by decide]
  have hB : (0 : ℕ)<137636 := by norm_num
  have hp := SemiprimeEuclidRowBudget.publicPrimeAtLeast_prime 137636 hB
  have hlo := SemiprimeEuclidRowBudget.publicPrimeAtLeast_ge 137636 hB
  have hhi := SemiprimeEuclidRowBudget.publicPrimeAtLeast_minimal 137636 hB
    (by norm_num : Nat.Prime 137639) (by norm_num : 137636≤137639)
  have hcases : SemiprimeEuclidRowBudget.publicPrimeAtLeast 137636 hB=137636 ∨
      SemiprimeEuclidRowBudget.publicPrimeAtLeast 137636 hB=137637 ∨
      SemiprimeEuclidRowBudget.publicPrimeAtLeast 137636 hB=137638 ∨
      SemiprimeEuclidRowBudget.publicPrimeAtLeast 137636 hB=137639 := by omega
  rcases hcases with h|h|h|h
  · rw [h] at hp; norm_num at hp
  · rw [h] at hp; norm_num at hp
  · rw [h] at hp; norm_num at hp
  · exact h

/-- The public modulus GCD prefix does not recover this input. -/
theorem frontier_control_modulus_coprime :
    Nat.Coprime 137639 6798061565397654183415201602281 := by norm_num [Nat.Coprime]

end RiemannGaussian.SemiprimeCompanionCenterSpectrum
