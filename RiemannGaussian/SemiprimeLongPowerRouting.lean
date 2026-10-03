/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeKernelDescent
import RiemannGaussian.SemiprimeLongPeriodExtraction

/-!
# Public power refinement and exact long-order decoding

Retain the two long coprime local periods. A known global order would
determine the literal factor sum, but is not supplied to the public
refinement. Two additional short batches use the public N and N+1 powers.
Their failed outcomes preserve the original long carrier and certify
additional coprimality. The final linear-source extractor and complete
one-sixth bit bound remain open.
-/

namespace RiemannGaussian.SemiprimeLongPowerRouting

open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeCentreFreeCover

/-- Retain the original long-period, coprime and rough local information. -/
def CoreData (p q B : ℕ) (h : (ZMod (p*q))ˣ) : Prop :=
  LocalLong h (2*B) ∧
    (orderOf (leftUnit h)).Coprime (orderOf (rightUnit h)) ∧
    (∀ r, r.Prime → r∣orderOf (leftUnit h) → B<r) ∧
    (∀ r, r.Prime → r∣orderOf (rightUnit h) → B<r)

/-- The actual public projected unit supplies the complete retained core. -/
theorem projected_core {p q B : ℕ} (g : (ZMod (p*q))ˣ) (hd : LongData g B) :
    CoreData p q B (SemiprimeCentreFreeCover.projectedUnit g B) :=
  ⟨hd.2.2.2.1,hd.2.2.2.2⟩

/-- The retained projected unit has the literal public scalar value;
this view keeps the original unit available for later channels. -/
theorem projectedUnit_val {N : ℕ} (g : (ZMod N)ˣ) (B : ℕ) :
    (projectedUnit g B : ZMod N)=
      ((g : ZMod N)^(N-1))^((B.factorial)^(Nat.clog 2 (N+1))) := by
  simp only [projectedUnit,Units.val_pow_eq_pow_val]

/-- Prime-field orders divide their literal group cardinalities. -/
theorem local_card_divisors {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : (ZMod (p*q))ˣ) :
    orderOf (leftUnit h)∣p-1 ∧ orderOf (rightUnit h)∣q-1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  exact ⟨ZMod.orderOf_units_dvd_card_sub_one _,ZMod.orderOf_units_dvd_card_sub_one _⟩

/-- Long local periods give public lower bounds for both prime factors. -/
theorem local_card_bounds {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : (ZMod (p*q))ˣ) (hl : LocalLong h (2*B)) :
    (2*B)^2<p-1 ∧ (2*B)^2<q-1 := by
  have hd := local_card_divisors hp hq h
  exact ⟨hl.1.trans_le (Nat.le_of_dvd (by have hh:=hp.one_lt; omega) hd.1),
    hl.2.trans_le (Nat.le_of_dvd (by have hh:=hq.one_lt; omega) hd.2)⟩

/-- The long-period complement also has a small literal factor sum. -/
theorem factor_sum_bound {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 0<B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hl : LocalLong h (2*B)) : p+q≤2*B^4 := by
  have hb2 : 0<B^2 := pow_pos hB 2
  obtain ⟨hP,hQ⟩ := local_card_bounds hp hq h hl
  have hpB : B^2≤p := by
    have hh : p-1<p := by omega
    nlinarith
  have hqB : B^2≤q := by
    have hh : q-1<q := by omega
    nlinarith
  have he : B^6=B^4*B^2 := by ring
  have hpup : p≤B^4 := by
    have hm : p*B^2≤B^4*B^2 :=
      (Nat.mul_le_mul_left p hqB).trans (he ▸ hbudget)
    nlinarith
  have hqup : q≤B^4 := by
    have hm : q*B^2≤B^4*B^2 := by
      calc q*B^2≤q*p := Nat.mul_le_mul_left q hpB
           _=p*q := Nat.mul_comm _ _
           _≤B^4*B^2 := he ▸ hbudget
    nlinarith
  omega

/-- Coprime long periods make the global order a divisor of the actual
totient, strictly exceeding the factor sum. This is proof-side information. -/
theorem global_order_totient_and_sum {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (hB : 0<B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hl : LocalLong h (2*B))
    (hc : (orderOf (leftUnit h)).Coprime (orderOf (rightUnit h))) :
    orderOf h∣(p-1)*(q-1) ∧ p+q<orderOf h := by
  have he := global_order_eq_lcm hp hq hpq h
  rw [hc.lcm_eq_mul] at he
  have hd := local_card_divisors hp hq h
  constructor
  · rw [he]
    exact Nat.mul_dvd_mul hd.1 hd.2
  · have hn : 0<orderOf (rightUnit h) := orderOf_pos _
    have hm : 16*B^4<orderOf (leftUnit h)*orderOf (rightUnit h) := by
      calc 16*B^4=(2*B)^2*(2*B)^2 := by ring
           _≤(2*B)^2*orderOf (rightUnit h) := Nat.mul_le_mul_left _ hl.2.le
           _<orderOf (leftUnit h)*orderOf (rightUnit h) :=
             Nat.mul_lt_mul_of_pos_right hl.1 hn
    have hsum := factor_sum_bound hp hq hB hbudget h hl
    rw [he]
    have hb4 : 0<B^4 := pow_pos hB 4
    omega

/-- Retain the exact integer factor-sum encoding from a supplied modulus. -/
def sumSignal (N m : ℕ) : ℕ := (N+1)%m

/-- A large known divisor of the totient determines the literal factor sum. -/
theorem sumSignal_eq_sum {p q m : ℕ} (hp : 1<p) (hq : 1<q)
    (hd : m∣(p-1)*(q-1)) (hs : p+q<m) : sumSignal (p*q) m=p+q := by
  have he : p*q+1=(p-1)*(q-1)+(p+q) := by
    have hP := Nat.sub_add_cancel hp.le
    have hQ := Nat.sub_add_cancel hq.le
    nlinarith
  unfold sumSignal
  rw [he,Nat.add_mod,Nat.mod_eq_zero_of_dvd hd,zero_add,
    Nat.mod_eq_of_lt hs,Nat.mod_eq_of_lt hs]

/-- Public quadratic candidate from the retained factor-sum signal. -/
def sumCandidate (N m : ℕ) : ℕ :=
  let s := sumSignal N m
  (s-(s^2-4*N).sqrt)/2

/-- The candidate recovers the smaller prime exactly when its sum is known. -/
theorem sumCandidate_of_sum {p q m : ℕ} (hpq : p≤q)
    (hs : sumSignal (p*q) m=p+q) : sumCandidate (p*q) m=p := by
  unfold sumCandidate
  rw [hs]
  dsimp only
  rw [SemiprimeCommonOrder.index_discriminant_square hpq,Nat.sqrt_eq']
  have he := Nat.sub_add_cancel hpq
  omega

/-- Independently check the single factor-sum candidate before returning it. -/
def recoverKnownOrder (N m : ℕ) : Option ℕ := checkedSignal N (sumCandidate N m)

/-- The decoder never returns an improper divisor, even for an incorrect modulus. -/
theorem recoverKnownOrder_sound {N m d : ℕ} (hd : recoverKnownOrder N m=some d) :
    ProperDivisor N d := checkedSignal_sound hd

/-- An actual known global long order gives one direct quadratic recovery.
Acquiring that order is a charged frontier, not an input to the public router. -/
theorem recoverKnownOrder_of_long {p q B m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (hB : 0<B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hl : LocalLong h (2*B))
    (hc : (orderOf (leftUnit h)).Coprime (orderOf (rightUnit h)))
    (hm : orderOf h=m) : recoverKnownOrder (p*q) m=some p := by
  obtain ⟨hd,hs⟩ := global_order_totient_and_sum hp hq hpq.ne hB hbudget h hl hc
  rw [hm] at hd hs
  have he := sumCandidate_of_sum hpq.le (sumSignal_eq_sum hp.one_lt hq.one_lt hd hs)
  have hg : (p*q).gcd p=p := Nat.gcd_eq_right (dvd_mul_right p q)
  unfold recoverKnownOrder
  rw [he,checkedSignal,hg,if_pos]
  exact ⟨hp.one_lt,by nlinarith [hp.pos,hq.one_lt]⟩

/-- The public successor exponent cannot annihilate both long coprime channels. -/
theorem successor_power_ne_one {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (hB : 0<B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hl : LocalLong h (2*B))
    (hc : (orderOf (leftUnit h)).Coprime (orderOf (rightUnit h))) : h^(p*q+1)≠1 := by
  obtain ⟨hd,hs⟩ := global_order_totient_and_sum hp hq hpq hB hbudget h hl hc
  intro he
  have hm := orderOf_dvd_of_pow_eq_one he
  have hsum : orderOf h∣p+q := by
    have hid : p*q+1=(p-1)*(q-1)+(p+q) := by
      have hP := Nat.sub_add_cancel hp.one_lt.le
      have hQ := Nat.sub_add_cancel hq.one_lt.le
      nlinarith
    rw [hid] at hm
    exact (Nat.dvd_add_iff_right hd).mpr hm
  have hpos : 0<p+q := by omega
  exact (not_le_of_gt hs) (Nat.le_of_dvd hpos hsum)

/-- If one local period contains the other prime, the public N power
keeps one long channel and reduces the other inside the quadratic short
cover. Both original group cardinalities and the input budget are charged. -/
theorem cross_power_order_bounds {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p q B : ℕ} (hp : p.Prime) (hq : q.Prime) (hbudget : p*q≤B^6)
    (a : G) (b : H) (hda : orderOf a∣p-1) (hdb : orderOf b∣q-1)
    (hla : (2*B)^2<orderOf a) (hcross : p∣orderOf b) :
    (2*B)^2<orderOf (a^(p*q)) ∧ orderOf (b^(p*q))≤B^2 := by
  have haPos := orderOf_pos a
  have hbPos := orderOf_pos b
  have hpCard : 0<p-1 := by have hh:=hp.one_lt; omega
  have hqCard : 0<q-1 := by have hh:=hq.one_lt; omega
  have haLe := Nat.le_of_dvd hpCard hda
  have hbLe := Nat.le_of_dvd hqCard hdb
  have hpLe := Nat.le_of_dvd hbPos hcross
  have hpq : p<q := by omega
  have haP : orderOf a<p := by omega
  have haQ : orderOf a<q := haP.trans hpq
  have hcP : (orderOf a).Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt haPos haP)).symm
  have hcQ : (orderOf a).Coprime q :=
    (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt haPos haQ)).symm
  have he := (hcP.mul_right hcQ).orderOf_pow
  constructor
  · rw [he]
    exact hla
  · have hdCard : p∣q-1 := hcross.trans hdb
    have hafter := SemiprimeOrderSeparation.order_pow_dvd_quotient b hdb hdCard
      (dvd_mul_right p q)
    have hquotPos : 0<(q-1)/p := Nat.div_pos (Nat.le_of_dvd hqCard hdCard) hp.pos
    have hafterLe := Nat.le_of_dvd hquotPos hafter
    have hpB : B^2≤p := by
      have hh : p-1<p := by omega
      nlinarith
    have hs : B^6≤p*p*B^2 := by
      calc B^6=(B^2*B^2)*B^2 := by ring
           _≤(p*p)*B^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul hpB hpB)
    have hqp : q≤p*B^2 := by nlinarith [hp.pos]
    have hquot : (q-1)/p≤B^2 := by
      calc (q-1)/p≤(p*B^2)/p := Nat.div_le_div_right ((Nat.sub_le q 1).trans hqp)
           _=B^2 := Nat.mul_div_cancel_left _ hp.pos
    exact hafterLe.trans hquot

/-- Either orientation of a cross-prime period is recovered by the N batch. -/
theorem recover_N_of_cross {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 0<B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hl : LocalLong h (2*B))
    (hcross : p∣orderOf (rightUnit h) ∨ q∣orderOf (leftUnit h)) :
    ∃ d, recoverShort (h^(p*q)) (2*B)=some d := by
  obtain ⟨hda,hdb⟩ := local_card_divisors hp hq h
  have hP : leftUnit (h^(p*q))=(leftUnit h)^(p*q) := by simp only [leftUnit,map_pow]
  have hQ : rightUnit (h^(p*q))=(rightUnit h)^(p*q) := by simp only [rightUnit,map_pow]
  apply recoverShort_of_unequal hp hq _ (by omega)
  · rcases hcross with hc | hc
    · obtain ⟨hleft,hright⟩ := cross_power_order_bounds hp hq hbudget
        (leftUnit h) (rightUnit h) hda hdb hl.1 hc
      rw [hP,hQ]
      intro he
      rw [he] at hleft
      nlinarith
    · obtain ⟨hright,hleft⟩ := cross_power_order_bounds hq hp
        (by simpa only [Nat.mul_comm q p] using hbudget)
        (rightUnit h) (leftUnit h) hdb hda hl.2 hc
      rw [Nat.mul_comm q p] at hright hleft
      rw [hP,hQ]
      intro he
      rw [he] at hleft
      nlinarith
  · rcases hcross with hc | hc
    · have hs := (cross_power_order_bounds hp hq hbudget
        (leftUnit h) (rightUnit h) hda hdb hl.1 hc).2
      rw [hP,hQ]
      have hm := (min_le_right (orderOf ((leftUnit h)^(p*q)))
        (orderOf ((rightUnit h)^(p*q)))).trans hs
      nlinarith
    · have hs := (cross_power_order_bounds hq hp
        (by simpa only [Nat.mul_comm q p] using hbudget)
        (rightUnit h) (leftUnit h) hdb hda hl.2 hc).2
      rw [Nat.mul_comm q p] at hs
      rw [hP,hQ]
      have hm := (min_le_left (orderOf ((leftUnit h)^(p*q)))
        (orderOf ((rightUnit h)^(p*q)))).trans hs
      nlinarith

/-- A failed N batch excludes both cross-prime periods and makes the
global order coprime to N. The original two channels remain retained. -/
theorem failed_N_forces_coprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (hB : 0<B) (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ)
    (hl : LocalLong h (2*B)) (hnone : recoverShort (h^(p*q)) (2*B)=none) :
    (orderOf h).Coprime (p*q) := by
  have hpOne := hp.one_lt
  have hqOne := hq.one_lt
  have hnot : ¬(p∣orderOf (rightUnit h) ∨ q∣orderOf (leftUnit h)) := by
    intro hc
    obtain ⟨d,hd⟩ := recover_N_of_cross hp hq hB hbudget h hl hc
    rw [hnone] at hd
    contradiction
  obtain ⟨hda,hdb⟩ := local_card_divisors hp hq h
  have hpa : ¬p∣orderOf (leftUnit h) := by
    have hle := Nat.le_of_dvd (show 0<p-1 by have hh:=hp.one_lt; omega) hda
    exact Nat.not_dvd_of_pos_of_lt (orderOf_pos _) (by omega)
  have hqb : ¬q∣orderOf (rightUnit h) := by
    have hle := Nat.le_of_dvd (show 0<q-1 by have hh:=hq.one_lt; omega) hdb
    exact Nat.not_dvd_of_pos_of_lt (orderOf_pos _) (by omega)
  have hqa : ¬q∣orderOf (leftUnit h) := fun hc => hnot (Or.inr hc)
  have hpb : ¬p∣orderOf (rightUnit h) := fun hc => hnot (Or.inl hc)
  have hcA : (orderOf (leftUnit h)).Coprime (p*q) :=
    (hp.coprime_iff_not_dvd.mpr hpa).symm.mul_right
      (hq.coprime_iff_not_dvd.mpr hqa).symm
  have hcB : (orderOf (rightUnit h)).Coprime (p*q) :=
    (hp.coprime_iff_not_dvd.mpr hpb).symm.mul_right
      (hq.coprime_iff_not_dvd.mpr hqb).symm
  rw [global_order_eq_lcm hp hq hpq h]
  exact (hcA.mul_left hcB).of_dvd_left (Nat.lcm_dvd_mul _ _)

/-- Two coprime powered local orders cannot be equal when the powered
global unit is nontrivial. This retains both fields through the CRT step. -/
theorem powered_orders_unequal {p q E : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (h : (ZMod (p*q))ˣ)
    (hc : (orderOf (leftUnit h)).Coprime (orderOf (rightUnit h)))
    (hne : h^E≠1) : orderOf (leftUnit (h^E))≠orderOf (rightUnit (h^E)) := by
  have hP : leftUnit (h^E)=(leftUnit h)^E := by simp only [leftUnit,map_pow]
  have hQ : rightUnit (h^E)=(rightUnit h)^E := by simp only [rightUnit,map_pow]
  have hcop : (orderOf (leftUnit (h^E))).Coprime (orderOf (rightUnit (h^E))) := by
    rw [hP,hQ]
    exact hc.of_dvd (orderOf_pow_dvd E) (orderOf_pow_dvd E)
  intro he
  rw [←he,Nat.coprime_self] at hcop
  have hg := global_order_eq_lcm hp hq hpq (h^E)
  rw [←he,Nat.lcm_self,hcop] at hg
  exact hne (orderOf_eq_one_iff.mp hg)

/-- A rough prime shared by a powering exponent and a cubic-bounded
field cardinality reduces that field inside the short quadratic cover. -/
theorem small_card_power_bound {G : Type*} [Group G]
    {p B r E : ℕ} (hp : 1<p) (hB : 0<B) (hpB : p≤B^3)
    (a : G) (hda : orderOf a∣p-1) (hr : B<r) (hrd : r∣orderOf a) (hrE : r∣E) :
    orderOf (a^E)≤B^2 := by
  have hrCard := hrd.trans hda
  have hpCard : 0<p-1 := by omega
  have hquotPos : 0<(p-1)/r :=
    Nat.div_pos (Nat.le_of_dvd hpCard hrCard) (by omega)
  have hafter := SemiprimeOrderSeparation.order_pow_dvd_quotient a hda hrCard hrE
  have hle := Nat.le_of_dvd hquotPos hafter
  have hpr : p≤r*B^2 := by
    have hs : B^3≤r*B^2 := by
      calc B^3=B*B^2 := by ring
           _≤r*B^2 := Nat.mul_le_mul_right _ hr.le
    exact hpB.trans hs
  have hquot : (p-1)/r≤B^2 := by
    calc (p-1)/r≤(r*B^2)/r := Nat.div_le_div_right ((Nat.sub_le p 1).trans hpr)
         _=B^2 := Nat.mul_div_cancel_left _ (by omega)
  exact hle.trans hquot

/-- Failure of the N+1 batch forces the smaller field's retained period
to be coprime to that public exponent, in either prime orientation. -/
theorem failed_successor_forces_min_coprime {p q B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hB : 0<B)
    (hbudget : p*q≤B^6) (h : (ZMod (p*q))ˣ) (hcore : CoreData p q B h)
    (hnone : recoverShort (h^(p*q+1)) (2*B)=none) :
    (p≤q → (orderOf (leftUnit h)).Coprime (p*q+1)) ∧
    (q≤p → (orderOf (rightUnit h)).Coprime (p*q+1)) := by
  obtain ⟨hda,hdb⟩ := local_card_divisors hp hq h
  have hne := powered_orders_unequal hp hq hpq h hcore.2.1
    (successor_power_ne_one hp hq hpq hB hbudget h hcore.1 hcore.2.1)
  have hP : leftUnit (h^(p*q+1))=(leftUnit h)^(p*q+1) := by simp only [leftUnit,map_pow]
  have hQ : rightUnit (h^(p*q+1))=(rightUnit h)^(p*q+1) := by simp only [rightUnit,map_pow]
  have hmin : (2*B)^2<min (orderOf (leftUnit (h^(p*q+1))))
      (orderOf (rightUnit (h^(p*q+1)))) := by
    by_contra hn
    obtain ⟨d,hd⟩ := recoverShort_of_unequal (b:=2*B) hp hq _ (by omega) hne (by omega)
    rw [hnone] at hd
    contradiction
  constructor
  · intro horder
    by_contra hn
    obtain ⟨r,hr,hrd,hrE⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hpB : p≤B^3 := by
      have hs := SemiprimeLongPeriodExtraction.smaller_factor_group_budget horder hbudget
      omega
    have hs := small_card_power_bound hp.one_lt hB hpB (leftUnit h) hda
      (hcore.2.2.1 r hr hrd) hrd hrE
    rw [hP,hQ] at hmin
    have hm := hmin.trans_le (min_le_left _ _)
    nlinarith
  · intro horder
    by_contra hn
    obtain ⟨r,hr,hrd,hrE⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hqB : q≤B^3 := by
      have hs := SemiprimeLongPeriodExtraction.smaller_factor_group_budget horder
        (by simpa only [Nat.mul_comm q p] using hbudget)
      omega
    have hs := small_card_power_bound hq.one_lt hB hqB (rightUnit h) hdb
      (hcore.2.2.2 r hr hrd) hrd hrE
    rw [hP,hQ] at hmin
    have hm := hmin.trans_le (min_le_right _ _)
    nlinarith

/-- A divisor surviving the raw exponent consumes one stripped copy and the retained final period in the original group cardinality. -/
theorem retained_raw_power_dvd {G : Type*} [Group G] [Finite G] (a : G)
    {A E M r : ℕ} (ha : orderOf a∣A) (hrE : r∣E)
    (hr : r∣orderOf ((a^E)^M)) : r*orderOf ((a^E)^M)∣A := by
  have hraw : r∣orderOf (a^E) := hr.trans (orderOf_pow_dvd M)
  have hstrip := surviving_power_dvd a hrE 1 (by simpa only [pow_one] using hraw)
  have hstep : r*orderOf ((a^E)^M)∣r*orderOf (a^E) :=
    Nat.mul_dvd_mul_left r (orderOf_pow_dvd M)
  have hstrip' : r*orderOf (a^E)∣orderOf a := by
    simpa only [pow_one] using hstrip
  exact hstep.trans (hstrip'.trans ha)

/-- A prime above B cannot be a shared cardinality divisor when both retained local periods exceed the short cap and N is at most B^6. -/
theorem large_common_survivor_impossible {p q B A D r : ℕ}
    (hp : 1<p) (hq : 1<q) (hB : 0<B) (hbudget : p*q≤B^6)
    (hA : (2*B)^2<A) (hD : (2*B)^2<D) (hr : B<r)
    (ha : r*A∣p-1) (hd : r*D∣q-1) : False := by
  have hb2 : 0<B^2 := pow_pos hB 2
  have hrpos : 0<r := by omega
  have hPA : r*A≤p-1 := Nat.le_of_dvd (by omega) ha
  have hQD : r*D≤q-1 := Nat.le_of_dvd (by omega) hd
  have hp3 : B^3<p := by
    have hh : B*B^2<r*B^2 := Nat.mul_lt_mul_of_pos_right hr hb2
    have hl : r*B^2≤r*A := Nat.mul_le_mul_left r (by nlinarith)
    have he : B^3=B*B^2 := by ring
    rw [he]
    omega
  have hq3 : B^3<q := by
    have hh : B*B^2<r*B^2 := Nat.mul_lt_mul_of_pos_right hr hb2
    have hl : r*B^2≤r*D := Nat.mul_le_mul_left r (by nlinarith)
    have he : B^3=B*B^2 := by ring
    rw [he]
    omega
  have he : B^6=B^3*B^3 := by ring
  have hlt : B^6<p*q := by
    rw [he]
    exact (Nat.mul_le_mul_left (B^3) hq3.le).trans_lt
      (Nat.mul_lt_mul_of_pos_right hp3 (by omega))
  omega

/-- The surviving left period is coprime to N-1. Otherwise one stripped prime copy at each factor violates the literal product budget. -/
theorem projected_left_coprime_predecessor {p q B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hB : 0<B) (hbudget : p*q≤B^6)
    (g : (ZMod (p*q))ˣ) (hc : CoreData p q B (projectedUnit g B)) :
    (orderOf (leftUnit (projectedUnit g B))).Coprime (p*q-1) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  apply Nat.coprime_of_dvd
  intro r hr hrA hrE
  have hcard := local_card_divisors hp hq (projectedUnit g B)
  have hsurvive : r*orderOf (leftUnit (projectedUnit g B))∣p-1 := by
    have hr' : r∣orderOf (((leftUnit g)^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1)))) := by
      simpa only [leftUnit,projectedUnit,map_pow] using hrA
    have hh := retained_raw_power_dvd (leftUnit g)
      (ZMod.orderOf_units_dvd_card_sub_one _) hrE hr'
    simpa only [leftUnit,projectedUnit,map_pow] using hh
  have hrgcd := Nat.dvd_gcd (hrA.trans hcard.1) hrE
  rw [SemiprimeOrderSeparation.gcd_sub_one_mul hp.pos hq.pos] at hrgcd
  have hrq : r∣q-1 := hrgcd.trans (Nat.gcd_dvd_right _ _)
  have hcR : r.Coprime (orderOf (rightUnit (projectedUnit g B))) :=
    hc.2.1.of_dvd_left hrA
  have hother := hcR.mul_dvd_of_dvd_of_dvd hrq hcard.2
  exact large_common_survivor_impossible hp.one_lt hq.one_lt hB hbudget
    hc.1.1 hc.1.2 (hc.2.2.1 r hr hrA) hsurvive hother

/-- The same cardinality-budget argument retains the right field and proves its surviving period coprime to N-1. -/
theorem projected_right_coprime_predecessor {p q B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hB : 0<B) (hbudget : p*q≤B^6)
    (g : (ZMod (p*q))ˣ) (hc : CoreData p q B (projectedUnit g B)) :
    (orderOf (rightUnit (projectedUnit g B))).Coprime (p*q-1) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  apply Nat.coprime_of_dvd
  intro r hr hrD hrE
  have hcard := local_card_divisors hp hq (projectedUnit g B)
  have hsurvive : r*orderOf (rightUnit (projectedUnit g B))∣q-1 := by
    have hr' : r∣orderOf (((rightUnit g)^(p*q-1))^((B.factorial)^(Nat.clog 2 (p*q+1)))) := by
      simpa only [rightUnit,projectedUnit,map_pow] using hrD
    have hh := retained_raw_power_dvd (rightUnit g)
      (ZMod.orderOf_units_dvd_card_sub_one _) hrE hr'
    simpa only [rightUnit,projectedUnit,map_pow] using hh
  have hrgcd := Nat.dvd_gcd (hrD.trans hcard.2) hrE
  rw [SemiprimeOrderSeparation.gcd_sub_one_mul_right hp.pos hq.pos] at hrgcd
  have hrp : r∣p-1 := hrgcd.trans (Nat.gcd_dvd_left _ _)
  have hcR : r.Coprime (orderOf (leftUnit (projectedUnit g B))) :=
    hc.2.1.symm.of_dvd_left hrD
  have hother := hcR.mul_dvd_of_dvd_of_dvd hrp hcard.1
  exact large_common_survivor_impossible hq.one_lt hp.one_lt hB
    (by simpa only [Nat.mul_comm] using hbudget)
    hc.1.2 hc.1.1 (hc.2.2.2 r hr hrD) hsurvive hother

/-- Both retained fields certify that the actual projected global order is coprime to N-1, without any additional public query. -/
theorem projected_predecessor_coprime {p q B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hB : 0<B) (hbudget : p*q≤B^6)
    (g : (ZMod (p*q))ˣ) (hc : CoreData p q B (projectedUnit g B)) :
    (orderOf (projectedUnit g B)).Coprime (p*q-1) := by
  have hleft := projected_left_coprime_predecessor hp hq hB hbudget g hc
  have hright := projected_right_coprime_predecessor hp hq hB hbudget g hc
  rw [global_order_eq_lcm hp hq hpq]
  exact (hleft.mul_left hright).of_dvd_left (Nat.lcm_dvd_mul _ _)


/-- Retain the cached N power as its own public unit. -/
def nPower {N : ℕ} (h : (ZMod N)ˣ) : (ZMod N)ˣ := h^N

/-- The successor channel uses one multiplication of the cached N power. -/
def successorPower {N : ℕ} (h : (ZMod N)ˣ) : (ZMod N)ˣ := nPower h*h

/-- The cached successor channel is the literal N+1 power. -/
theorem successorPower_eq {N : ℕ} (h : (ZMod N)ˣ) : successorPower h=h^(N+1) :=
  (pow_succ h N).symm

/-- Check one closing residue before building its short batch. -/
def checkPower {N : ℕ} (h : (ZMod N)ˣ) : Option ℕ :=
  checkedSignal N ((h : ZMod N)-1).val

/-- The direct power GCD returns only proper factors. -/
theorem checkPower_sound {N d : ℕ} (h : (ZMod N)ˣ) (hd : checkPower h=some d) :
    ProperDivisor N d := checkedSignal_sound hd

/-- Two public power channels, each followed by a degree-at-most-2B
short batch only when its direct GCD did not already recover a factor. -/
noncomputable def scanPowers {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) : Option ℕ :=
  match checkPower (nPower h) with
  | some d => some d
  | none =>
    match recoverShort (nPower h) (2*B) with
    | some d => some d
    | none =>
      match checkPower (successorPower h) with
      | some d => some d
      | none => recoverShort (successorPower h) (2*B)

/-- A successful first direct test determines the scan without unfolding
any numerical short-batch construction. -/
theorem scanPowers_eq_of_first {N B d : ℕ} (h : (ZMod N)ˣ)
    (hc : checkPower (nPower h)=some d) : scanPowers h B=some d := by
  simp only [scanPowers,hc]

/-- A successful successor direct test determines the scan after the
literal preceding direct test and short batch are both clear. -/
theorem scanPowers_eq_of_successor {N B d : ℕ} (h : (ZMod N)ˣ)
    (hc : checkPower (nPower h)=none) (hn : recoverShort (nPower h) (2*B)=none)
    (hs : checkPower (successorPower h)=some d) : scanPowers h B=some d := by
  simp only [scanPowers,hc,hn,hs]

/-- Every factor from either channel is proper, without period advice. -/
theorem scanPowers_sound {N B d : ℕ} (h : (ZMod N)ˣ) (hd : scanPowers h B=some d) :
    ProperDivisor N d := by
  unfold scanPowers at hd
  cases hn : checkPower (nPower h) with
  | some f =>
    rw [hn] at hd
    have he := Option.some.inj hd
    exact he ▸ checkPower_sound _ hn
  | none =>
    rw [hn] at hd
    cases hs : recoverShort (nPower h) (2*B) with
    | some f =>
      rw [hs] at hd
      have he := Option.some.inj hd
      exact he ▸ recoverShort_sound _ hs
    | none =>
      rw [hs] at hd
      cases hx : checkPower (successorPower h) with
      | some f =>
        rw [hx] at hd
        have he := Option.some.inj hd
        exact he ▸ checkPower_sound _ hx
      | none =>
        rw [hx] at hd
        exact recoverShort_sound _ hd

/-- A failed scan preserves both actual failed short-batch results. -/
theorem scanPowers_none_info {N B : ℕ} (h : (ZMod N)ˣ) (hn : scanPowers h B=none) :
    recoverShort (nPower h) (2*B)=none ∧
    recoverShort (successorPower h) (2*B)=none := by
  unfold scanPowers at hn
  cases hc : checkPower (nPower h) with
  | some d => rw [hc] at hn; contradiction
  | none =>
    rw [hc] at hn
    cases hs : recoverShort (nPower h) (2*B) with
    | some d => rw [hs] at hn; contradiction
    | none =>
      rw [hs] at hn
      cases hx : checkPower (successorPower h) with
      | some d => rw [hx] at hn; contradiction
      | none =>
        rw [hx] at hn
        exact ⟨rfl,hn⟩

/-- GCD queries along the literal two-channel scan, including direct tests. -/
noncomputable def scanGcdCount {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) : ℕ :=
  1 + match checkPower (nPower h) with
  | some _ => 0
  | none => shortGcdCount (nPower h) (2*B)+
    match recoverShort (nPower h) (2*B) with
    | some _ => 0
    | none => 1 + match checkPower (successorPower h) with
      | some _ => 0
      | none => shortGcdCount (successorPower h) (2*B)

/-- All added batches and direct tests cost at most 8B+2 GCD queries. -/
theorem scanGcdCount_le {N : ℕ} (h : (ZMod N)ˣ) (B : ℕ) : scanGcdCount h B≤8*B+2 := by
  have hn := shortGcdCount_le (nPower h) (2*B)
  have hs := shortGcdCount_le (successorPower h) (2*B)
  cases hc : checkPower (nPower h) with
  | some d => simp only [scanGcdCount,hc,Nat.add_zero]; omega
  | none =>
    cases hb : recoverShort (nPower h) (2*B) with
    | some d => simp only [scanGcdCount,hc,hb,Nat.add_zero]; omega
    | none =>
      cases hx : checkPower (successorPower h) with
      | some d =>
        simp only [scanGcdCount,hc,hb,hx,Nat.add_zero]
        calc
          1+(shortGcdCount (nPower h) (2*B)+1) ≤ 1+(2*(2*B)+1) :=
            Nat.add_le_add_left (Nat.add_le_add_right hn 1) 1
          _ ≤ 8*B+2 := by omega
      | none =>
        simp only [scanGcdCount,hc,hb,hx]
        calc
          1+(shortGcdCount (nPower h) (2*B)+(1+shortGcdCount (successorPower h) (2*B)))
              ≤ 1+(2*(2*B)+(1+2*(2*B))) :=
            Nat.add_le_add_left (Nat.add_le_add hn (Nat.add_le_add_left hs 1)) 1
          _ ≤ 8*B+2 := by omega

/-- The original core cannot live at a prime square: equal reductions
would have equal coprime orders and hence a trivial local period. -/
theorem core_distinct {p q B : ℕ} (hB : 0<B) (h : (ZMod (p*q))ˣ)
    (hc : CoreData p q B h) : p≠q := by
  intro he
  subst q
  have heq : leftUnit h=rightUnit h := rfl
  have hcop := hc.2.1
  rw [←heq,Nat.coprime_self] at hcop
  have hl := hc.1.1
  rw [hcop] at hl
  nlinarith

/-- A factor or a retained richer power carrier. No known order is stored
as advice: all four units are derived from the public input and seed. -/
inductive PowerRoute (N : ℕ) where
  | factor (d : ℕ)
  | remaining (original active nPower successor : (ZMod N)ˣ)
  | unresolved

/-- Keep the original long certificate and both public power channels,
alongside the exact additional facts extracted by their failed batches. -/
def GoodPower (p q B : ℕ) : PowerRoute (p*q) → Prop
  | .factor d => ProperDivisor (p*q) d
  | .remaining g h z s => LongData g B ∧ h=projectedUnit g B ∧
      z=nPower h ∧ s=z*h ∧ recoverShort z (2*B)=none ∧ recoverShort s (2*B)=none ∧
      (orderOf h).Coprime (p*q) ∧
      (orderOf h).Coprime (p*q-1) ∧
      (p≤q → (orderOf (leftUnit h)).Coprime (p*q+1)) ∧
      (q≤p → (orderOf (rightUnit h)).Coprime (p*q+1))
  | .unresolved => False

/-- N-only refinement of a certified long seed. Projection regeneration
and its unit GCD are part of the implementation, not free cached advice. -/
noncomputable def refineLong (N B k : ℕ) : PowerRoute N :=
  if hc : k.Coprime N then
    let g := ZMod.unitOfCoprime k hc
    let h := projectedUnit g B
    match scanPowers h B with
    | some d => .factor d
    | none => .remaining g h (nPower h) (successorPower h)
  else .unresolved

/-- A checked scan factors the public long handler directly; the theorem
keeps numerical short-source reductions out of the wrapper proof. -/
theorem refineLong_eq_of_scan {N B k d : ℕ} (hc : k.Coprime N)
    (hs : scanPowers (projectedUnit (ZMod.unitOfCoprime k hc) B) B=some d) :
    refineLong N B k=.factor d := by
  simp only [refineLong,dif_pos hc,hs]

/-- The public long handler either factors or retains its original
certificate plus the newly proved coprimality facts and failed sources. -/
theorem refineLong_good {p q B k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hB : 0<B) (hbudget : p*q≤B^6)
    (hroute : GoodRoute p q B (.longBase k)) : GoodPower p q B (refineLong (p*q) B k) := by
  obtain ⟨hc,hdata⟩ := hroute
  let g := ZMod.unitOfCoprime k hc
  let h := projectedUnit g B
  have hcore := projected_core g hdata
  have hpq := core_distinct hB h hcore
  unfold refineLong
  rw [dif_pos hc]
  dsimp only
  cases hs : scanPowers h B with
  | some d => exact scanPowers_sound h hs
  | none =>
    obtain ⟨hn,hnext⟩ := scanPowers_none_info h hs
    have hn' : recoverShort (h^(p*q)) (2*B)=none := hn
    have hnext' : recoverShort (h^(p*q+1)) (2*B)=none := by
      rwa [successorPower_eq] at hnext
    have hcN := failed_N_forces_coprime hp hq hpq hB hbudget h hcore.1 hn'
    have hcPrevious := projected_predecessor_coprime hp hq hpq hB hbudget g hcore
    have hcNext := failed_successor_forces_min_coprime hp hq hpq hB hbudget h hcore hnext'
    exact ⟨hdata,rfl,rfl,rfl,hn,hnext,hcN,hcPrevious,hcNext⟩

/-- The public wrapper additionally pays its input-unit check. -/
noncomputable def refinementGcdCount (N B k : ℕ) : ℕ :=
  1 + if hc : k.Coprime N then scanGcdCount (projectedUnit (ZMod.unitOfCoprime k hc) B) B
      else 0

/-- At most 8B+3 GCDs are added, including the public seed-unit test. -/
theorem refinementGcdCount_le (N B k : ℕ) : refinementGcdCount N B k≤8*B+3 := by
  unfold refinementGcdCount
  split_ifs with hc
  · have hs := scanGcdCount_le (projectedUnit (ZMod.unitOfCoprime k hc) B) B
    omega
  · omega

/-- Leaf certificates retain a real semiprime and the strengthened long
power data, rather than treating a failed refinement as a factor. -/
inductive PowerCertified : {N : ℕ} → PowerRoute N → Prop where
  | factor {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
      (hd : ProperDivisor (p*q) d) : PowerCertified (.factor d : PowerRoute (p*q))
  | remaining {p q : ℕ} {g h z s : (ZMod (p*q))ˣ}
      (hp : p.Prime) (hq : q.Prime)
      (hd : GoodPower p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) (.remaining g h z s)) :
      PowerCertified (.remaining g h z s)

/-- A good literal public leaf result supplies its indexed certificate. -/
theorem powerCertified_of_good {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (route : PowerRoute (p*q))
    (hg : GoodPower p q (SemiprimeLehmanCoverage.sixthWidth (p*q)) route) :
    PowerCertified route := by
  cases route with
  | factor d => exact .factor hp hq hg
  | remaining g h z s => exact .remaining hp hq hg
  | unresolved => exact False.elim hg

/-- A certified leaf factor is proper for its exact leaf input. -/
theorem powerCertified_factor {N d : ℕ} (hc : PowerCertified (.factor d : PowerRoute N)) :
    ProperDivisor N d := by
  cases hc with
  | factor hp hq hd => exact hd

/-- An unresolved leaf has no semiprime power certificate. -/
theorem powerCertified_not_unresolved {N : ℕ}
    (hc : PowerCertified (.unresolved : PowerRoute N)) : False := by
  cases hc

/-- Refine only the terminal long seed, while keeping the entire original
kernel descent available as a separate richer carrier. -/
noncomputable def leafRefinement {N : ℕ} (trace : SemiprimeKernelDescent.Trace N) :
    PowerRoute (SemiprimeKernelDescent.leafInput trace) :=
  match SemiprimeKernelDescent.leafRoute trace with
  | .factor d => .factor d
  | .longBase k => refineLong (SemiprimeKernelDescent.leafInput trace)
      (SemiprimeLehmanCoverage.sixthWidth (SemiprimeKernelDescent.leafInput trace)) k
  | _ => .unresolved

/-- Every certified original descent produces a certified refined leaf. -/
theorem leafRefinement_certified {N : ℕ} {trace : SemiprimeKernelDescent.Trace N}
    (hc : SemiprimeKernelDescent.Certified trace) : PowerCertified (leafRefinement trace) := by
  induction hc with
  | factor hp hq hd => exact .factor hp hq hd
  | longBase hp hq hgood =>
    exact powerCertified_of_good hp hq _ (refineLong_good hp hq
      (SemiprimeKernelDescent.sixthWidth_pos (Nat.mul_pos hp.pos hq.pos))
      (SemiprimeLehmanCoverage.sixthWidth_upper _) hgood)
  | child hp hq hgood hchild ih => exact ih

/-- Lift a newly obtained leaf factor through every retained active unit.
The original trace is not discarded by this downstream recovery view. -/
noncomputable def transportCandidate {N : ℕ} : SemiprimeKernelDescent.Trace N → ℕ → Option ℕ
  | .factor d, _ => some d
  | .longBase _, d => checkedSignal N d
  | .unresolved, _ => none
  | .child R _ h _ _ trace, d =>
    match transportCandidate trace d with
    | some f => SemiprimeKernelResidual.recoverResidual h R f
    | none => none

/-- The transported option returns only proper original-input factors. -/
theorem transportCandidate_sound {N d f : ℕ} {trace : SemiprimeKernelDescent.Trace N}
    (hc : SemiprimeKernelDescent.Certified trace) (hf : transportCandidate trace d=some f) :
    ProperDivisor N f := by
  cases hc with
  | factor hp hq hd =>
    have he := Option.some.inj hf
    exact he ▸ hd
  | longBase hp hq hgood => exact checkedSignal_sound hf
  | @child p q R g h primes route trace hp hq hgood hchild =>
    dsimp only [transportCandidate] at hf
    cases hs : transportCandidate trace d with
    | none => rw [hs] at hf; contradiction
    | some f' =>
      rw [hs] at hf
      exact SemiprimeKernelResidual.recoverResidual_sound h hf

/-- Any proper refined leaf factor is transported back completely.
All successful edge powers, candidates and GCDs remain charged calls. -/
theorem transportCandidate_complete {N d : ℕ} {trace : SemiprimeKernelDescent.Trace N}
    (hc : SemiprimeKernelDescent.Certified trace)
    (hd : ProperDivisor (SemiprimeKernelDescent.leafInput trace) d) :
    ∃ f, transportCandidate trace d=some f ∧ ProperDivisor N f := by
  induction hc generalizing d with
  | factor hp hq hproper => exact ⟨_,rfl,hproper⟩
  | @longBase p q k hp hq hgood =>
    have hg : (p*q).gcd d=d := Nat.gcd_eq_right hd.2.2
    have hproper : 1<d ∧ d<p*q := ⟨hd.1,hd.2.1⟩
    refine ⟨d,?_,hd⟩
    simp only [transportCandidate,checkedSignal,hg,if_pos hproper]
  | @child p q R g h primes route trace hp hq hgood hchild ih =>
    obtain ⟨f,hf,hproper⟩ := ih hd
    obtain ⟨f',hf',hproper'⟩ :=
      SemiprimeKernelResidual.residual_transport hp hq g h primes route hgood hproper
    refine ⟨f',?_,hproper'⟩
    simp only [transportCandidate,hf,hf']

/-- Decode the original factor option once; a newly successful leaf is
then lifted through the unchanged retained descent. -/
noncomputable def factorWithLeaf {N : ℕ} (trace : SemiprimeKernelDescent.Trace N)
    (leaf : PowerRoute (SemiprimeKernelDescent.leafInput trace)) : Option ℕ :=
  match SemiprimeKernelDescent.recoveredFactor trace with
  | some d => some d
  | none => match leaf with
    | .factor d => transportCandidate trace d
    | _ => none

/-- Exhaustive refined result: a recovered original factor or a retained
certified nonfactor leaf. The pending mathematics remains explicit. -/
theorem factorWithLeaf_cases {N : ℕ} {trace : SemiprimeKernelDescent.Trace N}
    (hc : SemiprimeKernelDescent.Certified trace)
    (leaf : PowerRoute (SemiprimeKernelDescent.leafInput trace)) (hl : PowerCertified leaf) :
    (∃ d, factorWithLeaf trace leaf=some d ∧ ProperDivisor N d) ∨
    (factorWithLeaf trace leaf=none ∧ PowerCertified leaf ∧ ∀ d,leaf≠.factor d) := by
  cases ho : SemiprimeKernelDescent.recoveredFactor trace with
  | some d =>
    exact Or.inl ⟨d,by simp only [factorWithLeaf,ho],
      SemiprimeKernelDescent.recoveredFactor_sound hc ho⟩
  | none =>
    cases leaf with
    | factor d =>
      obtain ⟨f,hf,hproper⟩ := transportCandidate_complete hc (powerCertified_factor hl)
      exact Or.inl ⟨f,by simp only [factorWithLeaf,ho,hf],hproper⟩
    | remaining g h z s =>
      exact Or.inr ⟨by simp only [factorWithLeaf,ho],hl,by intro d he; cases he⟩
    | unresolved => exact False.elim (powerCertified_not_unresolved hl)

/-- Rich public result retains both the original descent and its refined
leaf, with the proper original factor option as a downstream summary. -/
structure Packet (N : ℕ) where
  /-- Complete original descent, retaining every transport frame. -/
  source : SemiprimeKernelDescent.Trace N
  /-- The actual refined terminal leaf with its retained power channels. -/
  leaf : PowerRoute (SemiprimeKernelDescent.leafInput source)
  /-- A downstream checked original-input factor when recovery succeeds. -/
  factor : Option ℕ

/-- Complete N-only refinement, computing the initial descent and actual
leaf once each. No supplied numerical order enters this procedure. -/
noncomputable def publicPacket (N : ℕ) : Packet N :=
  let source := SemiprimeKernelDescent.publicTrace N
  let leaf := leafRefinement source
  ⟨source,leaf,factorWithLeaf source leaf⟩

/-- Universal original-factor-or-strengthened-long-leaf routing, including
all kernel descent. The final one-sixth extractor and bit theorem are open. -/
theorem publicPacket_cases {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (∃ d,(publicPacket (p*q)).factor=some d ∧ ProperDivisor (p*q) d) ∨
    ((publicPacket (p*q)).factor=none ∧ PowerCertified (publicPacket (p*q)).leaf ∧
      ∀ d,(publicPacket (p*q)).leaf≠.factor d) :=
  factorWithLeaf_cases (SemiprimeKernelDescent.publicTrace_certified hp hq) _
    (leafRefinement_certified (SemiprimeKernelDescent.publicTrace_certified hp hq))

/-- The terminal input is no larger than the original input in every
certified trace, including traces that already recover a factor. -/
theorem certified_leaf_input_le {N : ℕ} {trace : SemiprimeKernelDescent.Trace N}
    (hc : SemiprimeKernelDescent.Certified trace) :
    SemiprimeKernelDescent.leafInput trace≤N := by
  induction hc with
  | factor hp hq hd => exact Nat.le_refl _
  | longBase hp hq hg => exact Nat.le_refl _
  | child hp hq hgood hchild ih =>
    have hh := hgood.1
    exact ih.trans (by omega)

/-- Count only the actual new terminal refinement; factor leaves add no
power scan. Projection construction remains a separate charged operation. -/
noncomputable def leafRefinementGcdCount {N : ℕ} (trace : SemiprimeKernelDescent.Trace N) : ℕ :=
  match SemiprimeKernelDescent.leafRoute trace with
  | .longBase k => refinementGcdCount (SemiprimeKernelDescent.leafInput trace)
      (SemiprimeLehmanCoverage.sixthWidth (SemiprimeKernelDescent.leafInput trace)) k
  | _ => 0

/-- The new refinement allowance uses the original input's sixth-root
width even after any number of retained kernel descents. -/
theorem publicPacket_refinement_queries_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    leafRefinementGcdCount (SemiprimeKernelDescent.publicTrace (p*q))≤
      8*SemiprimeLehmanCoverage.sixthWidth (p*q)+3 := by
  have hw := SemiprimeKernelDescent.sixthWidth_mono
    (certified_leaf_input_le (SemiprimeKernelDescent.publicTrace_certified hp hq))
  cases he : SemiprimeKernelDescent.leafRoute (SemiprimeKernelDescent.publicTrace (p*q)) with
  | factor d => simp only [leafRefinementGcdCount,he]; omega
  | kernelBase k => simp only [leafRefinementGcdCount,he]; omega
  | unresolved => simp only [leafRefinementGcdCount,he]; omega
  | longBase k =>
    simp only [leafRefinementGcdCount,he]
    exact (refinementGcdCount_le _ _ k).trans (by omega)

set_option maxRecDepth 32768 in
/-- Exact arithmetic of the cross-period control. Its actual public seed
and projection are checked separately in the charged replay. -/
theorem control_cross_arithmetic :
    Nat.Prime 10163 ∧ Nat.Prime 20327 ∧ 10163*20327=206583301 ∧
    206583301≤(25 : ℕ)^6 ∧ (2*25 : ℕ)^2<5081 ∧ (2*25 : ℕ)^2<10163 ∧
    Nat.Coprime 5081 10163 ∧ sumSignal 206583301 51638203=30490 ∧
    recoverKnownOrder 206583301 51638203=some 10163 := by
  norm_num [sumSignal,recoverKnownOrder,sumCandidate,checkedSignal,Nat.Coprime]

/-- The cross control's public N-power is checked by fast modular
exponentiation inside Lean; no supplied order is used for this test. -/
theorem control_cross_power :
    (125510454 : ZMod 206583301)^206583301=2967743 := by
  reduce_mod_char

set_option maxRecDepth 32768 in
/-- The first control's projected scalar is calculated from the public
base two and the literal public exponents, rather than supplied as advice. -/
theorem control_cross_projection_value :
    ((2 : ZMod 206583301)^(206583301-1 : ℕ))^
      ((Nat.factorial 25)^(Nat.clog 2 (206583301+1)))=125510454 := by
  have hlog : Nat.clog 2 (206583301+1)=28 := by decide
  have hfact : Nat.factorial 25=15511210043330985984000000 := by
    norm_num [Nat.factorial]
  rw [hlog,hfact]
  reduce_mod_char

set_option maxRecDepth 32768 in
/-- On the certified projected value the first added direct GCD already
recovers the larger factor; no new short source is needed on this control. -/
theorem control_cross_scan (h : (ZMod 206583301)ˣ)
    (hh : (h : ZMod 206583301)=125510454) : scanPowers h 25=some 20327 := by
  have hv : (nPower h : ZMod 206583301)=2967743 := by
    rw [nPower,Units.val_pow_eq_pow_val,hh]
    exact control_cross_power
  have hc : checkPower (nPower h)=some 20327 := by
    have he : (2967743 : ZMod 206583301)-1=2967742 := by reduce_mod_char
    unfold checkPower
    rw [hv,he,ZMod.val_ofNat]
    norm_num [checkedSignal]
  exact scanPowers_eq_of_first h hc

set_option maxRecDepth 32768 in
/-- The complete new long handler at public base two recovers 20327 on
the first control. Its full preceding routing is covered by the replay. -/
theorem control_cross_refine : refineLong 206583301 25 2=.factor 20327 := by
  have hc : Nat.Coprime 2 206583301 := by norm_num [Nat.Coprime]
  have hg : (ZMod.unitOfCoprime 2 hc : ZMod 206583301)=2 := ZMod.coe_unitOfCoprime 2 hc
  have hp : (projectedUnit (ZMod.unitOfCoprime 2 hc) 25 : ZMod 206583301)=125510454 := by
    rw [projectedUnit_val,hg]
    exact control_cross_projection_value
  exact refineLong_eq_of_scan hc (control_cross_scan _ hp)

set_option maxRecDepth 32768 in
/-- Exact factor, budget and direct signal data for the successor control.
The first short batch's failed outcome remains an independent replay check. -/
theorem control_successor_arithmetic :
    Nat.Prime 11483 ∧ Nat.Prime 22963 ∧ 11483*22963=263684129 ∧
    263684129≤(26 : ℕ)^6 ∧ (2*26 : ℕ)^2<5741 ∧ (2*26 : ℕ)^2<3827 ∧
    Nat.Coprime 5741 3827 := by
  norm_num [Nat.Coprime]

/-- Both public power channels of the successor control are checked
without constructing the unreduced integer powers. -/
theorem control_successor_powers :
    (116995666 : ZMod 263684129)^263684129=243780042 ∧
    (243780042 : ZMod 263684129)*116995666=191639788 := by
  constructor <;> reduce_mod_char

set_option maxRecDepth 32768 in
/-- The second control's literal projected scalar is also checked from
the public base and public projection exponents inside Lean. -/
theorem control_successor_projection_value :
    ((2 : ZMod 263684129)^(263684129-1 : ℕ))^
      ((Nat.factorial 26)^(Nat.clog 2 (263684129+1)))=116995666 := by
  have hlog : Nat.clog 2 (263684129+1)=28 := by decide
  have hfact : Nat.factorial 26=403291461126605635584000000 := by
    norm_num [Nat.factorial]
  rw [hlog,hfact]
  reduce_mod_char

set_option maxRecDepth 32768 in
/-- The N test is clear, while the N+1 direct signal recovers 11483. -/
theorem control_successor_checks (h : (ZMod 263684129)ˣ)
    (hh : (h : ZMod 263684129)=116995666) :
    checkPower (nPower h)=none ∧ checkPower (successorPower h)=some 11483 := by
  have hv : (nPower h : ZMod 263684129)=243780042 := by
    rw [nPower,Units.val_pow_eq_pow_val,hh]
    exact control_successor_powers.1
  have hs : (successorPower h : ZMod 263684129)=191639788 := by
    rw [successorPower,Units.val_mul,hv,hh]
    exact control_successor_powers.2
  have heN : (243780042 : ZMod 263684129)-1=243780041 := by reduce_mod_char
  have heS : (191639788 : ZMod 263684129)-1=191639787 := by reduce_mod_char
  unfold checkPower
  rw [hv,hs,heN,heS,ZMod.val_ofNat,ZMod.val_ofNat]
  norm_num [checkedSignal]

set_option maxRecDepth 32768 in
/-- If the preceding N short batch is clear, the successor control
returns its checked factor. This hypothesis is not silently assumed. -/
theorem control_successor_scan (h : (ZMod 263684129)ˣ)
    (hh : (h : ZMod 263684129)=116995666)
    (hn : recoverShort (nPower h) 52=none) : scanPowers h 26=some 11483 := by
  obtain ⟨hc,hs⟩ := control_successor_checks h hh
  exact scanPowers_eq_of_successor h hc hn hs

end RiemannGaussian.SemiprimeLongPowerRouting
