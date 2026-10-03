/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCompanionRows

/-!
# Complete companion exhaustion and the zero anchor

The original public companion detector has an exact unit-separation
criterion, including its endpoint scan. Inserting one public zero root
combines all endpoint and off-diagonal information in a single derivative.
A literal balanced semiprime audits universal coverage of the original
axis. The requested construction-inclusive sixth-root bit guarantee
remains open.
-/

namespace RiemannGaussian.SemiprimeCompanionCoverage

open SemiprimeCompanionRows SemiprimeCartesianCompletion

-- Bound closed certificate quantifiers by their retained roots rather
-- than enumerating the entire ZMod carrier. The kernel checks both.
attribute [local instance 1100] Finset.decidableDforallFinset

/-- All distinct whole-modulus roots remain separated by units. -/
def UnitSeparated {N : ℕ} (S : Finset (ZMod N)) : Prop :=
  ∀ t∈S, ∀ x∈S, x≠t → IsUnit (t-x)

/-- The endpoint scan distinguishes global zero from a nonzero nonunit. -/
theorem endpoints_none_iff {N : ℕ} [NeZero N] (S : Finset (ZMod N)) :
    scanProper N (S.toList.map ZMod.val)=none ↔ ∀ t∈S, t=0 ∨ IsUnit t := by
  rw [scanProper_none_iff]
  constructor
  · intro h t ht
    apply (SemiprimeTraceRows.checkedSignal_none_iff t).mp
    exact h t.val (List.mem_map.mpr ⟨t,Finset.mem_toList.mpr ht,rfl⟩)
  · intro h v hv
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hv
    exact (SemiprimeTraceRows.checkedSignal_none_iff t).mpr
      (h t (Finset.mem_toList.mp ht))

/-- This is the exhaustion criterion for the whole original program,
including all endpoint, derivative and saturated-output recovery work. -/
theorem recoverCompanionRows_none_iff {N m : ℕ} [NeZero N] :
    recoverCompanionRows N m=none ↔
      (∀ t∈publicCompanionRoots N m, t=0 ∨ IsUnit t) ∧
        UnitSeparated (publicCompanionRoots N m) := by
  have h : recoverCompanionRows N m=none ↔
      scanProper N ((publicCompanionRoots N m).toList.map ZMod.val)=none ∧
        SemiprimeRowDerivative.recoverRows (publicCompanionRoots N m)=none := by
    unfold recoverCompanionRows
    cases hs : scanProper N ((publicCompanionRoots N m).toList.map ZMod.val) <;>
      simp only [hs,Option.some_ne_none,false_and,iff_self,true_and]
  rw [h,endpoints_none_iff,SemiprimeRowDerivative.recoverRows_none_iff]
  simp only [UnitSeparated,SemiprimeBulkNorm.gcd_one_iff_unit]

/-- A zero anchor retains every ordinary root and all endpoint differences. -/
def anchoredRoots {N : ℕ} (S : Finset (ZMod N)) : Finset (ZMod N) := insert 0 S

theorem anchoredRoots_unitSeparated_iff {N : ℕ} (S : Finset (ZMod N)) :
    UnitSeparated (anchoredRoots S) ↔ (∀ t∈S, t=0 ∨ IsUnit t) ∧ UnitSeparated S := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro t ht
      by_cases hz : t=0
      · exact Or.inl hz
      · right
        simpa only [sub_zero] using
          h t (Finset.mem_insert_of_mem ht) 0 (Finset.mem_insert_self _ _) (Ne.symm hz)
    · intro t ht x hx hne
      exact h t (Finset.mem_insert_of_mem ht) x (Finset.mem_insert_of_mem hx) hne
  · rintro ⟨he,hp⟩ t ht x hx hne
    rcases Finset.mem_insert.mp ht with rfl|ht
    · rcases Finset.mem_insert.mp hx with rfl|hx
      · exact False.elim (hne rfl)
      · have hu : IsUnit x := (he x hx).resolve_left hne
        simpa only [zero_sub] using hu.neg
    · rcases Finset.mem_insert.mp hx with rfl|hx
      · have hu : IsUnit t := (he t ht).resolve_left (Ne.symm hne)
        simpa only [sub_zero] using hu
      · exact hp t ht x hx hne

/-- One anchored derivative source combines the old two-stage detector. -/
noncomputable def recoverAnchoredCompanions (N m : ℕ) : Option ℕ :=
  SemiprimeRowDerivative.recoverRows (anchoredRoots (publicCompanionRoots N m))

theorem recoverAnchoredCompanions_sound {N m d : ℕ}
    (hd : recoverAnchoredCompanions N m=some d) :
    SemiprimeGroupSelection.ProperDivisor N d :=
  SemiprimeRowDerivative.recoverRows_sound hd

/-- The anchored derivative has exactly the original complete hit union.
It need not return the same first divisor or visit roots in the same order. -/
theorem recoverAnchoredCompanions_none_iff {N m : ℕ} [NeZero N] :
    recoverAnchoredCompanions N m=none ↔ recoverCompanionRows N m=none := by
  rw [recoverCompanionRows_none_iff,recoverAnchoredCompanions,
    SemiprimeRowDerivative.recoverRows_none_iff]
  simp only [SemiprimeBulkNorm.gcd_one_iff_unit]
  exact anchoredRoots_unitSeparated_iff _

/-- The full anchored source asks at most two GCDs per root, including
selected-row recovery; the extra zero adds only one root. -/
theorem recoverAnchoredCompanions_gcd_bound (N m : ℕ) :
    recoveryGcdCount N
      (fun i => residueLeaves (anchoredRoots (publicCompanionRoots N m)) (i : ZMod N))
      (evaluatedColumns (anchoredRoots (publicCompanionRoots N m))
        (anchoredRoots (publicCompanionRoots N m)).toList)≤
      4*(SemiprimeEuclidRowFamily.publicPackets N m).length+2 := by
  have h1 := SemiprimeRowDerivative.recoverRows_gcd_bound
    (anchoredRoots (publicCompanionRoots N m))
  have h2 : (anchoredRoots (publicCompanionRoots N m)).card≤
      (publicCompanionRoots N m).card+1 := Finset.card_insert_le 0 (publicCompanionRoots N m)
  have h3 := publicCompanionRoots_card_le N m
  omega

/-- Retain both additive signs and the public zero anchor in one root axis. -/
def signedRoots {N : ℕ} (S : Finset (ZMod N)) : Finset (ZMod N) :=
  anchoredRoots (S∪S.image (fun t => -t))

theorem signedRoots_mem {N : ℕ} {S : Finset (ZMod N)} {t : ZMod N} (ht : t∈S) :
    t∈signedRoots S := Finset.mem_insert_of_mem (Finset.mem_union_left _ ht)

theorem signedRoots_neg_mem {N : ℕ} {S : Finset (ZMod N)} {t : ZMod N} (ht : t∈S) :
    -t∈signedRoots S :=
  Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t,ht,rfl⟩))

theorem signedRoots_card_le {N : ℕ} (S : Finset (ZMod N)) :
    (signedRoots S).card≤2*S.card+1 := by
  have h0 : (signedRoots S).card≤(S∪S.image (fun t => -t)).card+1 :=
    Finset.card_insert_le 0 _
  have h1 := Finset.card_union_le S (S.image (fun t => -t))
  have h2 : (S.image (fun t => -t)).card≤S.card := Finset.card_image_le
  omega

/-- The signed axis retains exactly endpoint, difference and sum channels.
Only whole-modulus zero sums are excluded from the proper-pair channel. -/
theorem signedRoots_unitSeparated_iff {N : ℕ} (S : Finset (ZMod N)) :
    UnitSeparated (signedRoots S) ↔ (∀ t∈S, t=0 ∨ IsUnit t) ∧ UnitSeparated S ∧
      (∀ t∈S, ∀ x∈S, t+x≠0 → IsUnit (t+x)) := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro t ht
      by_cases hz : t=0
      · exact Or.inl hz
      · right
        simpa only [sub_zero] using
          h t (signedRoots_mem ht) 0 (Finset.mem_insert_self _ _) (Ne.symm hz)
    · intro t ht x hx hne
      exact h t (signedRoots_mem ht) x (signedRoots_mem hx) hne
    · intro t ht x hx hne
      have hn : -x≠t := by
        intro he
        apply hne
        rw [←he,neg_add_cancel]
      simpa only [sub_neg_eq_add] using h t (signedRoots_mem ht) (-x) (signedRoots_neg_mem hx) hn
  · rintro ⟨he,hp,hs⟩
    apply (anchoredRoots_unitSeparated_iff _).mpr
    refine ⟨?_,?_⟩
    · intro t ht
      rcases Finset.mem_union.mp ht with ht|ht
      · exact he t ht
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
        rcases he u hu with hz|hu
        · exact Or.inl (by rw [hz,neg_zero])
        · exact Or.inr hu.neg
    · intro t ht x hx hne
      rcases Finset.mem_union.mp ht with ht|ht <;>
        rcases Finset.mem_union.mp hx with hx|hx
      · exact hp t ht x hx hne
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
        have hn : t+u≠0 := by
          intro hz
          apply hne
          calc -u=t-(t+u) := by ring
               _=t := by rw [hz,sub_zero]
        simpa only [sub_neg_eq_add] using hs t ht u hu hn
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
        have hn : u+x≠0 := by
          intro hz
          apply hne
          calc x=(u+x)-u := by ring
               _=-u := by rw [hz,zero_sub]
        rw [show -u-x=-(u+x) by ring]
        exact (hs u hu x hx hn).neg
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
        have hn : v≠u := fun h => hne (congrArg Neg.neg h)
        rw [show -u-(-v)=-(u-v) by ring]
        exact (hp u hu v hv hn).neg

/-- The complete public signed source needs no group base or power. -/
noncomputable def recoverSignedCompanions (N m : ℕ) : Option ℕ :=
  SemiprimeRowDerivative.recoverRows (signedRoots (publicCompanionRoots N m))

theorem recoverSignedCompanions_sound {N m d : ℕ}
    (hd : recoverSignedCompanions N m=some d) :
    SemiprimeGroupSelection.ProperDivisor N d :=
  SemiprimeRowDerivative.recoverRows_sound hd

/-- Complete exhaustion of the signed program is exactly separation of
all three original local channels, with global diagonals retained as such. -/
theorem recoverSignedCompanions_none_iff {N m : ℕ} [NeZero N] :
    recoverSignedCompanions N m=none ↔
      (∀ t∈publicCompanionRoots N m, t=0 ∨ IsUnit t) ∧
        UnitSeparated (publicCompanionRoots N m) ∧
          (∀ t∈publicCompanionRoots N m, ∀ x∈publicCompanionRoots N m,
            t+x≠0 → IsUnit (t+x)) := by
  rw [recoverSignedCompanions,SemiprimeRowDerivative.recoverRows_none_iff]
  simp only [SemiprimeBulkNorm.gcd_one_iff_unit]
  exact signedRoots_unitSeparated_iff _

/-- Every proper companion sum is retained as one signed-root difference. -/
theorem recoverSignedCompanions_of_proper_sum {N m : ℕ} [NeZero N] {c e : ℤ}
    (hc : c∈publicCompanions N m) (he : e∈publicCompanions N m)
    (hp : SemiprimeGroupSelection.ProperDivisor N
      (N.gcd ((e : ZMod N)+(c : ZMod N)).val)) :
    ∃ d, recoverSignedCompanions N m=some d := by
  apply SemiprimeRowDerivative.recoverRows_succeeds_of_proper_pair
    (signedRoots_neg_mem (publicCompanionRoots_mem hc))
    (signedRoots_mem (publicCompanionRoots_mem he))
  simpa only [sub_neg_eq_add] using hp

/-- Exhaustion of the larger signed carrier implies exhaustion of the
complete original detector; no original successful hit can be erased. -/
theorem recoverSignedCompanions_none_implies_original {N m : ℕ} [NeZero N]
    (hn : recoverSignedCompanions N m=none) : recoverCompanionRows N m=none := by
  apply recoverAnchoredCompanions_none_iff.mp
  rw [recoverAnchoredCompanions,SemiprimeRowDerivative.recoverRows_none_iff]
  have h := (SemiprimeRowDerivative.recoverRows_none_iff _).mp hn
  intro t ht x hx hne
  apply h t _ x _ hne
  · rcases Finset.mem_insert.mp ht with rfl|ht
    · exact Finset.mem_insert_self _ _
    · exact signedRoots_mem ht
  · rcases Finset.mem_insert.mp hx with rfl|hx
    · exact Finset.mem_insert_self _ _
    · exact signedRoots_mem hx

theorem recoverSignedCompanions_preserves_success {N m d : ℕ} [NeZero N]
    (hd : recoverCompanionRows N m=some d) :
    ∃ f, recoverSignedCompanions N m=some f := by
  cases hs : recoverSignedCompanions N m with
  | some f => exact ⟨f,rfl⟩
  | none =>
    have hn := recoverSignedCompanions_none_implies_original hs
    rw [hd] at hn
    contradiction

/-- Both signs and the zero anchor still have a linear recovery-GCD
envelope in the original complete packet count. This is not a bit clock. -/
theorem recoverSignedCompanions_gcd_bound (N m : ℕ) :
    recoveryGcdCount N
      (fun i => residueLeaves (signedRoots (publicCompanionRoots N m)) (i : ZMod N))
      (evaluatedColumns (signedRoots (publicCompanionRoots N m))
        (signedRoots (publicCompanionRoots N m)).toList)≤
      8*(SemiprimeEuclidRowFamily.publicPackets N m).length+2 := by
  have h1 := SemiprimeRowDerivative.recoverRows_gcd_bound
    (signedRoots (publicCompanionRoots N m))
  have h2 := signedRoots_card_le (publicCompanionRoots N m)
  have h3 := publicCompanionRoots_card_le N m
  omega

set_option maxRecDepth 32768 in
/-- Every actual companion endpoint of the complete control is a unit. -/
theorem missed_control_endpoints : ∀ t∈publicCompanionRoots 7303 5,
    (7303 : ℕ).gcd t.val=1 := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Every distinct actual companion difference is a unit on the control. -/
theorem missed_control_pairs : ∀ t∈publicCompanionRoots 7303 5,
    ∀ x∈publicCompanionRoots 7303 5, x≠t → (7303 : ℕ).gcd (t-x).val=1 := by
  decide +kernel

/-- A literal balanced input fails the entire ordinary companion program. -/
theorem missed_control_public_none : recoverCompanionRows 7303 5=none := by
  apply recoverCompanionRows_none_iff.mpr
  constructor
  · intro t ht
    exact Or.inr ((SemiprimeBulkNorm.gcd_one_iff_unit t).mp (missed_control_endpoints t ht))
  · intro t ht x hx hne
    exact (SemiprimeBulkNorm.gcd_one_iff_unit (t-x)).mp (missed_control_pairs t ht x hx hne)

theorem missed_control_anchored_none : recoverAnchoredCompanions 7303 5=none :=
  recoverAnchoredCompanions_none_iff.mpr missed_control_public_none

/-- The input is balanced, lies in the fifth-modulus sixth-power range,
and is outside the squared-modulus small-factor prefix. -/
theorem missed_control_arithmetic : Nat.Prime 67 ∧ Nat.Prime 109 ∧
    7303=67*109 ∧ 67≤109 ∧ 109≤2*67 ∧ (5 : ℕ)^2<67 ∧ 7303≤(5 : ℕ)^6 := by
  norm_num

set_option maxRecDepth 32768 in
/-- Opposite additive signs reveal a proper sum on the failed control. -/
theorem missed_control_signed_witness : (57 : ℤ)∈publicCompanions 7303 5 ∧
    (77 : ℤ)∈publicCompanions 7303 5 := by
  constructor <;>
    apply publicCompanion_mem_of_residue (j:=2) (by norm_num) (by norm_num [Nat.Coprime]) <;>
    decide +kernel

theorem missed_control_signed_recovers : ∃ d, recoverSignedCompanions 7303 5=some d := by
  apply recoverSignedCompanions_of_proper_sum missed_control_signed_witness.1
    missed_control_signed_witness.2
  norm_num [SemiprimeGroupSelection.ProperDivisor]
  decide +kernel

end RiemannGaussian.SemiprimeCompanionCoverage
