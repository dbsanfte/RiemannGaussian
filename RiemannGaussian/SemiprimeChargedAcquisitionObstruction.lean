import RiemannGaussian.SemiprimeFullEuclidAcquisitionObstruction

/-!
# Charge-derived complete Euclidean acquisition catalog

Every full-height skipped multiplier e<q of an actual Euclidean current
is covered by the strict determinant charge r*y*e<m. Projecting positive
triple charges gives a universal signed catalog of cardinality at most
2*m*(log2(m)+1)^2; adjoining every original current and intermediate gives
at most 18*m*(log2(m)+1)^2. Membership and coordinate bounds retain the
actual recursive frame and full source. No hidden factor or period advice
is supplied. The classical stronger union constant10 is not used here.

The investigation journal extends the prior actual infinite all-hit
obstruction to the legal full-N lifts of this amended catalog, with a
classically paid soft-linear centered norm. It thereby excludes short
commensurability and endpoint transport for every within-frame skipped
advance, even at tall heights. Literal adjacent-frame support, the
generic long-norm charged floor after numeric target deduplication and
bounded-order polynomial recurrence rigidity remain classical arguments.

The finite catalogs here are proof envelopes. Their generated cube/image
enumerations do not implement the separately paid harmonic enumeration,
long scalar norm, proper recovery or a bit/memory clock. Published density,
global infinitude and all asymptotic acquisition estimates remain classical;
none is a Lean axiom. The full guaranteed one-sixth goal remains open.
-/

namespace RiemannGaussian.SemiprimeChargedAcquisitionObstruction

open SemiprimeQuotientRows SemiprimeEuclidRowFamily SemiprimeEuclidRowBudget

/-- Project the strict positive determinant budget to signed scaled rays. -/
def chargedRayCatalog (m : ℕ) : Finset (ℤ×ℕ) :=
  (Finset.univ ×ˢ positiveTriples (m-1)).image fun b : Bool×(ℕ×ℕ×ℕ) =>
    (signed b.1 (b.2.1*b.2.2.2), b.2.2.1*b.2.2.2)

/-- Positive product factors are individually bounded by the product. -/
theorem triple_factors_le {r y e : ℕ} (hr : 0<r) (hy : 0<y) (he : 0<e) :
    r≤r*y*e ∧ y≤r*y*e ∧ e≤r*y*e := by
  have hr' : r≤r*y := Nat.le_mul_of_pos_right r hy
  have hy' : y≤r*y := Nat.le_mul_of_pos_left y hr
  have hprod : r*y≤r*y*e := Nat.le_mul_of_pos_right _ he
  have he' : e≤r*y*e := Nat.le_mul_of_pos_left e (Nat.mul_pos hr hy)
  exact ⟨hr'.trans hprod,hy'.trans hprod,he'⟩

/-- Every signed strict-budget triple appears in the universal catalog. -/
theorem mem_chargedRayCatalog {m r y e : ℕ} (hr : 0<r) (hy : 0<y)
    (he : 0<e) (hprod : r*y*e<m) (negative : Bool) :
    (signed negative (r*e),y*e)∈chargedRayCatalog m := by
  have hf := triple_factors_le hr hy he
  have hb : r*y*e≤m-1 := by omega
  have ht : (r,y,e)∈positiveTriples (m-1) :=
    positiveTriples_mem_iff.mpr
      ⟨hr,hf.1.trans hb,hy,hf.2.1.trans hb,he,hf.2.2.trans hb,hb⟩
  apply Finset.mem_image.mpr
  exact ⟨(negative,(r,y,e)),Finset.mem_product.mpr ⟨Finset.mem_univ _,ht⟩,rfl⟩

/-- Every catalog member has nonzero coordinates strictly below m. -/
theorem chargedRayCatalog_bounds {m : ℕ} {z : ℤ×ℕ}
    (hz : z∈chargedRayCatalog m) :
    0<z.1.natAbs ∧ z.1.natAbs<m ∧ 0<z.2 ∧ z.2<m := by
  obtain ⟨⟨negative,r,y,e⟩,hb,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hr,_,hy,_,he,_,hprod⟩ :=
    positiveTriples_mem_iff.mp (Finset.mem_product.mp hb).2
  dsimp only at hr hy he hprod ⊢
  have hre : r*e≤r*y*e := by
    calc
      r*e≤(r*y)*e := Nat.mul_le_mul_right e (Nat.le_mul_of_pos_right r hy)
      _ = _ := rfl
  have hye : y*e≤r*y*e :=
    Nat.mul_le_mul_right e (Nat.le_mul_of_pos_left y hr)
  have hp0 : 0<r*y*e := Nat.mul_pos (Nat.mul_pos hr hy) he
  have hre' : r*e<m := by omega
  have hye' : y*e<m := by omega
  have habs : (signed negative (r*e)).natAbs=r*e := by
    cases negative <;> simp [signed,Int.natAbs_mul]
  simp only [habs]
  exact ⟨Nat.mul_pos hr he,hre',Nat.mul_pos hy he,hye'⟩

/-- The projected universal catalog inherits the squared-log triple budget. -/
theorem chargedRayCatalog_card_le (m : ℕ) :
    (chargedRayCatalog m).card≤2*m*(Nat.log2 m+1)^2 := by
  have hlog : Nat.log2 (m-1)≤Nat.log2 m := by
    rw [Nat.log2_eq_log_two,Nat.log2_eq_log_two]
    exact Nat.log_mono_right (Nat.sub_le m 1)
  have hs : (Nat.log2 (m-1)+1)^2≤(Nat.log2 m+1)^2 := by nlinarith
  calc
    _ ≤ (Finset.univ ×ˢ positiveTriples (m-1) : Finset (Bool×(ℕ×ℕ×ℕ))).card :=
      Finset.card_image_le
    _ = 2*(positiveTriples (m-1)).card := by
      rw [Finset.card_product,Finset.card_univ,Fintype.card_bool]
    _ ≤ 2*((m-1)*(Nat.log2 (m-1)+1)^2) :=
      Nat.mul_le_mul_left 2 (positiveTriples_card_le (m-1))
    _ ≤ 2*(m*(Nat.log2 m+1)^2) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.sub_le m 1) hs)
    _ = _ := by ring

/-- A strict skipped slot uses strictly less than the determinant budget. -/
theorem frame_skipped_product_lt {m : ℕ} {f : EuclidFrame}
    (hr : 0<f.smaller) (hy : 0<f.currentWeight)
    (hfit : f.larger*f.currentWeight+f.smaller*f.priorWeight=m)
    {e : ℕ} (he : e<frameQuotient f) :
    f.smaller*f.currentWeight*e<m := by
  have h := frame_charge_product hfit he
  have hp : 0<f.smaller*f.currentWeight := Nat.mul_pos hr hy
  nlinarith

/-- Every actual full-height skipped current multiplier is in the catalog. -/
theorem actual_skipped_mem_chargedRayCatalog {N m j : ℕ} (hm : 0<m)
    {f : EuclidFrame} (hf : f∈residueFrames N m j) {e : ℕ}
    (he0 : 0<e) (he : e<frameQuotient f) :
    (signed f.negative (f.smaller*e),f.currentWeight*e)∈chargedRayCatalog m := by
  have hfit := euclidFrames_fit (m:=m) (Nat.mod_lt _ hm) (by decide)
      (by simp) hf
  exact mem_chargedRayCatalog hfit.1 hfit.2.1 he0
    (frame_skipped_product_lt hfit.1 hfit.2.1 hfit.2.2.2 he) f.negative

/-- Retain the complete original source together with every charged skipped ray. -/
def amendedRayCatalog (m : ℕ) : Finset (ℤ×ℕ) :=
  SemiprimeFullEuclidAcquisitionObstruction.universalRayCatalog m ∪ chargedRayCatalog m

/-- The enlarged catalog still has a linear-modulus squared-log bound. -/
theorem amendedRayCatalog_card_le {m : ℕ} (hm : m.Prime) (hm2 : m≠2) :
    (amendedRayCatalog m).card≤18*m*(Nat.log2 m+1)^2 := by
  calc
    _ ≤ (SemiprimeFullEuclidAcquisitionObstruction.universalRayCatalog m).card+
        (chargedRayCatalog m).card := Finset.card_union_le _ _
    _ ≤ 16*m*(Nat.log2 m+1)^2+2*m*(Nat.log2 m+1)^2 :=
      Nat.add_le_add (SemiprimeFullEuclidAcquisitionObstruction.universalRayCatalog_card_le hm hm2)
        (chargedRayCatalog_card_le m)
    _ = _ := by ring

/-- No original actual current or intermediate is lost in the amendment. -/
theorem actual_pair_mem_amendedRayCatalog {N m j : ℕ} (hm : 0<m)
    {z : ℤ×ℕ} (hz : z∈publicPairs N m j) : z∈amendedRayCatalog m :=
  Finset.mem_union.mpr (Or.inl
    (SemiprimeFullEuclidAcquisitionObstruction.mem_universalRayCatalog_of_publicPairs hm hz))

/-- Every actual full-height skipped current multiplier survives the amendment. -/
theorem actual_skipped_mem_amendedRayCatalog {N m j : ℕ} (hm : 0<m)
    {f : EuclidFrame} (hf : f∈residueFrames N m j) {e : ℕ}
    (he0 : 0<e) (he : e<frameQuotient f) :
    (signed f.negative (f.smaller*e),f.currentWeight*e)∈amendedRayCatalog m :=
  Finset.mem_union.mpr (Or.inr (actual_skipped_mem_chargedRayCatalog hm hf he0 he))

end RiemannGaussian.SemiprimeChargedAcquisitionObstruction
