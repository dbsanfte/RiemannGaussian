import RiemannGaussian.SemiprimeCenteredAcquisitionObstruction
import RiemannGaussian.SemiprimeEuclidRowBudget

/-!
# Universal complete Euclidean ray catalog

At an odd prime modulus, two square classes cover every nonzero canonical
quotient slope. Unit field solutions are converted to the literal Bezout
slope and original Euclidean packets. Projecting and deduplicating those
packets gives a universal signed ray catalog, uniform in the entire input
state, of cardinality at most 16*m*(log2(m)+1)^2. Every intermediate vector
of every literal input is retained; no square-root truncation is imposed.

This is the finite catalog used by the investigation journal's classical
prime-first, selector-subbox false-hit count and reversed ray/prime own-hit
count. Together they give an actual infinite all-hit miss family for the
FULL original Euclidean source in the specified centered windows, with a
paid classical soft-linear whole-family scalar norm. Published prime supply,
selector-gap estimates, center geometry, weighted dyadic estimates and the
global infinitude/counting argument remain classical, not Lean axioms.

The catalog definitions are finite ray enumerations, not a norm evaluator
or factorization algorithm. Their generated code proves no asymptotic bit
clock. The two square classes are constructed within the cardinality proof,
not supplied as factor advice or a coverage oracle. Wider original index
windows, arbitrary centers and source-specialized scalar queries remain open.
The full guaranteed one-sixth factorization and time/memory goal is open.
-/

namespace RiemannGaussian.SemiprimeFullEuclidAcquisitionObstruction

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily SemiprimeEuclidRowBudget

/-- Two square classes cover every nonzero slope at an odd prime. -/
theorem two_square_classes {m : ℕ} [Fact m.Prime] (hm2 : m≠2) :
    ∃ η : ZMod m, η≠0 ∧ ∀ u : ZMod m, u≠0 →
      ∃ j : ZMod m, j≠0 ∧ (u*j^2=1 ∨ u*j^2=η) := by
  have hc : ringChar (ZMod m)≠2 := by
    rw [ringChar.eq (ZMod m) m]
    exact hm2
  obtain ⟨η,hη⟩ := FiniteField.exists_nonsquare (F:=ZMod m) hc
  have hη0 : η≠0 := by intro h; exact hη (h ▸ IsSquare.zero)
  have hηpow : η^(Fintype.card (ZMod m)/2)= -1 := by
    rcases FiniteField.pow_dichotomy hc hη0 with h|h
    · exact False.elim (hη ((FiniteField.isSquare_iff hc hη0).mpr h))
    · exact h
  refine ⟨η,hη0,?_⟩
  intro u hu
  by_cases hs : IsSquare u
  · obtain ⟨s,hs⟩ := hs.exists_sq
    have hs0 : s≠0 := by intro h; simp [h] at hs; exact hu hs
    refine ⟨s⁻¹,inv_ne_zero hs0,Or.inl ?_⟩
    rw [hs,←mul_pow, mul_inv_cancel₀ hs0,one_pow]
  · have hupow : u^(Fintype.card (ZMod m)/2)= -1 := by
      rcases FiniteField.pow_dichotomy hc hu with h|h
      · exact False.elim (hs ((FiniteField.isSquare_iff hc hu).mpr h))
      · exact h
    have he : IsSquare (η/u) := by
      apply (FiniteField.isSquare_iff hc (div_ne_zero hη0 hu)).mpr
      rw [div_pow,hηpow,hupow]
      simp
    obtain ⟨j,hj⟩ := he.exists_sq
    have hj0 : j≠0 := by
      intro h
      have hz : η/u=0 := by simpa only [h,zero_pow (by decide : 2≠0)] using hj
      exact (div_ne_zero hη0 hu) hz
    refine ⟨j,hj0,Or.inr ?_⟩
    rw [←hj,mul_div_cancel₀ _ hu]

/-- The literal Bezout slope has the same prime-field value. -/
theorem quotientSlope_field {N m j : ℕ} (hm : 0<m) (hj : j.Coprime m) :
    (quotientSlope N m j : ZMod m)*(j : ZMod m)^2=(N : ZMod m) := by
  have hs := (ZMod.intCast_eq_intCast_iff _ _ m).mpr (quotientSlope_modEq (N:=N) (j:=j) hm)
  have hi := (ZMod.intCast_eq_intCast_iff _ _ m).mpr (publicInverse_correct hj)
  have hs' : (quotientSlope N m j : ZMod m)=
      (N : ZMod m)*(publicInverse m j : ZMod m)^2 := by
    simpa only [Int.cast_mul,Int.cast_pow,Int.cast_natCast] using hs
  have hi' : (j : ZMod m)*(publicInverse m j : ZMod m)=1 := by
    simpa only [Int.cast_mul,Int.cast_natCast,Int.cast_one] using hi
  rw [hs']
  calc
    _ = (N : ZMod m)*((j : ZMod m)*(publicInverse m j : ZMod m))^2 := by ring
    _ = _ := by rw [hi',one_pow,mul_one]

/-- A unit field solution produces a literal canonical slope equality. -/
theorem quotientSlope_eq_of_field {m N u : ℕ} [Fact m.Prime]
    (hu : u<m) {j : ZMod m} (hj : j≠0) (he : (u : ZMod m)*j^2=(N : ZMod m)) :
    j.val.Coprime m ∧ quotientSlope N m j.val %m=u := by
  have hm : m.Prime := Fact.out
  have hjc : j.val.Coprime m := by
    apply (ZMod.isUnit_iff_coprime j.val m).mp
    simpa using (isUnit_iff_ne_zero.mpr hj : IsUnit j)
  refine ⟨hjc,?_⟩
  have hz := quotientSlope_field (N:=N) hm.pos hjc
  simp only [ZMod.natCast_zmod_val] at hz
  have hcast : (quotientSlope N m j.val : ZMod m)=(u : ZMod m) := by
    exact mul_right_cancel₀ (pow_ne_zero 2 hj) (hz.trans he.symm)
  have hv := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast,ZMod.val_natCast_of_lt hu] using hv

/-- Every nonzero canonical slope occurs in one of two literal sources. -/
theorem slope_two_source_cover {m : ℕ} [Fact m.Prime] (hm2 : m≠2) :
    ∃ η : ℕ, η<m ∧ ∀ u : ℕ, 0<u → u<m →
      ∃ j : ℕ, j<m ∧ j.Coprime m ∧
        (quotientSlope 1 m j %m=u ∨ quotientSlope η m j %m=u) := by
  obtain ⟨η,hη0,hcover⟩ := two_square_classes hm2
  refine ⟨η.val,η.val_lt,?_⟩
  intro u hu hum
  have hu0 : (u : ZMod m)≠0 := by
    intro h
    have hv := congrArg ZMod.val h
    simp only [ZMod.val_natCast_of_lt hum,ZMod.val_zero] at hv
    omega
  obtain ⟨j,hj,hjcover⟩ := hcover u hu0
  refine ⟨j.val,j.val_lt,?_,?_⟩
  · rcases hjcover with h|h
    · exact (quotientSlope_eq_of_field (N:=1) hum hj (by simpa using h)).1
    · exact (quotientSlope_eq_of_field (N:=η.val) hum hj (by simpa using h)).1
  · rcases hjcover with h|h
    · exact Or.inl (quotientSlope_eq_of_field (N:=1) hum hj (by simpa using h)).2
    · exact Or.inr (quotientSlope_eq_of_field (N:=η.val) hum hj (by simpa using h)).2

/-- Deduplicated signed rays retained by a literal input source. -/
def sourceRays (N m : ℕ) : Finset (ℤ×ℕ) :=
  ((publicPackets N m).map fun w => (w.original.a,w.original.t.toNat)).toFinset

/-- A literal ray appears in its packet projection, preserving its coordinates. -/
theorem mem_sourceRays_of_publicPairs {N m j : ℕ} (hj : j<m)
    (hc : j.Coprime m) {z : ℤ×ℕ} (hz : z∈publicPairs N m j) :
    z∈sourceRays N m := by
  classical
  let row := liftRow N m j (publicInverse m j) z.1 z.2
  let w : FamilyPacket := ⟨j,row,publicShift N m j row.a row.b row.t⟩
  have hw : w∈publicPackets N m := by
    apply List.mem_flatMap.mpr
    refine ⟨j,List.mem_range.mpr hj,?_⟩
    rw [ite_eq_left hc]
    apply List.mem_flatMap.mpr
    refine ⟨z,hz,?_⟩
    simpa only [w,row] using (List.mem_cons_self (a:=w) (l:=[⟨j,row,reflectedShift N m j row.a row.b row.t⟩]))
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨w,hw,?_⟩
  simp only [w,row,liftRow,Int.toNat_natCast]

/-- Every literal deduplicated ray source inherits the full packet budget. -/
theorem sourceRays_card_le (N : ℕ) {m : ℕ} (hm : m.Prime) :
    (sourceRays N m).card≤8*m*(Nat.log2 m+1)^2 := by
  unfold sourceRays
  exact (List.toFinset_card_le _).trans (by simpa using publicPackets_length_le N hm)

/-- All slopes' actual Euclidean rays, without counting duplicate coordinates. -/
def universalRayCatalog (m : ℕ) : Finset (ℤ×ℕ) :=
  ((List.range m).flatMap fun u => euclidPairs m u 0 1 false).toFinset

/-- The universal catalog contains every ray from every literal input. -/
theorem mem_universalRayCatalog_of_publicPairs {N m j : ℕ} (hm : 0<m)
    {z : ℤ×ℕ} (hz : z∈publicPairs N m j) : z∈universalRayCatalog m := by
  classical
  apply List.mem_toFinset.mpr
  exact List.mem_flatMap.mpr ⟨quotientSlope N m j %m,
    List.mem_range.mpr (Nat.mod_lt _ hm),hz⟩

/-- Two complete literal sources cover the entire universal ray catalog. -/
theorem universalRayCatalog_two_sources {m : ℕ} [Fact m.Prime] (hm2 : m≠2) :
    ∃ η : ℕ, η<m ∧ universalRayCatalog m⊆sourceRays 1 m∪sourceRays η m := by
  obtain ⟨η,hη,hcover⟩ := slope_two_source_cover hm2
  refine ⟨η,hη,?_⟩
  intro z hz
  obtain ⟨u,hu,hz⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hz)
  have hu0 : 0<u := by
    by_contra h
    have hzero : u=0 := by omega
    rw [hzero,euclidPairs] at hz
    simp only [ite_true,List.not_mem_nil] at hz
  obtain ⟨j,hj,hjc,he⟩ := hcover u hu0 (List.mem_range.mp hu)
  rcases he with he|he
  · apply Finset.mem_union.mpr
    apply Or.inl
    apply mem_sourceRays_of_publicPairs hj hjc
    simpa only [publicPairs,he] using hz
  · apply Finset.mem_union.mpr
    apply Or.inr
    apply mem_sourceRays_of_publicPairs hj hjc
    simpa only [publicPairs,he] using hz

/-- The prime-first catalog has a linear-modulus squared-logarithm bound,
uniformly in the complete input state and including every intermediate ray. -/
theorem universalRayCatalog_card_le {m : ℕ} (hm : m.Prime) (hm2 : m≠2) :
    (universalRayCatalog m).card≤16*m*(Nat.log2 m+1)^2 := by
  let : Fact m.Prime := ⟨hm⟩
  obtain ⟨η,_hη,hsub⟩ := universalRayCatalog_two_sources hm2
  calc
    _ ≤ (sourceRays 1 m∪sourceRays η m).card := Finset.card_le_card hsub
    _ ≤ (sourceRays 1 m).card+(sourceRays η m).card := Finset.card_union_le _ _
    _ ≤ 8*m*(Nat.log2 m+1)^2+8*m*(Nat.log2 m+1)^2 :=
      Nat.add_le_add (sourceRays_card_le 1 hm) (sourceRays_card_le η hm)
    _ = _ := by ring

end RiemannGaussian.SemiprimeFullEuclidAcquisitionObstruction
