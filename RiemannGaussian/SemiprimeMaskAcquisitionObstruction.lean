import RiemannGaussian.SemiprimeIsolatedRowAcquisitionObstruction

/-!
# Source-preserving row masks and honest-character unit gates

The original hit polynomial has a unique lift at every simple root, and
its repeated roots have precisely the two displayed lower-residue branches.
These are the finite algebraic kernels used by the classical all-hit miss
theorem for small accessible row catalogs depending on both public digits.

The public complementary-tag involution gives a balanced-input nonunit
forcing mask, whose half-row cardinality and retained isolated poles are
checked here. Acquisition of its interval norm is not supplied.

The finite Gauss gates exclude a single-root puncture once its square
identity is explicitly supplied. The exact public scalar gate is a unit
over the semiprime ring under the displayed no-auxiliary-root premises.
Construction of the cyclotomic Gauss sum, its trace and norm identities,
prime-density supply, infinitude and bit costs remain classical audit
arguments, rather than axioms or implicit claims of this native leaf.
-/

namespace RiemannGaussian.SemiprimeMaskAcquisitionObstruction

open SemiprimeOffsetCarryObstruction

/-- Clearing a genuine original field hit eliminates its interval index
from the residue polynomial, with its exact discarded multiple retained. -/
theorem hit_multiplier_polynomial_identity {F : Type*} [CommRing F]
    (p q m v R δ r K : F) (hcofactor : p-1=v*R)
    (hhit : q+δ-m^2*r=K*R) :
    K*p^2-(K+v*δ)*p-v*(p*q) = -v*p*m^2*r := by
  linear_combination K*p*hcofactor-v*p*hhit

/-- Every exact original hit satisfies the same fixed polynomial modulo
m squared after its complete public input state is fixed. -/
theorem hit_multiplier_polynomial_modEq {m : ℕ}
    (p q v R δ r K n : ℤ) (hcofactor : p-1=v*R)
    (hhit : q+δ-(m : ℤ)^2*r=K*R)
    (hstate : p*q ≡ n [ZMOD (m : ℤ)^2]) :
    K*p^2-(K+v*δ)*p-v*n ≡ 0 [ZMOD (m : ℤ)^2] := by
  obtain ⟨t,ht⟩ := hstate.dvd
  have he := hit_multiplier_polynomial_identity p q (m : ℤ) v R δ r K hcofactor hhit
  apply Int.modEq_iff_dvd.mpr
  refine ⟨v*p*r+v*t, ?_⟩
  linear_combination -he+v*ht

/-- A simple residue root of the actual quadratic has at most one lift
modulo m squared. No existence theorem or prime-distribution input is used. -/
theorem multiplier_simple_root_unique_lift {m : ℕ} (hm : m.Prime)
    (K v δ n p p₀ : ℤ)
    (hclass : p ≡ p₀ [ZMOD m])
    (hroot : K*p^2-(K+v*δ)*p-v*n ≡ 0 [ZMOD (m : ℤ)^2])
    (hroot₀ : K*p₀^2-(K+v*δ)*p₀-v*n ≡ 0 [ZMOD (m : ℤ)^2])
    (hsimple : ¬(m : ℤ) ∣ 2*K*p₀-(K+v*δ)) :
    p ≡ p₀ [ZMOD (m : ℤ)^2] := by
  let c := K*(p+p₀)-(K+v*δ)
  have hc : ¬(m : ℤ) ∣ c := by
    intro h
    apply hsimple
    have hdiff := (hclass.symm.dvd).mul_left K
    convert dvd_sub h hdiff using 1
    dsimp only [c]
    ring
  have hfactor : (p-p₀)*c =
      (K*p^2-(K+v*δ)*p-v*n)-(K*p₀^2-(K+v*δ)*p₀-v*n) := by
    dsimp only [c]
    ring
  have hd : (m : ℤ)^2 ∣ (p-p₀)*c := by
    rw [hfactor]
    exact (hroot.trans hroot₀.symm).symm.dvd
  have hc0 : (c : ZMod m) ≠ 0 := by
    intro hz
    apply hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd c m).mp hz
  have hp := (integer_coprime_square hm c hc0).dvd_of_dvd_mul_right hd
  apply Int.modEq_iff_dvd.mpr
  simpa only [neg_sub] using hp.neg_right

/-- The two repeated-root branches exhaust the literal lower-residue
quadratic, including the true factor tag and the second rational tag. -/
theorem multiplier_repeated_root_branches {F : Type*} [Field F]
    (K v a j x : F) (hv : v ≠ 0) (ha : a ≠ 0)
    (hroot : K*x^2-(K+v*a*(1-2*j))*x-v*a*j^2=0)
    (hderivative : 2*K*x-(K+v*a*(1-2*j))=0) :
    x=j ∨ (2*j-1)*x=j := by
  have hmass : v*a*((x-j)*((2*j-1)*x-j))=0 := by
    linear_combination (2*x-1)*hroot+(x^2-x*(2*x-1))*hderivative
  have hpair := (mul_eq_zero.mp hmass).resolve_left (mul_ne_zero hv ha)
  obtain h | h := mul_eq_zero.mp hpair
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

open scoped BigOperators
open Polynomial
open SemiprimeIsolatedRowAcquisitionObstruction
open SemiprimeBalancedAcquisitionObstruction SemiprimeSeedSumAcquisition
open SemiprimePhaseSumRecovery SemiprimeLongPowerRouting
open SemiprimeDenseRowCoverage SemiprimeGlobalPhaseCancellation
open SemiprimeDenseRowCarries SemiprimeIntervalJet

/-- The public complementary factor tag in a nonzero residue state. -/
def rowPartner {K : Type*} [Mul K] [Inv K] (s j : K) : K := s * j⁻¹

theorem rowPartner_involutive {K : Type*} [Field K] {s j : K}
    (hs : s ≠ 0) : rowPartner s (rowPartner s j) = j := by
  simp only [rowPartner, mul_inv_rev, inv_inv]
  rw [mul_comm j s⁻¹, ←mul_assoc, mul_inv_cancel₀ hs, one_mul]

theorem rowPartner_ne_zero {K : Type*} [Field K] {s j : K}
    (hs : s ≠ 0) (hj : j ≠ 0) : rowPartner s j ≠ 0 := by
  exact mul_ne_zero hs (inv_ne_zero hj)

/-- A public orbit cover contains at least one tag from any factorization
of its nonzero public residue state. -/
theorem orbit_cover_pair {K : Type*} [Field K] (S : Finset K) {s x y : K}
    (hx : x ≠ 0) (hxy : x*y=s)
    (hcover : ∀ j : K, j ≠ 0 → j ∈ S ∨ rowPartner s j ∈ S) :
    x ∈ S ∨ y ∈ S := by
  have hpartner : rowPartner s x = y := by
    rw [rowPartner, ←hxy]
    calc x*y*x⁻¹ = y*(x*x⁻¹) := by ring
         _ = y := by rw [mul_inv_cancel₀ hx, mul_one]
  simpa only [hpartner] using hcover x hx

/-- Every orbit cover needs at least half of all nonzero residue tags. -/
theorem orbit_cover_card_bound {m : ℕ} (hm : m.Prime)
    (s : ZMod m) (hs : s ≠ 0) (S : Finset (ZMod m))
    (hcover : ∀ j : ZMod m, j ≠ 0 → j ∈ S ∨ rowPartner s j ∈ S) :
    m-1 ≤ 2*S.card := by
  classical
  let : Fact m.Prime := ⟨hm⟩
  let T : Finset (ZMod m) := Finset.univ.erase 0
  have hsub : T ⊆ S ∪ S.image (rowPartner s) := by
    intro j hj
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    obtain h | h := hcover j hj0
    · exact Finset.mem_union_left _ h
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨rowPartner s j,h,rowPartner_involutive hs⟩
  have hc : T.card = m-1 := by
    simp only [T, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod m)), Finset.card_univ,
      ZMod.card]
  rw [←hc]
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (by nlinarith only [Finset.card_image_le (f:=rowPartner s) (s:=S)]))

/-- Retain the smaller canonical representative of each public partner
pair, including every fixed point. -/
noncomputable def canonicalRowMask {m : ℕ} [NeZero m] (s : ZMod m) :
    Finset (ZMod m) :=
  Finset.univ.filter fun j => j ≠ 0 ∧ j.val ≤ (rowPartner s j).val

theorem canonicalRowMask_cover {m : ℕ} [Fact m.Prime]
    (s : ZMod m) (hs : s ≠ 0) (j : ZMod m) (hj : j ≠ 0) :
    j ∈ canonicalRowMask s ∨ rowPartner s j ∈ canonicalRowMask s := by
  classical
  obtain h | h := le_total j.val (rowPartner s j).val
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,h⟩)
  · apply Or.inr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,rowPartner_ne_zero hs hj,?_⟩
    simpa only [rowPartner_involutive hs] using h

theorem canonicalRowMask_zero_excluded {m : ℕ} [NeZero m] (s : ZMod m) :
    (0 : ZMod m) ∉ canonicalRowMask s := by
  simp only [canonicalRowMask, Finset.mem_filter, Finset.mem_univ, true_and,
    ne_eq, not_true_eq_false, false_and, not_false_eq_true]

/-- The mask retains whole original rows, using the public canonical
representative of each nonzero residue tag. The non-original tag zero
is always erased before constructing the product. -/
noncomputable def rowMaskNorm {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (S : Finset (ZMod m)) : ZMod N :=
  ∏ j ∈ S.erase 0, intervalProduct ((seedBase g m : (ZMod N)ˣ) : ZMod N)
    ((progressionSeed g N m j.val).step : ZMod N) (seedLength m)

/-- A retained true factor tag forces the original masked norm to vanish
in its prime field on the balanced gates. -/
theorem retained_factor_row_norm_zero {N p q m : ℕ} (hp : p.Prime) (hm : 4≤m)
    (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3)
    (hprod : N=p*q) (hN : m.Coprime N) (g : (ZMod N)ˣ)
    (S : Finset (ZMod m)) (htag : (p : ZMod m) ∈ S) (hpN : p ∣ N) :
    ZMod.castHom hpN (ZMod p) (rowMaskNorm g m S)=0 := by
  classical
  subst N
  obtain ⟨r,_,hr,_,hhit⟩ := balanced_forced_seed_prime_hit hp hm
    hprefixp hprefixq hpupper hqupper hN g
  have hp0 : (p : ZMod m) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff p m).mp hz
    have hm1 := Nat.eq_one_of_dvd_coprimes
      (hN.of_dvd_right (dvd_mul_right p q)) (dvd_refl m) hd
    omega
  unfold rowMaskNorm
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hp0,htag⟩)
  simp only [ZMod.val_natCast]
  rw [intervalProduct_map,hhit]
  unfold intervalProduct
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hr) (sub_self _)

/-- A public orbit cover gives a guaranteed nonunit masked norm on the
balanced family. No guarantee of a proper factor or cheap acquisition
of this norm is included. -/
theorem balanced_orbit_cover_norm_nonunit {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (hprefixp : m^2≤p) (hprefixq : m^2≤q)
    (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3)
    (hN : m.Coprime (p*q)) (g : (ZMod (p*q))ˣ)
    (S : Finset (ZMod m))
    (hcover : ∀ j : ZMod m, j ≠ 0 →
      j ∈ S ∨ rowPartner (p*q : ZMod m) j ∈ S) :
    ¬IsUnit (rowMaskNorm g m S) := by
  let : Fact m.Prime := ⟨hmprime⟩
  have hpcop : m.Coprime p := hN.of_dvd_right (dvd_mul_right p q)
  have hp0 : (p : ZMod m) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff p m).mp hz
    exact (hmprime.coprime_iff_not_dvd.mp hpcop) hd
  have htags : (p : ZMod m) ∈ S ∨ (q : ZMod m) ∈ S :=
    orbit_cover_pair S hp0 rfl hcover
  intro hu
  obtain htag | htag := htags
  · let : Fact p.Prime := ⟨hp⟩
    have hz := retained_factor_row_norm_zero hp hm hprefixp hprefixq
      hpupper hqupper rfl hN g S htag (dvd_mul_right p q)
    exact (hu.map (ZMod.castHom (dvd_mul_right p q) (ZMod p))).ne_zero hz
  · let : Fact q.Prime := ⟨hq⟩
    have hz := retained_factor_row_norm_zero hq hm hprefixq hprefixp
      hqupper hpupper (Nat.mul_comm p q) hN g S htag (dvd_mul_left q p)
    exact (hu.map (ZMod.castHom (dvd_mul_left q p) (ZMod q))).ne_zero hz

/-- Any row mask retains all but the globally bad rows it deletes from
the isolated set; each retained isolated row keeps every signed pole. -/
theorem masked_isolated_grid_card_degree {K : Type*} [Field K] {M J : ℕ}
    (point weight : Fin M × Fin J → K) (S G : Finset (Fin M))
    (hunique : ∀ i ∈ G, ∀ j k l, point (i,k)=point (j,l) → i=j ∧ k=l)
    (hx : ∀ ik, point ik ≠ 0)
    (hw : ∀ i ∈ S ∩ G, ∀ k, weight (i,k) ≠ 0)
    (U V : K[X]) (hU : U.coeff 0=1)
    (hUV : (U : PowerSeries K) *
      (∑ ik ∈ S ×ˢ (Finset.univ : Finset (Fin J)),
        PowerSeries.C (weight ik) *
          SemiprimeSeedMomentPoleRetention.positiveMoments (point ik)) =
      (V : PowerSeries K)) :
    (S ∩ G).card*J ≤ U.natDegree := by
  classical
  let I := S ×ˢ (Finset.univ : Finset (Fin J))
  let T := (S ∩ G) ×ˢ (Finset.univ : Finset (Fin J))
  have hdeg : T.card ≤ U.natDegree := by
    apply unique_label_denominator_degree I T point weight
      (Finset.product_subset_product (Finset.inter_subset_left) (Finset.Subset.refl _))
      (fun ik _ => hx ik)
      (by
        intro a ha b _ he
        have hg := (Finset.mem_inter.mp (Finset.mem_product.mp ha).1).2
        obtain ⟨hr,hk⟩ := hunique a.1 hg b.1 a.2 b.2 he.symm
        exact Prod.ext hr.symm hk.symm)
      (fun a ha => hw a.1 (Finset.mem_product.mp ha).1 a.2) U V hU hUV
  calc
    _ = T.card := by simp only [T, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ U.natDegree := hdeg

/-- The masked carrier cannot erase globally unique retained labels by
cancelling against other rows, including retained nonisolated rows. -/
theorem masked_isolated_grid_denominator_degree {K : Type*} [Field K] {M J : ℕ}
    (point weight : Fin M × Fin J → K) (S G : Finset (Fin M))
    (hunique : ∀ i ∈ G, ∀ j k l, point (i,k)=point (j,l) → i=j ∧ k=l)
    (hx : ∀ ik, point ik ≠ 0)
    (hw : ∀ i ∈ S ∩ G, ∀ k, weight (i,k) ≠ 0)
    (U V : K[X]) (hU : U.coeff 0=1)
    (hUV : (U : PowerSeries K) *
      (∑ ik ∈ S ×ˢ (Finset.univ : Finset (Fin J)),
        PowerSeries.C (weight ik) *
          SemiprimeSeedMomentPoleRetention.positiveMoments (point ik)) =
      (V : PowerSeries K)) :
    (S.card-(Finset.univ \ G).card)*J ≤ U.natDegree := by
  classical
  have hbad : (S \ G).card ≤ (Finset.univ \ G).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _))
  have hc := Finset.card_sdiff_add_card_inter S G
  have hrows : S.card-(Finset.univ \ G).card ≤ (S ∩ G).card := by omega
  exact (Nat.mul_le_mul_right J hrows).trans
    (masked_isolated_grid_card_degree point weight S G hunique hx hw U V hU hUV)

/-- Splitting a covering union into multiple masks does not reduce the
total dense degree charged to their retained globally isolated rows. -/
theorem masked_union_total_degree {ι : Type*} {M J : ℕ}
    (A : Finset ι) (S : ι → Finset (Fin M)) (G : Finset (Fin M)) (d : ι → ℕ)
    (hdegree : ∀ a ∈ A, (S a ∩ G).card*J ≤ d a) :
    ((A.biUnion S).card-(Finset.univ \ G).card)*J ≤ ∑ a ∈ A, d a := by
  classical
  have hbad : ((A.biUnion S) \ G).card ≤ (Finset.univ \ G).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _))
  have hc := Finset.card_sdiff_add_card_inter (A.biUnion S) G
  have hrows : (A.biUnion S).card-(Finset.univ \ G).card ≤ ((A.biUnion S) ∩ G).card := by
    omega
  calc
    _ ≤ ((A.biUnion S) ∩ G).card*J := Nat.mul_le_mul_right J hrows
    _ = (A.biUnion fun a => S a ∩ G).card*J := by rw [Finset.biUnion_inter]
    _ ≤ (∑ a ∈ A, (S a ∩ G).card)*J := Nat.mul_le_mul_right J Finset.card_biUnion_le
    _ = ∑ a ∈ A, (S a ∩ G).card*J := Finset.sum_mul ..
    _ ≤ ∑ a ∈ A, d a := Finset.sum_le_sum hdegree

/-- Purely ring-theoretic gate: no Gauss library or chosen local embedding is used. -/
theorem omitted_root_unit {A : Type*} [CommRing A]
    (g a u : A) (m : ℕ) (hg : g ^ 2 = a) (hu : u ^ m = 1)
    (hgate : IsUnit (a ^ m - 1)) : IsUnit (g - u) := by
  have hgpow : g ^ (2 * m) = a ^ m := by
    rw [pow_mul, hg]
  have hupow : u ^ (2 * m) = 1 := by
    rw [Nat.mul_comm, pow_mul, hu, one_pow]
  apply isUnit_of_dvd_unit _ hgate
  simpa only [hgpow, hupow] using sub_dvd_pow_sub_pow g u (2 * m)

/-- The same gate covers adding the omitted root, since the exponent is even. -/
theorem added_root_unit {A : Type*} [CommRing A]
    (g a u : A) (m : ℕ) (hg : g ^ 2 = a) (hu : u ^ m = 1)
    (hgate : IsUnit (a ^ m - 1)) : IsUnit (g + u) := by
  have hgpow : g ^ (2 * m) = a ^ m := by
    rw [pow_mul, hg]
  have hupow : (-u) ^ (2 * m) = 1 := by
    rw [pow_mul, neg_sq, ← pow_mul, Nat.mul_comm, pow_mul, hu, one_pow]
  apply isUnit_of_dvd_unit _ hgate
  simpa only [hgpow, hupow, sub_neg_eq_add] using
    sub_dvd_pow_sub_pow g (-u) (2 * m)

/-- A square equal to a unit makes the complete Gauss element a unit. -/
theorem complete_square_unit {A : Type*} [CommRing A]
    (g a : A) (hg : g ^ 2 = a) (ha : IsUnit a) : IsUnit g := by
  rw [← hg] at ha
  exact (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp ha

/-- An arbitrary multiplicative homomorphism, including a scalar norm when available,
    preserves the unit gate's conclusion. -/
theorem omitted_root_map_unit {A B : Type*} [CommRing A] [CommRing B]
    (f : A →* B) (g a u : A) (m : ℕ) (hg : g ^ 2 = a) (hu : u ^ m = 1)
    (hgate : IsUnit (a ^ m - 1)) : IsUnit (f (g - u)) := by
  exact (omitted_root_unit g a u m hg hu hgate).map f



/-- If the base field has no nontrivial m-th roots, a non-one scalar square
    cannot equal the square of any m-th root in a faithful extension. -/
theorem no_base_root_square_gap_unit {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (a g u : L) (b : K) (m : ℕ)
    (ha : a = f b) (hg : g ^ 2 = a) (hu : u ^ m = 1)
    (hbase : ∀ v : K, v ^ m = 1 → v = 1) (hb : b ≠ 1) :
    IsUnit (g ^ 2 - u ^ 2) := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hs : f b = u ^ 2 := by
    rw [← ha, ← hg]
    exact sub_eq_zero.mp hz
  have hbpow : b ^ m = 1 := by
    apply f.injective
    rw [map_pow, hs, ← pow_mul, Nat.mul_comm, pow_mul, hu, one_pow, map_one]
  exact hb (hbase b hbpow)

/-- In particular the honest Gauss puncture cannot vanish on such a source. -/
theorem no_base_root_omitted_unit {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (b : K) (g u : L) (m : ℕ)
    (hg : g ^ 2 = f b) (hu : u ^ m = 1)
    (hbase : ∀ v : K, v ^ m = 1 → v = 1) (hb : b ≠ 1) :
    IsUnit (g - u) := by
  have hs := no_base_root_square_gap_unit f (f b) g u b m rfl hg hu hbase hb
  have hp : IsUnit ((g - u) * (g + u)) := by
    convert hs using 1
    ring
  exact isUnit_of_mul_isUnit_left hp

/-- The same pointwise source obstruction handles adding any m-th root. -/
theorem no_base_root_added_unit {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (b : K) (g u : L) (m : ℕ)
    (hg : g ^ 2 = f b) (hu : u ^ m = 1)
    (hbase : ∀ v : K, v ^ m = 1 → v = 1) (hb : b ≠ 1) :
    IsUnit (g + u) := by
  have hs := no_base_root_square_gap_unit f (f b) g u b m rfl hg hu hbase hb
  have hp : IsUnit ((g - u) * (g + u)) := by
    convert hs using 1
    ring
  exact isUnit_of_mul_isUnit_right hp



/-- A prime m absent from the group order permits only the trivial m-th root. -/
theorem finite_group_no_prime_root {G : Type*} [Group G] [Fintype G]
    (m : ℕ) (hm : m.Prime) (hn : ¬ m ∣ Fintype.card G)
    (x : G) (hx : x ^ m = 1) : x = 1 := by
  have hd : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hx
  rcases hm.eq_one_or_self_of_dvd (orderOf x) hd with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact False.elim (hn (h ▸ orderOf_dvd_card))

/-- The elementary no-root obstruction in an arbitrary finite field. -/
theorem finite_field_no_prime_root {K : Type*} [Field K] [Fintype K]
    (m : ℕ) (hm : m.Prime) (hn : ¬ m ∣ Fintype.card K - 1)
    (x : K) (hx : x ^ m = 1) : x = 1 := by
  classical
  have hx0 : x ≠ 0 := by
    intro hz
    rw [hz, zero_pow hm.ne_zero] at hx
    exact zero_ne_one hx
  let xu : Kˣ := Units.mk0 x hx0
  have hxu : xu ^ m = 1 := by
    apply Units.ext
    simpa [xu] using hx
  have hcard : ¬ m ∣ Fintype.card Kˣ := by
    simpa only [Fintype.card_units] using hn
  have he := finite_group_no_prime_root m hm hcard xu hxu
  exact congrArg (fun u : Kˣ => (u : K)) he

/-- This pointwise gate avoids any exception-count estimate. -/
theorem root_free_scalar_gate_unit {K : Type*} [Field K]
    (m : ℕ) (a : K) (hbase : ∀ v : K, v ^ m = 1 → v = 1)
    (ha : a ≠ 1) : IsUnit (a ^ m - 1) := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  exact ha (hbase a (sub_eq_zero.mp hz))



/-- The signed auxiliary modulus is distinct from one in a larger hidden field. -/
theorem signed_modulus_ne_one (p m : ℕ) [Fact p.Prime]
    (hm : 2 ≤ m) (hmp : m + 1 < p) (epsilon : ZMod p)
    (hepsilon : epsilon = 1 ∨ epsilon = -1) : epsilon * (m : ZMod p) ≠ 1 := by
  rcases hepsilon with rfl | rfl
  · simp only [one_mul]
    intro he
    have hv := congrArg ZMod.val he
    have hmplt : m < p := by omega
    simp only [ZMod.val_natCast_of_lt hmplt, ZMod.val_one] at hv
    omega
  · simp only [neg_one_mul]
    intro he
    have hz : ((m + 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_add, Nat.cast_one]
      have hneg : (m : ZMod p) = -1 := by
        exact neg_eq_iff_eq_neg.mp he
      rw [hneg, neg_add_cancel]
    have hd : p ∣ m + 1 := (ZMod.natCast_eq_zero_iff (m + 1) p).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hmp) hd

/-- The exact integer Gauss gate is a unit on every hidden field without m-th roots. -/
theorem signed_gauss_scalar_gate_unit (p m : ℕ) [Fact p.Prime]
    (hm : m.Prime) (hodd : Odd m) (hmp : m + 1 < p)
    (hnot : ¬ m ∣ p - 1) (epsilon : ZMod p)
    (hepsilon : epsilon = 1 ∨ epsilon = -1) :
    IsUnit (epsilon * (m : ZMod p) ^ m - 1) := by
  have hbase : ∀ v : ZMod p, v ^ m = 1 → v = 1 := by
    apply finite_field_no_prime_root m hm
    simpa only [ZMod.card] using hnot
  have hscalar := root_free_scalar_gate_unit m (epsilon * (m : ZMod p)) hbase
    (signed_modulus_ne_one p m hm.two_le hmp epsilon hepsilon)
  have hepspow : epsilon ^ m = epsilon := by
    rcases hepsilon with rfl | rfl
    · simp
    · exact hodd.neg_one_pow
  simpa only [mul_pow, hepspow] using hscalar

/-- The actual large-prime/cofactor decomposition excludes auxiliary m-th roots. -/
theorem auxiliary_not_dvd_large_prime_cofactor (m R v : ℕ)
    (hm : m.Prime) (hR : R.Prime) (hv : 0 < v) (hvm : v < m) (hmR : m < R) :
    ¬ m ∣ v * R := by
  intro hd
  rcases hm.dvd_mul.mp hd with hdv | hdR
  · exact (Nat.not_dvd_of_pos_of_lt hv hvm) hdv
  · rcases hR.eq_one_or_self_of_dvd m hdR with he | he
    · exact hm.ne_one he
    · omega

/-- Both hidden-field no-root gates certify the exact public integer
Gauss gate as a unit over the unknown semiprime ring. -/
theorem signed_gauss_scalar_gate_semiprime_unit {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : m.Prime) (hodd : Odd m)
    (hmp : m+1<p) (hmq : m+1<q)
    (hnotp : ¬m ∣ p-1) (hnotq : ¬m ∣ q-1)
    (epsilon : ℤ) (hepsilon : epsilon=1 ∨ epsilon = -1) :
    IsUnit ((epsilon : ZMod (p*q))*(m : ZMod (p*q))^m-1) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hep : (epsilon : ZMod p)=1 ∨ (epsilon : ZMod p) = -1 := by
    rcases hepsilon with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  have heq : (epsilon : ZMod q)=1 ∨ (epsilon : ZMod q) = -1 := by
    rcases hepsilon with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  apply RiemannGaussian.SemiprimeIntervalJet.isUnit_of_prime_reductions hp hq
  · simpa only [map_sub, map_mul, map_pow, map_intCast, map_natCast, map_one] using
      (signed_gauss_scalar_gate_unit p m hm hodd hmp hnotp (epsilon : ZMod p) hep).ne_zero
  · simpa only [map_sub, map_mul, map_pow, map_intCast, map_natCast, map_one] using
      (signed_gauss_scalar_gate_unit q m hm hodd hmq hnotq (epsilon : ZMod q) heq).ne_zero

/-- Once the explicitly stated Gauss square identity is supplied, its
single-root puncture is a unit in every coefficient-ring extension. -/
theorem semiprime_gauss_puncture_unit {A : Type*} [CommRing A] {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : m.Prime) (hodd : Odd m)
    (hmp : m+1<p) (hmq : m+1<q)
    (hnotp : ¬m ∣ p-1) (hnotq : ¬m ∣ q-1)
    (epsilon : ℤ) (hepsilon : epsilon=1 ∨ epsilon = -1)
    (f : ZMod (p*q) →+* A) (g u : A)
    (hg : g^2=f ((epsilon : ZMod (p*q))*(m : ZMod (p*q))))
    (hu : u^m=1) : IsUnit (g-u) ∧ IsUnit (g+u) := by
  have hbase := signed_gauss_scalar_gate_semiprime_unit hp hq hm hodd hmp hmq
    hnotp hnotq epsilon hepsilon
  have hepspow : (epsilon : ZMod (p*q))^m=(epsilon : ZMod (p*q)) := by
    rcases hepsilon with rfl | rfl
    · simp
    · simpa only [Int.cast_neg, Int.cast_one] using hodd.neg_one_pow
  have hgate : IsUnit ((f ((epsilon : ZMod (p*q))*(m : ZMod (p*q))))^m-1) := by
    have hbasepow : IsUnit (((epsilon : ZMod (p*q))*(m : ZMod (p*q)))^m-1) := by
      simpa only [mul_pow, hepspow] using hbase
    simpa only [map_sub, map_pow, map_one] using hbasepow.map f
  exact ⟨omitted_root_unit g _ u m hg hu hgate, added_root_unit g _ u m hg hu hgate⟩

end RiemannGaussian.SemiprimeMaskAcquisitionObstruction
