import RiemannGaussian.SemiprimeDistinctAcquisitionObstruction

/-!
# Exact finite arithmetic for centered whole-family acquisition

Fixing the actual prime first reduces a necessary original quotient-row
hit to at most two tags. At a false tag, the exact source relation fixes
the linear carry and then the entire input residue modulo m squared.
The denominator and false-tag cancellations are discharged internally
under their explicit coprimality gates; no simple-root condition is used.

These finite identities support the investigation journal's classical
all-hit obstruction at square-root ray height for the literal public,
reflected, stationary and negative-cancellation linear windows. Fixed
polylogarithmic padding of height and width is covered classically.
The target-polynomial acquisition in soft-linear time and the infinite
actual-input counting argument remain classical, including the published
prime-gap and large-order inputs. They are not imported as Lean axioms.

The noncomputable tag catalog is a proof object indexed by the hidden
prime. This module supplies no factorization algorithm, coverage theorem,
norm evaluator or asymptotic bit-time or peak-memory theorem. Arbitrary
centers and unbounded Euclidean weights remain outside the obstruction.
The full guaranteed one-sixth factorization goal remains open.
-/

namespace RiemannGaussian.SemiprimeCenteredAcquisitionObstruction

open SemiprimeQuotientRows SemiprimeDistinctAcquisitionObstruction

open Polynomial

/-- All possible tags for a fixed hidden prime, ray and hit multiplier.
This finite proof catalog is not an algorithm for finding the hidden prime. -/
noncomputable def candidateTags {m : ℕ} [Fact m.Prime]
    (p v K a : ZMod m) : Finset (ZMod m) :=
  (((X : (ZMod m)[X])^2-C (((K+v*a)*p*(p-1))/(v*a))).roots.toFinset).image
    fun y => p-y

/-- Counting tags AFTER fixing the actual prime gives at most two tags,
without enumerating all lower and upper input states first. -/
theorem candidateTags_card_le {m : ℕ} [Fact m.Prime] (p v K a : ZMod m) :
    (candidateTags p v K a).card≤2 := by
  unfold candidateTags
  exact Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans
    (Polynomial.card_roots_X_pow_sub_C (R:=ZMod m) (n:=2) (by decide) _))

/-- Every tag satisfying the exact reduced original hit equation lies
in the two-tag catalog when v*a is nonzero. -/
theorem mem_candidateTags {m : ℕ} [Fact m.Prime] (p v K a j : ZMod m)
    (hva : v*a≠0)
    (hhit : (K+v*a)*p*(p-1)-v*a*(p-j)^2=0) :
    j∈candidateTags p v K a := by
  classical
  have hpow : (p-j)^2=((K+v*a)*p*(p-1))/(v*a) := by
    apply (eq_div_iff hva).mpr
    linear_combination -hhit
  apply Finset.mem_image.mpr
  refine ⟨p-j,Multiset.mem_toFinset.mpr ?_,by ring⟩
  apply (Polynomial.mem_roots
    (X_pow_sub_C_ne_zero (by decide : 0<(2 : ℕ)) _)).mpr
  change ((X : (ZMod m)[X])^2-C (((K+v*a)*p*(p-1))/(v*a))).eval (p-j)=0
  simp only [eval_sub,eval_pow,eval_X,eval_C,hpow,sub_self]

/-- Eliminate the public state from the necessary hit polynomial using
the ORIGINAL quotient relation, with the complete discarded m-squared term. -/
theorem weighted_original_tag_identity {N m j a b c t p v K : ℤ}
    (h : quotientRelation N m j a b c t) :
    weightedHitPolynomial p v K t (weightedOffset m j a b) N =
      (K+v*a)*p*(p-1)-v*a*(p-j)^2-v*m*b*(p-j)-v*m^2*c := by
  unfold quotientRelation at h
  unfold weightedHitPolynomial weightedOffset
  linear_combination v*h

/-- Two local polynomial hits at the SAME false tag and multiplier
have the same linear carry modulo m. No derivative/simple-root gate is used. -/
theorem false_tag_carry_unique {N₁ N₂ m j a b₁ b₂ c₁ c₂ t p v K : ℤ}
    (hm : m≠0) (hfalse : IsCoprime m (v*(p-j)))
    (hrow₁ : quotientRelation N₁ m j a b₁ c₁ t)
    (hrow₂ : quotientRelation N₂ m j a b₂ c₂ t)
    (hhit₁ : weightedHitPolynomial p v K t (weightedOffset m j a b₁) N₁
      ≡0 [ZMOD m^2])
    (hhit₂ : weightedHitPolynomial p v K t (weightedOffset m j a b₂) N₂
      ≡0 [ZMOD m^2]) : b₁ ≡b₂ [ZMOD m] := by
  have hpoly₁ := weighted_original_tag_identity hrow₁ (p:=p) (v:=v) (K:=K)
  have hpoly₂ := weighted_original_tag_identity hrow₂ (p:=p) (v:=v) (K:=K)
  have hd : m*m ∣ m*(v*(p-j)*(b₁-b₂)) := by
    obtain ⟨z,hz⟩ := (hhit₁.sub hhit₂).dvd
    rw [hpoly₁,hpoly₂] at hz
    refine ⟨z-v*(c₁-c₂),?_⟩
    linear_combination hz
  have hc : m ∣ v*(p-j)*(b₁-b₂) := Int.dvd_of_mul_dvd_mul_left hm hd
  have hb := hfalse.dvd_of_dvd_mul_left hc
  apply Int.modEq_iff_dvd.mpr
  simpa only [neg_sub] using dvd_neg.mpr hb

/-- Once the carry is fixed, legal rows with an invertible denominator
have the same COMPLETE two-digit input state. -/
theorem same_carry_input_state_unique {N₁ N₂ m j a b₁ b₂ c₁ c₂ t : ℤ}
    (ht : IsCoprime m t)
    (hrow₁ : quotientRelation N₁ m j a b₁ c₁ t)
    (hrow₂ : quotientRelation N₂ m j a b₂ c₂ t)
    (hb : b₁ ≡b₂ [ZMOD m]) : N₁ ≡N₂ [ZMOD m^2] := by
  obtain ⟨z,hz⟩ := hb.dvd
  have hd : m^2 ∣ t*(N₂-N₁) := by
    refine ⟨c₂-c₁-j*z,?_⟩
    unfold quotientRelation at hrow₁ hrow₂
    linear_combination hrow₁-hrow₂-j*m*hz
  exact Int.modEq_iff_dvd.mpr ((ht.pow_left (m:=2)).dvd_of_dvd_mul_left hd)

/-- Every false-tag local hit fixes at most one complete public state
for fixed prime, ray, tag, cofactor and integer hit multiplier. -/
theorem false_tag_input_state_unique {N₁ N₂ m j a b₁ b₂ c₁ c₂ t p v K : ℤ}
    (hm : m≠0) (hfalse : IsCoprime m (v*(p-j))) (ht : IsCoprime m t)
    (hrow₁ : quotientRelation N₁ m j a b₁ c₁ t)
    (hrow₂ : quotientRelation N₂ m j a b₂ c₂ t)
    (hhit₁ : weightedHitPolynomial p v K t (weightedOffset m j a b₁) N₁
      ≡0 [ZMOD m^2])
    (hhit₂ : weightedHitPolynomial p v K t (weightedOffset m j a b₂) N₂
      ≡0 [ZMOD m^2]) : N₁ ≡N₂ [ZMOD m^2] :=
  same_carry_input_state_unique ht hrow₁ hrow₂
    (false_tag_carry_unique hm hfalse hrow₁ hrow₂ hhit₁ hhit₂)

end RiemannGaussian.SemiprimeCenteredAcquisitionObstruction
