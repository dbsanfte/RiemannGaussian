import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeIneq
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe

/-! # Denominators and local membership for the division lattice

The local membership and finite-denominator arguments specialize the lemmas in
Alpöge's `GlobalSchurBounds.LinkPk`. We use only the prime decomposition,
lattice and span results needed for this comparison.
-/

namespace RiemannGaussian.AlpogeWindow.Localization
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

section
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem mem_of_locally (M : Submodule (𝓞 K) V) (x : V)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), InLoc v M x) : x ∈ M := by
  let I := M.comap (LinearMap.toSpanSingleton (𝓞 K) V x)
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩
    exact hs (hle (show s ∈ I from hsx))
  have h1 : (1 : 𝓞 K) ∈ I := htop ▸ Submodule.mem_top
  simpa only [one_smul] using (show (1 : 𝓞 K) • x ∈ M from h1)

omit [NumberField K] in
theorem exists_common_mul (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (h : ∀ y ∈ M, ∃ s : 𝓞 K, s ≠ 0 ∧ s • y ∈ N) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ y ∈ M, c • y ∈ N := by
  classical
  obtain ⟨S, hS⟩ := hM
  choose d hd hmem using fun y : S => h y.val (hS ▸ Submodule.subset_span y.property)
  let c := ∏ y : S, d y
  refine ⟨c, Finset.prod_ne_zero_iff.2 (fun y _ => hd y), ?_⟩
  change M ≤ N.comap (LinearMap.lsmul (𝓞 K) V c)
  rw [← hS, Submodule.span_le]
  intro y hy
  let i : S := ⟨y, hy⟩
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  change c • y ∈ N
  rw [show c = d i * b from hb, mul_comm, mul_smul]
  exact N.smul_mem _ (hmem i)

theorem locLe_zero {w : HeightOneSpectrum (𝓞 K)} {A B : Submodule (𝓞 K) V}
    (h : DV.LocLe w 0 A B) (x : V) (hx : x ∈ A) : InLoc w B x := by
  obtain ⟨s, hs, hsx⟩ := h x hx
  exact ⟨s, hs, by simpa only [pow_zero, Ideal.one_eq_top, Submodule.top_smul] using hsx⟩

variable [Module K V] [IsScalarTower (𝓞 K) K V]

theorem mem_span_of_multiple (M : Submodule (𝓞 K) V) (y : V) (d : 𝓞 K)
    (hd : d ≠ 0) (hy : d • y ∈ M) : y ∈ Submodule.span K (M : Set V) := by
  have h := (Submodule.span K (M : Set V)).smul_mem (algebraMap (𝓞 K) K d)⁻¹
    (Submodule.subset_span hy)
  rwa [← algebraMap_smul K d y, smul_smul, inv_mul_cancel₀
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd), one_smul] at h

theorem fg_of_clearing {M N : Submodule (𝓞 K) V} (hN : N.FG) (d : 𝓞 K)
    (hd : d ≠ 0) (h : ∀ y ∈ M, d • y ∈ N) : M.FG := by
  let f := LinearMap.lsmul (𝓞 K) V d
  have hinj : Function.Injective f := by
    intro x y hxy
    have h' : (algebraMap (𝓞 K) K d) • x = (algebraMap (𝓞 K) K d) • y := by
      simpa only [algebraMap_smul] using (show d • x = d • y from hxy)
    exact smul_right_injective _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd) h'
  have hle : M.map f ≤ N := Submodule.map_le_iff_le_comap.mpr h
  have : Module.Finite (𝓞 K) N := Module.Finite.iff_fg.2 hN
  have hfg := (IsNoetherian.noetherian ((M.map f).comap N.subtype)).map N.subtype
  rw [Submodule.map_comap_subtype, inf_eq_right.2 hle] at hfg
  exact Submodule.fg_of_fg_map_injective f hinj hfg

end

/-- Either the prime two or the host prime is an ordinary place away from the level. -/
theorem exists_ordinary_place (D : D7) (u : D.what₂.Word) :
    ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ (D.mem u).A.T ∧
      ¬ DV.InertK D (D.what₂.places.resChar w) := by
  have hfree : ∃ p : ℕ, p.Prime ∧ p ≠ (D.mem u).A.T ∧ ¬ DV.InertK D p := by
    by_cases hT : (D.mem u).A.T = 2
    · refine ⟨D.host.q, D.host.hyp.1, by rw [hT]; have := D.host.hyp.2.2.1; omega, ?_⟩
      simp [DV.InertK, Host.cls, primeClass, D.host.q_notMem_small]
    · refine ⟨2, Nat.prime_two, Ne.symm hT, ?_⟩
      simp [DV.InertK, Host.cls, primeClass, D.host.two_mem_small]
  obtain ⟨p, hp, hT, hfree⟩ := hfree
  have := J.span_prime_isMaximal p hp
  obtain ⟨P, hP, hOver⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.what₂.LL)))
  let v : HeightOneSpectrum (𝓞 D.what₂.LL) :=
    ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot (by simp [hp.ne_zero] : Ideal.span {(p : ℤ)} ≠ ⊥) P⟩
  let w := D.plEq.symm v
  have hw : D.plEq w = v := D.plEq.apply_symm_apply v
  have hmem := J.resChar_mem D w
  rw [hw] at hmem
  have hcon : ((D.what₂.places.resChar w : ℕ) : ℤ) ∈ Ideal.span {(p : ℤ)} := by
    rw [hOver.over, Ideal.mem_comap]
    simpa using hmem
  have hdvd : p ∣ D.what₂.places.resChar w := by exact_mod_cast Ideal.mem_span_singleton.mp hcon
  have heq := ((Nat.dvd_prime (D.what₂.places.resChar_prime w)).mp hdvd).resolve_left hp.ne_one
  exact ⟨w, heq ▸ hT, heq ▸ hfree⟩

end RiemannGaussian.AlpogeWindow.Localization
