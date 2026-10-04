/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeDenseEuclidDescent
import RiemannGaussian.SemiprimeEuclidRowBudget
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Prime.Factorial

/-!
# The unbalanced-factor obstruction in the complete dense recovery source

The actual candidate routine uses a floor square root and integer division.
Its candidates are first enclosed near genuine real roots, so a recovery
obstruction does not silently assume candidate soundness. The remaining
claims concern exact integer recovery, not every prime-field power collision
or every possible factorizer using the same source.
-/

namespace RiemannGaussian.SemiprimeDenseRatioObstruction

open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries

/-- The literal integer square root brackets the real square root. -/
theorem sqrt_bracket {d : ℤ} (hd : 0≤d) :
    (Int.sqrt d : ℝ)≤Real.sqrt (d : ℝ) ∧
      Real.sqrt (d : ℝ)<(Int.sqrt d : ℝ)+1 := by
  have hn := Int.toNat_of_nonneg hd
  have hlo : (Int.sqrt d)^2≤d := by
    simpa only [Int.sqrt,←Nat.cast_pow,hn] using
      (show ((Nat.sqrt d.toNat)^2 : ℤ)≤(d.toNat : ℤ) by
        exact_mod_cast Nat.sqrt_le' d.toNat)
  have hhi : d<(Int.sqrt d+1)^2 := by
    simpa only [Int.sqrt,Nat.cast_one,Nat.cast_add,Nat.cast_pow,hn] using
      (show (d.toNat : ℤ)<((Nat.sqrt d.toNat+1)^2 : ℤ) by
        exact_mod_cast Nat.lt_succ_sqrt' d.toNat)
  have hs : (Int.sqrt d : ℝ)≥0 := by exact_mod_cast Int.sqrt_nonneg d
  have hr := Real.sqrt_nonneg (d : ℝ)
  have he := Real.sq_sqrt (show (0 : ℝ)≤d by exact_mod_cast hd)
  have hl : (Int.sqrt d : ℝ)^2≤(d : ℝ) := by exact_mod_cast hlo
  have hh : (d : ℝ)<((Int.sqrt d : ℝ)+1)^2 := by exact_mod_cast hhi
  constructor <;> nlinarith

/-- Each floor-divided quadratic candidate lies within two of a real root.
This includes negative denominators and both square-root orientations. -/
theorem quotient_candidate_enclosure {a L C x : ℤ} (ha : a≠0)
    (hd : 0≤L^2-4*a*C) (negative : Bool)
    (hx : x=(-L+(if negative then -Int.sqrt (L^2-4*a*C)
      else Int.sqrt (L^2-4*a*C)))/(2*a)) :
    ∃ y : ℝ, |y-(x : ℝ)|≤2 ∧ (a : ℝ)*y^2+(L : ℝ)*y+(C : ℝ)=0 := by
  let d : ℤ := L^2-4*a*C
  let σ : ℝ := if negative then -1 else 1
  let n : ℤ := -L+(if negative then -Int.sqrt d else Int.sqrt d)
  let r : ℤ := n%(2*a)
  let v : ℝ := σ*Real.sqrt (d : ℝ)
  let y : ℝ := (-(L : ℝ)+v)/(2*(a : ℝ))
  have haR : (a : ℝ)≠0 := by exact_mod_cast ha
  have hden : 2*a≠0 := mul_ne_zero (by decide) ha
  have hdenR : 2*(a : ℝ)≠0 := mul_ne_zero (by norm_num) haR
  have hσ : |σ|=1 ∧ σ^2=1 := by cases negative <;> norm_num [σ]
  have hroot : v^2=(d : ℝ) := by
    dsimp only [v]
    rw [mul_pow,hσ.2,one_mul,Real.sq_sqrt (by exact_mod_cast hd)]
  have hy : y*(2*(a : ℝ))=-(L : ℝ)+v := div_mul_cancel₀ _ hdenR
  have he := Int.emod_add_mul_ediv n (2*a)
  change r+(2*a)*(n/(2*a))=n at he
  change x=n/(2*a) at hx
  rw [←hx] at he
  have hquo : (r : ℝ)+2*(a : ℝ)*(x : ℝ)=
      -(L : ℝ)+σ*(Int.sqrt d : ℝ) := by
    cases negative <;> simpa [n,σ] using
      (show (r : ℝ)+(2*(a : ℝ))*(x : ℝ)=(n : ℝ) by exact_mod_cast he)
  have hr₀ : (0 : ℝ)≤r := by exact_mod_cast Int.emod_nonneg n hden
  have hr₁ : (r : ℝ)<2*|(a : ℝ)| := by
    have h : r<2*|a| := by
      simpa [Int.natCast_natAbs,abs_mul] using Int.emod_lt n hden
    exact_mod_cast h
  have ha₁ : (1 : ℝ)≤|(a : ℝ)| := by
    have h : (1 : ℤ)≤|a| := by
      rcases lt_or_gt_of_ne ha with h | h
      · rw [abs_of_neg h]; omega
      · rw [abs_of_pos h]; omega
    exact_mod_cast h
  have hb := sqrt_bracket hd
  have hgap : |Real.sqrt (d : ℝ)-(Int.sqrt d : ℝ)|≤1 := by
    rw [abs_of_nonneg (by linarith only [hb.1])]
    linarith only [hb.2]
  have hdiff : (y-(x : ℝ))*(2*(a : ℝ))=
      σ*(Real.sqrt (d : ℝ)-(Int.sqrt d : ℝ))+(r : ℝ) := by
    dsimp only [v] at hy
    linear_combination hy-hquo
  have hdabs := abs_add_le (σ*(Real.sqrt (d : ℝ)-(Int.sqrt d : ℝ))) (r : ℝ)
  simp only [←hdiff,abs_mul,hσ.1,one_mul,abs_of_nonneg hr₀,
    abs_of_pos (by norm_num : (0 : ℝ)<2)] at hdabs
  have hclose : |y-(x : ℝ)|≤2 := by
    nlinarith only [hdabs,hgap,hr₁,ha₁]
  refine ⟨y,hclose,?_⟩
  have hdR : (d : ℝ)=(L : ℝ)^2-4*(a : ℝ)*(C : ℝ) := by
    simp [d]
  have hv : v=2*(a : ℝ)*y+(L : ℝ) := by linarith only [hy]
  rw [hv,hdR] at hroot
  have hzero : 4*(a : ℝ)*((a : ℝ)*y^2+(L : ℝ)*y+(C : ℝ))=0 := by
    nlinarith only [hroot]
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by norm_num) haR)

/-- Membership in the actual list gives an enclosure, not presumed exactness. -/
theorem integerRoots_enclosure {a L C x : ℤ} (ha : a≠0)
    (hx : x∈integerRoots a L C) :
    ∃ y : ℝ, |y-(x : ℝ)|≤2 ∧ (a : ℝ)*y^2+(L : ℝ)*y+(C : ℝ)=0 := by
  unfold integerRoots at hx
  dsimp only at hx
  split_ifs at hx with hd
  · simp only [List.not_mem_nil] at hx
  · have hd₀ : 0≤L^2-4*a*C := by omega
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx | hx
    · exact quotient_candidate_enclosure ha hd₀ false hx
    · exact quotient_candidate_enclosure ha hd₀ true hx

/-- A real quadratic root retains both coefficient-magnitude balances. -/
theorem real_root_balance {a L C y : ℝ} (hC : 0≤C)
    (hy : a*y^2+L*y+C=0) :
    C≤|a| * y^2+|L| * |y| ∧ |a| * y^2≤C+|L| * |y| := by
  have he : a*y^2+L*y=-C := by linarith only [hy]
  have hf : L*y+C=-(a*y^2) := by linarith only [hy]
  have h₁ := abs_add_le (a*y^2) (L*y)
  have h₂ := abs_add_le (L*y) C
  simp only [he,abs_neg,abs_of_nonneg hC,abs_mul,abs_pow,sq_abs] at h₁
  simp only [hf,abs_neg,abs_of_nonneg hC,abs_mul,abs_pow,sq_abs] at h₂
  exact ⟨h₁,by linarith only [h₂]⟩

/-- A uniform cofactor band excludes BOTH actual floor-rounded prime candidates.
Every bounded row is covered, before imposing any quotient congruence. -/
theorem candidate_gap_miss {p q m D t : ℕ} {a L x : ℤ}
    (hp : 2≤p) (ht : 0<t) (htm : t≤m)
    (ha : 1≤|a|) (ham : |a|≤m) (hL : |L|≤D)
    (hgap : m*(p+6)+2*D+8<q)
    (hmag : |x|=(p : ℤ) ∨ |x|=(q : ℤ)) :
    x∉integerRoots a L (t*p*q : ℕ) := by
  have ha₀ : a≠0 := by intro hz; rw [hz,abs_zero] at ha; omega
  have hpR : (2 : ℝ)≤p := by exact_mod_cast hp
  have htR : (1 : ℝ)≤t := by exact_mod_cast ht
  have htmR : (t : ℝ)≤m := by exact_mod_cast htm
  have hmR : (1 : ℝ)≤m := by linarith only [htR,htmR]
  have haR : (1 : ℝ)≤|(a : ℝ)| := by exact_mod_cast ha
  have hamR : |(a : ℝ)|≤(m : ℝ) := by exact_mod_cast ham
  have hLR : |(L : ℝ)|≤(D : ℝ) := by exact_mod_cast hL
  have hgapR : (m : ℝ)*((p : ℝ)+6)+2*(D : ℝ)+8<(q : ℝ) := by
    exact_mod_cast hgap
  have hqR : (2 : ℝ)≤q := by
    have h := mul_le_mul_of_nonneg_right hmR (show (0 : ℝ)≤(p : ℝ)+6 by linarith)
    have hD : (0 : ℝ)≤D := Nat.cast_nonneg D
    nlinarith only [h,hgapR,hpR,hD]
  have hp₀ : (0 : ℝ)<p := by linarith only [hpR]
  have hq₀ : (0 : ℝ)<q := by linarith only [hqR]
  have hC : (0 : ℝ)≤(t : ℝ)*p*q := by positivity
  have hlow : (p : ℝ)*q≤(t : ℝ)*p*q := by
    nlinarith only [mul_le_mul_of_nonneg_right htR (by positivity : (0 : ℝ)≤(p : ℝ)*q)]
  have hupper : (t : ℝ)*p*q≤(m : ℝ)*p*q := by
    nlinarith only [mul_le_mul_of_nonneg_right htmR (by positivity : (0 : ℝ)≤(p : ℝ)*q)]
  intro hx
  obtain ⟨y,hy,hroot⟩ := integerRoots_enclosure ha₀ hx
  simp only [Nat.cast_mul,Int.cast_natCast,Int.cast_mul] at hroot
  have hnear : |(|y|-|(x : ℝ)|)|≤2 :=
    (abs_abs_sub_abs_le_abs_sub y (x : ℝ)).trans hy
  rcases hmag with hmag | hmag
  · have hmagR : |(x : ℝ)|=(p : ℝ) := by exact_mod_cast hmag
    rw [hmagR] at hnear
    have hbal := (real_root_balance hC hroot).1
    have habs : |y|≤(p : ℝ)+2 := by
      have h := (abs_le.mp hnear).2
      linarith only [h]
    have hsq : y^2≤((p : ℝ)+2)^2 := by
      nlinarith only [sq_abs y,habs,abs_nonneg y,hpR]
    have h₁ := mul_le_mul hamR hsq (sq_nonneg y) (Nat.cast_nonneg m)
    have h₂ := mul_le_mul hLR habs (abs_nonneg y) (Nat.cast_nonneg D)
    have hmain : (p : ℝ)*q≤(m : ℝ)*((p : ℝ)+2)^2+(D : ℝ)*((p : ℝ)+2) := by
      linarith only [hlow,hbal,h₁,h₂]
    have hs : ((p : ℝ)+2)^2≤(p : ℝ)*((p : ℝ)+6) := by nlinarith only [hpR]
    have hd : (p : ℝ)+2≤2*(p : ℝ) := by linarith only [hpR]
    have hsm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg m)
    have hdD := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg D)
    have hg : (m : ℝ)*((p : ℝ)+6)+2*(D : ℝ)<(q : ℝ) := by linarith only [hgapR]
    have hg' := mul_lt_mul_of_pos_left hg hp₀
    nlinarith only [hmain,hsm,hdD,hg']
  · have hmagR : |(x : ℝ)|=(q : ℝ) := by exact_mod_cast hmag
    rw [hmagR] at hnear
    have hbal := (real_root_balance hC hroot).2
    have habs : |y|≤(q : ℝ)+2 := by
      have h := (abs_le.mp hnear).2
      linarith only [h]
    have hylo : (q : ℝ)-2≤|y| := by
      have h := (abs_le.mp hnear).1
      linarith only [h]
    have hsq : ((q : ℝ)-2)^2≤y^2 := by
      nlinarith only [hylo,hqR,sq_abs y]
    have h₁ := mul_le_mul_of_nonneg_right haR (sq_nonneg y)
    have h₂ := mul_le_mul hLR habs (abs_nonneg y) (Nat.cast_nonneg D)
    have hmain : ((q : ℝ)-2)^2≤(m : ℝ)*p*q+(D : ℝ)*((q : ℝ)+2) := by
      nlinarith only [hsq,h₁,hbal,hupper,h₂]
    have hd : (q : ℝ)+2≤2*(q : ℝ) := by linarith only [hqR]
    have hdD := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg D)
    have hg : (m : ℝ)*(p : ℝ)+2*(D : ℝ)+4<(q : ℝ) := by
      have hm₀ : (0 : ℝ)≤m := Nat.cast_nonneg m
      nlinarith only [hgapR,hm₀]
    have hg' := mul_lt_mul_of_pos_left hg hq₀
    nlinarith only [hmain,hdD,hg']

/-- Both emitted numerator orientations keep a uniformly bounded magnitude. -/
theorem dense_leading_bound {N m j t : ℕ} (hm : 0<m) (negative : Bool) :
    |(denseRow N m j t negative).a|≤(m : ℤ) := by
  have hr : (representative N m j t : ℤ)<m := by exact_mod_cast Nat.mod_lt _ hm
  have hr₀ : (0 : ℤ)≤representative N m j t := by positivity
  cases negative <;> simp only [denseRow,liftRow,if_false,if_true,Bool.false_eq_true,
    sub_zero] <;> apply abs_le.mpr <;> omega

/-- The actual uncentered cached coefficient has magnitude at most 2*m^2. -/
theorem rawLinear_bound {N m j t : ℕ} (hm : 1<m) (hjm : j<m)
    (ht : 0<t) (htm : t<m) (negative : Bool) :
    |rawLinear N m j t negative|≤2*(m : ℤ)^2 := by
  have hsb := abs_le.mp (denseRow_b_bound (N:=N) (j:=j) (t:=1) hm false)
  change -(m : ℤ)≤(seedRow N m j).b ∧ (seedRow N m j).b≤m at hsb
  have htz : (t : ℤ)≤m := by exact_mod_cast htm.le
  have hjz : (j : ℤ)≤m := by exact_mod_cast hjm.le
  have hkz : (leadingCarry N m j t negative : ℤ)≤m := by
    exact_mod_cast (leadingCarry_bound (by omega : 0<m) ht htm negative).le
  have htb₀ := mul_le_mul_of_nonneg_left hsb.1 (by positivity : (0 : ℤ)≤t)
  have htb₁ := mul_le_mul_of_nonneg_left hsb.2 (by positivity : (0 : ℤ)≤t)
  have htmul : (t : ℤ)*m≤(m : ℤ)^2 := by
    nlinarith only [htz,show (0 : ℤ)≤m by positivity]
  have hjk₀ : (0 : ℤ)≤(j : ℤ)*leadingCarry N m j t negative := by positivity
  have hjk₁ : (j : ℤ)*leadingCarry N m j t negative≤(m : ℤ)^2 := by
    have h := mul_le_mul hjz hkz
      (by positivity : (0 : ℤ)≤leadingCarry N m j t negative)
      (by positivity : (0 : ℤ)≤m)
    simpa only [pow_two] using h
  unfold rawLinear
  apply abs_le.mpr
  constructor <;> nlinarith only [htb₀,htb₁,htmul,hjk₀,hjk₁]

/-- The complete recovery coefficient retains a linear-radius cubic envelope. -/
theorem recoveryLinear_bound {m j K R : ℕ} {a b I : ℤ}
    (hjm : j≤m) (ha : |a|≤m) (hb : |b|≤(K : ℤ)*m) (hI : I.natAbs≤R) :
    |b*(m : ℤ)-2*a*j-(m : ℤ)^2*I|≤(((R+K+2)*m^2 : ℕ) : ℤ) := by
  have hm₀ : (0 : ℤ)≤m := by positivity
  have hj₀ : (0 : ℤ)≤j := by positivity
  have hjz : (j : ℤ)≤m := by exact_mod_cast hjm
  have hIb : |I|≤(R : ℤ) := by
    have h : (I.natAbs : ℤ)≤R := by exact_mod_cast hI
    simpa only [Int.natCast_natAbs] using h
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hI' := abs_le.mp hIb
  have hbm₀ := mul_le_mul_of_nonneg_right hb'.1 hm₀
  have hbm₁ := mul_le_mul_of_nonneg_right hb'.2 hm₀
  have haj₀ := mul_le_mul_of_nonneg_right ha'.1 hj₀
  have haj₁ := mul_le_mul_of_nonneg_right ha'.2 hj₀
  have hmj : (m : ℤ)*j≤(m : ℤ)^2 := by nlinarith only [hjz,hm₀]
  have hIm₀ := mul_le_mul_of_nonneg_left hI'.1 (sq_nonneg (m : ℤ))
  have hIm₁ := mul_le_mul_of_nonneg_left hI'.2 (sq_nonneg (m : ℤ))
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_pow]
  apply abs_le.mpr
  constructor <;> nlinarith only [hbm₀,hbm₁,haj₀,haj₁,hmj,hIm₀,hIm₁]

/-- Every cached dense row and orientation misses both factors in this band.
The full literal floor-rounded candidate list is excluded, independently of g. -/
theorem progressionRecovery_no_factors {G : Type*} [CommGroup G] (g : G)
    {p q m j t R : ℕ} (hp : 2≤p) (hm : 1<m) (hN : m.Coprime (p*q))
    (hj : j.Coprime m) (hjm : j<m) (ht : 0<t) (htm : t<m)
    (negative : Bool) {I : ℤ} (hI : I.natAbs≤R)
    (hgap : m*(p+6)+2*((R+2*m+2)*m^2)+8<q) :
    ∀ x∈progressionRecovery (p*q) m t negative
      (progressionSeed g (p*q) m j) I, x.natAbs≠p ∧ x.natAbs≠q := by
  have haeq := denseRow_leading_carry (p*q) m j t negative
  change (denseRow (p*q) m j t negative).a=(carryRow (p*q) m j t negative).a at haeq
  have ha : (carryRow (p*q) m j t negative).a≠0 := by
    rw [←haeq]
    exact denseRow_a_ne_zero hm hN hj ht htm negative
  have hab : |(carryRow (p*q) m j t negative).a|≤(m : ℤ) := by
    rw [←haeq]
    exact dense_leading_bound (by omega) negative
  have ha₁ : (1 : ℤ)≤|(carryRow (p*q) m j t negative).a| := by
    rcases lt_or_gt_of_ne ha with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  have hb : |(carryRow (p*q) m j t negative).b|≤(2*m : ℕ)*(m : ℤ) := by
    simpa only [carryRow,Nat.cast_mul,Nat.cast_ofNat,pow_two,mul_assoc] using
      rawLinear_bound (N:=p*q) hm hjm ht htm negative
  have hL := recoveryLinear_bound hjm.le hab hb hI
  intro x hx
  rw [progressionRecovery_eq] at hx
  have hx' : x∈integerRoots (carryRow (p*q) m j t negative).a
      ((carryRow (p*q) m j t negative).b*m-
        2*(carryRow (p*q) m j t negative).a*j-(m : ℤ)^2*I) (t*p*q : ℕ) := by
    simpa only [Nat.mul_assoc] using hx
  constructor
  · intro hp'
    have hmag : |x|=(p : ℤ) := by rw [←Int.natCast_natAbs,hp']
    exact candidate_gap_miss hp ht htm.le ha₁ hab hL hgap (Or.inl hmag) hx'
  · intro hq'
    have hmag : |x|=(q : ℤ) := by rw [←Int.natCast_natAbs,hq']
    exact candidate_gap_miss hp ht htm.le ha₁ hab hL hgap (Or.inr hmag) hx'

/-- Every proper divisor of a two-prime input is one of its two primes. -/
theorem proper_semiprime_divisor {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hd : SemiprimeGroupSelection.ProperDivisor (p*q) d) : d=p ∨ d=q := by
  by_cases hpd : p∣d
  · obtain ⟨k,rfl⟩ := hpd
    have hk : k∣q := Nat.dvd_of_mul_dvd_mul_left hp.pos hd.2.2
    rcases hq.eq_one_or_self_of_dvd k hk with hk | hk
    · exact Or.inl (by rw [hk,Nat.mul_one])
    · rw [hk] at hd
      exact False.elim (lt_irrefl _ hd.2.1)
  · have hc : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
    have hdq : d∣q := hc.dvd_of_dvd_mul_left hd.2.2
    rcases hq.eq_one_or_self_of_dvd d hdq with hd₁ | hdq
    · rw [hd₁] at hd
      exact False.elim (lt_irrefl _ hd.1)
    · exact Or.inr hdq

/-- Taking candidate absolute values and validating divisibility still
recovers no proper factor anywhere in the complete cached family in this band. -/
theorem progressionRecovery_no_proper {G : Type*} [CommGroup G] (g : G)
    {p q m j t R : ℕ} (hp : p.Prime) (hq : q.Prime) (hm : 1<m)
    (hN : m.Coprime (p*q)) (hj : j.Coprime m) (hjm : j<m)
    (ht : 0<t) (htm : t<m) (negative : Bool) {I : ℤ} (hI : I.natAbs≤R)
    (hgap : m*(p+6)+2*((R+2*m+2)*m^2)+8<q) :
    ∀ x∈progressionRecovery (p*q) m t negative
      (progressionSeed g (p*q) m j) I,
      ¬SemiprimeGroupSelection.ProperDivisor (p*q) x.natAbs := by
  intro x hx hd
  have h := progressionRecovery_no_factors g hp.two_le hm hN hj hjm ht htm
    negative hI hgap x hx
  rcases proper_semiprime_divisor hp hq hd with hd | hd
  · exact h.1 hd
  · exact h.2 hd

/-- The original centered dense quadratics have the same all-row obstruction,
with their tighter coefficient envelope and every signed rounded candidate. -/
theorem denseRecovery_no_proper {p q m j t R : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hm : 1<m) (hN : m.Coprime (p*q)) (hj : j.Coprime m) (hjm : j<m)
    (ht : 0<t) (htm : t<m) (negative : Bool) {I : ℤ} (hI : I.natAbs≤R)
    (hgap : m*(p+6)+2*((R+3)*m^2)+8<q) :
    ∀ x∈integerRoots (denseRow (p*q) m j t negative).a
      ((denseRow (p*q) m j t negative).b*m-
        2*(denseRow (p*q) m j t negative).a*j-(m : ℤ)^2*I) (t*(p*q) : ℕ),
      ¬SemiprimeGroupSelection.ProperDivisor (p*q) x.natAbs := by
  have ha := denseRow_a_ne_zero hm hN hj ht htm negative
  have hab := dense_leading_bound (N:=p*q) (j:=j) (t:=t) (by omega : 0<m) negative
  have ha₁ : (1 : ℤ)≤|(denseRow (p*q) m j t negative).a| := by
    rcases lt_or_gt_of_ne ha with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  have hb : |(denseRow (p*q) m j t negative).b|≤(1 : ℤ)*m := by
    simpa only [one_mul] using denseRow_b_bound (N:=p*q) (j:=j) (t:=t) hm negative
  have hL := recoveryLinear_bound hjm.le hab hb hI
  simp only [Nat.add_assoc] at hL
  intro x hx hd
  have hx' : x∈integerRoots (denseRow (p*q) m j t negative).a
      ((denseRow (p*q) m j t negative).b*m-
        2*(denseRow (p*q) m j t negative).a*j-(m : ℤ)^2*I) (t*p*q : ℕ) := by
    simpa only [Nat.mul_assoc] using hx
  have hmag : |x|=(p : ℤ) ∨ |x|=(q : ℤ) := by
    rcases proper_semiprime_divisor hp hq hd with he | he
    · exact Or.inl (by rw [←Int.natCast_natAbs,he])
    · exact Or.inr (by rw [←Int.natCast_natAbs,he])
  exact candidate_gap_miss hp.two_le ht htm.le ha₁ hab hL hgap hmag hx'

/-- Smaller prime in the source-exact failure control. -/
def controlP : ℕ := 50021

/-- Cofactor in the same failure control. -/
def controlQ : ℕ := 20000003

/-- The public input; factors are used only to prove the negative statement. -/
def controlN : ℕ := controlP*controlQ

/-- The actual least-prime ceiling-sixth-root modulus, verified below. -/
def controlM : ℕ := 101

/-- The entire prescribed signed cached baby radius. -/
def controlR : ℕ := 5*controlM+15

/-- Prime factors, prefix checks and the strict uniform rounding-safe gap. -/
theorem control_arithmetic :
    controlP.Prime ∧ controlQ.Prime ∧ controlM.Prime ∧
      controlM.Coprime controlN ∧ 4*controlM^2<controlP ∧ controlP<controlQ ∧
      controlN≤controlM^6 ∧
      controlM*(controlP+6)+2*((controlR+2*controlM+2)*controlM^2)+8<controlQ := by
  norm_num [controlP,controlQ,controlM,controlN,controlR,Nat.Coprime,Nat.gcd]

/-- The input survives even the enlarged 4*m^2 factorial prefix.
This follows from prime bounds, without constructing the factorial. -/
theorem control_prefix_coprime : controlN.Coprime (4*controlM^2).factorial := by
  have hp := control_arithmetic.1
  have hq := control_arithmetic.2.1
  have hlarge := control_arithmetic.2.2.2.2.1
  have hpq := control_arithmetic.2.2.2.2.2.1
  have hpC : controlP.Coprime (4*controlM^2).factorial :=
    hp.coprime_factorial_of_lt hlarge
  have hqC : controlQ.Coprime (4*controlM^2).factorial :=
    hq.coprime_factorial_of_lt (hlarge.trans hpq)
  have hc : (controlP*controlQ).Coprime (4*controlM^2).factorial := hpC.mul_left hqC
  unfold controlN
  exact hc

/-- The failure input has the literal public ceiling-sixth-root width 101. -/
theorem control_sixthWidth : SemiprimeLehmanCoverage.sixthWidth controlN=101 := by
  unfold SemiprimeLehmanCoverage.sixthWidth
  apply (Nat.find_eq_iff _).mpr
  constructor
  · norm_num [controlN,controlP,controlQ]
  · intro k hk hkn
    have hk₁ : k≤100 := by omega
    have hpow := Nat.pow_le_pow_left hk₁ 6
    have hl : (100 : ℕ)^6<controlN := by norm_num [controlN,controlP,controlQ]
    omega

/-- The original N-only least-prime selector really chooses 101 here. -/
theorem control_publicRowModulus : SemiprimeEuclidRowBudget.publicRowModulus controlN=controlM := by
  unfold SemiprimeEuclidRowBudget.publicRowModulus
  simp only [control_sixthWidth,max_eq_right (by norm_num : (1 : ℕ)≤101)]
  unfold SemiprimeEuclidRowBudget.publicPrimeAtLeast
  apply (Nat.find_eq_iff _).mpr
  constructor
  · norm_num [controlM]
  · intro k hk hkn
    have hk₀ : 101≤k := hkn.2
    have hk₁ : k<101 := by simpa [controlM] using hk
    omega

/-- The complete actual cached source misses exact factor recovery here:
all 100 residues, all 100 positive denominators, both orientations, every
signed index in the full radius, every base, and signed rounded candidates. -/
theorem control_no_recovery {G : Type*} [CommGroup G] (g : G)
    {j t : ℕ} (hj : j∈SemiprimeDenseCarryBoundary.residues controlM)
    (ht : t∈SemiprimeDenseCarryBoundary.residues controlM)
    (negative : Bool) {I : ℤ} (hI : I.natAbs≤controlR) :
    ∀ x∈progressionRecovery controlN controlM t negative
      (progressionSeed g controlN controlM j) I,
      ¬SemiprimeGroupSelection.ProperDivisor controlN x.natAbs := by
  have hja := SemiprimeDenseCarryBoundary.mem_residues.mp hj
  have hta := SemiprimeDenseCarryBoundary.mem_residues.mp ht
  have hc : j.Coprime controlM :=
    SemiprimeDenseCarryBoundary.residue_coprime control_arithmetic.2.2.1 hj
  exact progressionRecovery_no_proper g control_arithmetic.1 control_arithmetic.2.1
    (by norm_num [controlM]) control_arithmetic.2.2.2.1 hc hja.2 hta.1 hta.2
    negative hI control_arithmetic.2.2.2.2.2.2.2

/-- The original centered rows also miss every proper rounded candidate,
even in the larger cached radius; their original balanced radius is smaller. -/
theorem control_dense_no_recovery {j t : ℕ}
    (hj : j∈SemiprimeDenseCarryBoundary.residues controlM)
    (ht : t∈SemiprimeDenseCarryBoundary.residues controlM)
    (negative : Bool) {I : ℤ} (hI : I.natAbs≤controlR) :
    ∀ x∈integerRoots (denseRow controlN controlM j t negative).a
      ((denseRow controlN controlM j t negative).b*controlM-
        2*(denseRow controlN controlM j t negative).a*j-(controlM : ℤ)^2*I)
      (t*controlN : ℕ),
      ¬SemiprimeGroupSelection.ProperDivisor controlN x.natAbs := by
  have hja := SemiprimeDenseCarryBoundary.mem_residues.mp hj
  have hta := SemiprimeDenseCarryBoundary.mem_residues.mp ht
  have hc : j.Coprime controlM :=
    SemiprimeDenseCarryBoundary.residue_coprime control_arithmetic.2.2.1 hj
  exact denseRecovery_no_proper control_arithmetic.1 control_arithmetic.2.1
    (by norm_num [controlM]) control_arithmetic.2.2.2.1 hc hja.2 hta.1 hta.2
    negative hI (by norm_num [controlM,controlP,controlQ,controlR])

end RiemannGaussian.SemiprimeDenseRatioObstruction
