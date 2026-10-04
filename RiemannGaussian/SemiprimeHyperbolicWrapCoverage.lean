/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWrapIndexRecovery

/-!
# Ratio-adaptive exact index forcing in a hyperbolic carry range

Using only the number of quotient bins actually needed strengthens the
widened source's pigeonhole witness: t*m is at most the factor quotient.
The exact seed identity then bounds the extra wrap beyond its canonical
carry by t*abs(extraWrap)<=4*m. This is a public hyperbolic source, with
uniform arbitrary-ratio exact collision and quadratic recovery coverage.

The quotient and seed index occur only in the proof. The constructor uses
N-only cached seeds and public denominator/carry ranges. Coverage and its
source input count do not complete the one-sixth bit-operation bound.
-/

namespace RiemannGaussian.SemiprimeHyperbolicWrapCoverage

open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open SemiprimeDensePeriodForcing SemiprimeWideWrapCoverage
open SemiprimeGroupSelection SemiprimeLocalOrderRouting SemiprimeWrapIndexRecovery
open SemiprimeCentreFreeCover

/-- Use the actual number of quotient bins rather than all m bins.
The SAME short exact index has both a ratio-scaled denominator and a
linear wrap bound, uniformly in the unknown quotient and seed index. -/
theorem scaled_quotient_pigeonhole {m x : ℕ} (hm : 1<m)
    (hx₀ : m≤x) (hx₁ : x≤m^2) {iSeed : ℤ}
    (hi₀ : 0 ≤ iSeed) (hi₁ : iSeed≤(wrapCap m : ℤ)) :
    ∃ t k : ℕ, 0<t ∧ t<m ∧ t*m≤x ∧ k≤2*m+1 ∧
      |(t : ℤ)*iSeed-(k : ℤ)*x|<(2*m : ℕ) := by
  have hxpos : 0<x := by omega
  have hxz : (0 : ℤ)<x := by exact_mod_cast hxpos
  by_cases hxsmall : x≤2*m
  · let k := (iSeed/(x : ℤ)).toNat
    have hk₀ : 0 ≤ iSeed/(x : ℤ) := Int.ediv_nonneg hi₀ hxz.le
    have hkcast : (k : ℤ)=iSeed/(x : ℤ) := Int.toNat_of_nonneg hk₀
    have hcap : wrapCap m≤(2*m+1)*x := by unfold wrapCap; nlinarith only [hm,hx₀]
    have hbound : iSeed≤((2*m+1 : ℕ) : ℤ)*x := by
      exact hi₁.trans (by exact_mod_cast hcap)
    have hdiv := Int.ediv_le_ediv hxz hbound
    rw [Int.mul_ediv_cancel (2*m+1 : ℕ) hxz.ne'] at hdiv
    have hrem₀ := Int.emod_nonneg iSeed hxz.ne'
    have hrem₁ := Int.emod_lt_of_pos iSeed hxz
    have he : iSeed-(k : ℤ)*x=iSeed%(x : ℤ) := by
      rw [hkcast]
      linear_combination -Int.emod_add_mul_ediv iSeed (x : ℤ)
    refine ⟨1,k,by omega,by omega,by simpa only [one_mul] using hx₀,by omega,?_⟩
    simpa only [Nat.cast_one,one_mul,he,abs_of_nonneg hrem₀] using
      hrem₁.trans_le (by exact_mod_cast hxsmall)
  · have hm₃ : 3≤m := by
      by_contra! hn
      have he : m=2 := by omega
      subst m
      norm_num only [Nat.reducePow] at hx₁
      omega
    let n : ℕ := x/(2*m)+2
    have hn : 1<n := by
      have hd₀ := Nat.zero_le (x/(2*m))
      dsimp only [n]
      omega
    have hmax : x<(m-1)*(2*m) := by
      have hs : m-1+1=m := by omega
      nlinarith only [hx₁,hm₃,hs]
    have hquot := (Nat.div_lt_iff_lt_mul (by positivity : 0<2*m)).mpr hmax
    have hnm : n≤m := by dsimp only [n]; omega
    have hsub : n-1=x/(2*m)+1 := by dsimp only [n]; omega
    have hdm := Nat.div_mul_le_self x (2*m)
    have hrem := Nat.mod_lt x (by positivity : 0<2*m)
    have hdiv := Nat.mod_add_div x (2*m)
    have hcap : x≤(n-1)*(2*m) := by rw [hsub]; nlinarith only [hrem,hdiv]
    have hscaled : (n-1)*m≤x := by rw [hsub]; nlinarith only [hdm,hxsmall]
    have htwice : (n-1)*(2*m)≤x+2*m := by rw [hsub]; nlinarith only [hdm]
    have hmul := Nat.mul_le_mul_right m htwice
    have htail : n-1≤x := by omega
    have hwide : (n-1)*wrapCap m≤(2*m+1)*x := by
      unfold wrapCap
      nlinarith only [hmul,htail,hxsmall]
    obtain ⟨s,t,hst,htn,hclose⟩ := period_index_pigeonhole hn
      (by positivity : 0<2*m) hxpos hcap (fun t => (t : ℤ)*iSeed)
    let d : ℤ := ((t : ℤ)*iSeed)/(x : ℤ)-((s : ℤ)*iSeed)/(x : ℤ)
    have hd₀ : 0≤d := by
      have he := Int.ediv_le_ediv hxz
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hst.le : (s : ℤ)≤t) hi₀)
      dsimp only [d]
      omega
    have htcap : t*wrapCap m≤(2*m+1)*x :=
      (Nat.mul_le_mul_right (wrapCap m) (by omega : t≤n-1)).trans hwide
    have hbound : (t : ℤ)*iSeed≤((2*m+1 : ℕ) : ℤ)*x := by
      have he := mul_le_mul_of_nonneg_left hi₁ (by positivity : (0 : ℤ)≤t)
      exact he.trans (by exact_mod_cast htcap)
    have htdiv := Int.ediv_le_ediv hxz hbound
    rw [Int.mul_ediv_cancel (2*m+1 : ℕ) hxz.ne'] at htdiv
    have hsdiv : 0≤((s : ℤ)*iSeed)/(x : ℤ) :=
      Int.ediv_nonneg (mul_nonneg (by positivity) hi₀) hxz.le
    have hd₁ : d≤(2*m+1 : ℕ) := by dsimp only [d]; omega
    let k := d.toNat
    have hkcast : (k : ℤ)=d := Int.toNat_of_nonneg hd₀
    have hsquot := Int.emod_add_mul_ediv ((s : ℤ)*iSeed) (x : ℤ)
    have htquot := Int.emod_add_mul_ediv ((t : ℤ)*iSeed) (x : ℤ)
    have he : ((t-s : ℕ) : ℤ)*iSeed-(k : ℤ)*x=
        (t : ℤ)*iSeed%(x : ℤ)-(s : ℤ)*iSeed%(x : ℤ) := by
      rw [hkcast]
      have hT : ((t-s : ℕ) : ℤ)=(t : ℤ)-(s : ℤ) := by omega
      rw [hT]
      dsimp only [d]
      linear_combination hsquot-htquot
    have hscale : (t-s)*m≤x :=
      (Nat.mul_le_mul_right m (by omega : t-s≤n-1)).trans hscaled
    exact ⟨t-s,k,by omega,by omega,hscale,by omega,by simpa only [he] using hclose⟩

/-- The factor product budget and the scaled denominator control the
quadratic cofactor term in the extra-carry estimate. -/
theorem scaled_cofactor_bound {m x q t : ℕ} (hm : 0<m)
    (hqx : q*x≤m^5) (htx : t*m≤x) : t^2*q≤m^3*x := by
  have ht₂ := Nat.pow_le_pow_left htx 2
  have hmul := Nat.mul_le_mul_right q ht₂
  have hqx₂ := Nat.mul_le_mul_right x hqx
  have hh : (t^2*q)*m^2≤(m^3*x)*m^2 := by
    nlinarith only [hmul,hqx₂]
  exact (Nat.mul_le_mul_right_iff (by positivity : 0<m^2)).mp hh

/-- The exact seed and short-index identities force the EXTRA wrap
past the canonical leading carry into a public hyperbolic budget. The
scaled cofactor bound comes from N, not a balanced-factor hypothesis. -/
theorem hyperbolic_wrap_budget {m x q t a j k : ℕ} {b iSeed i : ℤ}
    (hm : 1<m) (hx : m≤x) (ht : 0<t) (htm : t<m) (htx : t*m≤x)
    (ha : a≤m) (hj : j≤m) (hb : |b|≤(m : ℤ))
    (hq : t^2*q≤m^3*x)
    (hseed : (m : ℤ)^2*iSeed=(a : ℤ)*m*x+b*m-(a : ℤ)*j+q)
    (hindex : i=(t : ℤ)*iSeed-(k : ℤ)*x) (hi : |i|<(2*m : ℕ)) :
    (t : ℤ)*|(k : ℤ)-((a*t/m : ℕ) : ℤ)|≤(4*m : ℕ) := by
  let κ := a*t/m
  let r := a*t%m
  let u : ℤ := (k : ℤ)-κ
  have hmz : (2 : ℤ)≤m := by exact_mod_cast hm
  have hxm : (m : ℤ)≤x := by exact_mod_cast hx
  have htz : (t : ℤ)≤m := by exact_mod_cast htm.le
  have htxz : (t : ℤ)*m≤x := by exact_mod_cast htx
  have haz : (a : ℤ)≤m := by exact_mod_cast ha
  have hjz : (j : ℤ)≤m := by exact_mod_cast hj
  have hrz : (r : ℤ)≤m := by exact_mod_cast (Nat.mod_lt (a*t) (by omega : 0<m)).le
  have hcarry : (a : ℤ)*t=(m : ℤ)*κ+r := by
    have hh := Nat.mod_add_div (a*t) m
    dsimp only [κ,r]
    exact_mod_cast (by omega : a*t=m*(a*t/m)+a*t%m)
  have htransport : (m : ℤ)^2*u*x=(r : ℤ)*m*x+(t : ℤ)*b*m-
      (t : ℤ)*a*j+(t : ℤ)*q-(m : ℤ)^2*i := by
    dsimp only [u]
    linear_combination (t : ℤ)*hseed+(m : ℤ)^2*hindex+(m : ℤ)*x*hcarry
  have hT : (m : ℤ)^2*x*((t : ℤ)*u)=
      (t : ℤ)*r*m*x+(t : ℤ)^2*b*m-(t : ℤ)^2*a*j+
        (t : ℤ)^2*q-(t : ℤ)*(m : ℤ)^2*i := by
    linear_combination (t : ℤ)*htransport
  have htr := mul_le_mul htz hrz (by positivity : (0 : ℤ)≤r) (by positivity : (0 : ℤ)≤m)
  have hA : (t : ℤ)*r*m*x≤(m : ℤ)^3*x := by
    have hh := mul_le_mul_of_nonneg_right htr (by positivity : (0 : ℤ)≤(m : ℤ)*x)
    nlinarith only [hh]
  have ht₂ : (t : ℤ)^2≤x := by
    have hh := (Nat.mul_le_mul_left t htm.le).trans htx
    exact_mod_cast (by simpa only [pow_two] using hh : t^2≤x)
  have hsq : (t : ℤ)^2*(m : ℤ)^2≤(m : ℤ)^2*x := by
    have hh := mul_le_mul_of_nonneg_right ht₂ (sq_nonneg (m : ℤ))
    nlinarith only [hh]
  have hblo := mul_le_mul_of_nonneg_right (abs_le.mp hb).1
    (by positivity : (0 : ℤ)≤(t : ℤ)^2*m)
  have hbhi := mul_le_mul_of_nonneg_right (abs_le.mp hb).2
    (by positivity : (0 : ℤ)≤(t : ℤ)^2*m)
  have hB : -((m : ℤ)^2*x)≤(t : ℤ)^2*b*m ∧
      (t : ℤ)^2*b*m≤(m : ℤ)^2*x := by
    constructor <;> nlinarith only [hblo,hbhi,hsq]
  have haj := mul_le_mul haz hjz (by positivity : (0 : ℤ)≤j) (by positivity : (0 : ℤ)≤m)
  have hC : (t : ℤ)^2*a*j≤(m : ℤ)^2*x := by
    have hh := mul_le_mul_of_nonneg_left haj (sq_nonneg (t : ℤ))
    nlinarith only [hh,hsq]
  have hD : (t : ℤ)^2*q≤(m : ℤ)^3*x := by exact_mod_cast hq
  have hi' := abs_lt.mp hi
  have hilo := mul_le_mul_of_nonneg_left hi'.1.le
    (by positivity : (0 : ℤ)≤(t : ℤ)*(m : ℤ)^2)
  have hihi := mul_le_mul_of_nonneg_left hi'.2.le
    (by positivity : (0 : ℤ)≤(t : ℤ)*(m : ℤ)^2)
  have hEcap := mul_le_mul_of_nonneg_right htxz (by positivity : (0 : ℤ)≤2*(m : ℤ)^2)
  have hE : -2*((m : ℤ)^2*x)≤(t : ℤ)*(m : ℤ)^2*i ∧
      (t : ℤ)*(m : ℤ)^2*i≤2*((m : ℤ)^2*x) := by
    push_cast at hilo hihi
    constructor <;> nlinarith only [hilo,hihi,hEcap]
  have hA₀ : 0≤(t : ℤ)*r*m*x := by positivity
  have hC₀ : 0≤(t : ℤ)^2*a*j := by positivity
  have hD₀ : 0≤(t : ℤ)^2*q := by positivity
  have hxpos : 0<x := (Nat.mul_pos ht (by omega : 0<m)).trans_le htx
  have hM : (0 : ℤ)<(m : ℤ)^2*x := by positivity
  have hupper : (m : ℤ)^2*x*((t : ℤ)*u)≤
      (2*(m : ℤ)+3)*((m : ℤ)^2*x) := by
    nlinarith only [hT,hA,hB.2,hC₀,hD,hE.1]
  have hlower : -4*((m : ℤ)^2*x)≤(m : ℤ)^2*x*((t : ℤ)*u) := by
    nlinarith only [hT,hA₀,hB.1,hC,hD₀,hE.2]
  have hu : |(t : ℤ)*u|≤(4*m : ℕ) := by
    push_cast
    apply abs_le.mpr
    constructor <;> nlinarith only [hupper,hlower,hM,hmz]
  simpa only [abs_mul,abs_of_nonneg (by positivity : (0 : ℤ)≤t),u,κ] using hu

/-- The public extra-carry radius decreases with the denominator. -/
def extraWrapRadius (m t : ℕ) : ℕ := 4*m/t

/-- Reconstruct the nonnegative numerator wrap from the canonical
cached leading carry and one signed extra carry. -/
def shiftedWrap (N m j t : ℕ) (u : ℤ) : ℕ :=
  ((leadingCarry N m j t false : ℤ)+u).toNat

/-- Emit every public denominator and only its hyperbolic extra-carry
range. No factor quotient or seed index enters this constructor. -/
def hyperbolicRows (N m : ℕ) : List (ℕ×QuotientRow) :=
  (List.range (m-1)).flatMap fun r =>
    (List.range (m-1)).flatMap fun s =>
      (List.range (2*extraWrapRadius m (s+1)+1)).map fun v : ℕ =>
        let u : ℤ := (v : ℤ)-extraWrapRadius m (s+1)
        (r+1,wrappedRow N m (r+1) (s+1) (shiftedWrap N m (r+1) (s+1) u))

/-- Every signed extra carry in its public radius is emitted by the
literal constructor at the requested residue and denominator. -/
theorem hyperbolicRow_mem {N m j t : ℕ} {u : ℤ}
    (hj : 0<j) (hjm : j<m) (ht : 0<t) (htm : t<m)
    (hu : u.natAbs≤extraWrapRadius m t) :
    (j,wrappedRow N m j t (shiftedWrap N m j t u))∈hyperbolicRows N m := by
  apply List.mem_flatMap.mpr
  refine ⟨j-1,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨t-1,List.mem_range.mpr (by omega),?_⟩
  have hj' : j-1+1=j := by omega
  have ht' : t-1+1=t := by omega
  rw [hj',ht']
  have huabs : |u|≤(extraWrapRadius m t : ℤ) := by
    exact_mod_cast (by simpa only [Int.natCast_natAbs] using
      (show (u.natAbs : ℤ)≤extraWrapRadius m t by exact_mod_cast hu))
  let v := (u+(extraWrapRadius m t : ℤ)).toNat
  have hvcast : (v : ℤ)=u+extraWrapRadius m t :=
    Int.toNat_of_nonneg (by have hh := (abs_le.mp huabs).1; omega)
  have hv : v<2*extraWrapRadius m t+1 := by
    have hh := (abs_le.mp huabs).2
    omega
  change (j,wrappedRow N m j t (shiftedWrap N m j t u))∈
    (List.range (2*extraWrapRadius m t+1)).map (fun v : ℕ =>
      (j,wrappedRow N m j t (shiftedWrap N m j t ((v : ℤ)-extraWrapRadius m t))))
  apply List.mem_map.mpr
  refine ⟨v,List.mem_range.mpr hv,?_⟩
  have he : (v : ℤ)-extraWrapRadius m t=u := by rw [hvcast]; omega
  simp only [he]

/-- The true signed extra carry reconstructs the original full wrap. -/
theorem shiftedWrap_eq {N m j t k : ℕ} {u : ℤ}
    (hu : u=(k : ℤ)-(leadingCarry N m j t false : ℤ)) :
    shiftedWrap N m j t u=k := by
  unfold shiftedWrap
  rw [hu]
  have he : (leadingCarry N m j t false : ℤ)+
      ((k : ℤ)-(leadingCarry N m j t false : ℤ))=k := by ring
  rw [he,Int.toNat_natCast]

/-- Every factor ratio has an informative hyperbolic row at a short
EXACT factor index. The constructor uses only N and m. -/
theorem hyperbolicRows_index_coverage {p q m : ℕ} (hm : 1<m) (hp : 0<p)
    (hpq : p≤q) (hprefix : m^2≤p) (hN : m.Coprime (p*q)) (hsize : p*q≤m^6) :
    ∃ (t k : ℕ) (i : ℤ),
      (p%m,wrappedRow (p*q) m (p%m) t k)∈hyperbolicRows (p*q) m ∧
      0<t ∧ t<m ∧ t*m≤p/m ∧ k≤2*m+1 ∧ i.natAbs<2*m ∧
      (wrappedRow (p*q) m (p%m) t k).a≠0 ∧
      quadratic (wrappedRow (p*q) m (p%m) t k).a
        (wrappedRow (p*q) m (p%m) t k).b
          (wrappedRow (p*q) m (p%m) t k).c (p/m : ℕ)=(p : ℤ)*i := by
  have hm₀ : 0<m := by omega
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hj₀ : 0<p%m := by
    by_contra! hn
    have he : p%m=0 := by omega
    simp only [he,Nat.coprime_zero_left] at hj
    omega
  obtain ⟨iSeed,hiSeed,hquadSeed⟩ := row_index_exists hp hN
    (denseRow_relation (N:=p*q) (t:=1) hm₀ hj false)
  have hden : (denseRow (p*q) m (p%m) 1 false).t=(1 : ℤ) := rfl
  rw [hden,one_mul] at hiSeed
  change (m : ℤ)^2*iSeed=(seedRow (p*q) m (p%m)).a*p+
    (seedRow (p*q) m (p%m)).b*m-2*(seedRow (p*q) m (p%m)).a*(p%m : ℕ)+q at hiSeed
  change quadratic (seedRow (p*q) m (p%m)).a (seedRow (p*q) m (p%m)).b
    (seedRow (p*q) m (p%m)).c (p/m : ℕ)=(p : ℤ)*iSeed at hquadSeed
  have hiBounds := seed_index_bounds hm hpq hprefix hsize hiSeed
  obtain ⟨_hp,_hq,hx₀,hx₁⟩ := post_prefix_factor_bounds hm hpq hprefix hsize
  obtain ⟨t,k,ht,htm,htx,hk,hclose⟩ := scaled_quotient_pigeonhole hm hx₀ hx₁
    hiBounds.1 hiBounds.2
  let i : ℤ := (t : ℤ)*iSeed-(k : ℤ)*(p/m : ℕ)
  have hi : i.natAbs<2*m := by
    have hz : (i.natAbs : ℤ)<(2*m : ℕ) := by
      simpa only [Int.natCast_natAbs] using hclose
    exact_mod_cast hz
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hd := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hqx : q*(p/m)≤m^5 := by
    have hh := (Nat.mul_le_mul_right q (Nat.mul_div_le p m)).trans hsize
    have he : m^6=m*m^5 := by ring
    have hb : m*(q*(p/m))≤m*m^5 := by nlinarith only [hh,he]
    exact (Nat.mul_le_mul_left_iff hm₀).mp hb
  have hqscaled := scaled_cofactor_bound hm₀ hqx htx
  let a := representative (p*q) m (p%m) 1
  let b := (seedRow (p*q) m (p%m)).b
  have hseed : (m : ℤ)^2*iSeed=(a : ℤ)*m*(p/m : ℕ)+b*m-(a : ℤ)*(p%m : ℕ)+q := by
    change (m : ℤ)^2*iSeed=(a : ℤ)*p+b*m-2*(a : ℤ)*(p%m : ℕ)+q at hiSeed
    linear_combination hiSeed+(a : ℤ)*hcoord
  have hu := hyperbolic_wrap_budget hm hx₀ ht htm htx
    (Nat.mod_lt _ hm₀).le (Nat.mod_lt p hm₀).le
    (denseRow_b_bound (N:=p*q) (j:=p%m) (t:=1) hm false) hqscaled hseed rfl hclose
  let u : ℤ := (k : ℤ)-(leadingCarry (p*q) m (p%m) t false : ℤ)
  have hub : (t : ℤ)*|u|≤(4*m : ℕ) := by
    simpa only [u,leadingCarry,Bool.false_eq_true,ite_false,Nat.add_zero,a,representative] using hu
  have huNat : t*u.natAbs≤4*m := by
    have hh : ((t*u.natAbs : ℕ) : ℤ)≤(4*m : ℕ) := by
      simpa only [Nat.cast_mul,Int.natCast_natAbs] using hub
    exact_mod_cast hh
  have hur : u.natAbs≤extraWrapRadius m t := by
    apply (Nat.le_div_iff_mul_le ht).mpr
    simpa only [Nat.mul_comm] using huNat
  have hmem := hyperbolicRow_mem hj₀ (Nat.mod_lt p hm₀) ht htm hur (N:=p*q)
  rw [shiftedWrap_eq (by rfl)] at hmem
  exact ⟨t,k,i,hmem,ht,htm,htx,hk,hi,wrappedRow_a_ne_zero hm hN hj ht htm,
    wrappedRow_index hcoord hquadSeed⟩

/-- The smaller literal family retains a prime-field collision AND the
exact factor in its original integer recovery list, for every base. -/
theorem hyperbolic_prime_collision_coverage {p q m : ℕ} (hm : 1<m)
    (hp : p.Prime) (hpq : p≤q) (hprefix : m^2≤p) (hN : m.Coprime (p*q))
    (hsize : p*q≤m^6) (g : (ZMod p)ˣ) :
    ∃ (t k : ℕ) (i : ℤ),
      (p%m,wrappedRow (p*q) m (p%m) t k)∈hyperbolicRows (p*q) m ∧
      0<t ∧ t<m ∧ t*m≤p/m ∧ k≤2*m+1 ∧ i.natAbs<2*m ∧
      wrappedValue t k (progressionSeed g (p*q) m (p%m))=g^((m : ℤ)^2*i) ∧
      (p : ℤ)∈wrappedRecovery (p*q) m t k
        (progressionSeed g (p*q) m (p%m)) i := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t,k,i,hmem,ht,htm,htx,hk,hi,ha,hquad⟩ :=
    hyperbolicRows_index_coverage hm hp.pos hpq hprefix hN hsize
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ)
      (wrappedRow (p*q) m (p%m) t k).a (wrappedRow (p*q) m (p%m) t k).b
      (wrappedRow (p*q) m (p%m) t k).c (t : ℤ) := by
    simpa only [Nat.cast_mul,wrappedRow] using
      wrappedRow_relation (N:=p*q) (t:=t) (k:=k) (by omega : 0<m) hj
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have hd := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hperiod : g^((p : ℤ)-1)=1 := by
    have h := ZMod.units_pow_card_sub_one_eq_one p g
    have hz : g^((p-1 : ℕ) : ℤ)=1 := by simpa only [zpow_natCast] using h
    simpa only [Nat.cast_sub hp.one_le,Nat.cast_one] using hz
  have hhit := quotient_row_power_hit g hcoord hrel hquad
    (by exact_mod_cast hp.ne_zero) hperiod
  have hroot := integerRoots_complete ha (quotient_row_recovery_equation hcoord hrel hquad)
  refine ⟨t,k,i,hmem,ht,htm,htx,hk,hi,?_,?_⟩
  · rw [wrappedValue_eq]
    exact hhit
  · rw [wrappedRecovery_eq]
    exact hroot

/-- Both the descriptor and its successful full row belong to the public
source. Only the proof uses the unavailable prime-field projection. -/
theorem public_hyperbolic_coverage {p q m : ℕ} (hm : 1<m)
    (hp : p.Prime) (hpq : p≤q) (hprefix : m^2≤p) (hN : m.Coprime (p*q))
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) :
    let π : (ZMod (p*q))ˣ→*(ZMod p)ˣ :=
      Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
    ∃ (t k : ℕ) (i : ℤ),
      progressionSeed g (p*q) m (p%m)∈progressionSeeds g (p*q) m ∧
      (p%m,wrappedRow (p*q) m (p%m) t k)∈hyperbolicRows (p*q) m ∧
      0<t ∧ t<m ∧ t*m≤p/m ∧ k≤2*m+1 ∧ i.natAbs<2*m ∧
      π (wrappedValue t k (progressionSeed g (p*q) m (p%m)))=(π g)^((m : ℤ)^2*i) ∧
      (p : ℤ)∈wrappedRecovery (p*q) m t k (progressionSeed g (p*q) m (p%m)) i := by
  let π : (ZMod (p*q))ˣ→*(ZMod p)ˣ :=
    Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
  obtain ⟨t,k,i,hmem,ht,htm,htx,hk,hi,hhit,hroot⟩ :=
    hyperbolic_prime_collision_coverage hm hp hpq hprefix hN hsize (π g)
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hN.of_dvd_right (dvd_mul_right p q)
  have hj₀ : 0<p%m := by
    by_contra! hn
    have he : p%m=0 := by omega
    simp only [he,Nat.coprime_zero_left] at hj
    omega
  refine ⟨t,k,i,progressionSeed_mem g hj₀ (Nat.mod_lt p (by omega)),
    hmem,ht,htm,htx,hk,hi,?_,?_⟩
  · rw [wrappedValue_map]
    exact hhit
  · rw [wrappedRecovery_base_independent g (π g)]
    exact hroot

/-- Failure of the original complete quadratic prefix discharges the
factor-size and inverse hypotheses of the smaller family's coverage. -/
theorem public_hyperbolic_after_prefix {p q m : ℕ} (hm : 1<m)
    (hp : p.Prime) (hpq : p≤q) (hcover : m^2<p*q) (hsize : p*q≤m^6)
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q) m=none)
    (g : (ZMod (p*q))ˣ) :
    let π : (ZMod (p*q))ˣ→*(ZMod p)ˣ :=
      Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
    ∃ (t k : ℕ) (i : ℤ),
      progressionSeed g (p*q) m (p%m)∈progressionSeeds g (p*q) m ∧
      (p%m,wrappedRow (p*q) m (p%m) t k)∈hyperbolicRows (p*q) m ∧
      0<t ∧ t<m ∧ t*m≤p/m ∧ k≤2*m+1 ∧ i.natAbs<2*m ∧
      π (wrappedValue t k (progressionSeed g (p*q) m (p%m)))=(π g)^((m : ℤ)^2*i) ∧
      (p : ℤ)∈wrappedRecovery (p*q) m t k (progressionSeed g (p*q) m (p%m)) i := by
  have hprefix := SemiprimeStrassenPrefix.prefix_none_excludes_small_prime
    hcover hp (dvd_mul_right p q) hnone
  have hmm : m≤m^2 := by nlinarith only [hm]
  have hc := SemiprimeStrassenPrefix.prefix_none_coprime_integer
    hcover hnone (by omega : 0<m) hmm
  exact public_hyperbolic_coverage hm hp hpq hprefix.le hc.symm hsize g

/-- Uniform literal-row and exact-recovery coverage at the actual N-only
least-prime modulus. It includes prime squares in the coverage statement. -/
theorem actual_public_hyperbolic_after_prefix {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (g : (ZMod (p*q))ˣ) :
    let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
    let π : (ZMod (p*q))ˣ→*(ZMod p)ˣ :=
      Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom
    ∃ (t k : ℕ) (i : ℤ),
      progressionSeed g (p*q) m (p%m)∈progressionSeeds g (p*q) m ∧
      (p%m,wrappedRow (p*q) m (p%m) t k)∈hyperbolicRows (p*q) m ∧
      0<t ∧ t<m ∧ t*m≤p/m ∧ k≤2*m+1 ∧ i.natAbs<2*m ∧
      π (wrappedValue t k (progressionSeed g (p*q) m (p%m)))=(π g)^((m : ℤ)^2*i) ∧
      (p : ℤ)∈wrappedRecovery (p*q) m t k (progressionSeed g (p*q) m (p%m)) i := by
  have hN : 0<p*q := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 1<SemiprimeEuclidRowBudget.publicRowModulus (p*q) := by omega
  have hbudget := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hmBounds.1 6)
  exact public_hyperbolic_after_prefix hm hp hpq
    (public_modulus_prefix_below_input hN hB) hbudget hnone g

/-- The guaranteed collision in the smaller family is recoverable by
the existing saturation-complete blocked reader on an actual public long
outcome. The successful source tags are retained in this interface. -/
theorem long_public_route_hyperbolic_recoverable_column {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q)
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q))=none)
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∃ (t k : ℕ) (i : ℤ),
        progressionSeed h (p*q) m (p%m)∈progressionSeeds h (p*q) m ∧
        (p%m,wrappedRow (p*q) m (p%m) t k)∈hyperbolicRows (p*q) m ∧
        0<t ∧ t<m ∧ t*m≤p/m ∧ k≤2*m+1 ∧ i.natAbs<2*m ∧
        ∃ d, recoverBlockedWrapColumn h m t (progressionSeed h (p*q) m (p%m)) i=some d := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
  let g := ZMod.unitOfCoprime a hc
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 1<m := by dsimp only [m]; omega
  have hsize : p*q≤m^6 := (SemiprimeLehmanCoverage.sixthWidth_upper (p*q)).trans
    (Nat.pow_le_pow_left hmBounds.1 6)
  have hcover : m^2<p*q := public_modulus_prefix_below_input hN hB
  have hprefix := SemiprimeStrassenPrefix.prefix_none_excludes_small_prime
    hcover hp (dvd_mul_right p q) hnone
  have hj : 1<p%m := by
    have he := long_true_residue_ne_one hp hpq.le hm hprefix.le hsize g hlong
    have hmm : m≤m^2 := by nlinarith only [hm]
    have hcop := SemiprimeStrassenPrefix.prefix_none_coprime_integer
      hcover hnone (by omega : 0<m) hmm
    have hjcop : (p%m).Coprime m := by
      change Nat.gcd (p%m) m=1
      rw [←Nat.gcd_rec]
      exact hcop.symm.of_dvd_right (dvd_mul_right p q)
    have hjpos : 0<p%m := by
      by_contra! hn
      have hz : p%m=0 := by omega
      simp only [hz,Nat.coprime_zero_left] at hjcop
      omega
    omega
  have hperiods := long_carry_periods hm hj (Nat.mod_lt p (by omega)) g hlong
  obtain ⟨t,k,i,hcache,hrow,ht,htm,htx,hk,hi,hhit,hroot⟩ :=
    actual_public_hyperbolic_after_prefix hp hq hpq.le hB hnone (projectedUnit g m)
  have hkold : k≤wrapCap m := by unfold wrapCap; nlinarith only [hm,hk]
  obtain ⟨d,hd⟩ := recoverWrapColumn_succeeds_of_exact_hit hp hq hpq hm
    (projectedUnit g m) _ _ hkold hperiods.1 hperiods.2 hhit hroot
  refine ⟨hc,t,k,i,hcache,hrow,ht,htm,htx,hk,hi,d,?_⟩
  rw [recoverBlockedWrapColumn_eq (by omega)]
  exact hd

/-- The public emitted-row count for one residue, including duplicate
clamped wraps. Counting duplicates makes this a literal construction bound. -/
def residueRowCount (m : ℕ) : ℕ :=
  ∑ s∈Finset.range (m-1), (2*extraWrapRadius m (s+1)+1)

/-- Convert the literal constructor's list sum to its arithmetic count. -/
theorem list_sum_range_eq_finset (f : ℕ→ℕ) (n : ℕ) :
    ((List.range n).map f).sum=∑ s∈Finset.range n, f s := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ,Finset.sum_range_succ,ih]

/-- Exact output count for the entire smaller public family. -/
theorem hyperbolicRows_length (N m : ℕ) :
    (hyperbolicRows N m).length=(m-1)*residueRowCount m := by
  simp only [hyperbolicRows,List.length_flatMap,List.length_map,List.length_range,
    list_sum_range_eq_finset,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    Nat.cast_id,residueRowCount]

/-- The decreasing carry radii have a harmonic total at each residue. -/
theorem residueRowCount_harmonic_bound (m : ℕ) :
    (residueRowCount m : ℝ)≤((m-1 : ℕ) : ℝ)+8*(m : ℝ)*(harmonic m : ℝ) := by
  have hf : (∑ s∈Finset.range (m-1), ((4*m/(s+1) : ℕ) : ℝ))≤
      4*(m : ℝ)*(harmonic m : ℝ) := by
    calc
      _≤∑ s∈Finset.range (m-1), ((4*m : ℕ) : ℝ)/((s+1 : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun _ _ => Nat.cast_div_le)
      _=4*(m : ℝ)*∑ s∈Finset.range (m-1), (((s+1 : ℕ) : ℝ))⁻¹ := by
        simp only [div_eq_mul_inv,Finset.mul_sum,Nat.cast_mul,Nat.cast_ofNat]
      _≤4*(m : ℝ)*∑ s∈Finset.range m, (((s+1 : ℕ) : ℝ))⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono (Nat.sub_le m 1)
        · intro _ _ _
          positivity
      _=4*(m : ℝ)*(harmonic m : ℝ) := by
        simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  have he : (residueRowCount m : ℝ)=
      2*(∑ s∈Finset.range (m-1), ((4*m/(s+1) : ℕ) : ℝ))+((m-1 : ℕ) : ℝ) := by
    simp [residueRowCount,extraWrapRadius,Finset.sum_add_distrib,Finset.mul_sum]
  rw [he]
  nlinarith only [hf]

/-- The full public family has a proved quadratic-times-logarithm output
bound. It is still larger than the intended near-linear bit budget. -/
theorem hyperbolicRows_log_bound (N m : ℕ) :
    ((hyperbolicRows N m).length : ℝ)≤((m-1 : ℕ) : ℝ)*
      (((m-1 : ℕ) : ℝ)+8*(m : ℝ)*(1+Real.log m)) := by
  have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log m)
    (by positivity : (0 : ℝ)≤8*(m : ℝ))
  have hb : (residueRowCount m : ℝ)≤
      ((m-1 : ℕ) : ℝ)+8*(m : ℝ)*(1+Real.log m) := by
    nlinarith only [residueRowCount_harmonic_bound m,hh]
  rw [hyperbolicRows_length,Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- Expanding this particular public list still incurs quadratic output
size. This does not exclude a different compressed acquisition algorithm. -/
theorem hyperbolicRows_output_lower_bound (N m : ℕ) :
    (m-1)^2≤(hyperbolicRows N m).length := by
  have hh : m-1≤residueRowCount m := by
    calc
      _=∑ _s∈Finset.range (m-1), (1 : ℕ) := by simp
      _≤residueRowCount m := by
        unfold residueRowCount
        apply Finset.sum_le_sum
        intro _ _
        unfold extraWrapRadius
        omega
  rw [hyperbolicRows_length,pow_two]
  exact Nat.mul_le_mul_left (m-1) hh

end RiemannGaussian.SemiprimeHyperbolicWrapCoverage
