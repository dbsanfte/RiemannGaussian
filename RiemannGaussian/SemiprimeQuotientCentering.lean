/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeQuotientRows

/-!
# Target-preserving public centering of quotient rows

The original quadratic is retained alongside its public integer shift.
The RH-path unit-phase identity preserves the complete residual GCD.
Balanced factor boxes provide a shorter common index interval, without a
hidden-factor input or a baby/giant matrix. This is a construction and
coverage theorem, not a one-sixth factoring or bit-complexity theorem.
-/

namespace RiemannGaussian.SemiprimeQuotientCentering

open SemiprimeQuotientRows

/-- Shift along the trivial linear direction, keeping the original row
available separately. The Euclidean coordinates and division count survive. -/
def shiftRow (m j : ℕ) (k : ℤ) (z : QuotientRow) : QuotientRow :=
  { z with b := z.b-k*m, c := z.c-k*j }

/-- The public shift preserves the exact quotient class. -/
theorem shiftRow_relation {N m j : ℕ} {z : QuotientRow}
    (hz : quotientRelation N m j z.a z.b z.c z.t) (k : ℤ) :
    quotientRelation N m j (shiftRow m j k z).a (shiftRow m j k z).b
      (shiftRow m j k z).c (shiftRow m j k z).t := by
  simpa only [shiftRow, neg_mul, sub_eq_add_neg] using quotientRelation_shift hz (-k)

/-- The full polynomial loses precisely k copies of the trivial linear
row; the quadratic leading coordinate is retained. -/
theorem shiftRow_quadratic (m j : ℕ) (k x : ℤ) (z : QuotientRow) :
    quadratic (shiftRow m j k z).a (shiftRow m j k z).b (shiftRow m j k z).c x=
      quadratic z.a z.b z.c x-k*((m : ℤ)*x+j) := by
  simp only [shiftRow,quadratic]
  ring

/-- The giant exponent and collision index have the same public shift. -/
theorem shiftRow_giant (m j : ℕ) (k : ℤ) (z : QuotientRow) :
    giantExponent m j (shiftRow m j k z).a (shiftRow m j k z).b (shiftRow m j k z).c=
      giantExponent m j z.a z.b z.c-k*(m : ℤ)^2 := by
  simp only [shiftRow,giantExponent]
  ring

/-- The candidate recovery polynomial is unchanged when its retained
index is transported with the row. No collision channel is discarded. -/
theorem shiftRow_recovery (N m j : ℕ) (k i : ℤ) (z : QuotientRow) :
    integerRoots (shiftRow m j k z).a
        ((shiftRow m j k z).b*m-2*(shiftRow m j k z).a*j-(m : ℤ)^2*(i-k))
        ((shiftRow m j k z).t*N)=
      integerRoots z.a (z.b*m-2*z.a*j-(m : ℤ)^2*i) (z.t*N) := by
  simp only [shiftRow]
  congr 1
  ring

/-- A center phase factors from the ORIGINAL difference only when the
baby target is shifted too. This identity works over every public ring. -/
theorem shiftRow_residual {R : Type*} [CommRing R] (g : Rˣ)
    (m j : ℕ) (k i : ℤ) (z : QuotientRow) :
    ((g^giantExponent m j (shiftRow m j k z).a (shiftRow m j k z).b
        (shiftRow m j k z).c : Rˣ) : R)-((g^((m : ℤ)^2*(i-k)) : Rˣ) : R)=
      ((g^(-k*(m : ℤ)^2) : Rˣ) : R)*
        (((g^giantExponent m j z.a z.b z.c : Rˣ) : R)-
          ((g^((m : ℤ)^2*i) : Rˣ) : R)) := by
  rw [shiftRow_giant]
  have h₁ : giantExponent m j z.a z.b z.c-k*(m : ℤ)^2=
      -k*(m : ℤ)^2+giantExponent m j z.a z.b z.c := by ring
  have h₂ : (m : ℤ)^2*(i-k)=-k*(m : ℤ)^2+(m : ℤ)^2*i := by ring
  rw [h₁,h₂,zpow_add,zpow_add,Units.val_mul,Units.val_mul,mul_sub]

/-- Exact public GCD preservation includes prime powers and saturation.
The existing RH cancellation theorem supplies the unit transport. -/
theorem shiftRow_residual_gcd {N : ℕ} (g : (ZMod N)ˣ)
    (m j : ℕ) (k i : ℤ) (z : QuotientRow) :
    N.gcd (((g^giantExponent m j (shiftRow m j k z).a (shiftRow m j k z).b
        (shiftRow m j k z).c : (ZMod N)ˣ) : ZMod N)-
          ((g^((m : ℤ)^2*(i-k)) : (ZMod N)ˣ) : ZMod N)).val=
      N.gcd (((g^giantExponent m j z.a z.b z.c : (ZMod N)ˣ) : ZMod N)-
        ((g^((m : ℤ)^2*i) : (ZMod N)ˣ) : ZMod N)).val := by
  rw [shiftRow_residual]
  exact SemiprimeRHCancellation.unit_mul_gcd_eq _ _

/-- Public lower endpoint of the signed factor sum. Its sign is kept
before applying the interval estimate. -/
def lowerSum (N m j : ℕ) (a b t : ℤ) : ℤ :=
  a*(if 0≤a then (N/2).sqrt else N.sqrt)+t*N.sqrt+b*m-2*a*j

/-- Public upper endpoint, retaining the same offset and orientation. -/
def upperSum (N m j : ℕ) (a b t : ℤ) : ℤ :=
  a*(if 0≤a then N.sqrt else (N/2).sqrt)+t*(2*N).sqrt+b*m-2*a*j

/-- Round the public interval midpoint to the nearest m-squared shift.
Integer division handles either signed orientation. -/
def publicShift (N m j : ℕ) (a b t : ℤ) : ℤ :=
  (lowerSum N m j a b t+upperSum N m j a b t+(m : ℤ)^2)/(2*(m : ℤ)^2)

/-- The packet keeps its original quadratic and the exact public shift,
so normalization does not erase recovery or phase information. -/
structure CenteredPacket where
  /-- The actual Euclidean row before the new phase extraction. -/
  original : QuotientRow
  /-- The public integer change of collision origin. -/
  shift : ℤ
deriving Repr

/-- Construct the retained packet with N-only public row data. -/
def publicPacket (N m j : ℕ) : CenteredPacket :=
  let z := publicRow N m j
  ⟨z,publicShift N m j z.a z.b z.t⟩

/-- Derive a centered quadratic without discarding its source. -/
def packetRow (m j : ℕ) (w : CenteredPacket) : QuotientRow :=
  shiftRow m j w.shift w.original

/-- Both actual balanced factors lie in the literal public square-root
box. No primality or oracle is required for this arithmetic statement. -/
theorem balanced_factor_box {p q : ℕ} (hpq : p≤q) (hq₂ : q≤2*p) :
    (p*q/2).sqrt≤p ∧ p≤(p*q).sqrt ∧ (p*q).sqrt≤q ∧ q≤(2*(p*q)).sqrt := by
  have hN : p*q≤2*p^2 := by nlinarith only [Nat.mul_le_mul_left p hq₂]
  have hhalf : p*q/2≤p^2 := by omega
  have hpRoot : p≤(p*q).sqrt := Nat.le_sqrt'.mpr (by nlinarith only [Nat.mul_le_mul_left p hpq])
  have hqRoot : (p*q).sqrt≤q := by
    have h := Nat.sqrt_le_sqrt (show p*q≤q^2 by nlinarith only [Nat.mul_le_mul_right q hpq])
    simpa only [Nat.sqrt_eq'] using h
  have hqUp : q≤(2*(p*q)).sqrt :=
    Nat.le_sqrt'.mpr (by nlinarith only [Nat.mul_le_mul_right q hq₂])
  have hpLo : (p*q/2).sqrt≤p := by
    simpa only [Nat.sqrt_eq'] using Nat.sqrt_le_sqrt hhalf
  exact ⟨hpLo,hpRoot,hqRoot,hqUp⟩

/-- Signed rectangle endpoints bound the exact coupled factor sum.
The factors occur only in the proof of coverage. -/
theorem factor_sum_interval {N m j p q : ℕ} {a b t : ℤ}
    (hpLo : (N/2).sqrt≤p) (hpHi : p≤N.sqrt)
    (hqLo : N.sqrt≤q) (hqHi : q≤(2*N).sqrt) (ht : 0≤t) :
    lowerSum N m j a b t≤a*p+t*q+b*m-2*a*j ∧
      a*p+t*q+b*m-2*a*j≤upperSum N m j a b t := by
  have hpLoZ : ((N/2).sqrt : ℤ)≤p := by exact_mod_cast hpLo
  have hpHiZ : (p : ℤ)≤N.sqrt := by exact_mod_cast hpHi
  have hqLoZ : (N.sqrt : ℤ)≤q := by exact_mod_cast hqLo
  have hqHiZ : (q : ℤ)≤(2*N).sqrt := by exact_mod_cast hqHi
  have htLo := mul_le_mul_of_nonneg_left hqLoZ ht
  have htHi := mul_le_mul_of_nonneg_left hqHiZ ht
  unfold lowerSum upperSum
  split_ifs with ha
  · constructor <;> nlinarith only [htLo,htHi,mul_le_mul_of_nonneg_left hpLoZ ha,
        mul_le_mul_of_nonneg_left hpHiZ ha]
  · have ha' : a≤0 := (lt_of_not_ge ha).le
    constructor <;> nlinarith only [htLo,htHi,mul_le_mul_of_nonpos_left hpLoZ ha',
        mul_le_mul_of_nonpos_left hpHiZ ha']

/-- The public interval width contains no uncentered b or j cost. -/
theorem factor_sum_width (N m j : ℕ) (a b t : ℤ) :
    upperSum N m j a b t-lowerSum N m j a b t=
      |a| *((N.sqrt : ℤ)-(N/2).sqrt)+t*(((2*N).sqrt : ℤ)-N.sqrt) := by
  unfold lowerSum upperSum
  split_ifs with ha
  · rw [abs_of_nonneg ha]
    ring
  · rw [abs_of_neg (lt_of_not_ge ha)]
    ring

/-- The shared envelope depends on the width of the public factor box,
rather than on the full uncentered factor sum. -/
def centeredLength (N m : ℕ) : ℕ :=
  (m.sqrt*((2*N).sqrt-(N/2).sqrt)+m^2)/(2*m^2)+1

/-- Exact integer midpoint rounding centers every value in the original
interval, including negative sums and boundary ties. -/
theorem rounded_interval {lo hi x d : ℤ} (hd : 0<d)
    (hxLo : lo≤x) (hxHi : x≤hi) :
    2*|x-((lo+hi+d)/(2*d))*d|≤hi-lo+d := by
  let k := (lo+hi+d)/(2*d)
  have hmod : 0≤(lo+hi+d)%(2*d) := Int.emod_nonneg _ (by omega)
  have hlt : (lo+hi+d)%(2*d)<2*d := Int.emod_lt_of_pos _ (by omega)
  have he : (lo+hi+d)%(2*d)+(2*d)*k=lo+hi+d := Int.emod_add_mul_ediv _ _
  have hr : |2*(x-k*d)|≤hi-lo+d := abs_le.mpr (by constructor <;> nlinarith only [he,hmod,hlt,hxLo,hxHi])
  rw [abs_mul,abs_of_nonneg (by decide : (0 : ℤ)≤2)] at hr
  exact hr

/-- Every signed index of the exact factor sum has the shorter public
bound after transporting the row and target by the same public shift. -/
theorem centered_index_bound {N m j p q : ℕ} {a b t i : ℤ}
    (hm : 0<m) (hpLo : (N/2).sqrt≤p) (hpHi : p≤N.sqrt)
    (hqLo : N.sqrt≤q) (hqHi : q≤(2*N).sqrt)
    (ha : |a|≤(m.sqrt : ℕ)) (ht₀ : 0≤t) (ht : t≤(m.sqrt : ℕ))
    (hi : (m : ℤ)^2*i=a*p+t*q+b*m-2*a*j) :
    (i-publicShift N m j a b t).natAbs < centeredLength N m := by
  have hinterval := factor_sum_interval (m:=m) (j:=j) (a:=a) (b:=b) hpLo hpHi hqLo hqHi ht₀
  have hlo : (N/2).sqrt≤N.sqrt := Nat.sqrt_le_sqrt (Nat.div_le_self N 2)
  have hhi : N.sqrt≤(2*N).sqrt := Nat.sqrt_le_sqrt (by omega)
  have hloZ : ((N/2).sqrt : ℤ)≤N.sqrt := by exact_mod_cast hlo
  have hhiZ : (N.sqrt : ℤ)≤(2*N).sqrt := by exact_mod_cast hhi
  have hd₁ : (0 : ℤ)≤(N.sqrt : ℤ)-(N/2).sqrt := by omega
  have hd₂ : (0 : ℤ)≤((2*N).sqrt : ℤ)-N.sqrt := by omega
  have hwidth : upperSum N m j a b t-lowerSum N m j a b t≤
      (m.sqrt : ℤ)*(((2*N).sqrt : ℤ)-(N/2).sqrt) := by
    rw [factor_sum_width]
    have h₁ := mul_le_mul_of_nonneg_right ha hd₁
    have h₂ := mul_le_mul_of_nonneg_right ht hd₂
    nlinarith only [h₁,h₂]
  have hmZ : (0 : ℤ)<m := by exact_mod_cast hm
  have hround := rounded_interval (lo:=lowerSum N m j a b t) (hi:=upperSum N m j a b t)
    (x:=(m : ℤ)^2*i) (d:=(m : ℤ)^2) (sq_pos_of_pos hmZ)
    (by rw [hi]; exact hinterval.1) (by rw [hi]; exact hinterval.2)
  have he : (m : ℤ)^2*i-publicShift N m j a b t*(m : ℤ)^2=
      (i-publicShift N m j a b t)*(m : ℤ)^2 := by ring
  change 2*|(m : ℤ)^2*i-publicShift N m j a b t*(m : ℤ)^2|≤_ at hround
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg (m : ℤ)),←Int.natCast_natAbs] at hround
  have hd : ((2*N).sqrt : ℤ)-(N/2).sqrt=(((2*N).sqrt-(N/2).sqrt : ℕ) : ℤ) := by
    rw [Nat.cast_sub (hlo.trans hhi)]
  have hb : 2*(i-publicShift N m j a b t).natAbs*m^2≤
      m.sqrt*((2*N).sqrt-(N/2).sqrt)+m^2 := by
    have h : 2*((i-publicShift N m j a b t).natAbs : ℤ)*(m : ℤ)^2≤
        (m.sqrt : ℤ)*((((2*N).sqrt-(N/2).sqrt : ℕ) : ℤ))+(m : ℤ)^2 := by
      rw [←hd]
      linarith only [hround,hwidth]
    exact_mod_cast h
  have hdiv := (Nat.le_div_iff_mul_le (show 0<2*m^2 by positivity)).mpr
    (show (i-publicShift N m j a b t).natAbs*(2*m^2)≤
      m.sqrt*((2*N).sqrt-(N/2).sqrt)+m^2 by nlinarith only [hb])
  unfold centeredLength
  omega

/-- The actual public packet covers every balanced semiprime. It keeps
the original index, shifted index, nonzero quadratic and exact relation. -/
theorem publicPacket_balanced_coverage {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hq₂ : q≤2*p) (hm : 1<m) (hN : m.Coprime (p*q)) :
    let w := publicPacket (p*q) m (p%m)
    let z := packetRow m (p%m) w
    ∃ i : ℤ, i.natAbs < centeredLength (p*q) m ∧ z.a≠0 ∧
      quadratic z.a z.b z.c (p/m : ℕ)=p*i ∧
      quadratic w.original.a w.original.b w.original.c (p/m : ℕ)=p*(i+w.shift) ∧
      quotientRelation (p*q : ℕ) m (p%m : ℕ) z.a z.b z.c z.t ∧
      (p : ℤ)∈integerRoots z.a (z.b*m-2*z.a*(p%m : ℕ)-(m : ℤ)^2*i) (z.t*(p*q : ℕ)) := by
  let src := publicRow (p*q) m (p%m)
  let k := publicShift (p*q) m (p%m) src.a src.b src.t
  let z := shiftRow m (p%m) k src
  have hmp : m.Coprime p := hN.of_dvd_right (dvd_mul_right p q)
  have hj : (p%m).Coprime m := by
    change Nat.gcd (p%m) m=1
    rw [←Nat.gcd_rec]
    exact hmp
  have hc := publicRow_correct hm hN hj
  obtain ⟨i,_,ha,hi,_⟩ := publicRow_balanced_coverage hp hq hpq hq₂ hm hN
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ) src.a src.b src.c src.t := by
    simpa only [Nat.cast_mul] using hc.2.2.2.2.2.1
  have hp0 : (p : ℤ)≠0 := by exact_mod_cast hp.ne_zero
  have he : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have h := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hs := scaled_quadratic_factor_sum he hrel
  rw [hi] at hs
  have hsum : (m : ℤ)^2*i=src.a*p+src.t*q+src.b*m-2*src.a*(p%m : ℕ) := by
    apply mul_left_cancel₀ hp0
    nlinarith only [hs]
  have habs : |src.a|≤(m.sqrt : ℕ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast hc.2.1
  have hbox := balanced_factor_box hpq hq₂
  have hbound := centered_index_bound (m:=m) (j:=(p%m)) (by omega)
    hbox.1 hbox.2.1 hbox.2.2.1 hbox.2.2.2 habs hc.2.2.1.le hc.2.2.2.1 hsum
  have hnew : quadratic z.a z.b z.c (p/m : ℕ)=(p : ℤ)*(i-k) := by
    rw [shiftRow_quadratic,←he,hi]
    ring
  have hnewrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ) z.a z.b z.c z.t := by
    exact shiftRow_relation (by simpa only [Nat.cast_mul] using hrel) k
  have hnewa : z.a≠0 := ha
  have hroot := integerRoots_complete hnewa (quotient_row_recovery_equation he hnewrel hnew)
  change ∃ i', i'.natAbs < centeredLength (p*q) m ∧ z.a≠0 ∧
    quadratic z.a z.b z.c (p/m : ℕ)=p*i' ∧
    quadratic src.a src.b src.c (p/m : ℕ)=p*(i'+k) ∧
    quotientRelation (p*q : ℕ) m (p%m : ℕ) z.a z.b z.c z.t ∧
    (p : ℤ)∈integerRoots z.a (z.b*m-2*z.a*(p%m : ℕ)-(m : ℤ)^2*i') (z.t*(p*q : ℕ))
  refine ⟨i-k,hbound,hnewa,hnew,?_,?_,?_⟩
  · simpa only [sub_add_cancel] using hi
  · simpa only [Nat.cast_mul] using hnewrel
  · simpa only [Nat.cast_mul] using hroot

/-- The shorter shared baby axis still contains a real hidden-field
collision, and its shifted quadratic list still recovers the actual p. -/
theorem publicPacket_balanced_power_coverage {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hq₂ : q≤2*p) (hm : 1<m) (hN : m.Coprime (p*q))
    (g : (ZMod p)ˣ) :
    let w := publicPacket (p*q) m (p%m)
    let z := packetRow m (p%m) w
    ∃ i : ℤ, i.natAbs < centeredLength (p*q) m ∧
      g^giantExponent m (p%m : ℕ) z.a z.b z.c=g^((m : ℤ)^2*i) ∧
      (p : ℤ)∈integerRoots z.a (z.b*m-2*z.a*(p%m : ℕ)-(m : ℤ)^2*i) (z.t*(p*q : ℕ)) := by
  let : Fact p.Prime := ⟨hp⟩
  let w := publicPacket (p*q) m (p%m)
  let z := packetRow m (p%m) w
  obtain ⟨i,hindex,_,hi,_,hr,hroot⟩ := publicPacket_balanced_coverage hp hq hpq hq₂ hm hN
  have hrel : quotientRelation ((p : ℤ)*q) m (p%m : ℕ) z.a z.b z.c z.t := by
    simpa only [Nat.cast_mul] using hr
  have he : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+(p%m : ℕ) := by
    have h := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hperiod : g^((p : ℤ)-1)=1 := by
    have h := ZMod.units_pow_card_sub_one_eq_one p g
    have hz : g^((p-1 : ℕ) : ℤ)=1 := by simpa only [zpow_natCast] using h
    simpa only [Nat.cast_sub hp.one_le,Nat.cast_one] using hz
  exact ⟨i,hindex,quotient_row_power_hit g he hrel hi (by exact_mod_cast hp.ne_zero) hperiod,hroot⟩

/-- A fifth-root square modulus gives a smaller explicit input budget.
This counts row/point inputs only; it does not certify bit complexity. -/
theorem centeredLength_fifth_budget {N M : ℕ} (hM : 0<M) (hN : N≤M^10) :
    centeredLength N (M^2)≤M^2+2 := by
  have hroot : (2*N).sqrt≤2*M^5 := by
    have h : 2*N≤(2*M^5)^2 := by nlinarith only [hN]
    simpa only [Nat.sqrt_eq'] using Nat.sqrt_le_sqrt h
  have hdiff : (2*N).sqrt-(N/2).sqrt≤2*M^5 := (Nat.sub_le _ _).trans hroot
  have hb := Nat.mul_le_mul_left M hdiff
  have hn : M*((2*N).sqrt-(N/2).sqrt)+(M^2)^2≤(M^2+1)*(2*(M^2)^2) := by
    nlinarith only [hb]
  have hd : 0<2*(M^2)^2 := by positivity
  have hdiv := Nat.div_le_div_right (c:=2*(M^2)^2) hn
  rw [Nat.mul_div_cancel _ hd] at hdiv
  unfold centeredLength
  rw [Nat.sqrt_eq']
  omega

/-- Both signed giant orientations and the centered points have a
linear fifth-root construction budget, with their full pair grid absent. -/
theorem centered_fifth_layout {N M : ℕ} (hM : 0<M) (hN : N≤M^10) :
    2*M^2+centeredLength N (M^2)≤3*M^2+2 := by
  have h := centeredLength_fifth_budget hM hN
  omega

/-- At sixth-root modulus scale, this centering still gives a cubic
M index envelope. This upper bound is not a general factoring lower bound. -/
theorem centeredLength_sixth_budget {N M : ℕ} (hM : 0<M) (hN : N≤M^12) :
    centeredLength N (M^2)≤M^3+2 := by
  have hroot : (2*N).sqrt≤2*M^6 := by
    have h : 2*N≤(2*M^6)^2 := by nlinarith only [hN]
    simpa only [Nat.sqrt_eq'] using Nat.sqrt_le_sqrt h
  have hdiff : (2*N).sqrt-(N/2).sqrt≤2*M^6 := (Nat.sub_le _ _).trans hroot
  have hb := Nat.mul_le_mul_left M hdiff
  have hn : M*((2*N).sqrt-(N/2).sqrt)+(M^2)^2≤(M^3+1)*(2*(M^2)^2) := by
    nlinarith only [hb]
  have hd : 0<2*(M^2)^2 := by positivity
  have hdiv := Nat.div_le_div_right (c:=2*(M^2)^2) hn
  rw [Nat.mul_div_cancel _ hd] at hdiv
  unfold centeredLength
  rw [Nat.sqrt_eq']
  omega

/-- Literal public control: the original zero index becomes -2, and the
entire common axis shrinks from the previous 41 points to six. -/
theorem control_public_shift :
    publicShift 10403 4 1 (-1) (-1) 1=2 ∧ centeredLength 10403 4=6 ∧
      SemiprimeQuotientRows.indexLength 10403 4=41 ∧
      integerRoots (-1) ((-9)*4-2*(-1)*1-4^2*(-2)) 10403=[-103,101] := by
  norm_num [publicShift,lowerSum,upperSum,centeredLength,SemiprimeQuotientRows.indexLength,integerRoots]

/-- Centering the giant alone loses this actual factor signal. Moving
the baby target by the same phase retains the exact collision. -/
theorem control_target_transport :
    (2 : ZMod 101)^10400=1 ∧ (2 : ZMod 101)^10368≠1 ∧
      (2 : ZMod 101)^10368*(2 : ZMod 101)^32=1 := by
  reduce_mod_char
  norm_num
  decide

end RiemannGaussian.SemiprimeQuotientCentering
