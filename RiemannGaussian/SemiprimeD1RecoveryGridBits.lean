/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryPowerBits
import RiemannGaussian.SemiprimeSourceMemoryBits
import RiemannGaussian.SemiprimeEncodedRowSelection

/-! # Executed physical arithmetic for the original recovery grid
Only original native grid indices and loop-control metadata are digit-acquired.
All large grid powers/products, signed differences, slope divisions and Ezero
normalizations execute through Boolean rational arithmetic. Native index/control
acquisition is separately reported rather than called a primitive machine clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryGridBits
open SemiprimeRationalBits SemiprimeJetBits SemiprimeBitArithmetic
open SemiprimeD1RecoveryWeightRun SemiprimeD1RecoveryScalarRun
open SemiprimeD1WireKernelOriginal SemiprimeD1JetRecoveryGrid SemiprimeD1TaperedLoss
open SemiprimeD1WireKernelFactors
open SemiprimeD1RecoveryPowerBits SemiprimeSourceMemoryBits

/-- Literal positive physical two, with no scalar rational encoding. -/
def twoWord : RationalWord := ⟨⟨false,[false,true]⟩,[true]⟩

/-- Physical two has its exact scalar value. -/
theorem twoWord_value : twoWord.value=2 := by
  norm_num [twoWord,RationalWord.value,SemiprimeBitIndexClipping.SignedWord.value,bitValue,bitNat]

/-- Physical two is a legal rational. -/
theorem twoWord_valid : twoWord.Valid := by change 0 < 1; decide

/-- Physical two needs only its two actual magnitude cells. -/
theorem twoWord_width (W : ℕ) (hW : 2 ≤ W) : Width twoWord W := by
  constructor <;> dsimp [twoWord] <;> omega

/-- One actual original-index digit acquisition; scalar input stages stay explicit. -/
def index (a q : ℕ) : SemiprimeEncodedRowSelection.IntegerWordRun :=
  SemiprimeEncodedRowSelection.encode (a+1) (q:ℤ)

/-- Every acquired original grid index is represented exactly. -/
theorem index_value (a q : ℕ) (hq : q < size a) : (index a q).word.value=(q:ℚ) := by
  apply SemiprimeEncodedRowSelection.encode_value
  simpa only [Int.abs_natCast,size] using (Int.ofNat_le.mpr hq.le)

/-- Original index acquisition has positive literal denominator. -/
theorem index_valid (a q : ℕ) : (index a q).word.Valid := SemiprimeEncodedRowSelection.encode_valid _ _

/-- Native index input is already bounded by original geometry. -/
theorem index_width (a q W : ℕ) (hW : a+2 ≤ W) : Width (index a q).word W := by
  constructor
  · change (SemiprimeEncodedRowSelection.digits (a+2) (q:ℤ).natAbs).bits.length ≤ W
    rw [SemiprimeEncodedRowSelection.digits_length]
    exact hW
  · change 1 ≤ W
    omega

/-- Deep physical copies of every repeated rational slope. -/
structure Copies where
  /-- Actual repeated copied words. -/
  words : List RationalWord
  /-- All copied numerator/denominator bits and control. -/
  clock : ℕ

/-- Each slope repetition actually scans/copies both physical payloads. -/
def copies (x : RationalWord) : ℕ → Copies
  | 0 => ⟨[],1⟩
  | n+1 =>
    let head:=copyWord x
    let tail:=copies x n
    ⟨head.word::tail.words,head.clock+tail.clock+3⟩

/-- The physically copied list has precisely the original repeated slope values. -/
theorem copies_words (x : RationalWord) (n : ℕ) : (copies x n).words=List.replicate n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [copies,copyWord_word,ih,List.replicate_succ]

/-- Every actual repeated payload copy is paid from its physical width. -/
theorem copies_clock (x : RationalWord) (n W : ℕ) (hx : Width x W) :
    (copies x n).clock ≤ n*(8*W+9)+1 := by
  have hc:=copyWord_clock x W hx
  induction n with
  | zero => simp [copies]
  | succ n ih => simp only [copies,Nat.add_mul,Nat.one_mul]; omega

/-- Original raw grid values/slopes on physical words and both report classes. -/
structure GridReport where
  /-- Physical signed integer numerator product. -/
  numerator : RationalWord
  /-- Physical signed integer denominator product. -/
  denominator : RationalWord
  /-- Physical ordered/repeated slopes. -/
  slopes : List RationalWord
  /-- Actual rational bit arithmetic and copies. -/
  clock : ℕ
  /-- Native original-index/valuation/control acquisition stages. -/
  metadataWork : ℕ

/-- Full physical grid fold. Existing original valuation metadata determines
loop lengths, never any rational coefficient or answer word. -/
def loop (template : List Bool) (a h u t : ℕ) (g : Geometry)
    (center alpha node : RationalWord) : List ℕ → GridReport
  | [] => ⟨oneWord,oneWord,[],4,1⟩
  | q::qs =>
    let tail:=loop template a h u t g center alpha node qs
    if q=g.center.natAbs ∨ q=t then
      ⟨tail.numerator,tail.denominator,tail.slopes,tail.clock+3,tail.metadataWork+4⟩
    else
      let m:=multiplicityRun g h u q
      let qword:=index a q
      let negative:=executeOperation .neg qword.word qword.word template
      let numeratorBase:=executeOperation .add center negative.word template
      let denominatorBase:=executeOperation .add node negative.word template
      let numeratorPower:=power template numeratorBase.word m.value
      let denominatorPower:=power template denominatorBase.word m.value
      let reciprocal:=executeOperation .inv denominatorBase.word denominatorBase.word template
      let slope:=executeOperation .mul alpha reciprocal.word template
      let repeated:=copies slope.word m.value
      let numerator:=executeOperation .mul numeratorPower.word tail.numerator template
      let denominator:=executeOperation .mul denominatorPower.word tail.denominator template
      ⟨numerator.word,denominator.word,repeated.words++tail.slopes,
        tail.clock+negative.clock+numeratorBase.clock+denominatorBase.clock+
          numeratorPower.clock+denominatorPower.clock+reciprocal.clock+slope.clock+
          repeated.clock+numerator.clock+denominator.clock+2*repeated.words.length+15,
        tail.metadataWork+m.work+qword.work+10⟩

/-- Sufficient physical arithmetic width from original dimensions only. -/
def gridWidth (a h u : ℕ) : ℕ :=
  (a+1)*(h*u)*size a+(a+1)*(a+1)+a+10

/-- Physical original grid, its Ezero ratio and retained acquisition reports. -/
structure Report where
  /-- Actual original raw grid and slope data. -/
  grid : GridReport
  /-- Actual normalized Ezero word. -/
  scalar : RationalWord
  /-- Actual physical local argument -point/alpha. -/
  argument : RationalWord
  /-- Physical original centre. -/
  center : RationalWord
  /-- Physical original alpha. -/
  alpha : RationalWord
  /-- Every physical coefficient arithmetic/copy report retained. -/
  clock : ℕ
  /-- Native original input/index/valuation/control stages retained separately. -/
  metadataWork : ℕ

/-- Actual original-input physical acquisition with internally computed grid,
slopes, integer products, ratios and local argument. No coefficient supplier. -/
def acquire (template : List Bool) (a M u : ℕ) (t : Fin (size a)) : Report :=
  let h:=height M u
  let g:=geometry a t.val
  let center:=power template twoWord a
  let alpha:=power template twoWord (a+1)
  let node:=index a t.val
  let keys:=indices g.size
  let grid:=loop template a h u t.val g center.word alpha.word node.word keys.value
  let reciprocal:=executeOperation .inv grid.denominator grid.denominator template
  let scalar:=executeOperation .mul grid.numerator reciprocal.word template
  let negative:=executeOperation .neg node.word node.word template
  let point:=executeOperation .add center.word negative.word template
  let inverseAlpha:=executeOperation .inv alpha.word alpha.word template
  let argument:=executeOperation .mul point.word inverseAlpha.word template
  ⟨grid,scalar.word,argument.word,center.word,alpha.word,
    center.clock+alpha.clock+grid.clock+reciprocal.clock+scalar.clock+negative.clock+
      point.clock+inverseAlpha.clock+argument.clock+30,
    g.work+node.work+keys.work+grid.metadataWork+20⟩

/-- Integer-valued rational results derive capacities from original integer
magnitudes; the theorem supplies no normalized-output answer. -/
theorem integer_fits (z : ℤ) (W : ℕ) (hW : 0 < W) (hz : z.natAbs < 2^W) : Fits (z:ℚ) W := by
  exact ⟨by simpa only [Rat.num_intCast] using hz,by simpa only [Rat.den_intCast] using Nat.one_lt_two_pow (by omega : W≠0)⟩

/-- Original bounded signed factors all fit the derived grid width. -/
theorem factor_fits (a h u W : ℕ) (z : ℤ) (hz : z.natAbs ≤ size a)
    (hW : gridWidth a h u ≤ W) : Fits (z:ℚ) W := by
  apply integer_fits z W (by unfold gridWidth at hW; omega)
  have he : a+1 < W := by unfold gridWidth at hW; omega
  exact hz.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) he)

/-- Actual original grid-product bounds discharge every normalized integer
multiply result, including ALL raw suffix products. -/
theorem product_fits (a h u W : ℕ) (t : Fin (size a)) (qs : List ℕ)
    (hq : ∀q∈qs,q < size a) (hl : qs.length ≤ size a) (hW : gridWidth a h u ≤ W) :
    Fits ((gridRows (geometry a t.val) h u t.val qs).numerator:ℚ) W ∧
    Fits ((gridRows (geometry a t.val) h u t.val qs).denominator:ℚ) W := by
  have hb:=SemiprimeD1RecoveryWeightRunState.grid_bounds a h u t qs hq
  have he : (size a)^((h*u)*qs.length) < 2^W := by
    change (2^(a+1))^_ < _
    rw [← pow_mul]
    apply Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ))
    have hm:=Nat.mul_le_mul_left ((a+1)*(h*u)) hl
    unfold gridWidth at hW
    nlinarith only [hW,hm]
  exact ⟨integer_fits _ W (by unfold gridWidth at hW; omega) (hb.1.trans_lt he),
    integer_fits _ W (by unfold gridWidth at hW; omega) (hb.2.trans_lt he)⟩

/-- Elementary consequences of the literal original grid width. -/
theorem gridWidth_caps (a h u W : ℕ) (hW : gridWidth a h u ≤ W) :
    0 < W ∧ a+2 ≤ W ∧ (a+1)*(h*u)+1 ≤ W ∧ (a+1)*(a+1)+1 ≤ W := by
  have hN : 0 < size a := by unfold size; positivity
  have hm : (a+1)*(h*u) ≤ (a+1)*(h*u)*size a := Nat.le_mul_of_pos_right _ hN
  unfold gridWidth at hW
  omega

/-- A derived original integer fraction fits after REAL canonical normalization. -/
theorem ratio_fits (a h u W : ℕ) (n d : ℤ) (hd : d ≠ 0)
    (hn : n.natAbs ≤ size a) (hden : d.natAbs ≤ size a) (hW : gridWidth a h u ≤ W) :
    Fits ((n:ℚ)/(d:ℚ)) W := by
  have hr:=SemiprimeD1HermiteDenominatorHeight.int_ratio_representation n d
  have ht : size a < 2^W := Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ))
    (by have hc:=gridWidth_caps a h u W hW; omega)
  exact fits_of_representation (Int.natAbs_pos.mpr hd) hr (hn.trans_lt ht) (hden.trans_lt ht)

/-- Exact original grid arithmetic refinement, with legal and bounded physical words. -/
def Relation (W : ℕ) (out : GridReport) (native : SemiprimeD1RecoveryWeightRun.GridReport) : Prop :=
  out.numerator.value=(native.numerator:ℚ) ∧ out.denominator.value=(native.denominator:ℚ) ∧
  out.slopes.map RationalWord.value=native.slopes ∧
  out.numerator.Valid ∧ out.denominator.Valid ∧ (∀x∈out.slopes,x.Valid) ∧
  Width out.numerator W ∧ Width out.denominator W ∧ (∀x∈out.slopes,Width x W)

/-- Physical negation/addition acquire the original signed numerator factor. -/
theorem numeratorBase_correct (template : List Bool) (a h u q : ℕ)
    (centerWord : RationalWord) (hq : q < size a)
    (hc : centerWord.value=(center a:ℚ)) (hcv : centerWord.Valid)
    (hW : gridWidth a h u ≤ template.length) :
    let qword:=index a q
    let negative:=executeOperation .neg qword.word qword.word template
    let out:=executeOperation .add centerWord negative.word template
    out.word.value=(-(SemiprimeD1WireKernelOriginal.point a q):ℤ) ∧
      out.word.Valid ∧ Width out.word template.length := by
  dsimp only
  have qv:=index_value a q hq
  have qvalid:=index_valid a q
  have hnegfit : Fits (Operation.neg.value (index a q).word.value (index a q).word.value) template.length := by
    rw [qv]
    simpa only [Operation.value,Int.cast_neg,Int.cast_natCast] using factor_fits a h u template.length (-(q:ℤ))
      (by simpa using hq.le) hW
  have neg:=executeOperation_correct .neg (index a q).word (index a q).word template qvalid qvalid hnegfit
  have he : Operation.add.value centerWord.value (executeOperation .neg (index a q).word (index a q).word template).word.value=
      (-(SemiprimeD1WireKernelOriginal.point a q):ℤ) := by
    rw [neg.1]
    simp only [Operation.value,hc,qv,SemiprimeD1WireKernelOriginal.point,Int.cast_neg,Int.cast_sub,Int.cast_natCast]
    ring
  have hf : Fits (Operation.add.value centerWord.value
      (executeOperation .neg (index a q).word (index a q).word template).word.value) template.length := by
    rw [he]
    exact factor_fits a h u template.length _ (by
      simpa only [Int.natAbs_neg] using (SemiprimeD1JetRecoveryScalarHeight.point_abs_lt a q hq).le) hW
  have out:=executeOperation_correct .add centerWord
    (executeOperation .neg (index a q).word (index a q).word template).word template hcv neg.2.1 hf
  exact ⟨out.1.trans he,out.2⟩

/-- Physical subtraction acquires the original non-normalized denominator factor. -/
theorem denominatorBase_correct (template : List Bool) (a h u p q : ℕ)
    (node : RationalWord) (hp : p < size a) (hq : q < size a)
    (hc : node.value=(p:ℚ)) (hcv : node.Valid)
    (hW : gridWidth a h u ≤ template.length) :
    let qword:=index a q
    let negative:=executeOperation .neg qword.word qword.word template
    let out:=executeOperation .add node negative.word template
    out.word.value=(difference p q:ℚ) ∧ out.word.Valid ∧ Width out.word template.length := by
  dsimp only
  have qv:=index_value a q hq
  have qvalid:=index_valid a q
  have hnegfit : Fits (Operation.neg.value (index a q).word.value (index a q).word.value) template.length := by
    rw [qv]
    simpa only [Operation.value,Int.cast_neg,Int.cast_natCast] using factor_fits a h u template.length (-(q:ℤ))
      (by simpa using hq.le) hW
  have neg:=executeOperation_correct .neg (index a q).word (index a q).word template qvalid qvalid hnegfit
  have he : Operation.add.value node.value (executeOperation .neg (index a q).word (index a q).word template).word.value=
      (difference p q:ℚ) := by
    rw [neg.1]
    simp only [Operation.value,hc,qv,difference,Int.cast_sub,Int.cast_natCast]
    ring
  have hf : Fits (Operation.add.value node.value
      (executeOperation .neg (index a q).word (index a q).word template).word.value) template.length := by
    rw [he]
    exact factor_fits a h u template.length _ (difference_abs_lt (size a) p q hp hq).le hW
  have out:=executeOperation_correct .add node
    (executeOperation .neg (index a q).word (index a q).word template).word template hcv neg.2.1 hf
  exact ⟨out.1.trans he,out.2⟩

/-- The original slope division is acquired through REAL physical inversion and
multiplication, with normalization capacities derived from the original grid. -/
theorem slope_correct (template : List Bool) (a h u p q : ℕ) (alpha denominator : RationalWord)
    (hp : p < size a) (hq : q < size a) (hne : q ≠ p)
    (ha : alpha.value=((2:ℤ)^(a+1):ℚ)) (hav : alpha.Valid)
    (hd : denominator.value=(difference p q:ℚ)) (hdv : denominator.Valid)
    (hW : gridWidth a h u ≤ template.length) :
    let inverse:=executeOperation .inv denominator denominator template
    let out:=executeOperation .mul alpha inverse.word template
    out.word.value=((2:ℤ)^(a+1):ℚ)/(difference p q:ℚ) ∧
      out.word.Valid ∧ Width out.word template.length := by
  dsimp only
  have hN : 0 < size a := by unfold size; positivity
  have hdt:=difference_ne_zero p q hne
  have hdb:=(difference_abs_lt (size a) p q hp hq).le
  have hiFit : Fits (Operation.inv.value denominator.value denominator.value) template.length := by
    rw [hd]
    simpa only [Operation.value,Int.cast_one,one_div] using
      ratio_fits a h u template.length 1 (difference p q) hdt (by change 1 ≤ size a; omega) hdb hW
  have hi:=executeOperation_correct .inv denominator denominator template hdv hdv hiFit
  have he : Operation.mul.value alpha.value (executeOperation .inv denominator denominator template).word.value=
      ((2:ℤ)^(a+1):ℚ)/(difference p q:ℚ) := by
    rw [hi.1]
    simp only [Operation.value,ha,hd,div_eq_mul_inv]
  have hmFit : Fits (Operation.mul.value alpha.value
      (executeOperation .inv denominator denominator template).word.value) template.length := by
    rw [he]
    simpa only [Int.cast_pow,Int.cast_ofNat] using
      ratio_fits a h u template.length ((2:ℤ)^(a+1)) (difference p q) hdt
        (by simp [Int.natAbs_pow,size]) hdb hW
  have out:=executeOperation_correct .mul alpha
    (executeOperation .inv denominator denominator template).word template hav hi.2.1 hmFit
  exact ⟨out.1.trans he,out.2⟩

/-- The full ORIGINAL grid fold is executed on physical rational words. All
multiplication/division/GCD capacities come from the actual original grid
bounds; no intermediate Fits or coefficient/trace answer is an input. -/
theorem loop_correct (template : List Bool) (a h u : ℕ) (t : Fin (size a))
    (centerWord alpha node : RationalWord)
    (hc : centerWord.value=(center a:ℚ)) (hcv : centerWord.Valid)
    (ha : alpha.value=((2:ℤ)^(a+1):ℚ)) (hav : alpha.Valid)
    (ht : node.value=(t.val:ℚ)) (htv : node.Valid)
    (hW : gridWidth a h u ≤ template.length) (qs : List ℕ)
    (hqs : ∀q∈qs,q < size a) (hlen : qs.length ≤ size a) :
    Relation template.length (loop template a h u t.val (geometry a t.val) centerWord alpha node qs)
      (gridRows (geometry a t.val) h u t.val qs) := by
  have caps:=gridWidth_caps a h u template.length hW
  induction qs with
  | nil =>
    simp only [Relation,loop,gridRows,List.map_nil,Int.cast_one]
    exact ⟨oneWord_value,oneWord_value,by trivial,oneWord_valid,oneWord_valid,by simp,
      oneWord_width caps.1,oneWord_width caps.1,by simp⟩
  | cons q qs ih =>
    have hq:=hqs q List.mem_cons_self
    have htail:=ih (fun x hx => hqs x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons] at hlen; omega)
    rcases htail with ⟨htn,htd,hts,htnv,htdv,htsv,htnw,htdw,htsw⟩
    by_cases hs : q=(geometry a t.val).center.natAbs ∨ q=t.val
    · simpa only [Relation,loop,gridRows,hs,ite_true] using
        And.intro htn (And.intro htd (And.intro hts (And.intro htnv (And.intro htdv
          (And.intro htsv (And.intro htnw (And.intro htdw htsw)))))))
    · let g:=geometry a t.val
      have hsg : ¬(q=g.center.natAbs ∨ q=t.val) := hs
      let tail:=loop template a h u t.val g centerWord alpha node qs
      let m:=multiplicityRun g h u q
      let negative:=executeOperation .neg (index a q).word (index a q).word template
      let nb:=executeOperation .add centerWord negative.word template
      let db:=executeOperation .add node negative.word template
      let np:=power template nb.word m.value
      let dp:=power template db.word m.value
      let inverse:=executeOperation .inv db.word db.word template
      let slope:=executeOperation .mul alpha inverse.word template
      let repeated:=copies slope.word m.value
      let numerator:=executeOperation .mul np.word tail.numerator template
      let denominator:=executeOperation .mul dp.word tail.denominator template
      have hnb:=numeratorBase_correct template a h u q centerWord hq hc hcv hW
      have hdb:=denominatorBase_correct template a h u t.val q node t.isLt hq ht htv hW
      have hm : m.value ≤ h*u := SemiprimeD1RecoveryWeightRunBounds.multiplicity_value_le g h u q
      have hnp:=integer_correct template nb.word a (h*u) m.value (-point a q)
        (by simpa only [Int.natAbs_neg] using (SemiprimeD1JetRecoveryScalarHeight.point_abs_lt a q hq).le)
        hm hnb.1 hnb.2.1 caps.2.2.1
      have hdp:=integer_correct template db.word a (h*u) m.value (difference t.val q)
        (difference_abs_lt (size a) t.val q t.isLt hq).le hm hdb.1 hdb.2.1 caps.2.2.1
      have hsl:=slope_correct template a h u t.val q alpha db.word t.isLt hq
        (fun he => hs (Or.inr he)) ha hav hdb.1 hdb.2.1 hW
      have hbaseN : -((q:ℤ)-g.center) = -point a q := by rw [geometry_center]; rfl
      have hbaseD : g.point-((q:ℤ)-g.center)=difference t.val q := by
        rw [geometry_point,geometry_center]
        unfold point difference
        ring
      have hnum : (gridRows g h u t.val (q::qs)).numerator=
          (intPower (-point a q) m.value).value*(gridRows g h u t.val qs).numerator := by
        simp only [gridRows,hsg,ite_false,hbaseN]
        rfl
      have hden : (gridRows g h u t.val (q::qs)).denominator=
          (intPower (difference t.val q) m.value).value*(gridRows g h u t.val qs).denominator := by
        simp only [gridRows,hsg,ite_false,hbaseD]
        rfl
      have hnumValue : Operation.mul.value np.word.value tail.numerator.value=
          ((gridRows g h u t.val (q::qs)).numerator:ℚ) := by
        dsimp only [Operation.value]
        rw [hnp.1,htn,hnum,Int.cast_mul]
      have hdenValue : Operation.mul.value dp.word.value tail.denominator.value=
          ((gridRows g h u t.val (q::qs)).denominator:ℚ) := by
        dsimp only [Operation.value]
        rw [hdp.1,htd,hden,Int.cast_mul]
      have fit:=product_fits a h u template.length t (q::qs) hqs hlen hW
      have hn:=executeOperation_correct .mul np.word tail.numerator template hnp.2 htnv
        (by rw [hnumValue]; exact fit.1)
      have hd:=executeOperation_correct .mul dp.word tail.denominator template hdp.2 htdv
        (by rw [hdenValue]; exact fit.2)
      simp only [Relation,loop,hs,ite_false]
      change numerator.word.value=((gridRows g h u t.val (q::qs)).numerator:ℚ) ∧
        denominator.word.value=((gridRows g h u t.val (q::qs)).denominator:ℚ) ∧
        (repeated.words++tail.slopes).map RationalWord.value=(gridRows g h u t.val (q::qs)).slopes ∧
        numerator.word.Valid ∧ denominator.word.Valid ∧ (∀x∈repeated.words++tail.slopes,x.Valid) ∧
        Width numerator.word template.length ∧ Width denominator.word template.length ∧
        (∀x∈repeated.words++tail.slopes,Width x template.length)
      refine ⟨hn.1.trans hnumValue,hd.1.trans hdenValue,?_,hn.2.1,hd.2.1,?_,hn.2.2,hd.2.2,?_⟩
      · have hslv : slope.word.value=((2:ℤ)^(a+1):ℚ)/(difference t.val q:ℚ) := hsl.1
        have htss : tail.slopes.map RationalWord.value=(gridRows g h u t.val qs).slopes := hts
        have hAlpha : g.alpha=(2:ℤ)^(a+1) := geometry_alpha a t.val
        simp only [repeated,copies_words,List.map_append,List.map_replicate,hslv,htss,
          gridRows,hsg,ite_false,repeat_value,hbaseD,hAlpha,Int.cast_pow,Int.cast_ofNat]
        rfl
      · intro x hx
        rcases List.mem_append.mp hx with hh|hh
        · rw [copies_words] at hh
          obtain ⟨_,rfl⟩:=List.mem_replicate.mp hh
          exact hsl.2.1
        · exact htsv x hh
      · intro x hx
        rcases List.mem_append.mp hx with hh|hh
        · rw [copies_words] at hh
          obtain ⟨_,rfl⟩:=List.mem_replicate.mp hh
          exact hsl.2.2
        · exact htsw x hh

/-- Actual physical centre/alpha initialization uses only literal two and the
original number of repeated multiplications. No scalar power answer is encoded. -/
theorem initialization_correct (template : List Bool) (a h u : ℕ)
    (hW : gridWidth a h u ≤ template.length) :
    (power template twoWord a).word.value=(center a:ℚ) ∧
    (power template twoWord a).word.Valid ∧
    (power template twoWord (a+1)).word.value=((2:ℤ)^(a+1):ℚ) ∧
    (power template twoWord (a+1)).word.Valid := by
  have caps:=gridWidth_caps a h u template.length hW
  have htwo : (2:ℤ).natAbs ≤ size a := by
    have hp : (2:ℕ)^1 ≤ 2^(a+1) := Nat.pow_le_pow_right (by decide) (by omega)
    change 2 ≤ size a
    simpa only [size,pow_one] using hp
  have hc:=integer_correct template twoWord a (a+1) a 2 htwo (by omega)
    (by simpa only [Int.cast_ofNat] using twoWord_value) twoWord_valid caps.2.2.2
  have ha:=integer_correct template twoWord a (a+1) (a+1) 2 htwo le_rfl
    (by simpa only [Int.cast_ofNat] using twoWord_value) twoWord_valid caps.2.2.2
  refine ⟨?_,hc.2,?_,ha.2⟩
  · simpa only [intPower_value,Int.cast_pow,Int.cast_ofNat,center,Nat.cast_pow,Nat.cast_ofNat] using hc.1
  · simpa only [intPower_value,Int.cast_pow,Int.cast_ofNat] using ha.1

/-- ORIGINAL-INPUT actual physical grid acquisition equals the original raw
products and ordered slopes. There are no supplied initialized coefficients. -/
theorem acquire_grid_correct (template : List Bool) (a M u : ℕ) (t : Fin (size a))
    (hW : gridWidth a (height M u) u ≤ template.length) :
    Relation template.length (acquire template a M u t).grid
      (gridRows (geometry a t.val) (height M u) u t.val
        (indices (geometry a t.val).size).value) := by
  have hi:=initialization_correct template a (height M u) u hW
  have hq : ∀q∈(indices (geometry a t.val).size).value,q < size a := by
    simp only [indices_value,geometry_size,List.mem_range]
    exact fun q h => h
  have hl : (indices (geometry a t.val).size).value.length ≤ size a := by
    simp [indices_value,geometry_size]
  have h:=loop_correct template a (height M u) u t
    (power template twoWord a).word (power template twoWord (a+1)).word (index a t.val).word
    hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 (index_value a t.val t.isLt) (index_valid a t.val) hW
    (indices (geometry a t.val).size).value hq hl
  simpa only [acquire] using h

/-- A large original integer fraction is safe after actual normalization,
with capacities derived from its raw integer products. -/
theorem bounded_ratio_fits (e W : ℕ) (n d : ℤ) (hd : d ≠ 0)
    (hn : n.natAbs ≤ 2^e) (hden : d.natAbs ≤ 2^e) (hW : e < W) :
    Fits ((n:ℚ)/(d:ℚ)) W := by
  have hr:=SemiprimeD1HermiteDenominatorHeight.int_ratio_representation n d
  have ht : 2^e < 2^W := Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hW
  exact fits_of_representation (Int.natAbs_pos.mpr hd) hr (hn.trans_lt ht) (hden.trans_lt ht)

/-- The original raw product exponent is below the actual physical grid width. -/
theorem scalarExponent_lt (a h u W : ℕ) (hW : gridWidth a h u ≤ W) :
    SemiprimeD1JetRecoveryScalarHeight.bitExponent a h u < W := by
  have he : SemiprimeD1JetRecoveryScalarHeight.bitExponent a h u=(a+1)*(h*u)*size a := by
    unfold SemiprimeD1JetRecoveryScalarHeight.bitExponent
    ring
  rw [he]
  unfold gridWidth at hW
  omega

/-- Exact physical Ezero acquisition, including REAL reciprocal, product,
canonical normalization and GCD, derives its capacity from original raw factors. -/
theorem acquire_scalar_correct (template : List Bool) (a M u : ℕ) (t : Fin (size a))
    (hW : gridWidth a (height M u) u ≤ template.length) :
    (acquire template a M u t).scalar.value=SemiprimeD1JetRecoveryGrid.Ezero a (height M u) u t.val ∧
      (acquire template a M u t).scalar.Valid ∧ Width (acquire template a M u t).scalar template.length := by
  let out:=acquire template a M u t
  let h:=height M u
  have hg:=acquire_grid_correct template a M u t hW
  rcases hg with ⟨hn,hd,hs,hnv,hdv,hsv,hnw,hdw,hsw⟩
  rw [fullGrid_numerator] at hn
  rw [fullGrid_denominator] at hd
  have hp:=SemiprimeD1JetRecoveryScalarHeight.original_dyadic_height a h u t
  have hdn:=SemiprimeD1JetRecoveryScalarHeight.denominator_ne_zero a h u t.val
  have hE:=scalarExponent_lt a h u template.length hW
  have hf : Fits (Operation.inv.value out.grid.denominator.value out.grid.denominator.value) template.length := by
    rw [hd]
    simpa only [Operation.value,Int.cast_one,one_div] using
      bounded_ratio_fits (SemiprimeD1JetRecoveryScalarHeight.bitExponent a h u) template.length
        1 (SemiprimeD1JetRecoveryScalarHeight.denominator a h u t.val) hdn
        (by simpa only [Int.natAbs_one] using Nat.one_le_two_pow (n:=SemiprimeD1JetRecoveryScalarHeight.bitExponent a h u))
        hp.2 hE
  have inverse:=executeOperation_correct .inv out.grid.denominator out.grid.denominator template hdv hdv hf
  have he : Operation.mul.value out.grid.numerator.value
      (executeOperation .inv out.grid.denominator out.grid.denominator template).word.value=
      (SemiprimeD1JetRecoveryScalarHeight.numerator a h u t.val:ℚ)/
        (SemiprimeD1JetRecoveryScalarHeight.denominator a h u t.val:ℚ) := by
    rw [inverse.1,hn,hd]
    simp only [Operation.value,div_eq_mul_inv]
    rfl
  have cap : Fits (Operation.mul.value out.grid.numerator.value
      (executeOperation .inv out.grid.denominator out.grid.denominator template).word.value) template.length := by
    rw [he]
    exact bounded_ratio_fits _ _ _ _ hdn hp.1 hp.2 hE
  have result:=executeOperation_correct .mul out.grid.numerator
    (executeOperation .inv out.grid.denominator out.grid.denominator template).word template hnv inverse.2.1 cap
  have value : (executeOperation .mul out.grid.numerator
      (executeOperation .inv out.grid.denominator out.grid.denominator template).word template).word.value=
      Ezero a h u t.val := by
    rw [result.1,he,← SemiprimeD1JetRecoveryScalarHeight.ratio_spec]
  exact ⟨value,result.2⟩

/-- The local argument is acquired physically from the original node and
physical alpha, with no encoded rational argument answer. -/
theorem acquire_argument_correct (template : List Bool) (a M u : ℕ) (t : Fin (size a))
    (hW : gridWidth a (height M u) u ≤ template.length) :
    (acquire template a M u t).argument.value=SemiprimeD1WeightPrecision.argument a t.val ∧
      (acquire template a M u t).argument.Valid ∧ Width (acquire template a M u t).argument template.length := by
  let h:=height M u
  let c:=power template twoWord a
  let alpha:=power template twoWord (a+1)
  let node:=index a t.val
  let negative:=executeOperation .neg node.word node.word template
  let pointWord:=executeOperation .add c.word negative.word template
  let inverseAlpha:=executeOperation .inv alpha.word alpha.word template
  have init:=initialization_correct template a h u hW
  have hp:=numeratorBase_correct template a h u t.val c.word t.isLt init.1 init.2.1 hW
  have hne : (2:ℤ)^(a+1) ≠ 0 := pow_ne_zero _ (by decide)
  have hN : 0 < size a := by unfold size; positivity
  have ha : alpha.word.value=((2:ℤ)^(a+1):ℚ) := init.2.2.1
  have hiFit : Fits (Operation.inv.value alpha.word.value alpha.word.value) template.length := by
    rw [ha]
    simpa only [Operation.value,Int.cast_one,one_div,Int.cast_pow,Int.cast_ofNat] using
      ratio_fits a h u template.length 1 ((2:ℤ)^(a+1)) hne (by change 1 ≤ size a; omega)
        (by simp [Int.natAbs_pow,size]) hW
  have hi:=executeOperation_correct .inv alpha.word alpha.word template init.2.2.2 init.2.2.2 hiFit
  have he : Operation.mul.value pointWord.word.value inverseAlpha.word.value=
      SemiprimeD1WeightPrecision.argument a t.val := by
    rw [hp.1,hi.1]
    simp only [Operation.value,ha,SemiprimeD1WeightPrecision.argument,Int.cast_neg,div_eq_mul_inv,
      Int.cast_ofNat]
  have fit : Fits (Operation.mul.value pointWord.word.value inverseAlpha.word.value) template.length := by
    rw [he]
    simpa only [SemiprimeD1WeightPrecision.argument,Int.cast_neg,Int.cast_pow,Int.cast_ofNat] using
      ratio_fits a h u template.length (-point a t.val) ((2:ℤ)^(a+1)) hne
        (by simpa only [Int.natAbs_neg] using (SemiprimeD1JetRecoveryScalarHeight.point_abs_lt a t.val t.isLt).le)
        (by simp [Int.natAbs_pow,size]) hW
  have out:=executeOperation_correct .mul pointWord.word inverseAlpha.word template hp.2.1 hi.2.1 fit
  exact ⟨out.1.trans he,out.2⟩

/-- Every arithmetic output has the physically selected template width. -/
theorem operation_width (op : Operation) (x y : RationalWord) (template : List Bool) :
    Width (executeOperation op x y template).word template.length :=
  ⟨(fitRationalBits_width _ _).1.le,(fitRationalBits_width _ _).2.le⟩

/-- The literal emitted grid words have bounded payloads at every recursion frame. -/
theorem loop_width (template : List Bool) (a h u t : ℕ) (g : Geometry)
    (center alpha node : RationalWord) (qs : List ℕ) (ht : 0 < template.length) :
    Width (loop template a h u t g center alpha node qs).numerator template.length ∧
    Width (loop template a h u t g center alpha node qs).denominator template.length ∧
    (∀x∈(loop template a h u t g center alpha node qs).slopes,Width x template.length) := by
  induction qs with
  | nil => exact ⟨oneWord_width ht,oneWord_width ht,by simp [loop]⟩
  | cons q qs ih =>
    simp only [loop]
    split_ifs
    · exact ih
    · refine ⟨operation_width _ _ _ _,operation_width _ _ _ _,?_⟩
      intro x hx
      rcases List.mem_append.mp hx with hh|hh
      · rw [copies_words] at hh
        obtain ⟨_,rfl⟩:=List.mem_replicate.mp hh
        exact operation_width _ _ _ _
      · exact ih.2.2 x hh

/-- Every literal physical grid frame has this explicit fixed polynomial budget. -/
def frameBudget (W m : ℕ) : ℕ := (2*m+8)*(20000*(W+1)^3+8*W+50)

/-- Pure arithmetic envelope for all seven scalar operations, two actual
power loops and copied repeated payloads in one original grid visit. -/
theorem frame_envelope (W m mmax : ℕ) (hm : m ≤ mmax) :
    2*m*(20000*(W+1)^3+4)+7*(20000*(W+1)^3)+m*(8*W+9)+2*m+22 ≤ frameBudget W mmax := by
  have hp:=Nat.mul_le_mul_right (20000*(W+1)^3+4) hm
  have hc:=Nat.mul_le_mul_right (8*W+9) hm
  have hfirst : 2*m*(20000*(W+1)^3+4)+7*(20000*(W+1)^3)+m*(8*W+9)+2*m+22 ≤
      2*mmax*(20000*(W+1)^3+4)+7*(20000*(W+1)^3)+mmax*(8*W+9)+2*mmax+22 := by
    simp only [Nat.mul_assoc] at hp hc ⊢
    omega
  apply hfirst.trans
  have he : frameBudget W mmax=
      (2*mmax*(20000*(W+1)^3+4)+7*(20000*(W+1)^3)+mmax*(8*W+9)+2*mmax+22)+
        (mmax*(8*W+81)+20000*(W+1)^3+64*W+378) := by unfold frameBudget; ring
  rw [he]
  exact Nat.le_add_right _ _

end RiemannGaussian.SemiprimeD1RecoveryGridBits
