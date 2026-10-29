/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAcquiredPrefixSearch
import RiemannGaussian.SemiprimeMacroFiniteEnumerations
import RiemannGaussian.SemiprimePublicConstructedCount
import RiemannGaussian.SemiprimeSubdividedEntry

/-! # Executed acquired counter on the public integer factoring graph -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimePublicAcquiredExecution
open scoped BigOperators
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroParameters
open SemiprimeMacroFiniteEnumerations SemiprimeMacroEntryBitPrimitives
open SemiprimeCountRecovery SemiprimeCounterSearch

/-- Actual public half-edge type, without a polynomial layout parameter. -/
abbrev PublicEdge (N : ℕ) := Edge (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N))
/-- Actual public arithmetic and equality vertices. -/
abbrev PublicVertex (N : ℕ) := SubdividedVertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N))
/-- Explicit ascending-constructor enumeration of all public wires. -/
def edgeEnumeration (N : ℕ) := edges (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N))
/-- Explicit constructor enumeration of all public vertices. -/
def vertexEnumeration (N : ℕ) := subdividedVertices (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N))
/-- Runtime number of public wire bits. -/
def wireCount (N : ℕ) : ℕ := (edgeEnumeration N).values.length
/-- Runtime number of actual public factors in the tensor network. -/
def factorCount (N : ℕ) : ℕ := (vertexEnumeration N).values.length
/-- Public graph arity after its explicit finite indexing. -/
def indexedArity (N : ℕ) (e : Fin (factorCount N)) : ℕ := subdividedArity ((vertexEnumeration N).equivFin e)
/-- Literal port-to-wire map in finite indices. -/
def indexedCoordinate (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) (i : Fin (indexedArity N e)) : Fin (wireCount N) :=
  (edgeEnumeration N).equivFin.symm (SemiprimeScheduledCounter.publicCoordinate (bitLength_pos hN)
    ((vertexEnumeration N).equivFin e) i)
/-- Paid original arithmetic/equality local checker, not a supplied acceptance table. -/
def indexedEntry (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) (input : Fin (indexedArity N e) → Bool) : CheckRun :=
  SemiprimeSubdividedEntry.publicSubdividedEntry N hN ((vertexEnumeration N).equivFin e) input

/-- Exact port reindexing preserves all original incidences. -/
def portEquiv (N : ℕ) :
    ((e : Fin (factorCount N)) × Fin (indexedArity N e)) ≃
      ((v : PublicVertex N) × Fin (subdividedArity v)) :=
  Equiv.sigmaCongr (vertexEnumeration N).equivFin (fun _ => Equiv.refl _)

/-- Every indexed wire occurs in an actual public scope. -/
theorem indexed_coverage (N : ℕ) (hN : 0<N) (a : Fin (wireCount N)) :
    ∃ e i, indexedCoordinate N hN e i=a := by
  obtain ⟨v,i,hi⟩ := SemiprimePublicConstructedCount.public_coverage (bitLength_pos hN)
    ((edgeEnumeration N).equivFin a)
  let p := (portEquiv N).symm ⟨v,i⟩
  have hp : portEquiv N p=⟨v,i⟩ := (portEquiv N).apply_symm_apply ⟨v,i⟩
  refine ⟨p.1,p.2,?_⟩
  apply (edgeEnumeration N).equivFin.injective
  change (edgeEnumeration N).equivFin ((edgeEnumeration N).equivFin.symm
    (SemiprimeScheduledCounter.publicCoordinate (bitLength_pos hN) (portEquiv N p).1 (portEquiv N p).2)) = _
  rw [Equiv.apply_symm_apply,hp]
  exact hi

/-- Finite reindexing retains the actual occurrence-two source load B=2. -/
theorem indexed_occurrences (N : ℕ) (hN : 0<N) (a : Fin (wireCount N)) :
    (Finset.univ.filter (fun i : (e : Fin (factorCount N)) × Fin (indexedArity N e) =>
      indexedCoordinate N hN i.1 i.2=a)).card ≤ 2 := by
  classical
  let target := (edgeEnumeration N).equivFin a
  let f : {p : (e : Fin (factorCount N)) × Fin (indexedArity N e) // indexedCoordinate N hN p.1 p.2=a} →
      {p : (v : PublicVertex N) × Fin (subdividedArity v) //
        SemiprimeScheduledCounter.publicCoordinate (bitLength_pos hN) p.1 p.2=target} :=
    fun p => ⟨portEquiv N p.val, by
      change SemiprimeScheduledCounter.publicCoordinate (bitLength_pos hN)
        ((vertexEnumeration N).equivFin p.val.1) p.val.2=target
      have h := congrArg (edgeEnumeration N).equivFin p.property
      simpa only [indexedCoordinate, Equiv.apply_symm_apply] using h⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact (portEquiv N).injective (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  have ho := SemiprimeScheduledCounter.public_occurrences (bitLength_pos hN) target
  have hc' : (Finset.univ.filter (fun p : (e : Fin (factorCount N)) × Fin (indexedArity N e) =>
      indexedCoordinate N hN p.1 p.2=a)).card ≤ (Finset.univ.filter (fun p : (v : PublicVertex N) × Fin (subdividedArity v) =>
      SemiprimeScheduledCounter.publicCoordinate (bitLength_pos hN) p.1 p.2=target)).card := by
    simpa only [Fintype.card_subtype] using hc
  exact hc'.trans ho

/-- The executed indexed checker is exactly the actual public tensor table. -/
theorem indexedEntry_correct (N : ℕ) (hN : 0<N) (e : Fin (factorCount N)) (input : Fin (indexedArity N e) → Bool) :
    (indexedEntry N hN e input).accepted =
      subdividedTable (SemiprimePublicFactorCount.publicConfig N hN) ((vertexEnumeration N).equivFin e) input :=
  SemiprimeSubdividedEntry.publicSubdividedEntry_correct N hN _ input

/-- Original public accepting predicate in the executed finite wire indices. -/
def indexedPredicate (N : ℕ) (hN : 0<N) : Finset (Fin (wireCount N)) → Bool :=
  originalPredicate (indexedArity N) (fun e a => (indexedEntry N hN e a).accepted) (indexedCoordinate N hN)

/-- Indexed acceptance gives the true public subdivided arithmetic graph. -/
theorem indexed_to_public (N : ℕ) (hN : 0<N) (x : Finset (Fin (wireCount N)))
    (hx : indexedPredicate N hN x=true) :
    SubdividedAccepted (SemiprimePublicFactorCount.publicConfig N hN)
      (fun a => assignmentBit x ((edgeEnumeration N).equivFin.symm a)) := by
  have hh : ∀ e, (indexedEntry N hN e (fun i => assignmentBit x (indexedCoordinate N hN e i))).accepted=true :=
    by simpa only [indexedPredicate, originalPredicate, decide_eq_true_eq] using hx
  intro v
  obtain ⟨e,rfl⟩ := (vertexEnumeration N).equivFin.surjective v
  exact (indexedEntry_correct N hN e _).symm.trans (hh e)

/-- Actual natural prefix count of the public integer, using the source interpreter. -/
def prefixCount (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (fixed : List (Fin (wireCount N) × Bool)) : ℕ :=
  SemiprimeAcquiredPrefixSearch.prefixCount (r := r) (Q := Q)
    (indexedArity N) (indexedCoordinate N hN) eps R 2 J (indexedEntry N hN) fixed

/-- Every requested prefix is counted by the same actual public network. -/
theorem prefixCount_correct (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J)
    (fixed : List (Fin (wireCount N) × Bool)) :
    prefixCount N hN r Q eps R J fixed =
      acceptedCount (restricted assignmentBit (indexedPredicate N hN) fixed) :=
  SemiprimeAcquiredPrefixSearch.prefixCount_correct (indexedArity N) (indexedCoordinate N hN)
    eps R 2 J (indexedEntry N hN) (indexed_occurrences N hN) (indexed_coverage N hN)
    hQ hAQ hJ hprecision fixed

/-- Literal zero-first search over the actual public half-edge list. -/
def search (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) :
    SearchResult (Fin (wireCount N)) :=
  SemiprimeCountRecovery.search (prefixCount N hN r Q eps R J) (List.finRange (wireCount N))

/-- Explicit transport between indexed and original Boolean wire functions. -/
def assignmentEquiv (N : ℕ) : (Fin (wireCount N) → Bool) ≃ (PublicEdge N → Bool) where
  toFun f a := f ((edgeEnumeration N).equivFin.symm a)
  invFun f i := f ((edgeEnumeration N).equivFin i)
  left_inv f := by funext i; exact congrArg f ((edgeEnumeration N).equivFin.symm_apply_apply i)
  right_inv f := by funext i; simp

/-- The indexed whole public predicate counts exactly ordinary ordered factor pairs. -/
theorem indexed_factor_count (N : ℕ) (hN : 0<N) :
    acceptedCount (indexedPredicate N hN)=Fintype.card (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  classical
  unfold indexedPredicate
  rw [SemiprimePublicConstructedCount.accepted_eq_tensor]
  have hs : (∑ a : Fin (wireCount N) → Bool, ∏ e : Fin (factorCount N),
      if (indexedEntry N hN e (fun i => a (indexedCoordinate N hN e i))).accepted then (1 : ℕ) else 0) =
      (∑ a : PublicEdge N → Bool, ∏ v : PublicVertex N,
        if subdividedTable (SemiprimePublicFactorCount.publicConfig N hN) v
          (fun i => a (SemiprimeScheduledCounter.publicCoordinate (bitLength_pos hN) v i)) then (1 : ℕ) else 0) := by
    apply Fintype.sum_equiv (assignmentEquiv N)
    intro a
    simp only [indexedEntry_correct]
    exact (vertexEnumeration N).equivFin.prod_comp
      (fun v => if subdividedTable (SemiprimePublicFactorCount.publicConfig N hN) v
        (fun i => a ((edgeEnumeration N).equivFin.symm
          (SemiprimeScheduledCounter.publicCoordinate (bitLength_pos hN) v i))) then (1 : ℕ) else 0)
  exact hs.trans (SemiprimePublicFactorCount.public_tensor_factor_count N hN)

/-- The acquired empty-prefix count is the actual ordinary factor cardinal. -/
theorem factor_count (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J) :
    prefixCount N hN r Q eps R J []=Fintype.card (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  rw [prefixCount_correct N hN r Q eps R J hQ hAQ hJ hprecision]
  have he : restricted assignmentBit (indexedPredicate N hN) []=indexedPredicate N hN := by
    funext x
    simp only [restricted,List.all_nil,Bool.and_true]
  rw [he]
  exact indexed_factor_count N hN

/-- Decode physical input words by the literal little-endian bit algorithm.
No classical BitVec inverse or public normalizer is evaluated. -/
def decodeOperand (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) : ℕ :=
  let length := firstAxis (bitLength N)*secondAxis (bitLength N)
  ∑ i ∈ Finset.range (digitCount (bitLength N)),
    (if hi : i<length then SemiprimeMacroEntryExecution.binaryDecode
      (fun bit : Fin (length+1) => SemiprimeAcquiredPrefixSearch.selectedBits values
        ((edgeEnumeration N).equivFin.symm ((.inl (.input side ⟨i,hi⟩,bit)),false))) else 0) *
      (2^radixBits (bitLength N))^i

/-- The physical bit decoder is exactly the source operand used in the arithmetic proof. -/
theorem decodeOperand_eq (N : ℕ) (hN : 0<N) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) :
    decodeOperand N values side = sourceOperand (SemiprimePublicFactorCount.publicConfig N hN)
      (fun signal => SemiprimeAcquiredPrefixSearch.selectedBits values
        ((edgeEnumeration N).equivFin.symm (signal,false))) side := by
  unfold decodeOperand sourceOperand sourceFunction wordNat
  simp only [SemiprimeMacroEntryExecution.readWord_eq_binaryDecode]
  rfl

/-- The actual executed prefix search returns a proper integer factor. -/
def factor (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) : Option ℕ :=
  (search N hN r Q eps R J).values.map (fun values => decodeOperand N values 0)

/-- Every executed search branch uses the same acquired counter and has a common original witness. -/
theorem search_sound (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J)
    (values : List (Fin (wireCount N) × Bool))
    (h : (search N hN r Q eps R J).values=some values) :
    values.map Prod.fst=List.finRange (wireCount N) ∧
      ∃ x, indexedPredicate N hN x=true ∧ ∀ p ∈ values, assignmentBit x p.1=p.2 :=
  SemiprimeCountRecovery.search_some_sound (prefixCount N hN r Q eps R J) assignmentBit
    (indexedPredicate N hN) (prefixCount_correct N hN r Q eps R J hQ hAQ hJ hprecision)
    (List.finRange (wireCount N)) values h

/-- The reconstructed selected wires have genuine nontrivial product N. -/
theorem selected_factor_pair (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J)
    (values : List (Fin (wireCount N) × Bool))
    (h : (search N hN r Q eps R J).values=some values) :
    2≤decodeOperand N values 0 ∧ 2≤decodeOperand N values 1 ∧
      decodeOperand N values 0*decodeOperand N values 1=N := by
  obtain ⟨hindices,x,hx,hbits⟩ := search_sound N hN r Q eps R J hQ hAQ hJ hprecision values h
  have hcover (i : Fin (wireCount N)) : ∃ p ∈ values, p.1=i := by
    have hi : i ∈ values.map Prod.fst := by rw [hindices]; exact List.mem_finRange i
    exact List.mem_map.mp hi
  have heq : SemiprimeAcquiredPrefixSearch.selectedBits values=assignmentBit x := by
    funext i
    exact SemiprimeAcquiredPrefixSearch.selectedBits_eq values _ hcover hbits i
  have hp := subdivided_factor_pair (SemiprimePublicFactorCount.publicConfig N hN) _
    (indexed_to_public N hN x hx)
  have hdec (side : Fin 2) : decodeOperand N values side =
      sourceOperand (SemiprimePublicFactorCount.publicConfig N hN)
        (fun signal => assignmentBit x ((edgeEnumeration N).equivFin.symm (signal,false))) side := by
    rw [decodeOperand_eq N hN values side]
    congr 1
    funext signal
    exact congrFun heq _
  refine ⟨hp.1.trans_eq (hdec 0).symm,hp.2.1.trans_eq (hdec 1).symm,?_⟩
  exact ((congrArg₂ (fun a b : ℕ => a*b) (hdec 0) (hdec 1)).trans hp.2.2).trans
    (SemiprimePublicFactorCount.public_target_value N hN)

/-- A returned value is an actual proper divisor, with no modular or ring-only decoder. -/
theorem factor_sound (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J)
    (p : ℕ) (h : factor N hN r Q eps R J=some p) : 2≤p ∧ p<N ∧ p∣N := by
  unfold factor at h
  obtain ⟨values,hvalues,hp⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hle,hright,hprod⟩ := selected_factor_pair N hN r Q eps R J hQ hAQ hJ hprecision values hvalues
  subst p
  refine ⟨hle,?_,⟨decodeOperand N values 1,hprod.symm⟩⟩
  nlinarith

/-- Actual acquired search fails exactly when the integer has no ordinary proper factor pair. -/
theorem search_none_iff (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J) :
    (search N hN r Q eps R J).values=none ↔
      ¬Nonempty (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  classical
  have hs := SemiprimeCountRecovery.search_none_iff (prefixCount N hN r Q eps R J) assignmentBit
    (indexedPredicate N hN) (prefixCount_correct N hN r Q eps R J hQ hAQ hJ hprecision)
    (List.finRange (wireCount N))
  have he : (∃ x, indexedPredicate N hN x=true) ↔ Nonempty (SemiprimePublicFactorCount.OrdinaryFactors N) := by
    rw [← acceptedCount_pos_iff, indexed_factor_count, Fintype.card_pos_iff]
  exact hs.trans (not_congr he)

/-- The returned integer algorithm is complete as well as sound, including squares. -/
theorem factor_none_iff (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J) :
    factor N hN r Q eps R J=none ↔ ¬Nonempty (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  rw [factor,Option.map_eq_none_iff]
  exact search_none_iff N hN r Q eps R J hQ hAQ hJ hprecision

/-- Recovery makes one initial and at most one actual conditional query per half-edge. -/
theorem search_queries (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) :
    (search N hN r Q eps R J).queries ≤ wireCount N+1 := by
  simpa only [search,List.length_finRange] using SemiprimeCountRecovery.search_queries_le
    (prefixCount N hN r Q eps R J) (List.finRange (wireCount N))

/-- Finite indexing preserves the actual public variable-count schedule exactly. -/
theorem wireCount_eq (N : ℕ) : wireCount N=variableCount (bitLength N) :=
  (edgeEnumeration N).length_eq_card

/-- The indexed runtime scopes retain the actual public arity bound. -/
theorem indexedArity_le (N : ℕ) (e : Fin (factorCount N)) :
    indexedArity N e ≤ scopeBound (bitLength N) := actual_arity_le _

/-- Every original public callback has its proved polynomial bit-checker cost. -/
theorem indexedEntry_clock (N : ℕ) (hN : 0<N) (e : Fin (factorCount N))
    (input : Fin (indexedArity N e) → Bool) :
    (indexedEntry N hN e input).clock≤1048576*(64*bitLength N+2)^10 :=
  SemiprimeSubdividedEntry.publicSubdividedEntry_polynomial N hN _ input

/-- Natural-input wrapper; zero is rejected by an actual decidable branch. -/
def factorNat (N r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) : Option ℕ :=
  if hN : 0<N then factor N hN r Q eps R J else none

/-- Every output of the natural-input wrapper is a proper divisor of its input. -/
theorem factorNat_sound (N r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J)
    (p : ℕ) (h : factorNat N r Q eps R J=some p) : 2≤p ∧ p<N ∧ p∣N := by
  unfold factorNat at h
  split_ifs at h with hN
  · exact factor_sound N hN r Q eps R J hQ hAQ hJ hprecision p h

/-- The actual finite port enumeration has exactly two ports per Boolean wire. -/
theorem indexed_incidence_count (N : ℕ) (hN : 0<N) :
    (∑ e, indexedArity N e)=2*wireCount N := by
  have h := Fintype.card_congr (portEquiv N)
  have hc : Fintype.card ((e : Fin (factorCount N)) × Fin (indexedArity N e))=
      ∑ e, indexedArity N e := by simp only [Fintype.card_sigma,Fintype.card_fin]
  rw [hc] at h
  exact h.trans ((SemiprimeScheduledCounter.public_incidence_card (bitLength_pos hN)).trans
    (congrArg (fun a => 2*a) (wireCount_eq N).symm))

end RiemannGaussian.SemiprimePublicAcquiredExecution
