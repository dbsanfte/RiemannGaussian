# Paper study: two-time propagation, adaptive scales, and finite-query interfaces

26 October 2026. Read the supplied 59-page draft *Local smoothing for the Euclidean wave equation*, OpenAI, dated25 October2026, especially §§6–12 and AppendicesA–C. This is a study of its mechanisms and possible finite analogues, not an independent certification of its full PDE proof. No repository changes, experiments, or goal resumption. The factoring goal remains paused.

**Main finding.** The strongest useful pattern is not smoothing itself: it is aggregating ONE admissible low-pass at each observation scale and charging only a narrow exceptional band. The paper proves norm comparisons for that organization, not an algorithm evaluating an exact long product or selected pole. A native application needs an exact, acquired aggregate and a zero-safe remainder; positive elliptic comparison and small analytic errors do not supply either over Z/N.

## 1. The scalar two-time reduction really pays two passages

**Exact location:** §6 pp21–23, Lemma6.1, (6.1)–(6.3), Figure2; Remark6.2; Proposition6.3 (6.4).

The energy E(T,tau) is nonnegative, satisfies Delta_(T,tau)E≤V(|tau|)E, and is circularly averaged to H(T,s). For b≤r≤1, D=log(3/b), the conclusion is

    H(0,r) ≥ c(M) log(r/b)/D² * integral_[1,2] H(T,b)dT.   (6.2)

The proof first transports observed mass to a fixed annulus, losing1/D in (6.3), uses a fixed connected-band mean/Harnack comparison, then transports back to r near the inner wall. At r=2b the second harmonic measure loses another logarithm. The potential is controlled by its explicit weighted integral in (6.1), not assumed harmless. The radial equation becomes psi''=P psi after x=log(s/b); its Gronwall estimate retains quantitative boundary fractions.

Remark6.2 constructs a nonnegative scalar supersolution with V=0 attaining the two-log scale. Therefore an attempt to remove the return loss using ONLY the scalar inequality would contradict the paper's own example. A better bound needs additional structure of the actual wave energy. Proposition6.3 turns this into a log^(2/p_c) norm estimate by inserting the separately constructed energy and taking a p_c-th root.

**Finite query analogue to test.** Let pi_(j,i) be the (unacquired) exact CRT collision indicators; on the good unique bank sum pi=1. A small positive finite transfer network could propagate source mass to a boundary observation with only polylogarithmic attenuation. But its source-to-boundary evaluation must be acquired from q,F and row metadata in softK, and its observation must remain nonzero at the good component. A comparison theorem alone computes no observation. Over Z/N there is no ordering, maximum principle, or implication 'positive contribution cannot cancel'. Replacing pi by an already computed count/residue would put the desired acquisition into the hypothesis.

A meaningful exact interface would be a publicly acquired O(polylog h)-state network and a ring-safe solve whose boundary scalar is c*sum pi (and marked version c*sum w_j pi), with c a certified unit and total softK setup/solve. That is a concrete supplier hypothesis. No such network is constructed by Lemma6.1, and no claim that its scalar sharpness is a complexity lower bound is made.

## 2. Construction is substantial; the energy is not a free observable

**Locations:** §2.2 p7, Lemma2.1 (2.5); AppendixA pp38–41, TheoremA.1 (A.1)–(A.2), linearization and continuity argument.

The two auxiliary flows give an exact divergence-free positive-semidefinite tensor: four real squares arise from two complex fields. Its conservation law is an algebraic cancellation, while positivity is a real/complex metric statement. AppendixA solves a nonlinear determinant Dirichlet problem with positive Hessian and smooth parameter dependence. Its proof uses barriers, ellipticity, C² estimates, Evans–Krylov/Schauder theory, and a continuity method.

This is existence/regularity, not a bit-complexity theorem. It supplies no discretization size versus wavelength, condition-number bound for a native finite matrix, exact modular circuit, or target-precision algorithm. Even replacing it by the planar linear disk construction would not make a long native observable supplied. A proposed finite analogue must state the operator, right-hand side, normalization, all pivots, and the cost of solving; calling it a potential or energy is insufficient.

## 3. The most useful organizing idea: choose the admissible aggregate ONCE

**Locations:** AppendixB pp41–46: PropositionB.2 (B.1), LemmaB.4 (B.3)–(B.4), especially (B.6)–(B.8) pp44–45.

The paper separates radial frequency N and angular degree M. Bounded angular degree costs L(N)^(1/p)+L(M)^A in the strong estimate, and only L(M)^A in the weak estimate (B.1). It then uses doubly exponential angular cutoffs M_m=2^(2^m), with Q_m=S_m-S_(m-1), so logarithmic angular regularity gives decay2^(-mB) in (B.6).

At each output radius r and radial band N_j, it chooses the LARGEST m satisfying

    H_m≤min(N_j^eta,N_j*r), H_m=(2+2M_m)^K.         (B.7)

All selected low angular bands are treated as ONE S_m low-pass; the proof does not separately pay the spatial logarithm for every admitted band. Only unselected bands are charged separately, with a finite near-scale window and a decaying far tail. The r-dependent pieces need not individually retain the original annular support; the proof explicitly reassembles them before applying synthesis (p46). That detail matters for a proposed hierarchy.

**Concrete native candidate, not an achieved theorem.** Use the existing laminar phase-support tree along each primitive coefficient direction. For each actual clock/row-size cell, choose the maximal admissible coarse support whose physical window fits the paid query budget. Acquire a SINGLE aggregate marked pole for that entire selected support, not one per ancestor; retain the finer supports as an explicit exceptional correction. The needed finite identity is

    C_native = C_low(cutoff) + sum_exceptional C_band,

with actual carry/deletion terms, and either exact equality of the useful pole pair or a difference certified to have no physical pole. The proposal is useful only if C_low is acquired jointly in softK and the exceptional TOTAL acquisition is softK. Existing support metadata and min-cost partition DP do not by themselves compute C_low. Nor does a norm-small error become an exact modular unit or zero. In particular the old full-bin window-mass price cannot be defeated just by naming a cutoff.

**Meaningful next test:** apply this exact decomposition to the already initialized section/displacement operator, with cutoff depending on its quotient depth. Compute its low-pass action and its exceptional carry operator as finite matrices/circuits; determine whether their SAME-root diagonal can be contracted once rather than once per depth. A proof must charge action calls. This asks for an exact native aggregate, not transplantation of stationary-phase estimates.

## 4. Almost orthogonality pays logarithms, not arithmetic operations

**Locations:** §7.2 pp24–26, (7.3)–(7.4); §11 pp34–36, Lemmas11.2–11.3 and Theorem11.1 proof.

In §7.2, a little positive Sobolev epsilon makes 2^(-j epsilon)(1+j)^beta summable. Corollary7.1 instead combines signed multipliers, Khintchine and Littlewood–Paley bounds, paying beta(p)+(1/2-1/p) and a precise log-log threshold at equality. This is a stronger analytic combination than the triangle inequality but still not a method for evaluating all bands.

Lemma11.3 supplies a particularly concrete three-way split on each test cube: low scales k≤j-L are nearly constant by a derivative estimate, high scales k≥j+L split into local L² and decaying far-kernel terms, and only O(L)=O(log(1/delta)) middle scales need their Lp estimate. Hölder over the middle scales costs L^(1/2-1/p). Lemma11.2 pays delta^(1/2-sigma) for one interval of radii. The strict threshold alpha>1/2+s_+(p) absorbs the resulting factors when summing shells.

For a finite exact query, an analogous useful theorem would say that far-low/far-high *correction operators* are acquired low-rank/unit-boundary maps, while only logarithmically many middle maps require the expensive joint contraction. Bounds on operator norms do not imply such ranks or algorithms. If all band outputs are independently evaluated, arithmetic cost is their SUM; it does not become the square root of the sum of squared costs. Conversely one shared exact transform could combine them cheaply, but that transform is the missing algebraic work to prove.

## 5. Random signs: an exact algebraic identity, with acquisition still visible

**Locations:** §9.2 pp29–30, Lemma9.4 (9.5); AppendixC pp46–47, (C.1)–(C.2) and sign selection.

In Lemma9.4, disjoint frequency caps keep the input norm controlled for every sign choice. Jensen and independent signs turn expected squared output modulus into a sum of squared packet moduli; this doubles the logarithmic exponent from A to2A. AppendixC builds initially disjoint packets whose propagated tubes overlap in a set of measure O((log N)^(-d)), while the sum of individual core volumes remains bounded below. Their random-sign second moment proves existence of signs with large output mass. It does NOT search for the signs algorithmically.

There is an exact finite identity worth retaining. For genuine collision idempotents pi_j²=pi_j in the separated finite algebra, independent signs give

    E[(sum epsilon_j pi_j)²]=sum pi_j,
    E[(sum epsilon_j pi_j)(sum epsilon_j w_j pi_j)]=sum w_j pi_j.

These averages use only inversion of powers of2, a unit for odd N. They are therefore legitimate algebraic equations without a PDE metric. But pi_j are the unacquired pole masks. Evaluating the signed sums or all exact averages remains a source acquisition problem. If arbitrary cofactor amplitudes replace pi_j, the diagonal becomes sum a_j² pi_j, which can cancel over a finite field; positivity of |a_j|² cannot be imported. On the native global-unique bank, any supplied nonzero amplitude already suffices, so random signs give no additional uniqueness benefit.

The limited useful transfer is conditional: if a signed aggregate has a cheap initialized circuit even though an unsigned aggregate does not, randomized signs can sometimes prevent cancellation (conditional on the other signs, a nonzero coefficient has at most one cancelling choice). This gives no deterministic all-input supplier and no cost saving without that circuit. AppendixC also warns that disjoint INPUT labels do not guarantee disjoint transported supports; native carry/completion mutations must reprove their hit multiplicities, just as the existing unique-support construction does.

## 6. Radius selection and other surfaces are bounded-operator transfers

**Locations:** §10 pp32–33, Lemma10.2 and (10.3); §12 pp36–38, (12.2)–(12.4).

Lemma10.2 controls the supremum over shell radii by a decaying integral of waves, split at time delta^-1. It does not return a maximizing radius or a cheap radius predicate. Dyadic radius estimates combine using frequency localization and p≥2. Thus it cannot be used as a free native clock-phase selector.

Section12 passes sphere to paraboloid with a quantified approximation: the graph differs by O(delta²), the observation error is O(R delta²), and delta is chosen polynomially small in R. Fresnel rescaling then transports extension bounds to Schrödinger estimates. The logarithmic loss survives because the transformed scale has logarithm O(log R). This suggests tracking scale/precision explicitly in any representation change, but its approximate error control does not supply exact modulo-N equality, a root-of-unity specialization, or a missing small denominator inverse.

## 7. Concrete study outcome and next experiment, without resuming the goal

The paper offers three useful design requirements for a future finite identity:

1. A common positive/orthogonal aggregate may be evaluated once, with the rest organized as explicit boundary or exceptional corrections. The finite analogue must acquire that aggregate, rather than assume it from a norm inequality.
2. A cutoff should depend on TWO scales (the analogue of radial frequency and angular complexity), with a largest-admissible rule and a proved total exceptional cost. Public colour-domain size cannot replace actual phase support or physical clock span.
3. A representation change must carry its error, normalization, source construction and selection cost. Exact native zero predicates need exact identities or separately licensed unit remainders, not an analytic small-error estimate.

The best next paper-and-pencil test is an exact two-scale low-pass decomposition of the existing rational-Newton section/quotient circuit, preserving its selected pole and measuring the NUMBER of coupled action calls. If low-pass aggregation plus exceptional corrections can be jointly contracted in soft(K+J^(3/2)), the retuned row-index consumer is already paid. If the decomposition still requests each ancestor's old rational functional, then this particular propagation analogy has not provided acquisition. This is a sharply specified proposed test; it has not been executed here, and no new factoring bound or goal work is claimed.
