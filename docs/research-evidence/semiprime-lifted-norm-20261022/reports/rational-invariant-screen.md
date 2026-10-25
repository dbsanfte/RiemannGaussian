# A paid rational-invariant collision observable on the native norm descriptors

22 October 2026. Constructed a soft-m sufficient factor observable using only the O(m) native lifted-norm descriptors. No theorem forces its success on every input, and it does not acquire the two common H values. The exact additional native coverage assertion is stated below. No examples, tests, backend, repository edits or new analytic assumptions.

Retain M=m³ and the canonical exact relations

    v_j²+M B_j=4a_jN, 1≤a_j<m,

on the negative-norm branch. The construction below also works for signed B. Prepared P,Q>16m² make every a_j a unit modulo N. A proper gcd(v_j,N), if found, already factors; subsequent formulas do not actually need v_j invertible. Native descriptors have O(log N) bits. The actual H_eta targets and their nonzero exponent ledger are unchanged.

## Acquired observable, with all pair interactions compressed

Acquire the J rational invariants in the PUBLIC residue ring

    t_j=v_j²/a_j modN.

Batch inversion of the a_j and J modular multiplications cost soft O(J). Deduplicate exact equal residues t_j modulo N, retaining one original descriptor for each; this is a public sort, not hidden-prime grouping. Let the remaining s≤J residues be t_1,...,t_s, and acquire

    T(Z)=product_(j≤s)(Z-t_j),
    d_j=T'(t_j)=product_(h≠j)(t_j-t_h).

Balanced monic product trees, differentiation and monic multipoint evaluation acquire the WHOLE polynomial and all s derivative values in soft O(s) modular-ring operations. All divisors in the remainder tree are monic; no point difference is inverted and local collisions are permitted. Integer-packed multiplication gives the usual soft O(J log N) native bit bound, with polylogarithms suppressed. This is an actual sufficient observable, not a black-box resultant query with unacquired inputs. Its degree is O(m), not m².

If any gcd(d_j,N) is proper, it factors N. If every such gcd is one, all retained t_j are pairwise distinct in BOTH hidden fields. If some gcd is N, resolve one selected index j as follows. The sibling subtrees along j's path in the existing root tree partition all other leaves. Evaluate their monic polynomials at t_j by ordinary Horner and take gcds; their degrees sum to s-1, so this costs O(s) modular work. Select any nonunit sibling value, and descend its tree. A proper gcd returns a factor. At a saturated node, at least one child is nonunit; test both and continue through one if both are saturated. Degrees along the selected path sum to O(s). At a leaf h≠j, gcd(t_j-t_h,N) cannot be N because the retained PUBLIC residues were deduplicated. It is therefore proper. Saturation is fully discharged within soft O(J), with no hidden partner index or decoder assumption.

Thus the algorithm either factors N or certifies, after public duplicate removal,

    t_i≠t_j modulo P AND modulo Q for all i≠j.

It applies unchanged to any explicitly supplied O(m polylog N)-size bounded twist family; the bit size and generation of that family must be charged separately as in the earlier twist report. It is also restriction stable under row subsets, although its success is not guaranteed by the root collision promise of the original long query.

## Exact native meaning and useful factor condition

All denominators a_i,a_j,M are units modulo N, so

    t_i=t_j modP
      iff a_j v_i²-a_i v_j²=0 modP
      iff a_j B_i-a_i B_j=0 modP.

Consequently the observable factors whenever two acquired NORM DESCRIPTORS have the same ratio B/a at one hidden prime but different ratios at the other. If their ratios agree at both primes, they were public duplicates and cannot by themselves distinguish the factors. No integer square-class equality is needed. Conversely equality of integer negative square classes does not automatically force this rational-invariant collision: the reviewed Cauchy argument is a different sufficient mechanism. Both paid screens may be run within soft m and cover complementary conditions.

In particular, the new screen can use norms with entirely different coprime-base signatures. Its mathematical guarantee is exact local ratio equality, not closeness, matching Legendre symbols, or a numeric birthday heuristic. Its output is an ordinary proper factor, so no saturated annihilator recovery is needed in this branch.

## What is still missing for H values OR a guaranteed factor

The original native coverage guarantees an own-factor equality between a target gamma^E_j and one seed gamma^(m²I). It does NOT presently prove that two of the public t_j collide in a hidden field. The native second-digit relation I P=ah²+bh+c involves an unknown h and index I; eliminating those from one row gives the already acquired cubic congruence, not a second-row ratio collision. No exact identity converting all no-collision certificates above into the values H_+(y_j),H_-(y_j) was found.

The precise possible completion theorem is therefore:

    For every native input, either two retained norm descriptors satisfy
    equality of B/a at precisely one hidden prime, OR the no-collision
    case has an explicitly supplied soft-m evaluator/reduction for the
    two common H products.

Neither alternative coverage nor the no-collision evaluator is established. A simpler sufficient theorem would force a one-sided rational-invariant collision in some explicit soft-m twist family. That is a concrete target involving only the actual O(m) descriptors, with its factor consumer already acquired. There is no unproved generic sparse-nullspace step, no need to factor norm integers, and no assertion that dimension reduction alone computes the original degree-m² norm.

Outcome: one additional whole-family arithmetic screen is fully paid at soft m; universal success, or a source-preserving H evaluator on its certified no-collision branch, remains open. This is a conditional usable interface, not a rate gain or a new obstruction packet.
