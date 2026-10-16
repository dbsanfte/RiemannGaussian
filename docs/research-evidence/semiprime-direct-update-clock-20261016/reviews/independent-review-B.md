# Independent exact-byte review B

2026-10-16. Reviewer: moving_carrier_attack_615. Verdict: PASS for the mathematical representation statements and their stated qualifications. This is not an acquisition result or an operation lower bound. Neither reviewed report was authored by this reviewer. No reviewed source was changed.

## Exact reviewed objects

| Object | Bytes | SHA-256 |
|---|---:|---|
| direct-update-clock.md | 11654 | f07353444c81c063877bf68c6107edb62ffec547a231340e8f79e2d963572d62 |
| source-pins.json | 1015 | 6e33dac5ee8c8a148d11df9b97ab6c1f8c3a075e39a33834dee704ba71baf670 |
| direct-prefix-recurrence.md | 10819 | 598a3041a90f761744811df206d9ab11ea8452ec8263db35afd984ed0999fb59 |
| prefix-source-pins.json | 1034 | 82678e677b5a7cb02e1d8833985a2700c67489613ade0f2fff17aa5668799bca |

All three records in source-pins and all four records in prefix-source-pins were independently checked for byte length and SHA-256. The G15 gzip record was additionally decompressed and its 12559-byte plain hash d82b01d0c246795c2483c9316ced7e307d593d09debcfd2cd54d24343ce7c591 verified. Its stored 5303-byte hash is e7dca2a5bb92bea0ebef416546649265b94c771f0a068c999012933b36537c27. I read its theorem, proof premise and actual phase-padding transfer, rather than inferring its content from its title.

## Direct update theorem

The mask orientation z_j=Y_j^(-1) is correct: its rectangle differs from the Y_j-q^i rectangle by an explicitly known unit. The report separates an update multiplier from an undefined ratio after a cumulative product has become zero.

The short-arc argument is valid over the stated fields. Nonprimitive coefficient support of degree J supplies a nontrivial separable scaling root of unity because the characteristic exceeds J. Since it permutes roots already in the field, this scalar belongs to the beta subgroup. A whole nontrivial translation orbit on the cyclic exponent circle cannot fit an arc shorter than R/2. Repeated literal offsets are removed before using distinct roots. This is not an assertion that all mask coefficients are nonzero.

The expanded sample identity has at most (J+1)(D+1) frequencies: the numerator's frequencies are already the u=0 grid row. Ordinary Vandermonde grouping needs no distinctness of h^k. The explicit ord(q)>J condition covers D=0. Two alias differences eliminate h with determinant at most 2JD, so the order bound forces a common rational line. Its primitive direction need not itself be a numerical relation: each already-zero numerical group maps to a single formal exponent, and further merging preserves zero. Thus the formal coarsening is justified even with torsion.

For nonzero a, Laurent residue classes prove K(x^a)-membership has only exponents divisible by |a| without a separability assumption. Coprimality of the primitive direction and primitive support then give |a|=1. The reduced rational degree of A(H^b) or A(H^(-b)) is Jb: the latter denominator is H^(Jb), with no cancellation since the original leading coefficient is nonzero. This proves the claimed minimum J. The a=0 and no-alias cases are separately excluded. All bounds in the actual J<=m-1, D<J, L=2m²+2 application fit the paid order margins; no extra prime-order assumption enters this main theorem.

## Private unit subset and prefix theorem

The pinned density report is exactly the required BOTH-field statement. It counts total labelled row-hit incidences over the original balanced order-qualified supply and current menu, O(K_* M^6.969), deletes inputs with at least M^.997 hit rows at any one candidate/field, and charges O(M^5.992) exceptions. Its final simultaneous bound is J-2M^.997 unit COMPLETE rows for every L<=4m². This is not a theorem about the new arbitrary-composite-order beta on every input.

A complete product unit in Z/N implies each of its factors is a unit. Therefore restricting privately to those rows gives a genuinely unit cumulative prefix through L. The low-digit quadratic has at most two tags per literal offset, giving Theta(m) distinct offsets after deduplication. The subset is a proof witness, not a paid discovery procedure; it deliberately loses forced-collision coverage. These distinctions are explicit in both reports.

For the prefix theorem, shifting to a regular sample loses at most M-1 samples with M=(D_k+1)(D_h+1). Group repeated h-powers first. Confluent Vandermonde/Hermite evaluation, converted from falling factorials by factorials of orders <=D_k, is valid when characteristic exceeds D_k; it does not require characteristic greater than M. The report never extends the original nominal-r equation range after dropping identically zero coefficient functions. This avoids the finite-range pitfall.

After division by the unit prefix, B_t(Q)=prod_(i<t) A(q^(j+i)Q) has exact degree Jt. Frequency grouping, alias determinant bound and formal coarsening are valid with Jr replacing J. If a=0 or there are no aliases, strictly increasing B_t degrees exclude cancellation over K(Z). If a is nonzero, use the smallest effective t_0 and divide by B_(t_0); all later terms have A(q^(j+t_0)x^b). If there are no later terms the same identity immediately forces the coefficient zero, so no edge case is omitted.

At the Jb roots of that factor, separability uses b<=D_h<p. Images under h^j x^(-a) are distinct: equality implies a-th power of a root ratio is 1; the ratios are in the PRIME-order beta subgroup, and 0<|a|<=Jr<R. The ratio is therefore 1; gcd(a,b)=1 then gives equality of roots. This is the essential prime-order input and cannot be replaced merely by large composite order. Polynomial root counting over K(Z) now gives the contradiction D_h<J<=Jb. The proof also covers mixed ordinary-index coefficients and finite h-order. The coefficient field K(Z) is formal here; numerical field constants remain constants.

The fixed/polylogarithmic parameter specialization is valid on the old retained source: R>c m^2.031 dominates JrD_h, while the number of required samples is m times a polylogarithm, below L=Theta(m²). The matrix consequence correctly imports the earlier scalarization bounds and its regularity/degree charges rather than claiming a new scalarization constructor.

## Provenance and limits

G15 already proves same-clock finite-prefix rigidity K<=h*deg(F)+delta with delta<deg(F), distinct clock nodes and nonzero prefixes; its application explicitly pays zero-freeness by phase padding. Both new reports credit that prior result. Their additions are arbitrary geometric-clock transition degree rigidity, and arbitrary-clock/mixed-index prefix rigidity on a separate private unit restriction. The old G15 supplied product can have multiplicities; the new root-injection application uses deduplicated distinct targets, as explicitly constructed.

No claim is made that cumulative ratios remain defined on the full collision rectangle, that the private subset is cheaply found, that unit density transfers to the new all-input base, or that the representation obstruction lower-bounds arithmetic operations. Higher-degree or genuinely multigeometric representations, selected-output methods and direct factoring remain outside these statements. I found no correction requiring a report mutation.
