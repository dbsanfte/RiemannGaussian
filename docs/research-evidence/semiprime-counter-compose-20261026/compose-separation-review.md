# Counter composition and separation: semantic review

26 October 2026. **PASS for the finite algebraic composition and its stated certificate interface.** Reviewed root-owned `SemiprimeCounterCompose.lean` and `SemiprimeCounterSeparation.lean`, including the final finite-sample design cleanup, against frozen `semiprime-shared-counter-20261026/shared_counter.py`, paper Lemmas 3.2/3.3 and Proposition 3.4, and the supporting Native/SharedSummary definitions. No root-owned source was edited. Root performs the modules' strict compilation and axiom/lint audits; this report is an independent semantic/scope review, not a claim of a full machine proof.

## Local certificates, not the desired aggregate

`NodeCertificate` supplies an explicit partition equivalence A≃Sigma Local, a factor's assigned group, rational measurement rows, a finite measurement enumeration, exact readout of each row dot product, and off-group row-span coefficients. None of its fields asserts the desired global contraction, a precomputed packet, or the final count. The representative field is constrained only to match the selected measurement on each nonempty local fibre. This is local data that can be obtained by finite Boolean scans; its correctness does not depend on knowing the contraction.

`basePort_invariant` proves invariance from those local row spans and measurement readouts. `groupValue_invariant` then proves the necessary invariance for the actual streamed tensor products; it is not supplied as an additional oracle hypothesis. Fixed correction polynomials may depend on the finite Möbius choice U, but are independent of the original assignment x, precisely as in the implementation and paper (3.7).

The certificate does not assert integrality, bounded summary counts, row l1 limits, or inexpensive representatives. These are quantitative constructor/implementation obligations, not prerequisites for the exact finite identity. An application cannot infer the algorithm's speed solely from the existence of an arbitrary finite certificate.

## Actual bits and fibre packet

`splitAssignment` is a genuine equivalence between subsets of original coordinates and products of local Boolean assignments. It does not create independent Boolean copies for repeated factor incidences. `forced_splitAssignment` is exactly the iff that an original forced set S lies in x iff every corresponding local bit is true. The inverse direction uses the original partition equivalence, so no coordinate is lost.

The right side of `fibrePacket_eq` enforces S⊆x on the actual original assignment. On the separated side, `localForced` applies to the local **summation assignment a**, not to the representative. This matches the code, which finds unforced representatives and applies the forced-bit test only inside each fibre subtotal. The representatives may violate forced bits without affecting correctness.

Measurements may include empty fibres. Their local subtotal is zero, hence the full product contributes zero. This matches the implementation's early skip of a measurement tuple when any group has no representative. Empty groups and zero-arity factors are also consistent: a group has its unique empty Boolean assignment, and each factor appears exactly once through its assigned group.

`Function.update (representative y) g a` is the implementation's state with the active group set to a and every other group at its representative. The proved off-group invariance justifies this value. The code resets active groups after each subtotal, matching this fixed-reference expression.

## Native corrections, signs and the common cutoff

`nativeCorrection` uses the positive coefficients of the actual shifted replacement rows: monomial z^(k+1), k=0,...,R-1, with coefficient summed against indicator(U). Its constant is zero. `fibrePacket_native` therefore computes the actual P(t) dot x + (P(t+z)-P(t)) dot 1_U input, for bounded-degree rows, rather than an unrelated correction family.

`rawPacket` sums S with |S|<=J-1, U subset S, and coefficient (-1)^(|S|-|U|). Thus S is the code's E, not the code's U. Its forced set is S. The sign and placement agree with the streamed `mobius_pairs` and `separated_fibre_sum(..., forced=E)` loops.

`rawPacket_coeff` uses the already proved **native** Taylor diagonal, so no desired coefficient identity or degree filtration is assumed in its signature. The scalar base depends on original x, while the correction rows do not. `nodePacket_eq` proves equality modulo X^J from equality of every retained coefficient j<J. This is exactly the common J-coefficient packet the code stores. Interleaving truncation after each jet operation is a quotient-ring execution refinement, not a different finite algebra expression.

## Q, R, J and Hermite readout

The final precision is J=floor((sum arities)*R/Q)+1, with Q>0. Native degree <=(sum arities)*R and the strict precision inequality imply degree<QJ. This is the actual code's scope-incidence degree bound; it does not invoke a fixed scope-width theorem, omit the top retained coefficient, or substitute an effective smaller R without proof.

The cleaned `counterValue` now requests `NodeCertificate`s **only for t:samplePoints Q**. There is no residual all-rational-node certificate premise. The subtype sum enumerates precisely the Q nodes 1,...,Q, and `Finset.sum_coe_sort` converts it to the finite Hermite sum with no repeated nodes or extra sample requirements.

At every node, `nodePacket_eq` supplies the actual global polynomial's truncated Taylor packet. The Hermite expression keeps its constructed local quotient, cardinal factor evaluated at zero, and evaluation of the quotient at -t. These signs and normalizers match the code. The theorem obtains the original contraction by row restoration at zero; it does not assume either the original count or global packet equality.

## Tail/code consistency (author self-audit of CounterTail)

The newly owned `SemiprimeCounterTail` source was separately strictly compiled and all-declaration audited. This paragraph is a consistency self-audit, not independent peer review of my own proof.

The finite mean has Q trials, theta=(r-1)/(2r), and the exact code interval. The numerator is the literal outside sum of choose(Q,k)*(r-1)^k*(r+1)^(Q-k), with k=0,...,Q. Its normalization is proved, and the final integer inequality is numerator*(2*r^2*lambda)<=(2r)^Q. This equals the code's numerator*tau_denominator*r*b<=denominator when tau_denominator=r*lambda and b=2. The looser Chernoff constant 32 still gives exponent at least64nu from the actual schedule; no Q-1 substitution or supplied probability bound is used.

`exactScheduleGuard` includes actual positive dimensions, r>=2, 1<=R<Q, tau denominator>=2, interval containment, both balance tests, tail acceptance, R>=32 and6R<=Q. Incidence n<=M<=b*n is automatic for M=2n,b=2. The natural interval numerator is proved nonnegative on these ranges, so natural subtraction agrees with Python's signed-floor formula. Exact integer closed forms correspond mathematically to the previously reviewed streaming recurrence; operational refinement of the Python helper remains part of the implementation boundary, not claimed by this theorem.

## Remaining obligations

No substantive mathematical correction is requested. The remaining obligations are explicit: instantiate the local certificates from the constructed layout and actual finite measurement boxes; identify representatives with their streamed scans; prove array/jet/truncation/inverse execution correspondence; charge all integer/Fraction, enumeration, construction and Hermite bit/space costs; connect the actual network compiler and unique extensions; and compile the factor-prefix wrapper to the required primitive machine. CounterTail now removes the prior mathematical binomial-tail acceptance gap, but not those execution or runtime obligations. No new runtime bound follows merely from this semantic PASS.
