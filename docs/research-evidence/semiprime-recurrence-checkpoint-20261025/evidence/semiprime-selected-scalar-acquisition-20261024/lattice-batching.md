# Executed product fusion of residue-assisted lattices

24 October 2026. This tests a specific batched lattice constructor. It does not acquire a shorter index palette or improve the whole native query. No claim about all shared-lattice algorithms follows.

Inputs are the public N, m=d r² dividing k=d r³, gcd(m,N)=1, and the acquired class anchors J0. The frozen local-square source is `8e68b2fb169ed9f567ce7f25f4a958a41ebe574afe9be323f4cf18f2ede7af14`; the complete partial-tag decoder source is `79da1b9032b30777bd940709277f1687d47c51c5df431eb0d753168cdcfbd9cb`. Their existing scopes and prime/order guards are retained. The target is to replace m separately supplied residue decoders by fewer genuinely shared searches, without receiving the unknown t or c in the local square relation.

## An actual fused search and its initialization

Consider a smaller-prime size bin B<=P<=U=min(2B-1,floor(sqrt N)). Set n=ceil(log2 N), B=2^b and beta=b/n. Partition the PUBLIC full residue catalog 0,...,m-1 into groups C of size at most g. The full catalog is used here to give a literal initialized covering algorithm, not to claim that native class anchors have extra density. A restricted acquired catalog can use the same construction and its actual group count.

Every possible P=c+m s in the bin has s in the common interval [floor(B/m)-1,floor(U/m)], clipped at zero. Partition that interval into blocks starting at S, of length X_g. For a group C of size delta<=g acquire

    f_(C,S)(Z)=prod_(c in C)(Z+S+[m^-1 c]_N) mod N.

This polynomial is MONIC of degree delta. Acquire m^-1 by extended gcd; a proper gcd factors immediately. Product trees acquire each group polynomial, with no field inverses, and the integer coefficients used in the lattice are the canonical representatives. At the correct residue c and block, Z0=(P-c)/m-S satisfies f_(C,S)(Z0)=0 mod P. This is a single univariate unknown-divisor root problem, not a system of g guessed factors.

Use May's actual monic unknown-divisor theorem, Section3.2 Theorem6 of the primary dissertation cached and pinned in partial-tag.md. Choose epsilon=1/n and compute by exact integer powers/roots

    X_g=max(1,floor(N^(b²/(n²*g))/16)).

The real expression specifies an exact root computation, not floating-point advice. For X_g>=2 it is safely inside (1/2)N^(beta²/delta-epsilon), since delta<=g and N^(-1/n)>=1/2. The theorem's dimension and bit work are polynomial in n and g; hence they are soft-one only when g is bounded by a fixed power of log N. If X_g=1, enumerate the one Z and test all delta actual integer candidates directly.

For the lattice branch enumerate every integer root returned by the theorem, clip Z to its actual block, and test gcd(c+m(S+Z),N) for every c in C. Only a verified proper factor is accepted. All wrong groups/blocks run the same bounded algorithm. A correct P necessarily appears in some group and block. Thus this is a complete deterministic covering attempt, not a root oracle. The total number of lattice calls is

    O(ceil(m/g) * (1+B/(m X_g))).

Each group's degree, coefficient arrays, lattice dimensions, integer roots and validation costs must also be paid. There is no one-LLL assumption.

## What the execution costs

Ignoring only polynomial logarithms for polylogarithmic g, the balanced bin B~sqrt N has the following scheduled full-catalog, full-block search budget BEFORE early exit

    (m/g) + N^(1/2-1/(4g))/g.

For g=1 this is the ordinary all-residue interval method, soft(m+N^1/4), or k^(3/2) at sixth-root scale. For every fixed g>=2 the second exponent is strictly larger than 1/4. Allowing polylogarithmic g does not reverse the comparison: N^[1/4-1/(4g)]/g grows beyond every logarithmic saving. Polynomial g incurs non-soft-one lattice work in addition to a still smaller root radius. Grouping by polynomial products therefore fails to improve this scheduled complete-search budget. This is not an Omega runtime assertion on actual semiprimes: a verified factor may be found earlier and terminate the search. This is its ledger, not a lower bound on a different batched lattice algorithm. The known fifth-rate factoring algorithm is a separate better fallback and is not reclassified as new progress.

## Why the current local square does not reduce these calls

At the good class the distinguished relation is c_local=t²/a mod r², with t=(P-J0)/m. It supplies no public value of c_local. In the tested polynomial construction, retaining it with c_local as a free auxiliary residue admits every t: each t defines precisely that residue. Enumerating c_local to get two square roots modulo r² would require acquiring which residue to use; replacing this by all residues does not shrink the actual root interval. This statement is only about inserting that equation into the executed search. It does not discard its bounded-lift content or rule out a different detector.

A cross-class translation of the linear lattice does not fix this initialization: f_(c,S)(Z)=Z+S+[m^-1 c]_N. Reusing a small-norm polynomial by translating Z requires a norm certificate on the enlarged interval |Z|<=X+|Delta|, where Delta is the chosen integer representative of m^-1(c-c') modulo N (plus the actual block-start change). The acquired J0 and q carries provide no bound |Delta|=O(X) for all classes. Reducing Delta modulo N in the coefficients is not a bound on its integer translation height. No shared reduced basis with uniformly small certificates was constructed here.

The concrete result is a fully initialized product-batched algorithm and a failed cost optimization, rather than a new backend theorem. It leaves soft k^(3/2) as the existing native whole-query clock and supplies no sixth-rate acquisition. No numerical campaign, shared-source edit, hidden logarithm, unknown factor advice or q-character quotient was used.
