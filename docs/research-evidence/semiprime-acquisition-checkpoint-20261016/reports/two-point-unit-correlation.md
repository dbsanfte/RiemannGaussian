# Two-point unit correlation: exact acquisition target, unpaid

No universal soft O(N^(1/6)) acquisition is proved.

For N=P Q, distinct odd primes, define u_N(x)=[gcd(x,N)=1] and C_N(a)=sum_{x mod N}u_N(x)u_N(x-a). For gcd(a,N)=1, CRT gives C_N(a)=(P-2)(Q-2). Hence C_N(1)=N+4-2(P+Q).

For an odd auxiliary prime r not dividing N, knowing C_N(1) mod r gives t=(N+4-C_N(1))/2 mod r. Scan r candidates for roots of X^2-tX+N. There are at most two; they cover P,Q mod r, with repeated roots harmless. No division by a discriminant or P-1 is used. If r divides N, a gcd factors N. Therefore computing C_N(1) mod r in soft O(r^3), r~N^(1/18), would close the supplied conditional consumer in soft O(N^(1/6)), subject to its separately paid setup.

Coverage is elementary: modulo each factor exactly the two distinct classes 0 and 1 are forbidden. CRT multiplies the allowed cardinalities.

This is one matrix element (A^2)_{0,1} of the publicly specified adjacency matrix A_xy=[gcd(x-y,N)=1] of the unitary Cayley graph. It needs neither full spectral data nor full trace. The graph is K_P tensor K_Q after CRT.

CHARGE BOUNDARY: direct evaluation uses N gcd predicates; cyclic convolution uses N entries. Neither is within budget. Grouping x modulo r does not automatically give a closed r-state kernel, because gcd(x,N) retains the hidden-factor progression boundaries. Although the adjacency algebra has dimension at most four after CRT, its structure constants contain the missing P+Q or factors; invoking dimension four as a cost argument is circular.

Concrete next operator: factor-free additive convolution compression for the gcd-unit indicator, evaluating just C_N(1) modulo r with O(r) or O(r^2) states. No such compression is established. This is an exact different arithmetic target, not an available factoring algorithm. It may be easier to attack than a complete divisor-boundary sum because it involves only two forbidden translates, but that is a research suggestion, not evidence of the required bound.

Primary context: Klotz and Sander, Some properties of unitary Cayley graphs, EJC 14 (2007), R45, https://www.kurims.kyoto-u.ac.jp/EMIS/journals/EJC/Volume_14/PDF/v14i1r45.pdf . Identities above are proved directly; no complexity result is imported.
