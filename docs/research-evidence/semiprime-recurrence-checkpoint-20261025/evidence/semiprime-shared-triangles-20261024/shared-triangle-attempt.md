# Actual shared triangular factorial attempt

2026-10-24. Scratch only, no examples or repository edits. The shared computation below is fully initialized. It obtains all native Euclidean carry norms in soft m^2, not below soft m^1.5. Two exact structural contractions are established (a common-step transpose and native reflection pairing), but neither removes the quadratic emitted target list in this implementation. This is not a lower bound on another implicit aggregate.

Inputs and credit: shared-affine-factorial.md SHA256 5db88f386e78d69e60861ee96471ea66896fc94e1e275c782c5d68b319f2ae57, and euclidean-carry-attempt.md in /tmp/semiprime-recurrence-innovation-20261024. All native preparation and recovery promises remain inherited.

## Distinguish the two b's

Use A_j=[N j^-2]_m, B_j=center_m(-j^-1(N-A_j j^2)/m), C_j=m B_j-A_j j. The native centered B_j is different from the Euclidean remainder R_j=m-Q_j A_j, Q_j=floor(m/A_j). Let Z_j=C_j/m+mK0 modulo N. Then the first Euclidean triangle is

    T_j=product_(i=1)^(A_j-1) product_(t=0)^(Q_j i-1)
             (Z_j+R_j i+A_j t).

The gap recurrence S(A_j,m;Z_j)=S(R_j,A_j;Z_j) T_j is exact. All small Euclidean entries are certified units modulo N because they are below m<P,Q. A_j=1 contributes the empty gap product.

## Shared factorials: an actual aggregate algorithm

At every Euclidean stage (u,v), v=qu+r, emit the actual u-1 pairs

    x_i=(Z_j+r i)/u,  L_i=qi,  1<=i<u.

The triangular factor is u^D product_i B_(L_i)(x_i), D=qu(u-1)/2. Each L_i<v<=m. The residual stage keeps the same argument Z_j and replaces (u,v) by (r,u). Iterate to u=1. This emits every operand needed for every row, rather than supposing the long triangle values are inputs.

Build the common polynomials B_(2^k)(X)=product_(t=0)^(2^k-1)(X+t), for powers 2^k<=m, by product trees/doubling. Their summed degree is O(m). For each emitted (x,L), decompose L into binary. Initialize a cursor at x; a set bit k requests B_(2^k) at that cursor and advances the cursor by 2^k. Perform one monic MPE per k on its complete requested list. Multiply all acquired values and the row scale powers u^D, retaining per-row products if correction ratios are needed. Every requested point, cursor, exponent and scalar unit inverse has O(log N) bits. None of the evaluated values is inverted.

Euclidean u-values sum O(A_j) per row, so the emitted list has O(sum_j A_j)=O(m^2) entries. The actual first stage already emits sum_j(A_j-1)=Theta(m^2): each A-value has at most two preimages j; thus at least a constant fraction of j have A_j>=m/4. Consequently this implementation explicitly constructs Theta(m^2) inputs before MPE. Binary tails add logarithmic factors. The total degree of common polynomials is O(m), target count soft m^2, and total ring-operation upper bound soft m^2. The product is acquired; a short polynomial notation is not counted as its acquisition.

Generating all first-stage starts by recurrences in i takes O(1) ring operations per emitted start. It improves constants, but the full emitted list still has quadratic length. Quotient grouping q=floor(m/A_j) changes this list organization only: the range A_j>=m/4 has q<=4 and contains a constant fraction of all rows. No subquadratic target bound follows from grouping by q.

## Exact common-step transpose

For one triangle with v=qu+r, write the original index l=qt+s, 1<=s<=q. This gives

    T(u,v;z)=product_(s=1)^q product_(h>=1,t>=0,h+t<u)
                        (z-u s+v h+r t).

Fixing (s,t) leaves an interval in h of length u-1-t and COMMON step v. In particular at the first stage v=m, all rows really share the physical step m. The normalized starts are

    (z-u s+r t+m)/m,  length u-1-t,
    1<=s<=q, 0<=t<=u-2.

This is an initialized common-factorial MPE representation with q(u-1) starts for that triangle. They can be generated and evaluated by the same binary-tail engine above. It does not identify the starts across rows: r=m-qu and z depend on the row. Since q(u-1)>=u-1, the first stage again has Theta(m^2) explicit requests across the native family. The common-step property alone has not compressed the values. No generic restriction on a different transposed algorithm is inferred.

## Native reflection really pairs triangles, with a specific lift shift

For paired labels j and m-j, A is identical. Centering gives the exact integer identity

    B_(m-j)+B_j-2A=m tau_j,  tau_j in {-2,-1,0},
    C_(m-j)=-C_j+mA+m^2 tau_j.

Thus their normalized arguments are related by

    Z_(m-j)(K')=-Z_j(K)+A+m(tau_j+K+K').

For a Euclidean triangle T=T(A,q,r;z), D=qA(A-1)/2, direct reflection i->A-i gives the polynomial identity

    T(z) T(-z-Am+A)
      =(-1)^D product_(i=1)^(A-1) product_(t=0)^(qA-1)
                    (z+r i+A t).

Proof: negating the second triangle changes its t-range to qi,...,qA-1 at the reflected i, exactly complementing 0,...,qi-1. There is no division. To realize the argument -z-Am+A with the actual paired row, choose the public block lifts with

    K+K'=-A-tau_j.

For example K=0 and K'=-A-tau_j both lie in the supplied menu envelope. This is an actual native affine cancellation, beyond merely assuming equal a-slopes.

The paired product is now a rectangle: a common B_(qA) evaluated at A-1 starts z/A+(r/A)i, plus the certified scale A^(qA(A-1)) and sign. Constructing these starts and evaluating through the shared engine still costs soft A per pair, summing to soft m^2 over the native pairs. Pairing removes a factor of two and triangular tail variation, but not an exponent. The lower Euclidean residual gap factors must also be computed; their arguments are not automatically reflected for the smaller Euclidean pair, so one cannot silently reapply the first-stage native pairing there.

This pair of period-A blocks is not asserted to cover P. Their selected K-starts occupy only a small part of the complete native lift menu when A is small. Extending to all menu blocks requires additional public blocks and tails, with their acquisition charged. No small-lift coverage theorem follows from reflection alone.

## Nonunit handling and scope

All displayed engines use only inversion of certified small scalars. For a carry correction, acquire its denominator gap norm first. A proper gcd factors. A unit denominator may be inverted after acquisition. A saturated denominator requires descent, by public row, Euclidean stage, i interval and finally the ordinary progression factors, using the same initialized restricted engines. On the native menu envelope all such physical leaves are nonzero modulo m and have absolute value <N, so a nonunit leaf has a proper gcd. No saturated gcd is itself called a factor.

An integer interval overcover containing every native leaf can instead be acquired at the old soft m^1.5 factorial clock; its proven factor coverage comes from P<=sqrt N and the full original menu, not from the carry subset alone. This is the existing factorial channel, not a gain from the shared triangle formulas.

The missing positive operation is now precise: acquire the product of these varying affine factorial values without emitting all (j,i) targets, or prove that a cheaper selected family retains a native hit. This attempt supplies actual shared evaluation and exact reflection/transposition identities, but no faster such operation and no new worst-case factoring bound.
