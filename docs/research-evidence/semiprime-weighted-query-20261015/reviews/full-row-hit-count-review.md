# Independent arithmetic derivation: only o(m) full canonical seed rows hit on a retained majority

2026-10-15. PASS. New classical incidence bound; not a Lean theorem, runtime bound, or lower bound for arbitrary scalar acquisition.

## Exact statement

On the inherited original balanced order-qualified supply N=P Q, P,Q=Theta(M³), with Omega(M^6/log² M) ordered input pairs, permit all first-K candidate auxiliary primes with envelope K_*=O(M^.020). For each m use ALL original denominator-one seed tags 1<=j<m and the entire canonical prefix 0<=i<4m². The actual source is

    a_j j²=P Q mod m, a_j in {1,...,m-1},
    D_j=(P Q-a_j j²)/m, I_j=j^(-1) mod m,
    b_j=centered(m,-I_j D_j),
    delta_j=a_j+m b_j-2a_j j in [-3m²,m²],
    A_(j,i)=gamma^(P Q+delta_j)-gamma^(m² i).

Count incidences (N,m,field,j,i) with local residual zero. Their TOTAL over the original supply is

    O(K_* M^6.969).                                  (1)

Consequently deleting every input with at least M^.997 incidences at ANY one allowed m or in EITHER hidden field costs at most

    O(K_* M^(6.969-.997))=O(M^5.992).                 (2)

The deletion applies directly to the original supply and can be united with the frozen soft O(M^5.994) deletion. A retained Omega(M^6/log² M) family therefore has, at each allowed m, at most O(M^.997)=o(m) tags whose ENTIRE prefix row product is nonunit modulo N. All other m-1-o(m) row products are units in BOTH fields. The same bound holds for every shorter prefix, including the current native padded seedLength(m)<=4m², without an additional union bound.

The original native coverage still forces at least one local hit in the full canonical/padded query. The theorem does not identify which rows hit or supply an algorithm to find them.

## Verified source contracts

The canonical prescribed-tag source proof was read directly:

/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-canonical-query-20261015/reports/prescribed-tag-catalog-obstruction.md
SHA256 f3352537846c716c36f4ad3e191be857c484993f986f887fc770eba3e6ccfca4 (freshly recomputed).

Its historical source pins and previously reviewed endpoint/full-Euclid reports supply: m=Theta(M), exact local prime order R_P>P^.677>=cM^2.031, P,P-1 units modulo m², and the literal candidate-selector Q strips. For G_m=m-p_(-K_*)(m), fixed P,m require O(G_m+1) half-open boxes of width <=m² and sum_m(G_m+1)=O(K_*M). The large prime R_P is fixed once P is fixed, and the actual projection has that exact order for all retained partners/menu moduli. These are inherited source/supply facts, not new distribution estimates or algorithm inputs.

## All phase multipliers in one box

Fix an actual admissible P, one candidate m and one width-m² partner Q box. Let R=R_P. Local vanishing is precisely

    Q+delta_j-m² i=k R                              (3)

for some integer k, since P=1 mod R. Across the WHOLE box, ALL tags, and 0<=i<4m², the numerator on the left ranges over an interval of length at most

    4m^4+5m².

Therefore the number of possible k is

    O(m^4/R+1)=O(M^1.969).                           (4)

No hidden field order is computed by the hypothetical acquisition algorithm; it is only a proof-side count. The interval location can depend on the box but its length bound is uniform.

## Fixed k: O(m) TOTAL (Q,j,i) incidences

Fix one k in the interval (4). Unlike the sparse-catalog argument, i is now allowed to vary. This does not break full-lift uniqueness: modulo m² its entire term m² i vanishes.

Put A_j=j²-2Pj+P in F_m. Equation (3), reduced modulo m and multiplied by P, gives

    a_j A_j=P k R mod m.                            (5)

Three cases account for ALL tags and source slopes.

1. Nonexceptional false tags: if A_j!=0 and j!=P mod m, equation (5) fixes at most one canonical a_j and therefore one Q class modulo m. For two qualifying Q,Q' at this same a,j,k (possibly DIFFERENT i,i'), the source lift gives

       m(b_j(Q)-b_j(Q'))=-I_j P(Q-Q') mod m².

   Subtracting (3) modulo m² yields (1-P I_j)(Q-Q')=0 mod m². Its coefficient is a unit for a false tag, so Q=Q' mod m² and the half-open box contains at most one Q. Once Q,j are fixed, delta_j is fixed and the INTEGER equality (3) determines at most one i. Thus each such tag contributes at most one incidence, totaling O(m).

2. Exceptional tags: A_j=0 has at most two roots because it is a monic quadratic. They are false tags, since at j=P mod m, A_j=P(1-P)!=0 by the inherited P,P-1 unit premises. Allow all m-1 slopes at each exceptional tag. The same false-tag lift proof gives at most one Q for each a, and the exact equality then gives one i. Thus these tags contribute O(m) incidences TOTAL.

3. Own tag: at j=P mod m, A_j!=0, so (5) fixes a and Q modulo m. A half-open width-m² box contains at most m+1 such integers Q. Each Q determines at most one i from the exact equation. This contributes O(m) incidences. False-tag uniqueness is not incorrectly invoked here, and no own-index range separation is required.

Together these cases give O(m) incidences per k per box, not O(m²) or O(m³). There is no extra choice of i after the exact equation has determined it.

## Whole-supply total and Markov deletion

There are O(M³) possible actual P values in the bin. Combining O(m) incidences per k, (4), the boxes and the menu telescope gives

    O(M³ * M * M^1.969 * sum_m(G_m+1))
       =O(K_* M^6.969).

The local R is fixed by P and the bound is uniform in it, so no separate cofactor sum is missing. Field swapping is only a factor two. A hit incidence has been counted with its actual input/modulus/field labels throughout.

Markov's elementary counting inequality now says that the number of inputs with at least M^.997 hits at any one m/field is bounded by the summed incidence count divided by M^.997. No additional menu cardinality is charged: all menu labels were already included in (1). This proves (2). With K_*=O(M^.020), the exponent is .020+6.969-.997=5.992<5.994<6. Fixed logarithmic factors are harmless to the strict power gaps.

For each surviving input, at a given m each field has fewer than M^.997 hit incidences. Thus the union of bad rows from both fields has at most 2M^.997=o(m) tags. Since q has prime order R>4m² and gcd(R,m)=1, each row actually has at most one local zero in this prefix; this fact confirms that incidence and hit-row counting agree, although incidence counting alone already bounds the number of bad rows.

## Scope and consequence

This is full original uncentered canonical seed row-hit sparsity, not the older centered target-target root-collision mass theorem whose exponents happened to be similar. The new proof changes the counted observable and explicitly eliminates the varying index at fixed k before using the literal lift.

It does not say the full product is a unit: forced coverage remains. It does not identify the sparse hit rows cheaply, justify replacing the full row family by a fixed subset, or prove a lower bound on a norm-only/implicit scalar evaluator. Input-dependent or variable-length subqueries contained in this full prefix inherit the hit-count upper bound. Arbitrary shifted intervals outside the prefix need their own k-range analysis and are not automatically covered.

No experiment, large build, repository mutation or new native theorem was used. Only this local arithmetic review artifact was written.
