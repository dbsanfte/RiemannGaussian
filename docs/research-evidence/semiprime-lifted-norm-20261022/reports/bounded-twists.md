# Bounded public twists of the lifted norm relations

22 October 2026. Resumed bounded investigation; no network, tests, examples, backend, repository or frozen-packet edits. Preserve the earlier reviewed lifted-relation consumer. No universal completion theorem was obtained.

Put M=m³ and retain the native exact relation v_j²-4a_jN=M z_j. For any public integer t the twisted pair

    v_(j,t)=v_j+tM,
    z_(j,t)=z_j+2t v_j+t²M

is acquired exactly and satisfies the SAME relation with a_j. For a supplied set of polylogarithmically many t of polynomial magnitude, the entire family has soft O(m) entries and bits in the native regime. The previous coprime-base/signature/normalized-root algorithm screens every useful two-entry square dependency in this expanded family in soft O(m). Thus twist generation and all-pairs consumption are paid. What is missing is a theorem forcing an actionable pair, not its detection.

Before that consumer, compute gcd(v_(j,t),N); a proper result factors N. If it is N, do not treat the associated nonunit norm as invertible: it supplies no factor by itself. Record or discard that entry. For polynomially large t, the earlier |v|<N argument need not apply, so this exceptional branch must be handled explicitly. After retaining only gcd-one entries, their z values are nonzero units modulo N. Their integer size remains O(log N) bits.

## A forced square-class construction and its exact nontriviality limitation

One can force z'=z s² by seeking a rational point on the conic

    v'²-Mz s²=4aN

through the already known point (v,1). Take the public rational slope lambda and set v'=v+lambda(s-1). The second intersection is explicitly

    d=s-1=2(Mz-v lambda)/(lambda²-Mz),
    s=(lambda²+Mz-2v lambda)/(lambda²-Mz),
    v'=v+lambda d.

This is an exact useful construction of rational same-square-class norm relations. However, it does not force an actionable second modular square root. Suppose lambda is represented by a rational number whose denominator is a unit modulo N, and lambda²-Mz and s are also units. Reducing Mz=v² modulo N gives

    s=(lambda-v)/(lambda+v),
    v'=-v (lambda-v)/(lambda+v),
    v'/s=-v modulo N.

All cancellations are legal because lambda²-v² is a unit. The normalized new root therefore differs from the original root by a GLOBAL sign and their gcd comparison is trivial. The other intersection is the original point. Clearing rational denominators does not change this conclusion if the denominators remain units. A nonunit encountered in these checks may already give a proper factor, but no bounded public slope set is proved to force that event. This is an exact audit of this particular rational construction, not a lower bound on integral conic methods.

To obtain an actual representative twist, the rational point must additionally have integral v', integral s, and v'≡v modM. Even if those divisibility requirements happen to hold, the global-sign conclusion above persists on its unit branch. An independently acquired integral point not covered by unit slope denominators may be useful; the formula does not acquire one at the required clock.

Similarly the transparent compatible scaling (a,v,z)→(c²a,cv,c²z) supplies only a globally scaled root, hence a trivial normalized comparison. If a' is instead reduced to its prescribed representative modulo m or M, keeping v'=cv+tM gives

    z' = c²z+2tcv+t²M+4(c²a-a')N/M.

The last term is integral when M divides 4(c²a-a')N, for example when a'≡c²a modM. Merely reducing a' modulo m is insufficient. Changing representatives while restoring cubic divisibility generally requires a fresh lift and changes the norm's integer square class. No free square-class equality or nontrivial root follows from compatibility modulo the auxiliary prime.

The two opposite lifts v,-v likewise give the same z and only opposite GLOBAL roots. Choosing both Hensel signs cannot by itself establish nontriviality.

## Exact unproved premise and higher dependencies

For the acquired bounded-twist family, the useful pair premise is: two retained same-sign norm values have square product, and, after writing z_i=sigma D s_i² and z_j=sigma D s_j², their normalized roots v_i/s_i and v_j/s_j are NOT equal up to a global sign modulo N. The reviewed consumer certifies this premise and factors whenever it holds. No argument was found forcing it for a constant or polylogarithmic public twist set on every native input.

For higher dependencies, the exact needed object is a supplied subset with product(m z_i) an integer square, together with the condition that the resulting modular roots differ at the two primes. A coprime-base parity matrix can describe that search without prime-factorizing the norms, but neither existence, inexpensive general kernel extraction nor useful nontriviality is supplied by the cubic congruences. No pigeonhole based only on the number of auxiliary roots, smoothness heuristic, or generic Coppersmith independence assumption is used.

Outcome: bounded twists extend the paid input family and retain the soft-m all-pairs consumer. The natural rational parametrization that guarantees square-class equality has an explicit global-sign identity on its unit branch. A universally useful independent integral relation, denominator factor, or higher dependency remains the precise open premise. No rate gain or general obstruction is claimed.
