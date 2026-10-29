# Streamed shared-summary counter: executable interface and proof obligations

26 October2026. Scratch implementation of paper Proposition3.4, not a factoring oracle or a benchmark claim. `shared_counter.py` uses only the standard library and exact integers/Fractions. It accepts an ACTUAL supplied design; construction and parameter policy are separate. It neither invents a valid layout nor hides a direct exhaustive-count fallback.

## API

`Factor(scope, entry)` takes an ORDERED tuple of distinct zero-based variable indices and a local Boolean-assignment callback. For the factor network the callback returns exactly0 or1. Exact integer/Fraction values are also supported as a general rational contraction. Float values are rejected.

`count(n, factors, layout, validate_design=True, require_quantitative=False)` returns `CounterResult(value, stats)`. An integer-valued contraction returns an int; a genuinely rational contraction returns a Fraction. `as_dict()` gives a JSON-ready numerator/denominator result. The factor solver should request `require_quantitative=True` on its FAST branch; tiny algebra-only layouts may deliberately fail the asymptotic balance/count promises.

The agreed layout protocol has integer attributes n,r,Q,R,D, exact tau, and methods:

- `groups(t)`: r ordered variable tuples partitioning declared variables;
- `factor_group(t,f)`: assigned zero-based group;
- `measurement_rows(t,g)`: integer rows, columns ordered by that group's variables;
- `form(f,v)`: mapping global variable i to the Fraction coefficient tuple of T in P_(f,v), with v a GLOBAL member of factor f's scope.

Nodes t are1,...,Q. The implementation is compatible with `shared_layout.build_layout`/`construct_layout`. `ExplicitDesign` supplies the same protocol for hand-derived algebra controls.

## Exact design validation

The default validation checks declared indices, scope sets, exact rational coefficients, P_(f,v)(0)=delta_v, degree≤R, partitions, integer measurement rows with absolute row sum≤D, and assignment groups. For each nonassigned group it checks that P_(f,v)(t) restricted to the group belongs to the rational row span of its measurement matrix. Over Q this is exactly annihilation of that matrix's kernel. This is a polynomial-time check, not a truth-table check.

Group balance and the tau-dependent total summary-row bound are recorded separately. They are necessary for the claimed FAST complexity but not for the algebraic identity. `require_quantitative=True` rejects their failure or absent tau. Skipping all validation is an explicit caller promise, not a demonstrated valid design.

## Executed algorithm

Set d=sum_f |scope_f|, q=floor(dR/Q), J=q+1. This conservative degree bound is valid for every local multilinear extension. At each t, compute the exact shifted form jets and their constant values.

Stream every E subset of[n] with |E|≤q and every U subset E. The correction inputs are P(t)x+[P(t+z)-P(t)]1_U in Q[z]/z^J. For each pair:

1. Stream measurement tuples, one integer coordinate counter at a time. Coordinate a uses its ACTUAL symmetric row-sum radius, contained in[-D,D]; a zero row has only value0.
2. Find ONE representative in each nonempty group fibre by a Boolean-assignment scan. This representative need NOT satisfy E's forced bits.
3. Rescan that group's assignments with its measurements and forced bits, evaluate its assigned factor product at the candidate group and the fixed other-group representatives, and accumulate its jet. Restore the representative before moving to another group.
4. Multiply the group sums, sum over measurement tuples, then add with sign(-1)^(|E|-|U|).

Every assignment vector, subset and measurement tuple is streamed. No fibre list or Cartesian product of assignments is cached. Only one representative per group is retained. The resulting jet is exactly H(t+z) modulo z^J by Lemma3.3's Möbius identity.

Finally `hermite_at_zero` uses exact rational CRT/Hermite recovery. At node t it builds

    E_t(t+z)=prod_(u!=t)(1+z/(t-u))^J,
    E_t(0)=prod_(u!=t)(-u/(t-u))^J,

and adds E_t(0)*[H(t+z)/E_t(t+z)]_<J evaluated at z=-t. Its denominators t-u are explicit nonzero integers; its series inverse has constant1. It never inverts a count or a potentially zero target value. QJ>dR proves the reconstruction valid. All arithmetic is rational and exact, not modulo2 and not floating-point interpolation.

## Nonlinear local evaluation and resources

A local predicate T_f is evaluated away from the Boolean cube via the identity

    Phi_f(Y)=sum_eta T_f(eta)*prod_v(eta_v?Y_v:1-Y_v).

The code streams all2^w local assignments, computes each input-jet product, and adds it. It does NOT emit the truth table or all multilinear coefficients. This is an assignment-stream/product implementation; it is algebraically the same sum as a recursive Shannon evaluator but does not claim that its micro-operation count is exactly the Lean recursion's2^w leaves. Its cost is O(w*2^w) truncated-jet multiplications plus2^w local entry callbacks, with the chosen ordinary O(J²) jet arithmetic. Its memory is polynomial in w,J and stored coefficient height.

**Important resource contract:** algebraic correctness permits arbitrary exact rational callbacks. Polynomial space does NOT follow merely from polynomial bit length of EACH separate callback value: their denominators could have an exponentially large least common multiple. The asymptotic polynomial-space/bit-height proof applies to Boolean0/1 entries (the actual factor network), or to a separately supplied common polynomial-bit denominator and height bound for all entries. General rational callbacks have only algebraic correctness and their actual measured storage bound, not an automatic polynomial-space theorem.

For Boolean entries, the paper's common replacement denominator dden=(R-1)!Q! and coefficient bound give denominator dden^|scope| for each evaluated factor, and the SINGLE global denominator dden^d for products/sums across all enumeration. Coefficient heights are O(dQlogQ+n) up to polynomial interpolation factors. Exponentially many additions increase the numerator by the logarithm of the term count, not by an exponential denominator product. Hermite recovery has polynomial-size rational factors. This is the all-input bit-height justification, not evidence inferred from small observed numerators.

## Cost ledger

Let c_t be total summary rows, C_q=sum_(j≤min(q,n))2^j binom(n,j), w=max scope, and E_entry bound one Boolean predicate evaluation.

|Operation|Executed work/storage|
|---|---|
|Design validation|Polynomial rational row-span/restoration checks; no predicate-table calls|
|Point and subset loops|Q*C_q pairs, streamed|
|Measurement tuples|At most(2D+1)^c_t; actual row radii may reduce this|
|Representative plus fibre scans|At most2*sum_g2^|S_g| per tuple; one representative per group|
|Local nonlinear extension|2^w callbacks, O(w2^w) jet products per factor evaluation|
|Truncated jets|Ordinary O(J²) rational operations per multiplication; J coefficients stored|
|Hermite H(0)|Polynomial(Q,J) rational operations, only certified nonzero rational divisors|
|Counter total|Paper's vector-count bound times polynomial factors and2^w*(E_entry+polynomial jet work)|

Under the actual main-route schedule, b=2,d=2n,w=O(n^(3/4)), this gives the independently derived2^O(n(loglog n)^2/sqrt(log n)) bit bound and polynomial space for BOOLEAN entries, conditional on the generic paper design/identity lemmas. The executable code itself does not select that schedule or certify the paper's theorem by tests.

## Controls and output scope

`test_shared_counter.py --output PATH` runs ten focused controls, including nontrivial fractional form/Taylor/Möbius computation, second-order jets with size-two E, independent higher Hermite reconstruction, representatives that violate forced bits, narrowed measurement radii, the ACTUAL layout-constructor interface, invalid kernel/restoration/degree/partition/range rejection, empty groups/unused variables, and rational output/resource scope.

`direct_count` is an explicitly named diagnostic. `count` NEVER invokes it, and reports `diagnostics_invoked=False`. Results distinguish `proposition_3_4_streamed_exact` from `diagnostic_direct_boolean_sum`. Stats charge local Boolean-entry calls and record stored Fraction heights; they are not asymptotic performance measurements or an extrapolation from successful fixtures. Recorded JSON/text are `shared-counter-validation.json` and `.txt`.
