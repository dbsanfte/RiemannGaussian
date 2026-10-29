# Composed shared-summary counter, exact tail guard, and bit-network bridges

26 October 2026. Goal **active**: pursue the 1/6 (or better!) scaling goal.
The previous goal turn made progress. This checkpoint advances the same complete
factoring objective; it does not declare that objective achieved.

The main new result is
`RiemannGaussian.SemiprimeCounterCompose.counterValue_eq_original`: one compiled
theorem now joins the native rows, Boolean cancellation, measurement-fibre sums,
retained Taylor packets and explicit Hermite readout to the original contraction.
The original count and packet equalities are proved, not supplied as hypotheses.
The theorem requires local design certificates whose construction and cost still
need the implementation bridge described below.

## What is now proved

| Module | Substantive result | Boundary |
|---|---|---|
| `SemiprimeCounterNative` | Native H restores the original contraction at zero; total-incidence degree bound; actual shifted-row/Taylor/Möbius identity | Algebraic native row model |
| `SemiprimeCounterSeparation` | Actual off-group row-span witnesses imply streamed factor invariance and the separated fibre identity | No invariant or aggregate-count oracle premise |
| `SemiprimeCounterCompose` | Exact finite counter expression equals the original contraction, with J=floor(MR/Q)+1 | Local certificates and finite algebra, not yet the full array machine |
| `SemiprimeCounterTail` | The actual integer tail guard and all mathematical schedule checks eventually hold for b=2, M=2n, w<=C*n^(3/4) | No remaining tail/acceptance hypothesis; code-loop refinement and source-constructor guard conversions are separate |
| `SemiprimeJetRecurrence` | Literal inverse-coefficient recurrence, retained addition/convolution, and denominator-first truncation agree with Hermite's quotient | Cached-loop execution and bit cost remain |
| `SemiprimeCounterSearch` | The actual counter supplies correct prefix counts; sound search, exact emptiness, at most L+1 count calls | Same scopes and arities; all counting costs still must be charged |
| `SemiprimeBooleanNetwork` | Literal bit-word local relations count ordered nontrivial integer factor pairs within the input width, with unique internal extensions | This relation still has larger direct Fourier scopes |
| `SemiprimeMacroBitNetwork` | Canonical two-stage macro arrays, inverse normalization, unique intermediates, OR flags, exact signal-family sizes and macro arities | Complete producer/consumer graph assembly and its size connection remain open |

The source modules are snapshotted here. The source of truth remains the matching
files in `RiemannGaussian/`; hashes and strict verification are in
[review.json](review.json) and [combined-audit.log](combined-audit.log).

## Exact counter composition

For every sample node, an explicit partition equivalence splits original bits
into local groups. Finite row-span coefficients prove that other groups affect
a factor only through their shared measurements. Representatives need only
match measurements; the actual local summands enforce the forced bits. This
handles empty fibres without supplying their counts.

The fixed-U corrections are precisely the positive Taylor coefficients of the
native replacement rows. The signed menu |S|<=J-1, U subset S, forces S and yields
all retained coefficients. Hermite recovery then uses the actual packets to
recover H(0), which native restoration identifies with the original contraction.
Certificates are required only at the Q sample nodes, not at all rational nodes.
See [the composition proof account](composed-counter-proof.md) and the
[independent review](compose-separation-review.md).

Prefix search now uses this actual counter. Prefix constraints are inserted at
every existing occurrence of the fixed bit; coordinate coverage proves that
this is the same restriction on the original assignment. Scope sizes, variables
and incidences are unchanged. The counter's rational result is proved to be the
natural accepted count, so taking its natural floor introduces no approximation.
See [search notes](search-proof.md).

## The previous numerical tail gap is closed

The tail module proves a finite Q-trial Chernoff estimate for the exact centered
interval. The looser sufficient bound is

`tail <= 2*exp(-R^2/(32Q)) <= 1/(2*r^2*lambda)`.

The actual schedule gives R^2>=16*lambda and 128*nu*Q<=lambda, hence an exponent
at least64*nu. Exact denominator clearing proves the literal integer comparison
used by the guard. The final eventual theorem includes the other schedule tests
and allows the needed growing arity. See [tail proof](tail-proof.md).

This is a uniform theorem, not an extrapolation from successful input examples.
The integer closed form is proved; refinement of the code's consecutive-term
loop remains an execution obligation.

## What still blocks the complete scaling guarantee

1. **Construct the quantitatively bounded design.** The exact counter theorem
   accepts local row certificates. We must connect the actual layout producer to
   these certificates, measurement dimensions/ranges and construction cost.
   The published Lean constructor uses a different block/leftover representation,
   stronger load/head guards, and a Q-1-centered spectral interval. It cannot be
   substituted merely by citing our Q-trial guard. The source comparison finds
   a promising route through its actual integer row basis, preserving useful
   measurement ranges; explicit conversions remain necessary. See
   [the layout dependency map](layout-bridge-map.md).
2. **Assemble the complete small-port graph.** Correct macro stages and an exact
   signal-family cardinality do not alone identify all consumers and producers
   of the actual factor graph. We must join those stages to the integer carry
   relation, padding, input flags and target digits, then prove occurrence two,
   linear bit-wire count and the growing-arity bound for that graph. See
   [macro-stage notes](macro-bit-proof.md) and
   [the assembly map](macro-assembly-next.md).
3. **Prove the same execution's bit complexity.** Refine finite sums to the
   streamed arrays, cached recurrence, representative/fibre scans and prefix
   wrapper. Charge layout construction, rational/integer arithmetic, coefficient
   heights, enumeration, Hermite recovery and all-prefix space. Then connect the
   proved asymptotic envelope to actual binary length and actual wire count.

The proposed rate remains `poly(L)*exp(O(L*(loglog L)^2/sqrt(log L)))`, which is
N^o(1) under the required size connections. There is still **no complete compiled
factoring runtime theorem**. The native long-query soft-K^(5/4) rate is unchanged;
this alternative route bypasses that query.

## Verification and preservation

[CombinedComposeAudit.lean](CombinedComposeAudit.lean) imports the ordinary root
and all eight new modules, runs scoped lint, and audits every generated
declaration for custom or disallowed transitive axioms. Only propext,
Classical.choice and Quot.sound are allowed. Source/object hashes, independent
reviews and preservation checks are recorded in the packet. No finite coverage
campaign, commit, push or goal-completion claim is made.

The full pinned external SAT source build remains a separate tracked process;
see [its snapshot](external-build-snapshot.json). Continue its verified live
session 85099 rather than restarting on an observation timeout. The eight new
modules do not import that external endpoint, and its completion alone would not
prove this new factoring route.
