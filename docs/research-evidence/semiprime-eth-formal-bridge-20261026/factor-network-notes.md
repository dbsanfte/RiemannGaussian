# Executable macro-FFT compiler

`factor_network.py` is standard-library-only. It implements the EXACT finite network in the paper study; it does not implement a contraction solver, search for factors, or establish a new runtime from tests.

API:

- `compile(N)` returns a `Network` with actual ordered `vertices` and `edges`. Every vertex's `entry(bit_tuple)` evaluates its 0/1 local predicate; it emits no truth table.
- `descriptor()` exposes ordered bit ports, edge endpoints, local predicate kind/parameters, bipartition, and input-bit maps. Its finite size is O(L) ports/edges and O(L log L) wiring bits; local integer constants have polynomial total size.
- `witness(P,Q)` computes both forward transforms, canonical pointwise residues, inverse transform, flags and INTEGER carries, fills every subdivided bit edge, and validates every local predicate. It accepts exactly representable nontrivial positive factor pairs of N; such pairs automatically have at most L bits. Out-of-range inputs force an invalid encoding instead of silently truncating.
- `restrict({edge_id: bit})` changes existing vertex predicates without introducing ports/variables. This supplies the prefix-conditional network used in witness self-reduction.
- `statistics()` reports exact construction counts and the proved coarse bounds, not contraction performance.

CLI example: `python3 factor_network.py --N 49 --P 7 --Q 7 --output /tmp/example.json`. Add `--descriptor` only when an explicit wiring dump is wanted. Without P/Q it only compiles and reports construction statistics.

`test_factor_network.py --output /tmp/replay.json` runs ten focused structural controls: wiring/bipartition, noncanonical residue rejection, integer-carry overflow rejection, invalid/trivial supplied pairs, a square, unequal/equal FFT axes, prefix restrictions, equality subdivision, inverse-transform coefficients, and DFT inversion over the COMPOSITE auxiliary ring 2^32+1. Recorded results are `factor-network-validation.json` and `factor-network-validation.txt`. No truth-table enumeration, semiprime-success campaign, contraction timing or oracle factoring run is included.

The implementation uses L=N.bit_length(), exactly ceil(log2(N+1)) for positive N. Parameters are the root's safe choices n=least power of2≥4sqrtL, b=n/4,d=ceil(L/b), auxiliary modulus2^n+1, root4. Local FFT entry evaluation uses a direct polynomial-time DFT; macrovertices are not expanded into gates. Counting precision2L+1 and s=1024L are metadata for the separately audited theorem, not executed arithmetic-counting routines.

This executable version uses explicit one-word twiddle vertices and carry-endpoint
vertices. The earlier mathematical construction folded those into adjacent
predicates, so its smaller exact edge formula is not the executable's formula.
Here the pre-subdivision bit-edge count is exactly
`E0=(13*n+1)*(n+1)+4*d-2`, and the original vertex count is
`V0=7*n+2*d+3*(r+t)+2`. Subdivision gives `2*E0` edges and `V0+E0`
vertices. Both implementations retain O(L) edges and O(L^(3/4)) maximum degree;
the established coarse constants cover this explicit version.
