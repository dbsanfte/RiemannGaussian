# One fixed relation strengthens the carrier-plan obstruction

2026-10-16. Classical strengthening of the preceding static-plan theorem.
A successful cover annihilates EVERY pair/triple relation. Choosing the
first nonzero relation once per prescribed plan removes an unnecessary
factor M from the input count. Constructing that relation still scans
O(m) metadata; the saving is in counting possible successful inputs.

The [complete proof](reports/representative-and-local-carriers.md) now
excludes plans using N modulo m^4 even when the proposed geometric cover
exists only in ONE hidden prime field. Let m~M, P,Q~M^3 and B be the
prescribed plan-library size. Every row's origin differences, assignments
and positions are fixed by the specified residue. Group seeds/ratios and
selection among plans may receive full-input or factor advice.

| Cover requirement | Metadata residue | Allowed B | Success loss |
| --- | --- | --- | --- |
| Global modulo N | N mod m^2 | B<=M^2 | soft O(M^5.969) |
| Local in either hidden field | N mod m^3 | B<=M | soft O(M^5.969) |
| Local in either hidden field | N mod m^4 | B polylogarithmic | soft O(M^5.969) |

All three losses are negligible against the SAME original
Omega(M^6/log^2 M) supply. The energy qualification holds at CURRENT
candidates; counting every comparable m is only an overestimate. The
result concerns few carriers with k^2*T nearlinear, where T is total
listed length. It does not cover an arbitrarily small chosen tag subset.

The [encoding extension](reports/representative-and-local-carriers.md)
allows a nearlinear TOTAL explicit encoding of relative origins. A few
long entries can be omitted from the proof witness while retaining at
least m/2 light labels. The full cover must cover this witness; collision
coverage after trimming is not asserted. An arbitrary full-input-dependent
common origin cancels and can be absorbed into the carrier seeds.

The old cyclic-norm exponent-catalog count is credited and preserved.
The new scope comes from selecting one relation, using a higher residue
modulus, and retaining a short-origin witness. It is an obstruction to
this specified representation, without an operation lower bound or a
constructed acquisition algorithm. Full-input-dependent relative origins
and positions, larger libraries, succinct programs with uncharged expanded
lists, and other implicit queries remain open.

Two independent proof/source reviews and a separate integration review
pin the exact final bytes. These are classical proofs. The general
soft O(m^(3/2)) query bound, missing soft O(m) sufficient query, full
all-input/bit/controller proof and Lean sixth-rate composition are unchanged.
No native code, examples, Lean lemmas or broad builds were added. All
nineteen predecessor packets and exact journal entries are preserved.
