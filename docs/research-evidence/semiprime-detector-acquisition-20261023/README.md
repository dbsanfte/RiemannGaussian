# Structured coefficient catalog and collision-detection audit

23 October 2026. **No whole-family soft-O(r) detector or improved factoring
exponent is proved here.** The goal remains deterministic worst-case
soft-O(N^(1/6)) semiprime factorization, followed by executable and Lean
bit-complexity integration. The new construction below pays the source;
the product/count/selection query remains open.

## What was acquired

The [explicit catalog proof](reports/structured-catalog-proof.md) replaces
the previous per-residue Gauss output by bounded coefficient progressions.
For r=Theta(N^(1/6)), H=r^2, M=r^4 and each public factor-size window P0,
put A=floor(sqrt(N)/P0), T=floor(H/(A+1)). Enumerate

    1<=a<=A, 0<|C|<=T, CN=a mod r.

There are fewer than 3r descriptors per window, acquired in soft O(r)
total bit work over the logarithmically many windows. Each determines
one s=1 mod r and the actual centered B modulo M. A cyclic-gap argument
proves coverage of every surviving semiprime. Its true multiplier and
seed satisfy

    M sigma=a c^2P+B c+CQ, 1<=c<r, |sigma|<7r/2, |aC|<r^2.

This is a simpler all-input source, not a collision acquisition algorithm.
The [independent catalog review](reviews/structured-catalog-review.md)
and [acquisition review](reviews/acquisition-review.md) check its algebra,
costs, and zero-leaf handling. Unlike the old one-row-per-s family, many
descriptors can have s=1; the proof deletes individual public-zero leaves.
The inherited short-annihilator recovery applies to every useful saturated
leaf after the stated preparation.

The [direct arithmetic report](reports/arithmetic-detector.md) gives an
actual soft-O(r*|R|) decoder for a supplied rational menu R: solve one
integer quadratic per row/menu entry, then take a gcd. The menu itself
is not supplied by the catalog.

## What the selector investigation establishes

The [ratio analysis](reports/ratio-selector-continuation.md) proves

    denominator(sigma/c)=c/gcd(c,C).

Changing B by a multiple of M only adds an integer to the ratio. A
bounded-coefficient selector that must cover every AP residue/multiplier
label cannot pay for only soft-r explicit ratio tests, even with different
menus for different descriptors. More precisely, with J single-label
descriptors, total menu size L, |C|<=V, Pi primes in (r/2,r), and
b_V=floor(log(V)/log(r/2)), it must satisfy

    b_V J+L >= r Pi.

For V<=r^2 polylog(r), this requires order r^2/log(r) total volume. This
is a limitation of that residue-wise universal selector. It does **not**
exclude a method that uses N to select only its actual hidden divisor
labels, nor a decoder that avoids explicit ratio menus. The
[final selector review](reviews/ratio-selector-final-review.md) and one
[exact counterexample replay](implementation/ratio-counterexample-replay.json)
record that scope. There is no semiprime coverage campaign.

## Product, character, and discriminant checks

The [norm report](reports/norm-detector.md) retains the full product in an
exact short Ore-operator word and gives a checked recovery interface for
a rational output with the same local zero set. Evaluating that word on
the row data remains unpaid. The [finite-theta investigation](reports/theta-displacement-check.md)
pays its aggregate endpoint units but leaves corrections inside the
collision differences. The standard elliptic Cauchy specialization
degenerates; a low-rank displacement of the entry matrix does not compute
its entry product. The [independent norm/theta review](reviews/norm-theta-review.md)
checks these distinctions. Neither report claims a new detector.

The [count report](reports/count-acquisition.md) identifies the correct
square-completion modulus as the hidden local order. A public Jacobi
substitution modulo N can reject a genuine witness; its
[fixed replay](implementation/check_integer_character_filter.py) verifies
that exact failure. The [discriminant continuation](reports/discriminant-relations.md)
retains the cubic lift carry and shows that the clean norm identity gives
an already known global square root. Integer-square discriminants, or
duplicate discriminants among distinct descriptors in one window, really
would factor N in budget; no theorem forces either event. Smooth-part
computation does not supply enough useful square relations by itself.

The [trace-target clarification](reports/trace-target-audit.md) is a
research gate: the inherited ordinary cofactor family already admits h
specified power traces, and its length-h product prefix for h<=r, in
soft O(h). It still lacks the desired full detector. Faster traces in the
quadratic source therefore need a proved detection link before they count
as progress on the acquisition goal.

## Verification and remaining task

The [root review](reviews/root-review.md), independent reviews, three
focused identity replays, and [source pins](source-pins.json) support this
checkpoint. [Validation](validation.json) records the archival checks;
all 234 entries of the 13 preceding packets are preserved. These checks
are not a formal Lean proof, runtime certificate, or exponent improvement.

The remaining mathematical task is to acquire a useful collision, exact
local count, or alternative N-dependent witness within soft O(r) total
bit work. The constructive options tested here have not achieved that.
Complete bit-complexity and Lean integration would still follow a detector
theorem. No broad build, commit, or push was performed for this checkpoint.
