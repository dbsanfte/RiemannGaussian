# Independent review: the quadratic candidate fails its universal cover contract

2026-10-24. Reviewer: root. **PASS**.

Exact reviewed report: `quadratic-counterexample.md`, SHA256
`be4bd0ee878584be832f029202e33790fb6752ad33807397336b00e130ff1210`.
Exact reviewed and executed certificate: `tinyreplay.py`, SHA256
`5f09e0c77ea9e02e25181176928b5c29c419452ec0a157038ba6dc00268cc805`.
It targets the frozen construction `cover-literature.md`, SHA256
`28b9b5e14ac5e94a101213d17f4ca387ad959efb708160f90af66b2eb21970d1`.

I read the proof and script and independently ran the fixed certificate.
It passed using exact integer arithmetic; no random primality oracle or
search result is trusted. Trial division certifies each listed prime.
Since beta=4 is nonidentity and its powers at the prime orders r,s are
one, its local orders are exactly those primes. The explicit inequalities
check both local guards and the global order margin. The prime m=97 is
the canonical sixth-root ceiling in this instance.

The full N-sized smooth multiplier M has no prime factor r or s, so the
projected base retains both exact orders. The checked projected residue
and nonidentity gcd agree with that reasoning. The ordered initial
separator therefore has no local hit through 16m^2. Compatibility with
N-1 projection is an existence statement justified by gcd(N-1,rs)=1;
the report does not claim a particular deterministic base-selection
routine must output beta=4.

For every one of the m^2 pairs, u=mb-a lies in [1,9409], and v=mb+a
lies in [97,9505]. Each order is prime and exceeds 9409. The residues
N mod r=9721 and N mod s=445212 are both strictly above 9505 and below
their order moduli. Consequently neither order divides u nor N-v,
and neither divides Delta=u(N-v). This proves all actual group
cross-differences are units without enumerating the pair matrix.

This is a rigorous finite counterexample to a universal mathematical
claim about the proposed family. It is not positive finite testing and
does not need an infinite family of safe primes. It also does not imply
that other factoring routines fail on N, nor refute a future family
with different shifts or a stronger proved input contract. In particular
it is not a lower bound for fast recurrence algorithms.

Integration must supersede the frozen candidate report's unresolved
coverage status: universal coverage of THIS family is now disproved.
The report's conditional coverage equivalence and soft-m acquisition
algorithm remain valid. No reason remains to pursue a proof of universal
coverage for these unchanged lists.
