# Independent cross-review: shared recurrence and literal slice union

26 October 2026. Read both scratch reports and checked their finite
identities against the frozen common-character/phase-index/Gauss query
interfaces. No tests, source edits or repository changes.

**Scoped PASS.** The executed multiplication/envelope calculation and
Omega(k^3) distinct INTEGER-label count are sound. Their stated scope is
important: neither is a runtime, circuit, numerical-value-distinctness,
or factoring lower bound.

## Shared recurrence and finite multiplication

- For P_K(Z)=product_(h=0)^(K-1)(1-Zq^(-h)), shifting Z to qZ
  replaces exponents [1-K,0] by [2-K,1]. The displayed two endpoint
  multipliers therefore give the exact cleared recurrence. Its
  arbitrary-source coefficient may vanish; the native q-clock guard
  alone does not make it invertible.

- Writing r=rho+L*d gives
  `B_G^r-q^t = unit*(1-B_G^(rho+L*(d-t)))`.
  The exact source label satisfies
  `floor(E/H)=d+F_j*r+Cclock_j*s`, so its finite clock support is
  precisely `v=floor(E/H)-h`. No canonical carry is lost.

- Complete rho=0,...,L-1 and consecutive v=a,...,b reindex
  bijectively to every integer n in [La,L(b+1)-1]. The finite
  multiplication formula is valid over the composite ring, including
  negative endpoints. Literal n=0 is omitted BEFORE evaluation;
  no gamma-function or analytic normalization is being specialized.

- The extrema +/-S_E are actual signed-box extrema. With A,B>=2,
  at least one basis b-coordinate nonzero, |a_i|<=H and 0<=lambda_i<H,
  its label has magnitude at least N-2H. Thus S_E>=N-2H, and the
  completed factorial envelope has length Omega(N/G). For G=4 its
  symmetric positive extent certainly contains [1,ceil(sqrt N)]
  under N>256H^2. The old order/factorial fallback is consequently
  legitimate, but is not an acquisition of the original scalar.

- The proposed soft(S+sqrt T) bound is a SUFFICIENT block-acquisition
  theorem: group common-base intervals dyadically by length and sum
  inherited joint geometric-product bounds. It is not asserted that
  the actual family admits the stated S,T. Added nonzero labels have
  polynomial height, so the old extractor, including T_ext once,
  is the correct recovery interface.

## Actual fixed-scale label count

- A public p0 in (sqrt N/2,sqrt N] exists in the enumerated range.
  At this scale a_span<8k<H/2 and b_span<4k. Thus every j=2 mod3
  cell really passes the filter, regardless of the hidden factor
  scale; these are not freely chosen artificial points.

- There are k/6 such odd unit colours. Surjectivity of the lattice's
  b-projection implies one basis b-coordinate is a 3-unit. In every
  odd signed coordinate interval of length at least three, at least
  half its values along that direction give 3-nonzero b. Therefore
  each actual cell has Omega(k) such differences and Omega(k^2)
  difference/clock presentations.

- The error bound `|K-bN|<(8k+1)H`, together with N>256H^2,
  makes equal integer K force equal INTEGER b across all these cells.
  Modulo 3^e,
  `K/(bN)=(1-j^(-1))^2`. For j=2 mod3 the square-root branch
  `1-j^(-1)=2 mod3` is unique because the sum of two such roots is
  a 3-unit. The odd representative then determines j modulo k.
  Hence the selected different colours share none of the counted K.

- Splitting each signed coefficient box into four sign rectangles
  makes every same-piece difference an admitted source difference.
  Equal K would give a short literal q-shift, excluded by the actual
  filter, including negative shifts by reversal. Thus multiplicity
  is at most four per colour/scale. The resulting Omega(k^3)
  distinct integer labels is proved with all stated native filters.

- A literal normalized support position fixes K=G*n1-H*t, so the
  count survives unimodular basis changes and interval-union
  coalescence. Optional inversion identifies at most K with -K,
  changing only a constant factor; no numerical separation of
  beta^K values is claimed. Long support may still have a short
  descriptor or a fast implicit scalar algorithm.

The basis-minimization lemma also checks: the row gcd forces
s=delta/G to divide C, and C=s is attained by solving LF=-1 mod s.
When delta=G, row (G,H) is indeed legal. Thus the negative support
conclusion does not rest on an unjustified mandatory large clock step.

No substantive correction is required. Retain the explicit exclusions
of smaller coverage-preserving subfamilies, modular aliases, implicit
norm algorithms and general runtime lower bounds when summarizing.
