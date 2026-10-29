# A preprocessing lead checked against the actual query

26 October 2026. Primary-source comparison, not a generic lower bound.

[Bernstein–Lange, Computing small discrete logarithms faster](https://cr.yp.to/elliptic/cuberoot-20120812.pdf),
Section 3, describes precomputed distinguished-point tables for random-walk
discrete-logarithm searches. Its heuristic tradeoff is setup of order
sqrt(h*T) and per-target search of order sqrt(h/T). The paper reports
average experimental performance; it does not supply the deterministic
whole-family guarantee required here.

At our h=K^(3/2), choosing T=h^(1/3) makes setup of order K. The per-target
search is still of order K^(1/2); applying it independently to K targets
costs K^(3/2). Optimizing setup plus J searches instead returns the familiar
sqrt(Jh) scale. Most of our target rows need not hit the interval, so their
rejection cannot be omitted from the ledger.

There is an additional transfer obligation: our useful equality is modulo
an unknown factor, whereas the paper's table compares supplied group
elements. A representation-dependent random-walk hash is not automatically
compatible with reduction modulo that factor. A new modularly compatible,
deterministic aggregate construction could still be useful; this cited
algorithm is not already such a construction. No new implementation or
performance claim is made from this comparison.
