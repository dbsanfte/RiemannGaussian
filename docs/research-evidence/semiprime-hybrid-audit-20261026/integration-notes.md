# Integration and review resolutions

26 October 2026. The primary agent independently checked the new kernel
gap and stationary-index integrality, the residue-restricted query mass,
the exact moment-weight identity and zero band, and the native
integer-label union proof. These are paper checks, not kernel-checked
proofs. Five independent agent reviews accompany the packet.

The review corrections were integrated before archival:

* `moment-locator.md` now describes a weaker output specification,
  without claiming a computational separation. Its retained TQ product
  is explicitly `product_(i=2)^n F(x_(i-1))`; the last endpoint remains
  included even if screened as a unit. The first endpoint is the core
  at epsilon zero.
* `kernel-cover.md` Section 4 now proves
  `q^((P-1)/g)=beta^((H/g)*(P-1))=1 mod P` directly. No roughening
  assumption is needed for that divisibility. The coverage proof in
  Sections 6–7 already used the exact Fermat gap without this premise.
* Scratch-file links in the archived reports point to their archived
  counterparts or the frozen common-character input. Historical
  scratch-only wording has been clarified where it would otherwise
  misdescribe the archived packet.

The explicit integrality check for the universal kernel is useful.
At the true colour, c=[Q]_k, a=kt+cb, and
delta=2k*C_j-N-c. The stationary numerator is

    aP+bQ+kt+b*delta
       = kt(P+1)+b*((P-1)*(c-Q)+2k*C_j),

which is divisible by 2k because P is odd and k divides c-Q.
With C_j=C+epsilon and h=I-t-epsilon*b this gives

    H*(Cb-h)=(P-1)*(k/2)*(bQ-a).

The short-vector bound has |a|<Q. Thus this integer is nonzero for
every nonzero proof witness (a,b), and the guaranteed hit survives the
literal h=Cb omissions. The witness is used only to prove existence;
its unknown coordinates are not charged as acquired data.

For a supplied correct residue rho, the restricted query still keeps
all O(sqrt k) values of b. Its clock length is O(W/k+1), so the joint
evaluation and lawful recovery fit soft k. There is no hidden demand
for a unique hit or a known colour. A wrong residue has bounded cost
and can only yield a validated factor or failure. The cost of supplying
rho, or a covering polylogarithmic palette, is the open obligation.

The audit is intentionally a dependency comparison. It does not claim
an exhaustive search of pairings, a general lower bound for any of the
representations, a new classical factoring record, a new exponent, or
formal verification. The dated inventory uses explicit source locations
and the checkpoint errata; later reused language is not counted as an
independent algorithm.
