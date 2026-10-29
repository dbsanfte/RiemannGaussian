# Independent measurement and support-rate review

Disposition: PASS with the explicit scope boundaries below. Read-only source/API review; no edits, new compilation, or numerical experiments. Final source pins are recorded in review-measurement-rate-hashes.json.

## MeasurementBits

The measurement data path executes signed Boolean addition, physical copies, subtraction and zero scans. Its dot loop retains one actual suffix, copies every visited row word even on a false bit branch, and adds only when the corresponding bit is true. It does not compute an integer specification and assign a synthetic clock. The value, width and polynomial primitive-clock theorems concern that actual loop. There is no output-fit premise: integer scratch width grows by at most one cell per visited row entry.

Short/mismatched bit lists are deliberately totalized: a missing bit contributes zero and trailing bits are ignored. indexedTest uses List.ofFn at the same n for rows and assignments, so its actual native use has the required matched lengths. Positive/negative signed zero and leading-zero physical words are handled by numeric subtraction/nonzero scanning, rather than mistaken syntactic word equality. The target copies preserve values at their own actual physical width.

test computes every row's dot/equality and retains the recursive suffix, even when some equality is false. test_correct is exact simultaneous measurement equality. indexedTest_correct agrees with the original indexed integer equations, and indexedTest_accepted/representative_found preserve the actual false-first found word, not merely existence of a solution. Empty/unattained measurement fibres remain legitimate none results; no unique-fibre promise is introduced.

The physical width assumptions concern ACQUIRED matrix and target words. They are not desired-output bounds or a count oracle. representative_work charges every visited physical leaf test plus the existing findBits traversal ledger and has the advertised 2^n times polynomial(m,n,W) form.

Important execution boundary: indexedTest materializes lists from the supplied row/target callbacks and Boolean assignment. Its stated arithmetic leaf ledger excludes acquiring those callback words, listing/addressing a cached matrix, and the exact representation/closure/index costs of the outer representative traversal. The documentation says so. A complete machine/bit clock must attach these costs; raw integer matrix/target acquisition must not be treated as a free oracle. The current claims correctly stop at the physical leaf arithmetic and native search-control composition.

## SupportRate

weightedCount is the ACTUAL inclusive support-pair callback count, sum over 0<=j<=q of 2^j*binom(n,j), from the existing ternary traversal. weightedCount_bound applies only to 0<n and q<=n, treating q=0 separately. For q>0 it instantiates the prior choose bound at u=q and obtains the entropy form with entropy(a)=a log8-a log a; replacing q+1 by n+1 is justified by q<=n.

The continuous extension at a=0 is sound (a log a tends to zero, with the real-log convention). weightedCount_subexponential assumes the normalized cutoff q(n)/n tends to zero, then explicitly restricts to n>=1 and eventually q(n)<=n. Thus infinitely recurring zero cutoffs are covered, and finite small n or occasional early q>n are not silently asserted to satisfy the finite bound. It concludes an eventual bound exp(epsilon*n) for EVERY positive epsilon. This is an entropy/callback-count theorem, not a primitive clock or an explicit numerical threshold.

## ScheduledSupportRate

The scheduled cutoff is floor(2*n*scheduledDegree(clog2 n)/scheduledPointCount(clog2 n)). This is the correct strict-Taylor-width-minus-one support count for total incidence 2n; the public-network incidence identity still has to be instantiated when applying it to an actual graph. It is not a rate theorem for arbitrary networks with unrestricted total incidence.

The degree/sample ratio bound retains the actual rounded definitions: scheduledPointCount is the integer floor lambda/(128 clog2 lambda), and scheduledDegree is four times the integer ceiling square root. Under the stated eventual clog guard, Q>=1; the proof derives lambda<=256*clog(lambda)*Q and degree<=8*sqrt(lambda), giving the advertised 4096 ratio constant. The subsequent limit uses the true Nat.clog, not a smooth substitute. Floor division cannot increase cutoff/n, and the proof handles zero denominators only outside the eventual positive-Q regime where the natural/real divisions are both totalized.

Composing the vanishing degree/sample ratio with clog2(n)->infinity yields cutoff/n->0. scheduled_support_subexponential then obtains the exact weightedCount bound from SupportRate. This avoids importing the unpinned aggregate constant16435. It does not estimate Y, local fibre truth costs, acquisition, rational heights, storage or a whole factoring clock, and makes no all-small-input claim. Its eventual statements support the intended asymptotic tail once a separately correct explicit guard/fallback algorithm and all other cost factors are composed.

No substantive mathematical or interface correction requested. The new measurement arithmetic and the support entropy rate address different pieces; neither by itself establishes full guaranteed factoring bit time.
