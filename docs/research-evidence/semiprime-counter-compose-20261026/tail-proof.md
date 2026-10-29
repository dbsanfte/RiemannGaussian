# Exact tail guard closed for the implemented integer schedule

New module `RiemannGaussian/SemiprimeCounterTail.lean`, namespace of the same name. Source imports the owned `SemiprimeCounterRate` and Mathlib only. No existing module, frozen evidence, journal, AGENTS file or pinned external source was edited.

**Result:** `eventually_exact_schedule_guard` proves eventual acceptance of all mathematical checks of the actual integer schedule for occurrence b=2, incidence M=2n, and every positive scope width w<=C*n^(3/4), for fixed C>=0. There is no assumed tail bound or assumed eventual-acceptance premise. It does not assert implementation correctness or a machine/runtime theorem.

## Finite probability proof

The finite MGF/Chernoff derivation is adapted, with explicit attribution in the module, from the pinned Apache-2.0 OpenAI proof `SqrtLog/SpectralBinomial.lean` at commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. Existing pin/license provenance is in the earlier shared-counter packet. The proof is elaborated here against Mathlib, not imported from or equated to the external schedule.

`binomialMean theta Q f` is the finite sum of choose(Q,k)*(1-theta)^(Q-k)*theta^k*f(k). A direct binomial recurrence proves its MGF bound. The one-step Bernoulli bound is obtained using convexity of exp and Mathlib's cosh(t)<=exp(t^2/2), valid for every theta in [0,1]. Pointwise domination of a deviation event by two exponentials then gives the explicit finite bound 2*exp(-b^2/(2Q)). No probabilistic independence oracle, numerical approximation or supplied distribution theorem is needed.

Our actual parameter is theta=(r-1)/(2r), and the number of trials is **Q**, not the external centered-tail module's Q-1. Exact natural-division floor inequalities show the implemented A0 is the floor of Q*theta-(R-1)/2 on the accepted range. Every index outside [A0,A0+R) has distance at least R/4 from Q*theta. Thus

`tail <= 2*exp(-R^2/(32Q))`.

This intentionally weaker constant is sufficient; it is not an accidental reuse of a different schedule.

## Actual schedule budget, without a limiting-probability premise

The actual formulas give R^2>=16*lambda and 128*nu*Q<=lambda. Therefore R^2/(32Q)>=64*nu. Also r^2<=lambda<=2^nu. An elementary finite estimate

`4*4^nu <= exp(64*nu)` for nu>=1

follows from 4<=exp(4), the natural-power exponential identity, and an exponent comparison. It implies

`2*exp(-64*nu) <= 1/(2*r^2*lambda)`.

Combining these proves `scheduled_centered_tail_le_budget` whenever nu=clog_2(lambda)>=64; the existing exact range theorem supplies r>=2,R>=32,6R<=Q.

## Literal integer loop target

`tailNumerator r Q A0 R` is the sum of choose(Q,k)*(r-1)^k*(r+1)^(Q-k) over precisely the outside indices k=0,...,Q. `tailNumerator_normalized` proves its exact equality after division by (2r)^Q to the finite real probability above. This is the closed form of the streamed integer recurrence already independently reviewed in `shared_parameters.binomial_tail`.

Positive denominator clearing yields

`tailNumerator * (2*r^2*lambda) <= (2*r)^Q`.

This is the implemented comparison `tail * tau_denominator * r * occurrence <= denominator`, since tau_denominator=r*lambda and occurrence=2. Differences in multiplication order are only commutative integer arithmetic. No rounded probability or float comparison is involved.

`tailGuard lambda` records exactly that inequality. `scheduled_tail_guard` proves it under nu>=64. Since the double integer ceiling logarithm tends to infinity, `eventually_scheduled_tail_guard` has no supplied numerical assumption.

Finally, `exactScheduleGuard n w` packages positivity, r>=2, 1<=R<Q, tau denominator>=2, centered interval containment, the incidence and group balance inequalities, this exact integer tail guard, R>=32, and 6R<=Q. Its eventual theorem composes the tail result with the already proved non-tail schedule theorem. Mathematical ceiling logs/square roots/divisions match the frozen code's formulas; operational identification of those Python helpers is not presented as a Lean execution theorem.

## What remains

The **previous numerical-tail acceptance gap is now closed** for this schedule and growing-arity regime. The following do not follow merely from that result: constructed-layout realization, actual streamed counter-loop refinement, primitive operation costs and all-prefix space, the macro-FFT compiler and unique extensions, composition with factor-prefix recovery, and a full all-input factoring runtime theorem. Those remain the project's stated goals, not assumptions hidden in this guard result.

## Verification

Strict compile used `lake env lean -DwarningAsError=true -o .../SemiprimeCounterTail.olean .../SemiprimeCounterTail.lean`; log `tail-build.log`. Ordinary-root import and `#lint+` namespace audit passed all **15 linters** on 26 user declarations plus 32 automatically generated declarations. The all-declaration audit inspected **58 declarations / 53 theorem constants**, including generated and private proof dependencies, and allowed only propext, Classical.choice, Quot.sound. These are not counts of public named theorems. Main key theorem axiom reports are also retained.

Audit file/log: `tail-root-audit.lean`, `tail-root-audit.log`. `tail-verification.json` records source/object/audit hashes. No finite successful factor examples or numerical probability campaign was run; this is a compiled exact proof.

## Exact adapted-source and license pin

The pinned `SpectralBinomial.lean` git blob is `4a5fbb95d38a8d525c442adc5ef2d2cd8fe78cd3`, SHA-256 `59aba107edac67258f442374d612c63d5686560503006ba5c88f80ef26952c8f` (7641 bytes). The working sparse-checkout file was compared byte-for-byte against `git show 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a:lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SpectralBinomial.lean`. The Apache-2.0 license blob `261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64` has SHA-256 `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`; its bytes are retained as `LICENSE.OpenAI-Math.Apache-2.0.txt`. Full source URL, attribution, prior provenance link and matching metadata are in `tail-external-source-provenance.json` and embedded in `tail-verification.json`. No frozen baseline was modified.
