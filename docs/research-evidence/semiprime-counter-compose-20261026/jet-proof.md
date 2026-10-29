# Finite jet recurrence algebra and Hermite inverse handoff

Sole new source `RiemannGaussian/SemiprimeJetRecurrence.lean`; all previous source files and frozen evidence preserved.

## Actual inverse recurrence

`inverseCoeff a 0 = (a 0)^(-1)` and

`inverseCoeff a (n+1) = -(a 0)^(-1) * sum_(i=0..n) a(i+1)*inverseCoeff a(n-i)`.

This is the literal coefficient recurrence in frozen `shared_counter.py`'s `Jets.inverse`, with the summation reindexed from i=1..k. It is an executable well-founded natural-number recursion, with all recursive arguments strictly smaller. `inverseCoeff_convolution` proves the finite convolution is one at index zero and zero thereafter when the actual rational constant a0 is nonzero. No inverse-equation hypothesis is used.

`jetPolynomial a J` is the ordinary polynomial of the retained J entries. `jetPolynomial_coeff` and `coeff_mod_X_pow` establish exact coefficient and monic-remainder semantics. `jet_add` proves componentwise addition equals polynomial addition modulo X^J. `jet_mul` proves the truncated convolution equals polynomial multiplication modulo X^J. This includes J=0; code inverse use is separately guarded by positive width where indexing entry zero is meaningful.

`inversePolynomial_congruence` specializes the EXECUTED recurrence to a polynomial's coefficients and proves `X^J | p*jetPolynomial(inverseCoeff p.coeff,J)-1`, from the nonzero actual constant. It is derived by coefficient convolution, not supplied as a promise.

## Existing Hermite formula handoff

`recurrence_localQuotient` proves that multiplying H by the recurrence inverse and reducing modulo X^J gives exactly `SemiprimeHermiteRecovery.localQuotient H L J` for the normalized Hermite denominator L with constant one.

`packet_recurrence_localQuotient` proves the stronger code-facing statement: first truncate the denominator L to its actual packet `L mod X^J`, compute the recurrence from that packet, multiply H and truncate. The result is STILL exactly the existing localQuotient. Assumptions are J>0 and actual L.coeff(0)=1. The proof derives the packet's constant, transfers the recurrence congruence back to L, and compares it to the constructed finite-geometric inverse by polynomial divisibility. The original Hermite theorem's `localQuotient_truncate` handles truncating the numerator packet too.

Thus no inverse-congruence hypothesis or desired reconstructed-packet equality remains at this algebraic handoff.

## Gates and scope

Strict absolute-lake module compilation PASS with `autoImplicit=false` and `warningAsError=true`. Outputs: repository `.olean` and identical scratch `.olean`. Six explicit theorem axiom reports contain only standard axioms. Log `jet-build.log`.

This formalizes arithmetic results of the componentwise/convolution/recurrence operations. It does not yet prove the imperative tuple/list loop refinement, caching strategy, arithmetic bit cost, or full primitive-machine execution. The well-founded function may recompute earlier values if evaluated naively; the Python forward loop stores them. No O(J^2) time claim is inferred solely from this recursive definition. The next executable refinement can prove that the stored forward array realizes this uniquely specified recurrence, reusing the algebra proved here.

Final root-import audit PASS: `CheckJet.lean` imports existing root plus new leaf, all 15 namespace linters pass, and every emitted declaration is checked for project axioms and unexpected transitive axioms. It checked 30 declarations, including 25 theorem declarations. Log `jet-audit.log`. No broad build or external closure work was launched.
