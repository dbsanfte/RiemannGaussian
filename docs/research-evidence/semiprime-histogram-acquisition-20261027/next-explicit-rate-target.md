# Updated user goal: explicit paper-rate full bit complexity

The user replaced the earlier sixth-scaling goal after this histogram work was
completed. The ACTIVE objective is now a deterministic algorithm factoring every
semiprime N from its original binary input, with total bit complexity

    T(N) <= 2^(C*ell/sqrt(log(ell+2)))*(ell+1)^d,
    ell = ceil(log2(N+1)),

for constants C,d fixed before the entire family. A kernel-checked full runtime
and correctness theorem must include acquisition, preprocessing, coefficient
construction, memory/address operations and factor recovery. Subexponential
space remains allowed.

This supersedes the rate-completion criterion in next-whole-bit-join.md; the
physical pipeline and remaining machine joins listed there still apply. A full
runtime N^o(1) result is now a milestone, and N^(1/6) is a corollary. The already
proved retained-report subpower theorem is neither a full bit runtime theorem
nor by itself the explicit quantitative rate above.

Current MaterializedRate uses decay(lambda)=clog2(lambda)^2/sqrt(lambda) and a
coarse weighted-support envelope. The next investigation must trace the ACTUAL
public schedule and every original resource exponent, identify which logarithmic
losses are intrinsic to the current algorithm and which are loose estimates,
then refine the acquisition/counting or retune parameters while preserving all
source guards. Merely restating that decay tends to zero does not close this goal.

The completed histogram selector and its fixed seven-resource polynomial remain
reusable under any justified new schedule. Full original-input primitive costs
and the quantitative schedule bound must both be proved before completion.
Successor scratch: /tmp/semiprime-explicit-rate-20261027. Its investigations are
ongoing and are not counted among this checkpoint's 42 verified modules.
