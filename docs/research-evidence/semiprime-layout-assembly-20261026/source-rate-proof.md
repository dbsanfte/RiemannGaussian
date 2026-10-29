# Stronger published-constructor guards at the unchanged schedule

New source: `RiemannGaussian/SemiprimeSourceLayoutRate.lean`. All proofs use local audited rate/tail modules and Mathlib; no external proof path is imported. The module enables `autoImplicit=false` and has been compiled with both that option and warnings-as-errors. Existing source modules and frozen packets were preserved.

## Actual stronger guards

`eventually_source_layout_guard` proves, for fixed C>=0 and every positive w<=C*n^(3/4), eventual satisfaction of:

- actual r>=2, Q>=2, R>=4, 4R<=Q;
- epsilon=1/(r*lambda)>0 and epsilon<=1/2;
- **4*(2+w)*D^2*(r*lambda)^2<=2n**;
- **16*Q*r^2<=n**;
- **32*(Q-1)*log(2/epsilon)<=R^2**.

Here lambda=clog_2(n), nu=clog_2(lambda), r=floor(sqrt(lambda)/nu^2), Q=floor(lambda/(128nu)), R=4ceil(sqrt(lambda)), and D=r^(2Q) are exactly the already defined integer schedule. No premise asserts old-guard acceptance, stronger-guard acceptance, packing success or a desired spectral bound.

The actual ceiling-log bound `clog_2(n)<=log(n)/log(2)+1` is proved from integer dyadic inequalities. Every fixed power of that integer ceil is then eventually below every positive real power of n. In particular the added (r*lambda)^2 factor is bounded by lambda^4<=n^(1/64). Combining it with the proved actual D^2<=2*n^(1/64) gives a normalized packing load tending to zero, even for w=O(n^(3/4)).

The stronger factor16 group bound is proved independently by integer polynomial-versus-exponential induction, not inferred from the old factor2 test.

For the source spectral guard, r<=lambda<=2^nu gives log(2*r*lambda)<=64nu. The exact floor budget128nu*Q<=lambda and R^2>=16lambda then imply the displayed width condition, including its **Q-1** index. The module does not equate the source's Q-1 centered interval with the Python/current Q-trial interval.

## Literal height and enumeration budgets

Define the source's explicit post-pullback height budget W=4*(8Q)^(2R). The actual range6R<=Q and128nu*Q<=lambda imply 2R(nu+3)<=lambda. Hence, once the proved large-log range holds:

- W<=2^(lambda+2);
- the common integer signature-box base 2nW+1<=2^(6lambda);
- log(2nW+1)<=6lambda*log(2).

These are exact integer/logarithmic inequalities for the literal W, not a rank bound substituted for coefficient height or an exp(D) upper envelope.

If the constructor's selected total rank c satisfies its stated exact bound c*(r*lambda)<=4n, the module proves

`c*log(2nW+1) <= (24n/r)*log(2)`.

This charges the explicit integer summary box. The rank hypothesis is deliberately visible: actual source rows, their rank bound and height/pullback instantiation belong to the constructor assembly, not to this numerical module.

A further exact floor argument gives1/r<=2nu^2/sqrt(lambda), without replacing r by its asymptotic real expression. Thus the binary-log envelope is explicitly at most48n*nu^2/sqrt(lambda)*log(2). The comparison of this binary-ceiling expression with the previously defined natural-log rho is not separately exported here; nor is an execution-cost theorem. The existing analytic rho limit remains available, and no exact base-change identity is silently assumed.

## Verification and scope

Strict compilation PASS. Ordinary-root import plus all15 namespace linters PASS. The all-declaration axiom audit inspected48 declarations/44 theorem constants (including generated/private proof constants), with only propext, Classical.choice and Quot.sound. Source/object/audit hashes are in `source-rate-verification.json`; logs and a source copy are retained in this scratch directory.

This closes the stronger numerical guards identified in `layout-bridge-map.md` for the published generic construction while preserving the same actual schedule. It does not yet instantiate source packing/row data, prove actual pulled-back row height, produce NodeCertificates, construct a graph, identify imperative loops, or prove primitive bit/time/space costs. No full factoring theorem or goal completion is claimed.
