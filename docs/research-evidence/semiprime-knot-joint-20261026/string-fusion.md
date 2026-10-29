# Exact geometric strings: retained fusion normalization

Status: a concrete generic-parameter fusion calculation identifies the collision-bearing scalar discarded by an endpoint-only fused boundary value. It does **not** improve the whole-query bound. No experiments or repository changes.

## Primary finite fusion formula

Caradoc–Foda–Kitanine, *Higher spin vertex models with domain wall boundary conditions*, [math-ph/0601061v2](https://arxiv.org/pdf/math-ph/0601061), printed pp. 2–6, Eq. (3), footnote 3, and Eq. (4), use `[u]=sinh(lambda*u)`, `[u]_r=prod_{h=0}^{r-1}[u-h]`, and fundamental weights `a=[u+1], b=[u], c=[1]`. Two d-stacks with additive step one fuse to a spin-d/2 vertex, dividing by

$$N_d(u)=\prod_{p=0}^{d-1}\prod_{r=0}^{d-2}[u+p-r].$$

A fully domain-wall stacked square has the unique fused c+ boundary state. Hence their convention gives the cleared scalar identity

$$Z_{\mathrm{stack},d}(u)=N_d(u)[d]_d.\tag{1}$$

Their normalized c+ value is `[d]_d`, independent of the stack separation; the DJMO convention cited in footnote 3 instead makes it one. Neither convention licenses discarding this multiplier for a zero query on the unfused scalar.

## Explicit native test and general strips

For d=2 the exact identity is

$$Z_{\mathrm{stack},2}(u)=[u][u+1][2][1].\tag{2}$$

Put `q=exp(2 lambda)` and `x=exp(2 lambda u)`. The removed scalar `[u][u+1]` is a unit monomial times `(1-x)(1-q*x)`. These are exactly two adjacent comparison factors. The normalized fused readout `[2][1]` stays a unit under the native short-order guard when either comparison vanishes. This is a scalar-amplitude calculation, not an inference from rank deficiency.

Square roots of row values are unnecessary: use the polynomial-gauged normalizer

$$\mathcal N_d(X)=\prod_{p=0}^{d-1}\prod_{r=0}^{d-2}(1-Xq^{p-r}),\qquad \mathcal N_1=1.$$

It differs from the bracket normalizer only by invertible monomials and powers of two in a Laurent square-root extension, and its own definition lies in R[X]. Thus its collision assertions specialize directly over R=Z/NZ; 2 and all native clock/root monomials are units. Adding the two boundary strips proves the division-free identities

$$\mathcal N_{d+1}(X)=\mathcal N_d(X)\prod_{h=1-d}^{d}(1-Xq^h),\tag{3}$$

$$\mathcal N_{d+2}(X)\mathcal N_d(X)
=(1-Xq^{-d})(1-Xq^{d+1})\mathcal N_{d+1}(X)^2.\tag{4}$$

Equation (3) exposes a paired geometric prefix. Equation (4) looks endpoint-only, but advancing by division requires a unit pivot `mathcal N_d(X)`, which need not be a unit at a retained collision. The cleared identity remains true there but does not uniquely determine the next number. Prior symbolic cancellation yields the complete strip product (3), rather than a known-unit correction.

Taking X=t0/v_j maps (2) to two genuine adjacent native clock comparisons. This does not claim arbitrary selected comparisons are actual catalogue witnesses: it identifies the native factors the fused readout would erase whenever such a collision occurs. Across all roots of K, retaining the strips restores the original orbit product, including its reciprocal factors.

The quantum factorial only involves short clock differences. For d within the queried string length they are units under the local-order bound. A zero-only query need not acquire their numerical product. If requested, its scalar q-Pochhammer value has the existing square-root algorithm; this says nothing about the comparison-bearing normalizer being a unit.

The partially fused determinant of the source's Eq. (4) still has dimension d times the number of fused lines, and the fused spin module has dimension d+1. Neither a binary spin label nor the determinant descriptor pays the readout. There is no improved initialized cost here.

## Singular exact strings: source scope

Nepomechie–Wang, *Twisting singular solutions of Bethe's equations*, [1409.7382v3](https://arxiv.org/pdf/1409.7382), §3 Eqs. (26)–(33), treats generic XXZ anisotropy, not a root-of-unity string. Its length-2s+1 singular string is `s gamma,(s-1)gamma,...,-s gamma`; its multiplicative ratio is exp(2 gamma). The source's q=exp(gamma) is therefore the square root of our geometric clock when identifying these conventions.

Its necessary physicality constraints and modified remaining-root equations concern its homogeneous periodic chain, not every engineered native A,D system. Section 2 around Eq. (16) describes eigenvector construction as requiring higher-order twist corrections, through chain length in that XXX discussion. It supplies no cheap finite-ring regularized Gaudin/Slavnov readout for our family. Its chain length symbol N is not the semiprime modulus. Nor does its field statement permit dividing by native comparison values at collisions.

## Remaining constructive interface

The parent/q-holonomic geometric-string Bethe-Jacobian calculation is separate prior work. A new algorithm still needs an explicit regularized scalar/boundary identity evaluable in soft O(L+sqrt(m)), including seeds, whose comparison with the target cancels only certified units. It may exploit additional native collective structure. The fully fused DW boundary tested here does not provide that identity: its endpoint scalar cancels precisely the collision-bearing normalizer. Equations (1)–(4) locate this correction and its finite endpoint strips without any unknown period or root-of-unity limit. The old soft O(L+sqrt(Lm)) whole-query bound is unchanged.
