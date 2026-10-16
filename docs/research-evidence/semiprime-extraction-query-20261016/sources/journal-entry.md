## 2026-10-16 — Paid coefficient-block inverses; actual q-shift and mask ranks limit extraction shortcuts

The [extraction packet](research-evidence/semiprime-extraction-query-20261016/README.md)
adds constructive structured operators and rigorous limits on two proposed
cancellations. It does not acquire the whole-family soft O(m) long query.
Three user-authorized Sol 6.1 agents investigated the channel gcd, compatible
q-displacement, and mixed diagonal in parallel. The main proofs have
independent reviews of their final bytes. These are classical results;
the guaranteed sixth-rate theorem and its Lean implementation remain open.

**The block q-pencil now has paid operators and generators.** For width J,
M=CW is the matrix of degree<J block-polynomial values at the public nodes.
Interpolation gives the genuine finite-dimensional q-shift
Q_row=W^(-1)diag(q^s)W. The finite coefficient recurrence proves

    M(I-q^L Z)-diag(q^(Jn)) M Q_row(I-Z)
      = u 1^T-v (z_j^J)_j^T.

Shared selected coefficients pay both endpoint generators, and all the
operators have soft O(m) actions including setup. The pencil does not
invert potentially nonunit factors 1-z_j or 1-q^L z_j. Thus finite BLOCK
polynomials do close under interpolation; full degree-L closure or a
powered-node Trummer generator does not follow from that fact.

**Square coefficient blocks also have paid inverse actions on the retained
actual family.** Clearing a shared rational-Newton denominator produces a
polynomial basis with a triangular evaluation matrix at q^(L-k). Its
diagonal factors, coefficient seeds and evaluation differences are units.
Recursive basis inversion uses monic evaluation/interpolation and unit
batch inversion, giving soft O(J+sqrt L) setup/actions, with the usual
soft log N bit factor. The proof uses local order beyond L+J-1, supplied
by the retained prime-order family; it is not an all-native-input or
all-restriction claim. The determinant has a paid product formula as well.
Cheap inversion does not itself recover diag S from S=V_y C V_z^T.

**The natural rank-one q-boundary conversion fails arithmetically.** Let Q
act on column values of degree<J polynomials at distinct z_j. An explicit
Lagrange/Vandermonde factorization proves, for 1<=B<=J,

    rank(Q Z^B-q^B Z^B Q)=min(B, #{j:H(qz_j)!=0}),
    H(t)=prod_j(t-z_j).

For the literal quadratic source, the offset span and local order make
qz_i=z_j equivalent to delta_i-delta_j=m^2 as an INTEGER. The low-digit
quadratic fibers contain at most two tags, so these directed adjacencies
are disjoint pairs. At least ceil(J/2) rows remain nonzero in both fields.
A balanced dyadic B<=J makes the powered-node defect rank Omega(m).
Hence this correction cannot have polylog-rank generators. This proves
neither high rank for YS-SY nor a general diagonal/query lower bound;
other cancellations after composing the operators remain possible.

**Canonical mask weights also have actual linear separation rank.** For
the zero channel, w_0=e_0 and w_s=Y e_(B-s) for s>0, where e_s are the
mask polyphases. The carry Y gives

    w_s(z_j^B)=E_B(z_j) z_j^s/B.

The resulting unit Vandermonde minors force Omega(m) separable terms for
these coefficientwise weights. Any canonical channel combination that
preserves the many unit rows has the same obstruction. The channel
polynomials themselves have Omega(m) constant-linear span, despite their
small common collision factor. These are exact actual-family rank
statements. They do NOT exclude alternative weights related by the fixed
F_s q-recurrence syzygies, shared nonseparable algorithms, or direct gcd
acquisition; they are not operation lower bounds.

The local-channel audit also shows that safe-center jets generate the
whole truncated ring at every precision: the global locator is locally
a unit. At a target, fieldwise common valuation is exactly zero or one according
to collision. Thus local content alone cannot replace global content.
Blind polylog-many uniform target gcd probes miss the sparse informative
rows with probability 1-o(1) on the retained family; adaptive/global
algorithms and individual nonunit pivots remain outside this statement.

Fresh primary-source checks on structured determinants and recurrence
width did not supply the missing generator conversion or determinant
deformation. All eight predecessor packets and exact journal entries
remain byte-unchanged. The general query bound is still soft O(m^(3/2)).
The next required theorem remains a soft O(m), restriction-stable channel
remainder, collision locator, mixed diagonal, or sufficient factor query;
the full bit-complexity and Lean composition would still follow that.


