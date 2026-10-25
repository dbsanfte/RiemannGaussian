# Thin fixed-Q joint inner masks by rebalancing

24 October 2026. Scratch only. This is an input-acquisition improvement, not a completed native query.

Let L be the q-Pochhammer degree, D=4^m its actual inner digit dimension, and fix ONE active Q and ONE factorized outer ternary digit mask. The coefficient positions in this Q block are n=n0+D*r+d, 0<=r<N0, 0<=d<D, with n0 divisible by B0=D*N0. Positions outside [0,L] are zero. All 6^m active inner left masks are requested at this fixed outer mask.

Use the initialized coefficient-matrix action and mixed-radix alignment of /tmp/semiprime-implicit-thin-encoding-20261024/all-mask-sharing.md Sections 1 and 4. Assume D<sqrt(L+1); the thin application satisfies this. If B0>=sqrt(L+1), choose the first mixed-radix digit cut D0>=sqrt(L+1). Then D divides D0, D0 divides B0 and n0, and sqrt(L+1)<=D0<3sqrt(L+1), because this cut lies in the ternary outer digits. Write r=t+(D0/D)*s. The actual outer weight factors u_low(t)*u_high(s), since the cut is a digit boundary.

On the global coefficient reshape C0[R,e]=c_(D0*R+e), acquire a0=C0^t*u_high, placing u_high at its actual shifted global row interval n0/D0 and zero elsewhere. Both its explicit row vector and all a0 entries cost soft sqrt(L), including the padded final row. Then acquire every

    a[d]=sum_(0<=t<D0/D) u_low(t)*a0[D*t+d], 0<=d<D.

This folding is literal O(D0) arithmetic. It yields exactly sum_r u(r)c_(n0+D*r+d), with every boundary already clipped by coefficient padding. Apply the six-by-four digit transform K at each of the m radix-four digits to a. This returns ALL 6^m inner masks in O(6^m) operations.

If B0<sqrt(L+1), acquire the fewer-than-sqrt(L+1) coefficients in the entire shifted block by the selected-prefix primitive, fold all outer weights directly, then apply the same joint K transform. If n0>L the entire block is zero and may be represented/skipped according to the caller's output contract; requested zero outputs still cost 6^m writes.

## Native weights at ONE supplied parameter

For ONE supplied native x, the same algorithm handles coefficients c_n*x^n. Indeed n=n0+D0*s+D*t+d, so x^n=x^n0*(x^D0)^s*(x^D)^t*x^d. Incorporate these factors into u_high(s), u_low(t), and the final D-entry inner diagonal, retaining the actual x^n0 factor. Generate their power walks in soft sqrt(L); x may be zero or nonunit, and no x value is inverted. The transposed coefficient action still has exactly the same licensed preprocessing, with all moving weights supplied explicitly. This extension acquires all inner masks for this ONE x and ONE coefficient-index outer-digit mask.

## Scope of the actual folded thin left input

The outer mask in the proof acts on the COEFFICIENT row index r and factors over its ternary digits. It does not acquire a whole outer mask for the diagonal-folded thin left matrix

    X[i,d]=sum_r c_(D*r+d)*y_i^(D*r).

An outer mask on the TARGET index i gives coefficient-row weights

    mu_r=sum_i weights_i*(y_i^D)^r.

These mu_r are generally not digit-factorized in r. After rebalancing, the required mu_(t+(D0/D)*s) form a Hankel-type matrix of rank up to the number of participating targets, rather than the single product u_low(t)*u_high(s). The proof supplies neither that matrix nor its contraction at the stated cost. Applying the single-x extension separately to a mixture must charge every participating x, unless an additional sharing algorithm is proved. No whole folded-target outer mask or complete diagonal query is acquired by this lemma.

Thus a fixed Q and factorized coefficient-index outer mask admit the fully acquired joint bound

    soft(sqrt(L)+6^m),

at the actual thin dimension D, instead of the general arbitrary-outer-vector bound soft(L/D+D+6^m). No input/output weights are inverted. All preprocessing inverses are the licensed q-prefix denominators, within degree L. Both the low and high digit vectors are explicitly generated in soft sqrt(L).

For J=L^(2/3), the primary thin condition D<=J^(1/18)=L^(1/27) gives 6^m=D^(log_4 6)<=L^0.04789. The fixed-Q joint acquisition therefore costs soft L^(1/2). A literal p-description continuation costs soft(p*(sqrt(L)+6^m)); up to L^(1/6) actual descriptions fit the L^(2/3) budget. The actual wanted-leaf union can contain more descriptions and Q-dependent block assignments; this note does not bound it or replace it by one fixed-Q object.

Primary paper verified online: https://arxiv.org/abs/2610.06783v1 and https://arxiv.org/html/2610.06783v1 . Its theorem still charges the full encoding/wanted-leaf work. No full tensor input or diagonal terminal contraction is acquired free here. No shared/frozen file was edited.
