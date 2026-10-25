# Translated cyclotomic rows: initialized projected acquisition

2026-10-24. Scratch only; no repository edits or examples. A genuine rank-one projection of ALL native translated rows is acquired in soft m. Generic selected coefficients and the unweighted regular trace are initialized at soft m^2 by the streaming algorithm below; no soft-m algorithm for those outputs is obtained. The cheap rank-one projection is exactly a scalar native target list with a changed base. No observable is declared covered here; that is a separate requirement.

Source read: `/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-cyclotomic-row-cancellation-20261016/README.md`. Exact SHA256: 992e31ea5ece408e448dba91771a1616228b4629668552960c15311c9aafad6e. Native row acquisition, own-tag arithmetic and its index horizon are inherited. The translated choice u=beta+zeta is expressly outside that README's self-reciprocal cancellation theorem.

## Actual input and unit acquisition

Work in A=(Z/N)[zeta]/(zeta^m-1), m odd prime, m coprime to N. beta is a prepared scalar unit with odd local orders. Let u=beta+zeta and f=u^N. Then

    u * sum_(r=0)^(m-1) (-zeta)^r beta^(m-1-r)=beta^m+1.

The scalar beta^m+1 is a certified unit: beta^m has odd order in each hidden field, hence cannot equal -1. Compute the scalar inverse and the displayed length-m coefficient vector to acquire u^-1 in soft m. Cyclic polynomial multiplication and binary signed powering then acquire f, u^(m^2), and any ONE specified u^ell in soft m, including coefficient bit costs. No root of unity in R or hidden-field factorization is supplied.

For row j put k=j^-1 modulo m and

    a_j=[N j^-2]_m, ell_j=m b_j-2a_j j,
    L_j=u^ell_j (beta+zeta^j)^a_j,
    T_j=L_j sigma_k(f).

All row exponents have O(log N) bits. The list T_j is not supplied as input.

## Positive soft-m acquisition: augmentation projection and weighted trace

The augmentation epsilon:A->R sends zeta to 1. Put gamma=beta+1, a certified unit by the same odd-order argument. Since sigma_k fixes augmentation,

    epsilon(T_j)=gamma^(N+ell_j+a_j)=gamma^(N+delta_j).

Acquire gamma^N once and all signed powers gamma^delta_j by binary powering. This costs soft m scalar-bit operations in total; the row metadata were already acquired. Thus ALL augmentation values are actually computed, including initialization, with no degree-m row powers.

Equivalently let e0=(1/m)sum_(r=0)^(m-1) zeta^r. It is an acquired idempotent, sigma_j(e0)=e0 and

    e0 T_j=e0 epsilon(T_j).

The compact output consists of the ONE vector e0 and m-1 acquired scalars. Each coefficient of the projected e0 T_j equals epsilon(T_j)/m and is available on demand. Explicitly writing all m^2 projected coefficients would of course cost m^2; no such output is requested or charged as free.

This also acquires a legitimate weighted regular trace: on the free R-module A, multiplication by e0 T_j is rank one with trace epsilon(T_j). It is NOT the unweighted regular trace Tr(M_(T_j))=m*[zeta^0]T_j. Those two traces must not be conflated.

The projected matrix actions are initialized too: for any supplied vector v in A,

    e0 T_j v=e0 epsilon(T_j) epsilon(v).

Given v, its augmentation costs O(m) once; all j scalar actions then cost soft m. This is useful only for this one-dimensional summand.

This projection returns the old literal target list under scalar base gamma. It does not evaluate its geometric-horizon collision query, certify a new scalar base order, or prove a selector. Its own-tag equality is inherited after applying the ring homomorphism, but membership in the long power interval still needs acquisition. No factor-rate gain is claimed.

In the cyclotomic quotient R[zeta]/Phi_m(zeta), the augmentation summand is absent: e0=0. The above positive projection belongs to the full cyclic algebra and must not be transferred to the cyclotomic quotient as a nonzero observable.

## Exact selected-coefficient kernel

Write f=sum_t f_t zeta^t. For a fixed requested coordinate r,

    y_j=[zeta^r]T_j
       =sum_(t mod m) f_t [zeta^(r-k t)]L_j.

This is a precise transposed formulation, not an acquired matrix. If every L_j were one common acquired L, define h_s=[zeta^(r-s)]L. The nonzero-index contribution would be sum_(t!=0) f_t h_(k t), a multiplicative cyclic convolution on F_m^*. Together with f_0 L_r, all outputs would cost soft m after acquiring h. The nonzero residue group can be indexed using a primitive root of the small public prime m; factorization/search for m-1 fits soft m. No Fourier roots over R are assumed.

For the native row multipliers, L_j depends on both varying ell_j and a_j and on sigma_j(u). Thus the common-kernel hypothesis is false. A scalar formula for its entries or the list of O(m) row parameters does not itself acquire the m-by-m kernel action. Merely applying a multiplicative convolution to the f coefficient permutations omits these multipliers.

Applying sigma_j before constant-term extraction gives another exact form:

    y_j (r=0)=[zeta^0] f (beta+zeta^j)^ell_j
                              (beta+zeta^(j^2))^a_j.

The native congruence makes the extracted monomial phase constant:

    (beta+zeta^j)^ell_j(beta+zeta^(j^2))^a_j
      =zeta^(-N)(1+beta zeta^(-j))^ell_j
                  (1+beta zeta^(-j^2))^a_j.

This identity is exact for signed powers because the factors are units. It removes one known phase, but the two translated factors remain row-dependent. No fast action follows merely from this phase cancellation. Expanding them in a short formal beta-prefix would require a separate tail-evaluation theorem at the actual unit beta; no such theorem is used.

## Fully initialized streaming baseline for actual original coefficients

For each j:

1. Acquire u^ell_j by signed binary powering using the already acquired u,u^-1. This costs soft m.
2. Acquire (beta+zeta^j)^a_j. Since a_j<m, its a_j+1 binomial coefficients can be generated from factorials through m (all those small integers are certified units), powers of beta, and the actual coefficient positions j t modulo m. These are distinct for 0<=t<=a_j. This costs O(a_j+1) scalar operations. Alternatively use cyclic binary powering at soft m.
3. Multiply these two acquired vectors cyclically to get L_j, then compute the displayed dot product against f to obtain y_j. This costs soft m for any fixed number of requested coordinates. Discard L_j and proceed to the next row.

All outputs y_j are therefore acquired in soft m^2 with soft m active coefficient storage, without storing all T_j. The unweighted regular trace follows by multiplying the constant coordinate by m. The output vector itself has only O(m) entries; the larger bound is the actual work of this implementation, not an output-size lower bound.

Even the explicit binomial factor supports sum_j(a_j+1)=Theta(m^2): every a-value has at most two native preimages, so a constant fraction of a_j are at least m/4. This explains the quadratic emitted coefficient count of that literal route. It does not preclude another implicit aggregate or selected-output method.

## Stopping point

Acquired in soft m: f; u^-1; q_cyc; ALL augmentation/idempotent-projected rows and their rank-one matrix actions. Acquired in soft m^2: ALL requested original selected coefficients or regular traces via the explicit streaming kernel algorithm, with soft m storage.

Still missing: a fused algorithm for the genuinely row-varying coefficient kernel below that clock, together with a separately proved covered observable. The scalar rank-one projection is a real computation but returns the old scalar-list/query problem. The phase congruence, multiplicative-index permutation and diagonalization language alone do not initialize the remaining action. No generic lower bound or new sixth-rate factoring claim is made.
