# Positive character contraction: projective reduction and exact spectral charge

22 October 2026. New symbolic contraction attempt. No repository edits, backend or examples. The positive kernel and its decision gap are retained as representations, not counted as a near-linear query. This pass reduces it to a one-variable multiplicative convolution, proves its exact Fourier coefficients, and tracks the remaining startup.

## Homogeneity removes one leaf variable exactly

All scalar targets a and seeds b are units modulo N=P Q. Multiplication by b^-1 preserves which hidden primes divide a-b. Therefore

    c_N(a-b)=c_N(a/b-1),
    k(z)=c_N(z-1)^2-1,
    E(Y,S_L)=sum_(y in Y) F_L(y),
    F_L(z)=sum_(0<=i<L) k(z q^-i).

This is exact positive multiplicative convolution on the PUBLICLY DEFINED group G=(Z/N)^*. It includes local-only and global hits, with no sign or component ambiguity. All native integer exponents and q carries remain in z; no root-of-unity specialization is made.

Its exact one-variable boundary equation is

    F_L(qz)-F_L(z)=k(qz)-k(q^(1-L)z).           (1)

The earlier two-parameter Jacobi feature equation is a public entrywise realization of this identity before the complete correlation is contracted. Given one F_L startup, (1) acquires all values on a supplied q-orbit segment with constant-cost endpoint gcd/Jacobi arithmetic per step. But the original native values occur at distinct carried origins; (1) does not itself supply one startup per needed orbit.

## Multiplicative Fourier is explicit proof-side, not an acquired oracle

Let p=P,q0=Q denote hidden primes here (q0 is NOT the scalar step). Put A=p(p-2), B=q0(q0-2). The kernel is exactly

    k(z)=A*1_(z_P=1)+B*1_(z_Q=1)+A B*1_(z=1).

For any multiplicative character psi=psi_P*psi_Q of G, its unnormalized Fourier coefficient is

    k_hat(psi)=A*(q0-1)*1_(psi_Q trivial)
              +B*(p-1)*1_(psi_P trivial)+A B.   (2)

Proof: sum over the subgroup {z_P=1}, respectively {z_Q=1}, and use finite-group character orthogonality; the identity element contributes1. All coefficients are positive real integers. This proves PSD directly and gives the precise homogeneous spectrum without materializing the N-by-N matrix.

With these modes supplied, F_L's Fourier coefficients multiply by the explicit geometric sums sum_(i<L)psi(q)^(-i), with the orientation depending on the chosen transform convention. The desired scalar aggregate would then contract those with the target mode sums. However the group decomposition, character evaluation and coefficients in (2) are not acquired inputs. Replacing them by hidden local character data would assume factoring/order information. The public Jacobi character is trivial on every prepared odd-order scalar target and seed, so it cannot resolve the native indices through distinct phase samples. More generally every public 2-power-order Dirichlet character is trivial on that subgroup.

There is a sharp check against pretending even one relevant spectral constant is free. For the PUBLIC Jacobi character, both local components are nontrivial, so

    k_hat(Jacobi)=A B=N*(N-2(P+Q)+4).

Acquiring this complete coefficient exactly therefore gives

    P+Q=(N+4-k_hat(Jacobi)/N)/2,

and factors N by the quadratic discriminant. Thus a fast computation of that scalar would be a legitimate alternate solution, but not cheap metadata furnished by homogeneous Fourier analysis. This is an exact reduction, not a lower bound or a claim that such a computation is impossible. It also explains why the diagonal/mean constants of the positive kernel must not be treated as publicly known merely because individual Jacobi entries are cheap.

## Projective complete-sum route and its retained cost

For the public features chi(t+a)chi(u+a), scaling t,u simultaneously moves the long seed sum by only two endpoints. On the unit-u stratum one may set t=u v and write chi(t+a)chi(u+a)=chi(v+a/u)chi(1+a/u); the multiplier chi(u)^2 is1. This is an exact projective coordinate change, but it varies the targets/seeds by a/u and requires all u values or a paid contraction over them. Nonunit-u strata cannot simply be dropped: their CRT components contribute to the exact complete kernel, and separating them by hidden prime is not public preprocessing. An individual tested nonunit u would already factor, but no small public list is proved to replace those strata in the complete identity.

The geometric boundary equation can be integrated around a complete q-orbit only if its mean/startup is supplied. Summing the boundary around an orbit gives0=0 and does not determine the additive constant. Those orbit constants are actual sums of hidden local equality counts. Specifying a compact orbit descriptor or a public upper bound on the period does not acquire them. A supplied nonzero global annihilator bounding the actual period is already consumable by the existing decoder, so it cannot be assumed merely to initialize this representation.

## Positive partial outcome and remaining algorithm

The two-parameter positive representation has been reduced to a homogeneous one-variable group convolution, with an exact spectrum and an explicit scalar Fourier-coefficient factoring target. Neither requires changing the original scalar source or recovery. The additive boundary transport is genuinely cheap AFTER initialization. No deterministic initialization/elimination identity computing the native weighted complete trace in softm was established.

A completion could (a) acquire k_hat(Jacobi) by a new complete-character contraction in softm, which factors directly; (b) acquire the weighted geometric convolution at the native origins without all spectrum/startups; or (c) prove a source-preserving set of orbit boundary conditions whose total construction is softm. Any route must retain the original same-leaf support and count all complete sums, modes, and nonunit strata. The public amplified decision gap can reduce required approximation accuracy for an eventual certified algorithm, but does not pay these operations by itself. No near-linear collision query or rate gain is claimed by this pass.
