# Paired Vandermonde--Cauchy contractions: exact theorem application and the diagonal state

24 October 2026. Scratch only. The actual Gaussian-binomial coefficient matrix admits an acquired Cauchy factorization with lawful inverses. This report executes the strongest relevant structured-multiplication guarantee on that factorization, then tests the additional compatible-generator hypothesis needed for fast DIAGONAL output. The checked primary results do not supply the missing paired endpoint algorithm. No new factoring exponent or generic impossibility claim is made.

## 1. Actual input, exact paired values, and paid Cauchy factors

The acquired action source is `/tmp/semiprime-implicit-thin-encoding-20261024/all-mask-sharing.md`, SHA256 `5f79d577ff7fddf72a6e3670d5bca3b7ff2ef72557f137553d388b9fea9c0f31`, independently reviewed at SHA256 `131aa98fb6f09ce933d20dddb35045ab5ac3b555e233fabcb15f43413d6eaa02`. All actual ring data are in the fixed-rank quadratic algebra A over R=Z/N. The supplied unit q has 1-q^s certified unit for every 1<=s<=C=16k^2. Its local component orders are odd.

Use the precise root derivation `kernel-cauchy.md` in this directory, frozen SHA256 `0153202f0e05e06437085ec6c8050725be1603993d83383a8949b8acaf209181`. Its formulas are independently checked in the accompanying review; this report cross-pins rather than repeating its full proof. Choose b<=L=2k^2+2 and balanced width d=Theta(sqrt(b+1)), using a power of two when the separation argument below requires it. Bounded b is direct; all needed q differences through b+d are within the ACTUAL native screen.

Write

    P_b(Y)=prod_(i<b)(1-q^i Y)=sum_(n=0)^b c_nY^n,
    Rb=floor(b/d), U_rho=q^(d*rho), lambda_s=q^(b-s).

Restrict C_reg[rho,s]=c_(d*rho+s) to 0<=rho<Rb, 0<=s<d. The remaining at most d coefficients form an acquired tail. With S the lower shift and V=diag(q^s), the actual pencil is C_reg A0-U C_reg B0=g e_last^t, where A0=S-q^b I, B0=(qS-I)V. The lower Toeplitz W has first column

    h_t=q^(-bt)*(q^(b+1);q)_t/(q;q)_t, h_0=1.

The generalized eigenbasis has order E=B0 W, not W. The checked identity A0 W=B0 W diag(lambda) gives

    C_reg=diag(g) K diag(eta) E^(-1),
    K_(rho,s)=1/(lambda_s-U_rho), eta_s=h_(d-1-s).       (1)

All cross differences are units because 1<=b-s-d*rho<=b. Toeplitz coefficients and inverse series, B0 inverse prefix sums, actual g coefficients and all tail coefficients cost soft(sqrt b+Rb+d). No Rb*d table of inverse differences is acquired. W numerator factors need the broader guard through b+d-1, which the native screen really supplies. Pure Cauchy actions use actual rational numerator trees and monic MPE over A, with only the pre-certified scalar/fixed-rank unit inverses.

For each ACTUAL target y, the requested value is

    P_b(y)=u(y)^t diag(g) K diag(eta) E^(-1)v(y)
                       +y^(Rb*d) T_tail(y),
    u(y)=(1,y^d,...,y^((Rb-1)d)),
    v(y)=(1,y,...,y^(d-1)).                          (2)

All K_targets tail evaluations and powers cost soft(d+K_targets). Equation (2) is the hard paired diagonal: both geometric vectors come from the SAME y. The native block convention is exact: prod_(r<b)(V_j-q^(ab+r))=V_j^b P_b(q^(ab)/V_j), with known unit factors, literal tails and original labels. There are K_targets=J floor(L/b) full-block arguments. Their required product is not determinant(C_reg) or the product of unrelated vector contractions.

## 2. Execute the 2017 structured-multiplication theorem with its real parameters

Primary: [Bostan--Jeannerod--Mouilleron--Schost, On Matrices with Displacement Structure: Generalized Operators and Faster Algorithms](https://cs.uwaterloo.ca/~eschost/publications/BoJeMoSc17.pdf), SIAM J. Matrix Anal. Appl. 38 (2017), Theorems 1.1--1.2. For an acquired length-alpha generator under an INVERTIBLE associated block-companion displacement and beta explicit right-hand sides, its bound is soft(alpha'^(omega-2)*beta'*p), p=max(m,n), alpha'=min(alpha,beta), beta'=max(alpha,beta). Multiplication is deterministic; inversion/solving uses randomized regularization. Geometric-node cases remove some logarithmic costs. The theorem does not state a product-only or paired-diagonal-only output algorithm.

The Cauchy K in (1) actually meets the node/cross-difference conditions; its displacement rank is one and both node families are geometric. Thus use alpha=1, beta=K_targets, p=Theta(sqrt b). The guaranteed multiplication bound specializes to

    soft(K_targets*sqrt b).                         (3)

Every right column diag(eta)E^(-1)v(y_j) is acquired in soft d, including all of its d coordinates. K times that column gives Rb actual output coordinates; its left weighted contraction then costs O(Rb). This is a COMPLETE application of the theorem and of (1), not a cost with unacquired input columns. All preprocessing is soft sqrt b. The actual composite-ring implementation of this bound is also valid: repeat the explicit Cauchy numerator/MPE operation for these columns, with the certified denominators, rather than treating A as a field. No randomized or hidden-field operation is needed for (3).

The resulting Pochhammer batching cost is soft(sqrt b+K_targets sqrt b). With K_targets of order JL/b and b<=L it gives no saving over the prior soft(J+sqrt(JL)) completion; at b=Theta(L), J=Theta(k), it is soft k^2. Expanding P_b and using ordinary monic MPE costs soft(b+K_targets), whose classical block balance returns the better existing 3/2 query exponent. The 2017 theorem genuinely improves dependence when BOTH displacement rank and number of right sides grow. At rank one, its displayed estimate retains the number of supplied columns; it does not collapse this diagonal problem.

A square Cauchy K can also be solved/inverted lawfully here using its standard explicit node formulas, since all its relevant Cauchy/Vandermonde minor factors are certified units. Thus composite-ring pivot difficulties are not an artificial reason to reject this acquired Cauchy factor. Its inverse still does not provide the moving paired products (2).

## 3. The compatible-generator diagonal lemma, and where this sandwich fails its premise

There IS a useful exact fast-diagonal mechanism when the operators truly match. Suppose A1,A2 have acquired displacements

    D_x A1-A1 D_t=G1 H1^t,
    D_t A2-A2 D_y=G2 H2^t.

Then

    D_x(A1 A2)-(A1 A2)D_y
       =G1(H1^t A2)+(A1 G2)H2^t.                  (4)

If the generator lengths are small, the new generators are acquired by a few fast structured actions. If EACH x_i-y_i is a certified unit, the wanted diagonal is simply the corresponding row-generator dot product divided by that unit. All initialization and denominators are identifiable. This is the explicit compatible-generator contract that could solve the problem; it is not automatically a theorem about arbitrary products of structured factors.

For the actual left power matrix L_alpha=V(alpha,Rb), alpha_j=y_j^d, the Cauchy row operator is U=diag(q^(d*rho)). Its action is

    L_alpha U=V(q^d alpha,Rb),

not D_alpha L_alpha. Declaring those two operators compatible would drop a real q-rescaling of the evaluation points. Under this LITERAL proposed Sylvester pairing the defect columns are evaluations of

    X^rho*(X-q^(d*rho)), degree rho+1.              (5)

On K_targets distinct alpha nodes, the first min(Rb,K_targets)-1 such columns are independent over each local field: their degrees are below K_targets, with distinct monic leading degrees, and evaluation at that many distinct nodes is injective in that degree range. Thus this particular mismatch has rank at least min(Rb,K_targets)-1, not a supplied constant-length generator.

For a concrete actual native specialization choose b=L, so the arguments are retained globally distinct V_j^(-1), and d a balanced power of two. The target-separation preprocessing has already returned a factor or unit differences V_j-V_h. All their local components have odd orders, so raising a ratio to a power of two cannot create a new equality. Consequently alpha_j=y_j^d remain unit-separated, even if d>k. Here J,K_targets,Rb are each of order k, so the mismatch rank is linear. This statement is ONLY about the specific operator defect (5). It neither proves the full sandwich has high displacement rank under every operator nor excludes cancellation in a different acquired representation.

Fast ordinary Vandermonde evaluation does not fix that mismatch: replacing L_alpha by a Lagrange evaluation map inserts an inverse fixed-node Vandermonde and changes the middle factor as well. Those transformations must be carried through (1) before a compatible generator can be credited. No low-rank generator for the correct paired matrix has been acquired from merely naming each individual factor structured.

## 4. Primary diagonal-transform theorem: the kernel data are input

A targeted primary check is [Vadim Olshevsky, Pivoting for Structured Matrices with Applications](https://www2.math.uconn.edu/~olshevsky/papers/piv2.pdf), Sections 7.7.2--7.7.3, Theorems 7.5--7.6. Its polynomial-Hankel-to-Cauchy transformation is explicitly for a PARTIALLY reconstructible operator. The supplied generator includes a kernel component R_K, parameterized by n coefficients. After the compatible polynomial Vandermonde transformation, the diagonal is computed by applying a Vandermonde map to THOSE supplied parameters. The theorem does not reconstruct the kernel component from off-diagonal displacement generators.

This is exactly the potential omission to guard against in a paired-diagonal application. Even for ordinary D_a with distinct nodes,

    D_a M-M D_a

annihilates every diagonal matrix. Its generator cannot determine diag(M); those entries are the missing kernel data. If an attempted conversion places the desired values P_b(y_j) in that diagonal kernel, writing down a short off-diagonal generator has not acquired them. Choosing unequal outer spectra can make diagonal extraction by (4) legal, but the generator under that NEW operator must actually be produced; adding a spectral shift changes the displacement by a term involving the original matrix.

The Olshevsky theorem is not applied as a complexity lower bound, and we do not claim our whole sandwich is automatically in its polynomial-Hankel class. It identifies the exact extra input in a relevant compatible diagonalization theorem, which cannot be silently omitted to turn (1) into free paired output.

## 5. The acquired q-kernel relation really cancels on the desired diagonal

The full padded coefficient kernel in `kernel-cauchy.md` is

    G(X,Y)=sum_(rho<H,r<d)c_(d*rho+r)X^rhoY^r,
    G(Y^d,Y)=P_b(Y).

Its acquired boundary g(X), including the last padded row, satisfies

    (1-q^bY)G(X,Y)-(1-Y)G(q^d X,qY)=(Y^d-X)g(X).    (6)

Therefore on the ORIGINAL diagonal its forcing vanishes EXACTLY:

    (1-q^bY)P_b(Y)=(1-Y)P_b(qY).                  (7)

The sparse boundary is real, but its cancellation does not supply an amplitude on each native target's q-orbit. Dividing at a collision is invalid; even after handling a legal nonzero denominator, a value on that orbit is still needed. This is not a new initialized endpoint just because (7) has first order.

The same source's transverse derivative T(Y) has the honest forced relation

    (1-q^bY)T(Y)-q^d(1-Y)T(qY)=-g(Y^d).

Its forcing and coefficient start T(0)=c_d are acquired, but the polynomial can have degree b-d. The two moving Vandermonde arguments and the simultaneous endpoint acquisition are not removed by this derivative equation. No auxiliary forcing, transformed diagonal or Cauchy pivot zero is assigned the original saturation decoder.

## 6. Other primary routes checked and exact applicability

[Bostan--Jeannerod--Schost, Solving Structured Linear Systems with Large Displacement Rank](https://mathexp.eu/bostan/publications/BoJeSc08.pdf), Theoretical Computer Science 407 (2008), Theorems 1--3, gives probabilistic nearlinear-in-n structured system solving when displacement rank is constant, with explicit node/noncollision and generator inputs; its dependence is soft(alpha^(omega-1)n). This is a solver for an acquired structured system, not a paired endpoint oracle. We have an acquired Cauchy factor and can use its lawful operations, but no structured system whose supplied right-hand side/generator determines the unknown vector (P_b(y_j)) has been constructed here. The separate node guards do not certify every pivot of an unrelated endpoint system. Randomized field regularization is not imported as deterministic composite-ring preprocessing.

[Bostan--Yurkevich, Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications](https://yurkevi.ch/data/Alin%20Bostan%2C%20Sergey%20Yurkevich_2020_Fast%20Computation%20of%20the%20N-th%20Term%20of%20a%20q-Holonomic%20Sequence%20and%20Applications.pdf), Theorem 6 and the subsequent growing-degree discussion, batches many INDICES of one fixed recurrence. It does not give all parameter-specialized endpoints P_b(y_j) for free. The parameter y changes both vectors in (2); treating each as the same recurrence at a different already-known index would assume the very local discrete-log/shift information sought. Its genuine batch-prefix special case is already used to acquire the Cauchy generators and tail starts. It has not supplied the final pair contraction.

The focused primary search did not identify an exact theorem giving soft(Rb+d+K_targets) paired output for the native rational-Newton/Cauchy/Vandermonde data with complete deterministic composite-ring initialization. This is a result about the checked theorems and executed transformations, not a broad claim of absence or a lower bound on another algorithm. A promising next theorem would have to acquire a compatible displacement generator INCLUDING any diagonal kernel data for (2), or directly compute those paired values/their restricted product without materializing K_targets right sides. It must preserve the original block labels for a factor/nonunit leaf consumer.

## Cached primary pins and outcome

All input arrays/generators/basis conversions used above are paid; all inverses belong to already certified units. The actual strongest structured theorem application (3) costs soft K_targets sqrt b, with the correct pair left in (2). The original covered query remains soft(J+sqrt(JL))=soft k^(3/2). The fully acquired Cauchy factor and exact characteristic diagonal sharpen the remaining contract; they do not change the factoring exponent.

Primary PDFs in `sources/`:

- `BoJeSc08.pdf`: SHA256 `7a76e996fd9186c0d375ddf12c60eaf9b1f9ff43ba0915c7876ebb9754f2b5ee`.
- `BoJeMoSc17.pdf`: SHA256 `466d9112461876577fd631808b37f3fab3150d621ba7518b29aef85f1075ee3b`.
- `olshevsky-piv2.pdf`: SHA256 `bc415d3c5da2b4106225e9a7364b94f1589ec013c7859fcd6576056398005732`.
- `qholonomic-2022.pdf`: SHA256 `718904c094b78a76732fc7ca3959129c6996fd2689a251f580e20c2af91919fd`.
