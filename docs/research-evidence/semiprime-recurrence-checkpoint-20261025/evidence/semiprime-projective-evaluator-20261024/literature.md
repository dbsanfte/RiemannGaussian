# Compiled q-Pochhammer input and the output-degree GCD theorem

24 October 2026. Primary-source constructive audit. No deterministic many-point theorem beating soft sqrt(JL) was obtained at J~k,L~k². The strongest tested adaptation is specific: compile the geometric product into an ordinary uniform division-free circuit of softly sqrt-L size, then test the output-degree-sensitive straight-line GCD theorem on that ACTUAL input. The circuit compilation succeeds. The small-output GCD citation does not supply the missing uniform factor-selection algorithm. This report does not re-survey the old q-holonomic, Gosper, formal-composition or adjoint gates.

## 1. A real compact circuit, not just a recurrence descriptor

Let q be the actual unit in B and set

    G_L(X)=prod_(i<L)(X-q^i).

Choose b=ceil sqrt L and t=floor(L/b), and acquire

    B_b(T;X)=prod_(r<b)(X-q^r T)
             =sum_(s=0)^b d_s X^(b-s)T^s,
    d_s=[T^s] prod_(r<b)(1-q^rT).

The b+1 d_s are ACTUAL q-dependent constants, acquired by the existing product/doubling routine in soft b work. No coefficient of the degree-L G_L is requested. Put Q=q^b. For an indeterminate input X, compute X^0,...,X^b, form d_s X^(b-s), and evaluate this degree-b polynomial in T at the FIXED nodes Q^a, 0<=a<t. The resulting t values are exactly B_b(Q^a;X). Their product, multiplied by the actual <b remaining linear factors, is G_L(X).

The fixed-node MPE can be compiled as a straight-line circuit in X: its product/remainder-tree moduli depend only on q, and every division is by a monic polynomial; geometric evaluation may equivalently use a chirp convolution with powers of Q. No X or X-dependent factor is inverted. All fixed arithmetic constants/preprocessing and all scalar products are charged in soft(b+t). The resulting circuit is uniform and division-free WITH RESPECT TO X, over the already acquired coefficient ring. Its divisions during constant initialization are only the previously lawful public operations; the direct product-tree version needs no new q-difference inverses. It evaluates through arbitrary collisions and at X=0.

Thus there really is an ordinary acquired circuit of length l=soft sqrt L=soft k for G_L, not merely an O(log L) recurrence schema whose recursive calls conceal growing arrays. F=prod_j(X-V_j) adds soft J circuit construction work. This compilation is a direct restatement at the circuit-interface level of the old one-point Strassen/Pollard/q-holonomic baby/giant evaluation, not a new single-point speedup. Running the circuit at J unrelated supplied points separately costs soft J sqrt L; running it in B[X]/F costs soft l M(J), giving a soft k² execution. Neither is the desired batch algorithm; the existing shared block scheme remains better at soft sqrt(JL).

The useful now-explicit next contract is: acquire a scalar weak readout or the relevant low-degree collision factor from this supplied length-soft-k circuit and the supplied split degree-J F, with deterministic composite-ring validation, without expanding its degree-L output or doing J independent runs. This contract no longer has an unpaid compact circuit as its input.

## 2. Test the strongest output-degree-sensitive primary theorem

Erich Kaltofen, *Single-Factor Hensel Lifting and its Application to the Straight-Line Complexity of Certain Polynomials*, STOC 1987, 443–452:
https://doi.org/10.1145/28395.28443
https://users.cs.duke.edu/~elk27/bibliography/87/Ka87_stoc.pdf

Theorems 3 and 4 are directly relevant to the compact-input/small-GCD idea. Over a field, with the printed sufficiently-large-field condition card(F)>2^l(2d+1), Theorem 3 gives a division-free circuit of length

    O(l M(d³)+d² M(d²))

for a degree-d factor g of a division-free circuit polynomial f, provided gcd(g,f/g)=1. Theorem 4 gives the corresponding length bound for a degree-d GCD of supplied circuit polynomials. Small-field extension/descent is discussed in the source, but that setup is not free in our unknown composite algebra. In particular the polynomial local-order bounds do not imply the printed exponential-in-l field-size premise. This report does not silently improve that condition by substituting an actual degree bound.

At d=1 the stated OUTPUT CIRCUIT length would be O(l), which superficially matches the target after Section 1. But this is NOT a uniform O(l) construction algorithm from the input circuits. The introduction explicitly says polynomial-time constructibility is lost, and the discussion after Theorem 3 repeats the limitation. The Single-Factor Lifting algorithm requires, as INPUT,

    g0(x)=g(x,0),
    h(x,0) mod g0(x)^(d_y+1),
    the corresponding truncated g0-adic expansion of f(x,y).

The theorem's proof treats coefficients of the selected factor image g0 as field scalars with short circuit length. Their acquisition is not supplied merely by bounding d. In the present univariate degree-one problem that selected factor image already encodes the unknown common root (or which of the supplied V_j is the common one). A short linear answer circuit can plainly contain that root as a scalar. Its existence does not select the correct tag or acquire any nonzero readout denominator.

This is a literal execution of the candidate interface: Section 1 supplies the circuit length l; the good smaller nonsplit field supplies a mathematical degree-one local GCD and coprimality; the source still requires the actual field setup and selected initial factor data before its lifting computation runs. Neither is provided by the public unique-hit promise. On other local components the GCD degree may differ, so a degree-one local existence statement is not a monic global B-GCD algorithm either. Existing subresultant/norm/coordinate classification remains necessary for an actual acquired output.

The statement is useful as a sharply specified factor-seed subroutine, not a solution: once a suitable small factor image and the required local/quotient arithmetic are ACTUALLY available, the lifting stage can avoid reading all degree-L coefficients. Supplying that image by an original one-row query for an arbitrary guessed tag is a valid test, but no deterministic O(1)-tag cover follows; enumerating all tags does not improve the existing query. No hardness claim about this structured native case is inferred from the failure to initialize that theorem.

## 3. Check the modern few-point MPE theorem on these inputs

Joris van der Hoeven and Grégoire Lecerf, *Faster multi-point evaluation over any field*, primary author page (HTML dated 11 August 2025):
https://www.texmacs.org/joris/bieval/bieval.html
https://doi.org/10.1007/s00200-025-00704-7

The linked cached PDF identifies itself as the preliminary version of 8 November 2024; that exact version distinction is retained. Its Theorem 3.9 takes a supplied polynomial P of total degree <=d in a FIXED number n of variables over an effective field and evaluates it at N points. It includes the N<<d^n regime, but its size expression contains N+d^n. For our univariate d=L,N=J~sqrt L, the stated bound specializes to soft L. The proof explicitly performs coefficient-polynomial expansions and polynomial reductions; it does not take a q-difference descriptor or an arbitrary short evaluation circuit in place of the polynomial coefficient input.

A fixed-dimensional digit reshape of G_L likewise still has Theta(L) coefficient slots. The fact that those coefficients satisfy a first-order q-hypergeometric recurrence does not supply a recurrence-input variant of this theorem. Conversely Section 1's circuit is genuinely compact; this establishes an alternate input interface, not a license to substitute its circuit length for d in the theorem's degree/size terms. The source is over fields, so unknown composite-ring pivots/extensions would need their own proof even if the input-size issue were resolved. No generic lower bound for implicit evaluation is claimed.

## 4. The 2026 spiroid theorem really covers composite scalar moduli

A further recent primary source was checked rather than treating all modern composition algorithms as field or randomized oracles:

Joris van der Hoeven and Grégoire Lecerf, *Fast modular composition using spiroids*, Journal of Complexity 96 (2026), Article 102073:
https://doi.org/10.1016/j.jco.2026.102073
https://www.texmacs.org/joris/fftcomp/fftcomp.pdf

The current author PDF is dated 12 August 2026 (the HTML still advertises a December 2025 preliminary version). Its Theorem 1 gives degree-D modular composition over Z/rZ, for an arbitrary positive integer r, in

    D^[5/sqrt(log D)] soft(D log r) bit operations.

Thus it DOES have a deterministic exact scalar-composite-ring contract; a known hidden prime or random field pivot is not the missing assumption here. Its controlled floating-point computations are internal to a proved exact reconstruction algorithm, not an approximate oracle being substituted for modular equality. The factor D^[5/sqrt(log D)] is subpolynomial and is NOT silently called polylogarithmic/softly linear.

However Section 5 explicitly inputs coefficient arrays P,Q of degrees <D and monic R of degree D. It Kronecker-segments ALL coefficients of P into a multivariate polynomial and takes canonical integer lifts. It does not input a short circuit for P or its coefficient recurrence. Applying this with D=J and outer P=G_L is outside the degree contract. First replacing G_L by G_L modF is the very acquisition requested. A lawful padded application could take D=L+1, outer G_L, Q=X and modulus X^(L+1-J)F; it still requires the dense G_L input and charges L^[1+o(1)] time, or k^[2+o(1)], rather than beating the k^(3/2) baseline. A fixed-dimensional digit reshape still has Theta(L) coefficient data. These are costs of these literal executions, not lower bounds on a recurrence-aware extension of the spiroid algorithm. The quoted theorem is for Z/rZ; transferring it to the quadratic B would additionally require an explicit fixed-extension reduction, rather than an unmentioned field assumption. The input mismatch already occurs over Z/NZ itself.

## 5. Complete retained-cost execution and conclusion

For completeness the actual batch baseline is already an initialized zero-safe algorithm. Acquire a baby geometric product of length b, evaluate it at all J floor(L/b) ACTUAL starts associated with the supplied native targets, multiply the outputs by original row, and process clipped tails. Its complete ring cost is soft(b+JL/b+J), optimized at b near sqrt(JL), hence soft(J+sqrt(JL)). The polynomial-coefficient scalar/constant-width formulation instead builds degree-Jb blocks and uses L/b starts, with the same optimum. Monic evaluation, public powers and retained original row/index labels pay all inputs. Unit/zero/factor classification and the established native consumer remain unchanged. This old baseline is credited, not presented as a fresh theorem.

The targeted search therefore produced an explicit compact circuit suitable for further uniform implicit-GCD work and an exact audit of the tempting small-output theorem. It did not produce a theorem or adaptation giving a whole cost below k^(3/2). In particular no new deterministic semiprime exponent, implicit MPE oracle, known local order/field, or unverified factor seed is assumed. The next meaningful algorithm must uniformly select/recover the collision factor or weak tag readout from the already compiled circuit, rather than appeal only to the short size of a circuit that could contain the answer.

## Primary caches and duplicate credit

- sources/kaltofen-author.pdf, author-hosted text version: SHA256 56ea27444f536253f8e7bbbbb08c675c7dfc8c811b2f34ce5851e9f8c7e05257.
- sources/kaltofen-1987.pdf, original proceedings scan at https://userpages.cs.umbc.edu/phatak/691a/supl/hensel-kaltofen-1987.pdf : SHA256 e5585171b62235b7ed9afaa7399ca50e87d2a03cfaf8379e1d6e8e47156ad00e. Both primary versions were read for the theorem and its initialization caveat.
- sources/spiroids.pdf, author PDF dated 12 August 2026: SHA256 3fef0f8c6851f45dc9e876ae178c46d73264546e9bbcde6a9d1204b69d600ecc.
- sources/bieval.pdf, linked author PDF: SHA256 e2403c7a8fd8dca57f1a4a8c8b53e70d7606afab5f1af9e2dd45c77b0ff288e5.
- The one-point q-Pochhammer baby/giant algorithm is previously audited Bostan–Yurkevich, https://arxiv.org/abs/2012.08656; no new theorem is claimed for that old numerical bound.
- Earlier selected-coefficient/prefix, generic structured-system, formal-composition, unit-filter, gradient and subresultant consumers remain credited to their frozen packets. No shared or frozen source was edited.
