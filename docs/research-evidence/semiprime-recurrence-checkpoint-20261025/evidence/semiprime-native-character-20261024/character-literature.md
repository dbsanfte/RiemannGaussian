# Native character identities and an acquired primitive orbit norm

24 October 2026. Scratch only; no repository changes, numerical examples or backend work. Positive acquisition: the primitive-character scalar norm of ONE supplied packed element is acquired in soft k, including at zeros, by an explicit public automorphism-product algorithm. This is a classical Galois-norm construction adapted and fully charged here; no novelty claim is made. It is stronger than merely naming a packed power, but it does not acquire all weighted native rows or their long difference product. The native attempt and precise remaining data are derived below.

## Prior scope and the repaired conductor supply

Read journal 32100–32260 (packed Gauss quotient, exceptional characters and native phase cancellation), the composite polarized-Jacobi entry near 34100, and the older composite-colour/normalized Gauss work. One packed C_E vector, antipodal unit products and polarized reconstruction are credited as prior results. They are not renamed as long-query acquisition.

Choose an auxiliary prime ell in a paid dyadic interval of sixth-root scale, then set k=ell-1 and H=k². This is a change to the native ROW modulus, which is now composite and even. On the retained hard branch P,Q>16k², gcd(N,k*ell)=1. Factor k publicly, construct a primitive root modulo ell by exact order tests, and enumerate its log table. A sieve/SPF table through O(k), at most ell candidate primitive-root tests with polylogarithmic work each, and one power walk cost soft k. No least-prime-in-a-growing-progression theorem or hidden-prime logarithm is used.

For every unit tag j modulo k set a_j=[N*j^(-2)]_k. Choose the centered b_j solving

    b_j=((a_j*j²-N)/k)*j^(-1) modulo k,
    ell_j=k*b_j-2*a_j*j.

Then the original integer quotient construction works because only unit tags/inverses and the exact quotient are used. In particular its own tag is P modulo k. A prime-modulus two-to-one inverse-square map is NOT assumed for composite k. Any modulus-specific selector/coverage bound must use the actual unit-tag construction; the supplied scalar preparation does not transfer automatically to a Gauss-derived base.

Work in A=R[X]/(X^k-1), R=Z/N. k is a unit, so this algebra is etale locally. For proof only adjoin a primitive additive ell-th root Z. Let G_a be the original packed Gauss sums, u=G_1, rho_j:X->X^j for unit j, and q_G=u^H. The existing corrected Jacobi binary routine acquires a supplied C_E with u^E=C_E*G_(E mod k) in soft k for polynomial-size exponent E. It includes nonprimitive/trivial character corrections. It does not materialize a list of k such vectors in that same cost.

## Primary algorithm contracts actually checked

Nguyen–Schmidt, *Fast Computation of Gauss Sums and Resolution of the Root of Unity Ambiguity* (2009 author version), [primary PDF](https://personal.ntu.edu.sg/bernhard/Publications/pub/Gauss.pdf), Lemma 13 and Algorithms 20,30,31: ideal factorization is followed by integral lattice/Gram construction and Fincke–Pohst; root ambiguity is resolved through recursive H-polynomials. These are substantial exact algorithms, not a soft-k native mixed-norm theorem. Their letters specialized to characteristic p=ell and character order e=k give ord_e(p)=1: the stated Frobenius-fixed-field reduction is trivial. The ambient field degree is k*phi(k), and their H-polynomial representation is modulo X^(k*ell)-1. This distinguishes the explicit dense reconstruction from the sparse k-term input and the already cheaper packed quotient. Cache `sources/nguyen-schmidt-2009.pdf`, SHA256 `b08f0bdc0a9177c38985654db3dafd6768dc1937928f2812769e7f38103b6e09`.

Lenstra–Silverberg, *Testing isomorphism of lattices over CM-orders*, Theorem 1.3, [primary PDF](https://www.math.uci.edu/~asilverb/bibliography/CMorders.pdf), [NSF primary manuscript mirror](https://par.nsf.gov/servlets/purl/10173989), gives deterministic POLYNOMIAL-time recovery from an explicit CM-order, fractional ideal I and totally positive w with I*bar(I)=Aw, deciding/constructing v with I=Av and v*bar(v)=w. It does not promise linear rank cost, receive a factored modular difference circuit as an ideal basis, or infer the missing polarized product for free. The earlier composite-Jacobi application already records this distinction. Merely reconstructing a multiplicative Gauss product does not provide ideals of its shifted differences. Cached arXiv:1706.07373v2 manuscript: `sources/lenstra-silverberg-CMorders.pdf`, SHA256 `3ad0d7592e70aeb079c93324c6c20f2343de7a0f82547d2081a874e2fda97dcd`.

## 1. Concrete soft-k norm constructor: every input and group action acquired

Input one actual degree-<k vector V in A. No assumption of invertibility is required. The target is the scalar norm over the PRIMITIVE character component, not over the full algebra with its trivial augmentation.

Acquire the primitive idempotent using Ramanujan sums:

    e_prim=(1/k)*sum_(l=0)^(k-1)c_k(l)*X^l,
    c_k(l)=mu(k/d)*phi(k)/phi(k/d), d=gcd(k,l).

An SPF sieve through k supplies all needed mu/phi values and factors. Exact integer quotients, k gcds and reduction modulo N acquire this vector in soft k. Its coefficient at zero is phi(k)/k, a UNIT under P,Q>16k². The Fourier orthogonality identity gives e_prim(xi)=1 exactly at primitive k-th roots, zero at all other k-th roots, over each hidden splitting field. This is a proof device; no roots in either hidden field are acquired.

Acquire a direct-product decomposition of U(k). For odd prime powers p^e dividing k, the cyclic unit group has order phi(p^e); test primitive-root candidates by its factored exact-order conditions. There are at most p^e candidates. For powers of two use the explicit factors generated by -1 and 5, with the usual trivial/small cases. CRT lifts each local generator to a unit modulo k. The SPF sieve factors every test order; sum of the prime-power moduli is O(k), so all brute-force tests, CRTs and generator orders cost soft k. This is public finite-group setup, not factoring N.

For a cyclic factor generated by g of order d and an acquired W, define

    N_h(W)=product_(a=0)^(h-1) rho_(g^a)(W).

Compute it recursively by

    N_0=e_prim,
    N_(2h)=N_h*rho_(g^h)(N_h),
    N_(2h+1)=N_(2h)*rho_(g^(2h))(W).

Use W=e_prim*V and apply these cyclic norms successively for every direct-product generator. Their group actions commute. Each rho_t is a coefficient PERMUTATION in the full A representation, costing O(k); each cyclic multiplication costs soft k. At most O(sum log(d))=O(log phi(k)) recursion steps suffice. Starts, automorphism indices and all output coefficients are charged. There is no input inverse, denominator pivot, generic rank profile or hidden-field oracle. The only scalar inverses used are the certified public k and phi(k).

Let the result be Z=e_prim*product_(j in U(k))rho_j(V). In a splitting field, the primitive k-th roots are a transitive U(k) orbit. Z therefore takes the SAME value nu at every primitive root and zero elsewhere. Local etale evaluation is injective, so Z=nu*e_prim over R itself. This proves the invariant-constant assertion even when V has zeros or different local supports. Recover the actual scalar by

    nu= [X^0]Z * k/phi(k).

It is exactly Res_X(Phi_k,V), the primitive-component norm. Total arithmetic/bit work is soft k (with the usual log N factors) and explicit storage is soft k. An alternative implementation could reduce modulo Phi_k; the full coefficient-permutation representation above avoids assuming fast arbitrary automorphism composition in that quotient.

## 2. Execute it on one ACTUAL native difference

The native target has the exact expression

    T_j=u^(ell_j)*G_j^(a_j)*G_s^N, s=j^(-1) mod k,
    Lambda_j=ell_j*1+a_j*rho_j+N*rho_s.

Its additive-root grade is ell_j+a_j*j+N*s=0 modulo k, as is q_G's. Thus T_j and q_G descend to A. One fixed row is acquired by the existing corrected Jacobi quotient routine in soft k; signed powers use certified Gauss units. A fixed bounded seed q_G^i costs another soft k. Applying the constructor to V=T_j-q_G^i therefore REALLY acquires its primitive norm in soft k, including at zeros. A proper gcd with N is an independent valid factor.

Because k is even, a_j and N are odd and ell_j is even. At the trivial character every G_a=-1, hence T_j(1)=1 and q_G(1)=1. Their difference ALWAYS has zero augmentation. Its full A-norm is therefore identically zero; the primitive projection above is essential, not optional. A saturated primitive norm can still represent only componentwise zeros and does not by itself give a whole-local-algebra collision or the original-beta bounded decoder. Gauss-base order/recovery and useful support localization remain separate obligations.

This is a genuine new paid primitive in this task's ledger, not the desired long query: repeatedly applying it to all row/seed pairs pays for each acquired V. A scalar norm of an already supplied packed element is distinct from acquiring that packed element's long product.

## 3. Test the orbit shortcut against the native family exactly

For an acquired V the algorithm batches ALL its automorphism conjugates. Taking V=T_j-q_G^i computes

    product_(r in U(k))(rho_r(T_j)-rho_r(q_G)^i)

on the primitive component. The seed is transformed too. Native targets do not supply a single compatible orbit with one fixed seed. Applying rho_j to their actual formula gives

    rho_j(T_j)=u^N * G_(j²)^(a_j) * G_j^(ell_j),
    rho_j(q_G)=G_j^H.

The inverse-square weights and centered integer carries remain, as do the changing transformed seeds. Replacing these expressions by rho_j(T)-q_G^i changes the query; no cover theorem for that substituted family is claimed. Thus the acquired orbit norm does not silently become an all-native-row contraction.

For k>2, multiplicative identities do give cheap older aggregates; the bounded k=2 case is handled directly. With E0 the trivial projector and D=E0+(1-E0)*ell, unit-tag antipodal Gauss products equal D*X^(k/2). Native a_j=a_(-j), N+a_j even, and ell_j+ell_(-j)=H*tau_j with tau_j in {-2,-1,0}. Consequently

    T_j*T_(-j)=q_G^(tau_j)*D^(N+a_j).

All pair products have a shared-three-vector/scalar description, credited to the prior unit-normalization work and the companion acquisition report. Their shifted difference product is instead

    (T_j-z)*(T_(-j)-z)=z²-(T_j+T_(-j))*z+T_j*T_(-j).

The required pair TRACE remains. Known pair products, Stickelberger multiplicative ideals or norm phases do not supply it. No false norm-minus-one or phase cancellation is used here.

## 4. Stickelberger operator factorization: the exact remaining mixed norm

At the true own index HI=a_j*P+Q+ell_j, the group-ring identity is

    Lambda_j-HI = rho_s*(P-rho_j)*(Q-a_j*rho_j).   (1)

Expanding uses rho_s*rho_j=1 and N=PQ, and proves the identity exactly. It expresses the old Frobenius phase cancellation; P,Q are proof-side integers, not known operator inputs.

The original difference is a known unit times u^(Lambda_j-HI)-1. Stickelberger determines prime-ideal valuations of the MULTIPLICATIVE Gauss expression, supported above the known conductor ell. At P,Q distinct from ell those factors are units individually. Their difference can nevertheless vanish, precisely as the native own source requires. Valuations of multiplicative factors do not determine the extra cancellation in unit-minus-one. Root-of-unity ambiguities likewise cannot be discarded inside that difference.

Taking the relative norm over the additive-root automorphisms gives no compression here: grade zero fixes both T_j and q_G, so that norm is simply (T_j-q_G^i)^k. The primitive-character norm IS now cheaply acquired once V is supplied, but (1) gives neither all supplied V_j,i nor their long product. A proposed polarized reconstruction of that mixed norm must acquire its ACTUAL ideal and positive norm data; the previously checked CM theorem does not supply them from (1). Large N-weighted ideal exponents and their integer bit lengths cannot be called modularly free.

For comparison, if all J packed targets were explicitly acquired, ordinary monic blocking over rank-k A would acquire the long packed product at soft k*(J+sqrt(JL)) base-ring work, including input vectors and no collision-value inverses; taking its primitive norm then adds soft k. This prices a complete value computation in that representation, not a complete factor recovery theorem for spurious component hits. At J~k,L~k² the cost is soft k^(5/2), and no rank-k operation is priced as scalar. The existing original scalar query remains the better covered interface.

## Outcome

The conductor-first setup closes the specific auxiliary supply gap, with composite/even native bookkeeping retained. The concrete acquisition advance is an initialized, zero-safe soft-k PRIMITIVE orbit norm of one acquired packed vector, with public group setup and scalar extraction proved. It executes one actual native leaf norm and precisely tests why the full-row orbit substitution is not licensed. The Stickelberger/H-polynomial/polarized algorithms inspected do not provide the remaining soft-k mixed row/seed contraction under their actual contracts. No general absence theorem is asserted.

All-row weighted difference acquisition, retained useful support, new-base order preparation and saturated recovery are still unpaid. One packed power, one multiplicative weighted norm, a cheap primitive norm and the factorization (1) do not themselves compute the covered long query. No improved all-input factoring rate is claimed.
