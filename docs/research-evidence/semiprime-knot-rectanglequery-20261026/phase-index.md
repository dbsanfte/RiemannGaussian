# Exact native phase index and the obstruction to small literal wraps

26 October 2026. Parent arithmetic derivation, independently checked in
phase-index-review.md. This tests a specific proposed contraction of the
new Cartesian query: identify the sides of its small coefficient box up
to literal q-powers, then invoke a finite cyclic product identity. Such
wraps cannot hold at the proposed dimensions for a positive proportion
of the actual colours. This is not a lower bound on arbitrary implicit
evaluation, numerical modular aliases, or factoring.

## 1. The phase image is exactly computable

Let k=2*3^e, H=k^2, gcd(N,k)=1, and let j be a unit modulo k with
1<=j<k. Set g=gcd(j-1,k). On the actual lattice

    Lambda_j={(a,b): a*j^2=b*N mod k},

the unwrapped exponent character modulo H is

    chi_j(a,b)=a*(1-j)+b*N*(1-jinv) mod H,         (1)

where jinv is any inverse of j modulo H. Canonical phases give the
same residue; their integer carry changes the exponent by a multiple
of H. The exact image of (1) is

    image(chi_j)=g^2 Z/H Z,
    L_j=|image(chi_j)|=H/g^2=(k/g)^2.             (2)

Proof: use the lattice basis (k,0),(a0,1), where
a0=[N*j^(-2)]_k is an odd unit modulo 3. The two image generators are

    e1=k*(1-j),
    e2=(j-1)*(N*jinv-a0).

Both are divisible by 4: j is odd, and N*jinv and a0 are odd. If
j!=1, write t=v_3(j-1). Then t<e: the only other representative with
j=1 mod 3^e in [1,2*3^e) is 1+3^e, which is even. Moreover

    N*jinv-a0 = a0*(j-1)+k*c

for some integer c, since a0*j^2=N mod k. The first term on the right
has 3-adic valuation t<e, so v_3(e2)=2t exactly; v_3(e1)=e+t.
Consequently

    gcd(H,e1,e2)=4*3^(2t)=g^2.

This proves (2). For j=1 both generators vanish modulo H, g=k, and
the image has size one, as the same formula says. No factor of N is
used to compute g or L_j.

## 2. A proposed literal cyclic wrap must pay this index

Let u,w be ANY integer basis of Lambda_j, including the acquired
weighted Gauss basis. A literal q-wrap in the coefficient directions
with positive lengths C,D would require integer identities

    C*E_u=H*c, D*E_w=H*d                         (3)

for some integers c,d. The same congruences are required if one first
changes the generator labels by known q-powers. Equation (3) would
make chi_j factor through Z/C Z times Z/D Z. Since u,w generate the
whole image, the factor map is surjective. Therefore

    L_j divides C*D, in particular C*D>=L_j.       (4)

More generally any finite-index sublattice Gamma on which every
exponent is a literal multiple of H lies in ker chi_j. Thus
[Lambda_j:Gamma] is divisible by L_j. This also rules out bypassing
(4) merely by choosing a nonrectangular fundamental region.

There are exactly k/6 unit colours with j=2 mod 3. For all of them
g=2 and L_j=H/4. The new Gauss grid has A*B<7k+1. For sufficiently
large k its two sides cannot be identified as in (3), independently
of the choice of Gauss basis, because its area is too small even for
the index condition. This is an arithmetic contradiction for those
actual public colours, not a comparison with arbitrary generic roots.

A fully tabulated phase orbit closed under both basis translations
contains at least L_j distinct residue classes. Tabulating separate
complete orbits for these k/6 colours would therefore contain at least
k^3/24 colour-labelled states. This only charges that explicit
construction. It says nothing about the cost of an implicit determinant,
a compressed product circuit, reuse between colours, or a different
collision-preserving functional.

## 3. What this excludes and what it does not

The missing scalar in sparse-projection.md cannot be replaced by the
norm of its SAME small box with literal q-periodic sides. That exact
wrap premise fails for the colours just counted. Introducing an
auxiliary root of unity instead changes the parameter and needs a
separate theorem relating its norm to the original finite query.

Numerical equalities beta^E=beta^F modulo N or one prime may occur
without E=F mod H. They are not excluded by (2)-(4); usable nonliteral
equalities can themselves reveal a factor. This report supplies no
algorithm finding them and no lower bound against their use. Likewise,
the known scalar beta^(g^2) is a supplied root of q of degree L_j;
its existence does not evaluate the product over a phase orbit or
identify the small box's opposite sides. A one-dimensional scalar
character is not the missing whole-orbit product functional.

The phase image is useful exact structure, and it gives a rigorous
reason one natural cyclic contraction does not apply. It does not
rule out a direct nonperiodic joint product algorithm, a new sparse
arithmetic cover, or the desired sixth-exponent factoring algorithm.
The current full-query rate is unchanged.
