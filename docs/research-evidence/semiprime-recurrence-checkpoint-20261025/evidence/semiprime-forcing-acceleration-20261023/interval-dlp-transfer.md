# Bounded interval-DLP / shift-dispersion transfer check

23 October 2026. Scratch only. No deterministic factor-returning transfer
below the inherited soft(sqrt(JL)) native query was found in this bounded
primary-source check. This is a search outcome, not a statement that such
an algorithm cannot exist. Cheon/known-exponent-field results were not
reopened, and no generic-group lower bound is used.

## A genuinely order-oblivious deterministic theorem, at the wrong scale

Tinani--Rosenthal, *A deterministic algorithm for the discrete logarithm
problem in a semigroup*, arXiv:2101.11500v4 (15 March2022), Section4.1 Algorithm4/Theorem1
and Section4.2 Algorithm5/Theorem2, was read from the cached PDF. It does
not assume the element order as input: doubling plus deterministic
baby-step/giant-step computes the cycle and then the logarithm. Its
certified total cost is O(sqrt(n_x) log^2(n_x)) semigroup steps and
O(sqrt(n_x)) stored elements, where n_x is the actual cyclic-semigroup
size. The proof explicitly uses equality of represented elements and
sorted baby/giant lists.

Thus lack of a supplied order ALONE is not a valid rejection. But for
q mod N the actual global order is the product of its two coprime local
orders, hence exceeds 256m^4. This theorem's global-order scale is not
our interval length L~m^2. More importantly, an equality q^i=Y_j mod P
need not be an equality mod N. Running the published equality/sorting
algorithm mod N therefore need not see the native guaranteed witness.
Running it in F_P would need the unknown modulus P; its local square-root
scale can be m^1.5 and supplies no exponent improvement either.

Instrumenting actual arithmetic zero tests with gcds is legitimate, but
does not make sorting modulo N into sorting by equality modulo P.
For EXPLICIT baby and giant lists, replacing that comparison by a
product tree / monic MPE does give the inherited factor-aware algorithm:

    b baby seeds, J*ceil(L/b) shifted targets,
    cost soft(b+J*L/b+J).

Choosing b~sqrt(JL) returns soft(sqrt(JL)+J), including gcds and ordinary
interval localization. No sub-square-root list construction is supplied
by the semigroup theorem. The same observation preserves its positive
order-oblivious feature without pretending it supplies hidden-prime
partial equality.

## A rigorous subexponential FIELD algorithm is randomized and needs p

Pomerance, *Fast, Rigorous Factorization and Discrete Logarithm
Algorithms* (1987), printed pages120--121 and Algorithm IEC on p137,
was inspected directly in the scanned primary PDF. With
L_p=exp(sqrt(log p loglog p)), the stated bounds are EXPECTED worst-case
L_p^(sqrt(2)+o(1)) preprocessing and L_p^(sqrt(1/2)+o(1)) individual
discrete-log time. These are rigorous randomized bounds, not heuristic
NFS bounds and not deterministic bounds.

Algorithm IEC explicitly takes a prime p>3, a primitive element g mod p,
and a target x mod p. It repeatedly samples exponents from 1,...,p-1,
factors the canonical residues g^e mod p / p_j*g^e mod p into a smooth
factor base, and solves the resulting exponent relations modulo p-1.
Knowing only residues mod N does not supply these canonical mod-P
integers or the exponent modulus P-1. Factoring a representative mod N
does not yield the factorization of its reduction mod P. No construction
of that missing local relation input was found here. In addition, the
random sampling is not a deterministic hitting set. The favorable
subexponential field bound therefore does not furnish the requested
uniform deterministic native query.

The primary abstract/introduction of Galbraith--Pollard--Ruprai,
*Computing discrete logarithms in an interval*, ePrint2010/617 revised
version, was also inspected through indexed primary-PDF text. It
explicitly labels its improved constants times sqrt(L) as heuristic
average-case expected random-walk bounds. This is not a deterministic
worst-case exponent improvement. PDF fetching was denied, so no full
proof inspection or cached-PDF claim is made for that paper.

## Shift dispersion duplicate guard and exact outcome

The earlier inspected Koutschan--Zhang q-dispersion algorithms work over
characteristic-zero K(q), q transcendental. Their factor-pair power test
is not a finite-field partial-equality algorithm; this exact issue is
already recorded in `adaptive-dispersion.md`, Section3, and is not a new
finding of this pass. Formal absence of a q-shift does not certify that
its specialized resultant is a unit mod N.

Consequently this pass supplies neither a better one-shot gcd/witness
algorithm nor a faster forcing initializer. The constructive step still
needed is a bounded LOCAL interval/shift selector using N-residues and
gcd guards, with its own deterministic constructor and total cost below
soft(sqrt(JL)). A supplied field logarithm or an abstract equality oracle
for one hidden prime is not that constructor. No impossibility claim for
specialized native arithmetic, finite-field techniques, or adaptive
factor-aware polynomial pivots follows.

## Source/read pins

* Tinani--Rosenthal primary: https://arxiv.org/pdf/2101.11500 . Cached
  `tinani-rosenthal.pdf`, SHA256
  `fa6aa813d7a7d5ba72ee9e4fa65388dcc9455a9f6098f7a2acfec5a23b2f3f52`.
  Theorems/algorithms above read from pdftotext; published publisher PDF
  also opened: https://doi.org/10.1515/jmc-2021-0022 .
* Pomerance primary author scan: https://math.dartmouth.edu/~carlp/disclog.pdf .
  Cached `pomerance-1987.pdf`, SHA256
  `3c7c6254ee24fb88d6e8997d685003ee15435e09a5df9c191861889f56d584a1`.
  Printed pp120--121 and137 inspected as local rasterized scan images;
  no OCR/full-paper-read claim.
* GPR primary indexed PDF text: https://eprint.iacr.org/2010/617.pdf .
  Abstract/introduction only; no local cache/full-proof claim.
* Prior dispersion proof/interface audit:
  `/tmp/semiprime-first-collision-acquisition-20261023/adaptive-dispersion.md`,
  Section3, reread. No primary rereading claimed for that older audit.

No new backend, samples, example campaign, tracked edits, or code from
downloaded sources was executed.
