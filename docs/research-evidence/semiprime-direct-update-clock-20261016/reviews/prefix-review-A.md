# Review A: independent prefix proof review and main-report source self-audit

2026-10-16. Verdict: PASS with the exact attribution below. The reviewer authored direct-update-clock.md, so its mathematical checks here are a SELF-AUDIT, not an independent review. The separate direct-prefix-recurrence.md was written by another agent and receives independent mathematical review here. Independent reviewers separately cover the main report. No file being reviewed was edited, and no repository build was run.

## Exact targets

- direct-update-clock.md: 11654 bytes, SHA256 `f07353444c81c063877bf68c6107edb62ffec547a231340e8f79e2d963572d62`.
- source-pins.json: 1015 bytes, SHA256 `6e33dac5ee8c8a148d11df9b97ab6c1f8c3a075e39a33834dee704ba71baf670`.
- direct-prefix-recurrence.md: 10819 bytes, SHA256 `598a3041a90f761744811df206d9ab11ea8452ec8263db35afd984ed0999fb59`.
- prefix-source-pins.json: 1034 bytes, SHA256 `82678e677b5a7cb02e1d8833985a2700c67489613ade0f2fff17aa5668799bca`.

All three main metadata dependencies and all four prefix metadata dependencies match actual raw lengths/SHA256. The archived G15 gzip was also decompressed and its declared plain length/hash verified. Read its Theorem R and limitations, and read the exact unit-row-density source statement and its low-residue quadratic fiber argument.

## Independent prefix proof

The generic hypotheses are sufficient. U_n is explicitly nonzero through L, so division at all retained starts is legal. First regular evaluation at j<=M-1 follows from confluent independence after combining repeated h-frequencies, with the required characteristic>D_k. Dropping coefficient FUNCTIONS identically zero never extends the nominal k<=L-r range. The shifted equation count L-r-M+2 is paid explicitly. An effective order-zero relation contradicts the nonzero prefix immediately.

The update polynomials B_t have exact degrees Jt. Frequency expansion uses q^u h^v with u<=Jr and v<=D_h; the confluent bound forces zero coefficient POLYNOMIALS in the formal ordinary-index variable, not merely numerical zero values. No-alias cancellation is ruled out by the highest Q-degree B_t with nonzero multiplier; individual terms need not have disjoint coefficient supports.

Every nonzero alias has nonzero h-coordinate, and eliminating two aliases gives a q exponent of magnitude<=2JrD_h<R. Thus all aliases are collinear. A primitive direction has b>0, b<=D_h, |a|<=Jr and gcd(a,b)=1, without needing to be an actual numerical relation. Coarsening preserves already-zero groups. The a=0 case again uses distinct polynomial degrees and the selected nonzero evaluation. For a!=0 the substitution of H=x^-a is injective on coefficient polynomials over K(Z), so a smallest nonzero formal index t0 exists.

After division by B_t0, all later terms contain A(q^(j+t0)x^b). Its Jb roots are distinct: A has simple nonzero roots and b<=D_h<p (or characteristic0) ensures separability of x^b. For equal H-images, xi^a=1 and xi^b is the ratio of two original roots. That ratio lies in the prime-order beta group; 0<|a|<=Jr<R forces the same original root. Then xi^a=xi^b=1 and coprimality imply xi=1. Hence the H-images of all Jb roots are distinct. The coefficient polynomial of degree D_h<J cannot vanish at them all over the coefficient field Kbar(Z). This contradiction also covers t0=r: then the sole remaining coefficient is already zero as a rational identity. No characteristic, finite-clock or advised-coefficient exception was omitted.

The matrix consequence invokes the previous NONVACUOUS scalarization with nominal r=s, degrees s²delta_k,s²delta_h. Its degree/range costs and stronger characteristic bound are retained rather than hidden. It is an existence implication and not free access to recurrence coefficients or a clock order.

## Source and actual-family checks

The density source explicitly supplies m-1-2M^.997 simultaneous complete unit rows, after an O(M^5.992) inherited deletion against the same original qualified supply and earlier stated losses, at every current candidate and every L<=4m². Canonical L=2m²+2 lies in that range. This is restricted to the original balanced prime-order gamma family; it is not a density theorem for every input or the newly prepared beta.

Each literal offset's low residue c satisfies c j²+2Nj-N=0 modulo auxiliary prime m. This polynomial is nonzero since N is a unit modulo m and has at most two roots, so an equal literal offset occurs at most twice. Thus privately choosing all unit rows and deduplicating leaves Theta(m) targets. Complete unit row products imply every individual difference and every U-prefix is a unit modulo N. No acquisition of this private subset or preservation of forced collision coverage is claimed. The roots are in the same prime-order coset and the order/characteristic margins meet the generic theorem for fixed/polylogarithmic parameters eventually.

Old G15 already concerns the ORIGINAL cumulative product, coefficients in the actual baby clock, and a nonzero prefix. Its degree/order rigidity is not claimed new here. The extension is arbitrary clock/mixed-index dependence with root-fiber injection on the explicitly private zero-free restriction. It must not be applied to the saturated full rectangle; the report expressly avoids that inference.

## Main-report self-audit, not independent review

The mask orientation uses inverse targets z=Y^-1, so its factors at q^i are unit-scaled actual Y-q^i differences. Transition multipliers are distinguished from undefined numerical U_(k+1)/U_k after zeros. The short-arc argument excludes root-set scaling symmetries: a nontrivial cyclic translation orbit requires arc width at least R/2. Characteristic>J ensures the needed roots of unity are distinct. This gives primitive coefficient support. Alias-line coarsening and the residue-class argument for K(x^a) force primitive direction |a|=1; rational degree is then Jb, including the negative-power denominator case since A0 and A_J are nonzero. Exact minimum J is attained in the actual q clock. These are the author's final self-checks; their independent validation belongs to the other reviewers.

Both reports retain narrow representation scopes. They neither acquire a norm/witness nor prove an operation lower bound, hard scalar-value theorem, all-input prefix obstruction or Lean bit theorem. Higher-degree/sparse circuits, genuine multiple geometric clocks, selected-value methods and direct factor/witness extraction remain open. No correction requested.
