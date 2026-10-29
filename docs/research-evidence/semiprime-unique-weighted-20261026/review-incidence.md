# Independent root-colour incidence compiler review

26 October 2026. Paper derivation, no repository edits or numerical tests. **PASS** for the compiler stated by root/quantum on the completed ellipse. The compiled integer arrays are paid data; selecting their value at the unknown factor colour remains unpaid. This is not a general acquisition obstruction.

## 1. Exact root equation and derivative margin

For a nonaxis completed row write f(X)=aX²+ell_j X+bN, g=gcd(a,K)=gcd(b,K), A=a/g, m=K/g. Its own colour obeys H|f(j) and K|f'(j). Set c=f'(j)/K, an actual integer. The original valuation argument shows every unit root r modulo K of H|f(r) lies in r=j+m*t, t modulo g. Conversely direct expansion gives

 f(j+m*t)=f(j)+(H/g)*(c*t+A*t²),
 f'(j+m*t)=K*(c+2*A*t).

Therefore the exact root condition is

 g | t*(A*t+c).                                    (1)

The second equality shows EVERY root is still stationary modulo K. If an integer R has residue r modulo K, then f(R)=f(r)+(R-r)f'(r)+a(R-r)² is divisible by H. Thus no R modulo H is needed. In the correct bin the proven norm/clock bound converts this divisibility to the actual physical q-hit, with its index inside the clock. Conversely any actual hit has this divisibility by exact-integer provenance. Both directions use the existing coupled order margin; (1) is not a statement about raw-torus aliases.

## 2. Odd/even content, root count and explicit enumeration

Let 3^v be the odd part of g. A is a 3-unit. Modulo 3^v, complete the square:

 (2*A*t+c)²=c² mod 3^v.

There are O(sqrt(3^v)) roots. More explicitly, put s=v3(c), capped at v. If 2s<v, the two families are t=0 or -c/A modulo 3^(v-s), each with 3^s lifts. If 2s>=v, t=0 modulo 3^ceil(v/2), with 3^floor(v/2) lifts. The case v=0 gives just one residue. These are direct public modular divisions by a unit and valuation arithmetic, not an unknown-field square-root oracle. They enumerate roots with work proportional to the stated O(sqrt g) bound up to logarithms.

If g is odd, m is even and every resulting r remains odd. If g is even, m is odd and r=j+m*t is odd exactly when t is even; choose that CRT lift modulo 2. The modulus-2 part of (1) then holds automatically. Since v<=floor(e/2)<e, m is divisible by 3, so r remains nonzero modulo 3. Thus all narrow parity cases are paid constant filters, including g=1 and g=2. Full g=K cannot occur nonaxis because |ab|<=K/sqrt3.

The axes are NOT fed through this nonaxis formula. Retained primitive horizontal and vertical axes have their explicit root sets {j} modulo K, by the original axis proof. Larger axis multiples were not included in the ellipse catalogue.

## 3. Linear total incidence bound

At content g the ellipse has O(K/g) coloured rows, by the exact pair bound 4AB/g² and at most 2g unit-colour lifts. Each row has O(sqrt g) root colours by §2. Hence total explicit incidences are bounded by

 O(K sum_(g|K)g^(-1/2))=O(K),

since g ranges over divisors of 2*3^e and the geometric sum is bounded by (1+1/sqrt2)/(1-1/sqrt3). The separately filtered axes contribute only O(K). All arithmetic has O(log N)-bit inputs and polylogarithmic work per incidence; integer counts and canonical marks remain small. This is an actual sparse compiler, not a K-by-K table scan or existential counting argument.

## 4. Fixed-pair phase classes are exactly the root sets

For unit r in a row root set, H|a r²+ell_j r+bN implies

 ell_j=[-a*r-b*N*r^-1]_H=ell_r,

with the SAME centered canonical representative. Conversely equal canonical phases imply the root equation. By §1 the new r is compatible with the stationary lattice, so it is among the colours actually completed for this coefficient pair. Thus within fixed (a,b), the root sets are exactly the fibres of the canonical-phase map; their classes are either equal or disjoint. They contain the row's own j.

This claim is restricted to a fixed coefficient pair. No assertion that classes for DIFFERENT pairs are nested, disjoint or nonnested is required or proved here.

## 5. What is acquired and what remains

Initialize m_r=0 and c_r=0 for every public unit r modulo K. Each compiled row-root incidence adds one to m_r and its canonical u_j to c_r, preserving multiplicities. Since n divides K/g and r=j mod K/g on an incidence, u_j=[r²]_n. Hence

 c_r=m_r*[r²]_n.

All m_r,c_r are acquired in soft K; at the correct nonsplit factor the completed count and M1 equal m_[R]_K,c_[R]_K. This converts the native algebraic hit statement into an explicit public finite table lookup with UNKNOWN argument. It does not acquire the argument or the corresponding native scalar.

Indeed the ellipse contains an original Gauss witness for EVERY unit public colour r, so m_r>=1 for every such r: the compiled SUPPORT alone does not thin the unit palette. The nonconstant counts/phase classes may still admit another arithmetic acquisition method; this review supplies no bound against that possibility. A standard projection from the supplied native pi/barpi data to the table index is not furnished by incidence enumeration.

## 6. Final source transcription and conductor-collinearity check

Read the completed-source.md §7 addition in full. The displayed compiler, root bound, fixed-pair classes and array definitions agree with §§1–5 above.

The new overlap geometry is also CORRECT. If two admitted coefficient vectors v,w share a hypothetical colour r, they belong to Lambda_r={a*r²=bN mod K}. If a divisor d>1 of K divides both coordinates of both vectors, then v/d,w/d belong to the corresponding index-K/d lattice. Its index is exact because r,N are units. Consequently det(v,w) is a multiple of d*K. The physical weighted area inequality gives

 |det(v,w)|*B0²*N <= ||v_weighted||*||w_weighted||
                   <=(2/sqrt3)*K*B0²*N.

Thus |det(v,w)|<2K<=dK, forcing determinant zero. This proves parallelism, without a numerical approximation to the ellipse constant.

For g=1 the rootset is immediately {j}. For g=2, r-j is a multiple of K/2=3^e and also even, since both colours are odd; hence r=j modulo K. Therefore any genuinely ambiguous nonaxis rootset has both coefficients divisible by 3. If two such ambiguous rootsets overlap, the d=3 argument makes their vectors parallel. Ambiguous supports from different rational directions are consequently disjoint, and all ambiguity at a colour lies along one direction. Full-colour singleton rows and the explicitly handled axes can coexist without contradicting this conclusion.

This is a scoped positive geometry theorem. It does not assert a general nesting law for phase classes along one direction, a public normalization constant across all pairs, identification of the factor colour, or faster scalar acquisition. Final disposition: PASS; no further tests or corrections required.
