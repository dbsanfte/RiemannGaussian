# Packed original-bank residue: execute first-order endpoint cancellation

26 October 2026. Paper-only native calculation. No repository edits, numerical tests, implementation or Lean. **The explicit O(K) endpoint calculation below is acquired, but its interior residues cancel. A second exact adjacent-denominator sum retains the packed scalar with coefficient one and remains unpaid.** No soft-K acquisition or general lower bound is claimed.

Input read: frozen `semiprime-six-domain-acquisition-20261026/README.md`, especially §§1–2 and its exact packed coefficient. This report uses the ORIGINAL beta-coupled weighted bank, not the raw torus-only alternative. Its correct-bin provenance, one row per colour, common squared tag and d<=D0=3^floor(e/2) are retained. The new scalar target is

    C=[delta^-1] sum_j w_j sum_(i=0)^(h-1)1/(A−T_j*rho^i),
    A=1+delta, w_j=K/2+[j²]_n, n=3^ceil(e/2).

The existing packed integer recovery and HH consumer cost soft K once C is supplied. They are not repeated as an acquisition result.

## 1. Fully paid endpoint preparation on the actual original bank

All T_j,w_j,rho,h are acquired; h<16H, and 1−rho is a certified unit. Put

    a_(j,i)=A−T_j*rho^i, 0<=i<=h.

Compute a_(j,0)(0)=1−T_j and a_(j,h)(0)=1−T_j*rho^h for ALL rows in soft K, since rho^h is shared. Test their norms. Proper gcds factor. A saturated endpoint norm forces the actual endpoint multiplicative equality in the nonsplit field. In the new mixed-relation consumer it is a nontrivial short relation: writing B_j=a_j+b_j N,

    T_j*rho^i=beta^u W^v,
    u=ell_j+H M0−Hi+B_j,
    v=ell_j+H M0−Hi−B_j.

Here (u,v)!=(0,0) because B_j!=0 for the bounded nonzero coefficient row. If u!=0, take the quadratic norm to get a licensed scalar beta annihilator or proper factor; if u=0, v!=0 and the new torus-annihilator transfer applies. Thus an actual nonunit endpoint terminates in soft K, once only. This is not an assertion that an additive finite-part zero has such a label.

On no-factor continuation BOTH endpoint constants are genuine units at every component. Hence all endpoint rational functions used below have legal fixed-precision expansions over B. No mixed-component zero constant is inverted. Row roots may repeat; no F′ or Vandermonde inverse is introduced.

## 2. Exact first-order Casoratian and its acquired endpoint sum

Suppress j. The regulated row obeys

    a_(i+1)=rho*a_i+(1−rho)*A.                    (1)

In particular the additive regulator PRESERVES this exact recurrence with its known source A. Direct subtraction gives

    1/a_i−rho/a_(i+1)
      =(1−rho)*A/(a_i*a_(i+1)).                 (2)

Multiplying by rho^i and summing telescopes. Define

    T_1(A,T)=sum_(i=0)^(h-1)rho^i/(a_i*a_(i+1)).

Then the exact cleared rational identity is

    T_1(A,T)=[1/a_0−rho^h/a_h]/[(1−rho)*A].      (3)

Every right-hand input is acquired in §1. Summing w_j times (3) therefore supplies an actual endpoint observable in soft K, including any fixed Laurent/Taylor coefficient. All its negative coefficients are zero on the continuing branch because its endpoint denominators are units.

This is a complete initialized endpoint algorithm, not an uncomputed recurrence descriptor. It does NOT give C. At an interior good-field hit I, the two terms i=I−1,I have residues

    rho^(I−1)/(1−rho^-1)=rho^I/(rho−1),
    rho^I/(1−rho)=−rho^I/(rho−1).

They cancel exactly. The h endpoint has already been guarded, and a hit at i=0 would already have terminated. Every original interior witness therefore disappears in the observable that (3) computes. Packed row weights do not prevent this cancellation: they are the same on those two terms.

Unlike the torus-Lucas additive deformation, this first-order regulated identity needs no finite-part anomaly to restore its recurrence: (1) holds for every delta. An unweighted target cannot be identified with (3) by carrying over the former Lucas anomaly formula.

## 3. The exact noncancelling correction has coefficient one

Define instead

    T_0(A,T)=sum_(i=0)^(h-1)1/(a_i*a_(i+1)),
    S(A,T)=sum_(i=0)^(h-1)1/a_i.

Sum (2) WITHOUT the rho^i weight. Its left side is

    (1−rho)*S+rho/a_0−rho/a_h.

Thus

    S=A*T_0−rho/(1−rho)*(1/a_0−1/a_h).           (4)

Every displayed endpoint is already acquired, but T_0 is not. Adjacent leaves cannot both vanish at any component because 1−rho is a unit, so T_0 has at most a simple Laurent pole. At a good hit its adjacent residues add to

    1/(1−rho^-1)+1/(1−rho)=1.

Therefore its simple pole has EXACTLY the original normalized weight, not an unknown nonzero amplitude. On the guarded branch (4) proves

    C=[delta^-1]sum_j w_j*T_0(A,T_j).            (5)

This is an alternative scalar sufficient statistic with two adjacent denominators and a paid endpoint subtraction. It has no Hasse-depth search and no product amplitude, but it has not been evaluated in soft K. Its precise missing coefficient is still the selected interior pole, rather than a decoder or an endpoint seed.

A useful sanity check is obtained by unweighting the telescope through summation by parts: the correction is the sum of the reciprocal terms, not a short ordinary polynomial moment. Dropping it is exactly dropping C. The identities are valid over the composite ring after clearing and then extracting the justified componentwise Laurent coefficients.

## 4. Execute an acquired family of clock weights

For any supplied polynomial F, define

    T_F=sum_i F(rho^i)/(a_i*a_(i+1)).

At a native hit x=rho^I=T_j^-1, its residue is exactly

    [rho*F(x/rho)−F(x)]/(rho−1).                 (6)

This is a direct two-term calculation, not an imported characteristic-zero q-summability criterion. For the whole ACQUIRED affine family F(X)=alpha+beta X, (6) is simply alpha. Correspondingly

    T_F=alpha*T_0+beta*T_1.

The beta part is the paid endpoint (3) and has zero signal; retaining coefficient-one packed signal requires the alpha part, the unacquired T_0. No linear combination of these paid endpoint pieces supplies (5). This is a failure of this explicit affine-weight attempt only, not of arbitrary rational weights, nonlinear recurrences or selected-residue algorithms.

For a monomial X^m, (6) is x^m*(rho^(1−m)−1)/(rho−1). Indices m with 0<|m-1|<=16H have a known unit coefficient, and a row prefactor T_j^m can normalize it to one at the hit. This gives further legitimate output specifications, but materializing their finite sums is an additional operation. A formula for their residue is not their acquisition. The special m=1 endpoint mode is exactly the one whose residue vanishes.

## 5. Scalar result, paid fallback and further use

The actual endpoint experiment computes (3), its weighted row sum and fixed-precision expansions in soft K with all inverse constants certified. It yields a factor whenever one of its tested genuine endpoint leaves is nonunit. Otherwise it has exactly zero interior pole despite the correct bin's guaranteed original hit.

The noncancelling correction (4)–(5) is initialized as an explicit finite adjacent-resolvent target and has the SAME packed scalar C, without a new amplitude normalization. Its existing completion is the old shared row-value/flag algorithm at soft(K+sqrt(Kh))=soft K^(5/4): flags identify the actual count and squared-tag contributions, which are summed with the public packed weights. No Lucas regulator or torus-only singleton assumption is invoked. A first-jet route is optional, not needed for those normalized flags.

A productive next acquisition theorem could compute the selected residues (5), perhaps by an exact finite rational-sum or continuant correction algorithm that uses these already paid endpoint pieces. It must retain the alpha/constant clock-weight component singled out by (6); replacing it by the cheaply telescoping beta/linear component loses every native witness. This is a sharply executed missing operation, not a claim that all correction algorithms need full row products or a repetition of the old fixed-degree q-Gosper obstruction.

Literature context only: the [Chen–Singer rational-residue framework](https://arxiv.org/abs/1203.4200) studies characteristic-zero q-summability under its own hypotheses. No such theorem is used here to infer a finite-ring algorithm or impossibility statement. Equations (1)–(6) are elementary finite identities at the actual supplied native parameters.
