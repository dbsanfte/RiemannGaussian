# Actual native-group height and packet-fold width — completed

Two NEW modules, with old modules/packets frozen.

## Actual physical group representation

`NativeGroupBitsHeight.run_height` reconstructs the existing actual run_spec proof and retains `productList_correct.hp.2.2`, which the old value/validity conclusion discarded. It assumes exactly the original source validity/common representation, positive source denominator, original node bound, original parameter dyadic bounds, and original ±1 entry bound. It does not assume intermediate/output ArrayBound or Fits.

With s=sum arities, the actual decoded group output has precision J and one common denominator

`DG = (d^s)^F`,

with numerator bound `BG = N^(2F)`, where

`N = (J+1)*(d^s+(localBase J d (n*hornerBound J B T (R+1))+d+1)^s+1)`.

The product follows the actual original factor order. Absent factors use the actual truncated one array and are extended to the same denominator; original factor arity is bounded by s only in the polynomial word-width argument. There is no total-incidence Boolean truth-table sweep.

`denominator_dyadic` and `numerator_dyadic` prove both DG and BG at most `2^e`, where

`e = b*s*F + NativeGroupBits.factorExponent b R s*(2F)+1`.

The numerator proof uses the already proved original `factor_base_dyadic`. This e is a fixed polynomial in b,R,F,s. Common denominator positivity is explicit. These huge integer magnitudes are proof bounds, not runtime advice or a request to materialize them when choosing a width.

## Runtime width frontend

`WordPacketWidth.packetWidth b R n F s J r headCap Y Cq` uses only original dimensions and actual acquired traversal counts. Put

`k = J+headCap+e+4`,

`W = groupWidth b R F s+n+e*(r+1)+k*(2r+4)+Y+Cq+10`.

The module proves: groupWidth≤W and W>0; for `Np=(J+1)*(DG+headCap*BG+1)`, DG/headCapBG/J≤Np and Np≤2^k; strict product guard k*(2r+2)<W; strict caps for DG, headCapBG, DG^r, Y*Np^(2r), and Cq*Y*Np^(2r). Summary and support caps are separate. They need only the DG/BG dyadic bounds already derived from actual group input guards.

The intended headCap is `1+sum_g 2^(h g)`, Y the actual summaryCount, Cq the actual weighted support count. These counts may enter W linearly or polynomially; the formula never uses `2^Y`, `2^Cq` or a new `2^n` width. Powers of two appear only in proof inequalities bounding integers. Sums preserve one common denominator; multiplicative products use r factors. Nothing licenses doubling denominator exponents at every summary/support addition.

This supplies numeric guards for actual primitive word sum/product folds. Their execution, callback specialization and complete counter/controller composition are separate modules. It does not claim the complete original-input primitive-bit clock or transfer a public subpower theorem to a changed controller.

## Verification

Both final canonical strict compiles PASS; ordinary-root fifteen-linter and every-generated-declaration transitive standard-three-axiom audits PASS: 56 declarations, 49 theorem constants. Both isolated objects are byte-identical to canonical. Source/object pins are in group-packet-height-verification.json; build/audit/isolated logs and exact audit scripts are in this scratch directory. No finite factoring campaign or new timing evidence.
