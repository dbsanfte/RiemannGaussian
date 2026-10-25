# Native mixed-radix root-coset moment tree

24 October 2026. Exact sum identity and whole-family accounting; no faster full query claimed. Scratch only.

For each nonaxis pair/root coset, write lambda=lambda0+delta t, 0<=t<g, delta=H/g. All these cosets remain complete under public deletion. With u=beta^delta and Y0 the actual supplied base point (including any fixed q-centering or inversion consistently), y_t=Y0 u^t. If inversion was used, replace u by u^-1.

Choose a mixed radix g=prod_r d_r, d_r in {2,3}, positions L_r=prod_(s<r)d_s. An actual root-digit factor mask has w(t)=prod_r w_(r,t_r). Then the exact weighted moment is

    sum_(t<g) w(t)y_t^n
       =Y0^n prod_r [sum_(d=0)^(d_r-1) w_(r,d) u^(n L_r d)].       (1)

No root-of-unity assumption, inverse, nonzero mask value, or distinctness is used. The identity expands the mixed-radix Cartesian product. A native catalogue tree can put the signed divisor pair/root-branch label above these digits. For one mask that selects/factorizes its root digits, (1) is an exact short descriptor for all moments. The four exceptional axis rows may be subtracted explicitly with their actual weights. Swap/sign partners remain labeled leaves, so collision retention is unchanged.

Whole-family accounting is particularly simple for k=2*3^e. The binary component of every root coset has length 2, since lambda²=4abN modulo 4 has exactly lambda=0,2. For nonzero ab<k, the ternary component is unsaturated, and any solvable root has v_3(ab)=2v. Thus g=2*3^v, and 3^(2v) divides ab. At each g the number C_g of pair/root cosets is soft O(k/g²): enumerate ab=3^(2v)m<k, sum the divisor counts of these integers, and retain the constant number of unit-root branches. Smooth valuation divisor factors are only logarithmic. Therefore

    sum_g C_g=soft O(k),
    sum_g C_g g=soft O(k),
    sum_(g>=G) C_g g=soft O(k/G).

These counts concern nonaxis cosets; the four axis cosets each have g=k and contribute Theta(k) rows separately. The rare long nonaxis root-digit trees are inexpensive in aggregate. For example the nonaxis g>=G subfamily alone admits the existing complete query in soft(k/G+sqrt(kh/G)), apart from the soft-k acquisition already paid. But the low-ramification population, especially constant g, still contains soft-order-k coset labels; this tail estimate does not improve the complete query exponent.

Evaluating (1) at R explicit consecutive n values by literal descriptor evaluation costs soft(R sum_g C_g), and expanding to a single rational moment generating function costs soft(J+R), as for arbitrary supplied weighted points. The remaining operation is the correlated q-Newton contraction

    sum_(n<=h) c_n sum_C Y_C^n
        prod_r [sum_d w_(C,r,d)u_C^(n L_r d)],

or the analogous reshaped coefficient-mask family. Factoring the root digits does not factor the outer signed divisor/root-branch sum. No cheap contraction of that sum, no bound on the full tensor mask union, and no new whole-query or partial whole-query exponent improvement were obtained. This states the exact unpaid operation rather than assuming a low-rank digit oracle.
