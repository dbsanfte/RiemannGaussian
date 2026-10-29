# Frobenius screen executable prototype

26 October 2026. Scratch only; no system/repository dependency mutation. Python 3.10.12 scratch venv with python-flint 0.9.0. This is a functional implementation of the supplied product formula, **not** a verified full factoring result or proof of its native arithmetic interpretation.

Run from this packet directory:

```sh
/tmp/semiprime-frobenius-screen-20261026/venv/bin/python frobenius_screen.py N k q
/tmp/semiprime-frobenius-screen-20261026/venv/bin/python -m unittest discover -s . -v
```

To recreate the environment elsewhere:

```sh
python3 -m venv /tmp/semiprime-frobenius-screen-20261026/venv
/tmp/semiprime-frobenius-screen-20261026/venv/bin/pip install python-flint==0.9.0
```

`frobenius_screen(N,k,q)` returns the requested gcd. `screen_details`/CLI additionally reports A,B,w,Z,block size, full blocks and tail, and explicitly sets `native_order_contract_verified=false`. Cheap checks enforce N>=2,k>=1,N<=k^6,gcd(q,N)=1. Semiprimality and both hidden local q-order bounds are **not** verified by this script. The companion frobenius-screen.md proves that the gcd is only 1 or the larger prime under the native contract, with two independent reviews; the implementation returns an actual gcd N unchanged on out-of-contract inputs and does not mislabel it as a factor.

## Executed kernel

Let b=ceil(sqrt B), H=floor(B/b), t=B−Hb. Acquire the actual coefficient list

    F_b(X)=product_(r=1..b)(w^r X−1)

by a balanced FLINT polynomial product tree. Acquire H evaluation points w^(hb),0<=h<H by repeated multiplication using the powered step w^b. A monic subproduct/remainder tree evaluates F_b at those points, then multiply its scalar outputs and the t<=b direct tail factors. The blocks cover exactly exponents 1,...,Hb; the tail covers Hb+1,...,B. For B=0 return the empty product1.

Every remainder divisor is a product of (X−point), hence monic even over a composite modulus, repeated points, or nonunit point differences. The script never interpolates, calls a finite-field-only fast multipoint method, inverts the leading coefficient of F_b, or divides by any w^j−1. FLINT's `%` is used only with these monic divisors. Official arbitrary-modulus/division interfaces: [python-flint fmpz_mod_poly](https://python-flint.readthedocs.io/en/latest/fmpz_mod_poly.html), [FLINT remainder documentation](https://flintlib.org/doc/fmpz_mod_poly.html).

## Verification and complexity scope

Six small deterministic test methods pass. They cover empty/single products, an actual zero factor with repeated block points, product zero from separate nonzero zero-divisor leaves (mod21 factors1,3,7), a proper nonunit product, incomplete tails, exact squares, nonunit w as an extra kernel check, and a direct repeated-point remainder-tree comparison. Two integration fixtures verify only the public formula and the unverified-contract flag; they do not claim native order coverage. No semiprime coverage/sample campaign or large benchmark was run.

The code has O(b+B/b) acquired scalar points/factors and logarithmic-depth product/remainder trees. Under a quasi-linear polynomial multiplication/remainder implementation over Z/NZ, the standard tree analysis gives softly O(sqrt B) ring work and softly O(sqrt B*log N) bit work, plus powering/gcd polylogarithmic factors. Retaining tree levels uses O(sqrt B*log B) coefficients. Since B=N//(16k²+1)²<=k²/256, this abstract arithmetic bound is softly O(k).

**This is not a formal complexity guarantee for the installed python-flint binary.** The script exercises the actual fast-polynomial backend and balanced algorithms, but does not prove FLINT's internal dispatch thresholds or multiplication/remainder complexity uniformly for every modulus/degree. Its small tests establish functional behavior of the covered paths, not asymptotic timing. The native factor-or-interface theorem is proved in the companion report; its hidden input contract is not checked by this script. Uniform full factorization remains open.
