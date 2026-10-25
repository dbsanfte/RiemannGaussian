# An initialized supplied-advice batch, and the native residue test

24 October 2026. Outcome: a concrete shared-baby extension of a fresh primary algorithm is available for SUPPLIED residue advice, but the current complete scalar catalogue does not acquire that advice. No faster promised-root locator or factoring exponent is claimed.

## Primary algorithm actually inspected

Sean Ward and Maestro, iGent AI, `factorlab`, release 2026.09, exact commit `6bf5285492fe3ab96b1042e165f215b647f46620`:
https://github.com/iGentAI/factorlab/blob/6bf5285492fe3ab96b1042e165f215b647f46620/factorlab/experiments/harvey_residue.py

Its primary source code, including the module-level derivation, takes a balanced semiprime, a large-order seed, and an ACTUAL supplied residue p0=p mod M. It restricts the ordinary positive Lehman cell (a,b), ab<=R, using

    u=aQ+bP,
    omega_ab(p0)=a*N*p0^(-1)+b*p0 mod M,
    u=c_ab+j0+M*t,
    c_ab=ceil(2sqrt(abN)), j0=[omega_ab(p0)-c_ab]_M.

The windows have length ceil(sqrt(N)/(4R sqrt(ab))). Their coverage is the ordinary Lehman/Harvey coverage in the source's stated balanced regime. The implementation counts babies, giants and cells; its claimed single-residue schedule is N^(1/5+o(1))*M^(-2/5). I did not execute its experiments, infer an asymptotic theorem from its data, or acquire its separately distributed report PDF.

## Explicit multiple-advice extension

Suppose instead an explicit set S of t unit residues modulo M is supplied and is promised to contain the smaller factor's residue. Retain the balanced-regime premise above. For each cell use the distinct offsets j0 arising from S. Build ONE baby table (alpha^M)^i, 0<=i<m, and all corresponding giants

    alpha^(aN+b-c_ab-j0) * (alpha^M)^(-m*v).

Monic product-tree evaluation detects their collisions over Z/N without division by a collision value. There are soft(R) cells, at most t offsets per cell, and

    sum_(ab<=R) window_ab = soft(sqrt(N)/sqrt(R)).

Thus the actual arrays, arguments and products cost

    soft(tR + m + t*sqrt(N)/(M*m*sqrt(R)) + t).

This charges ceil(window/M) and ceil(tested/m) via the tR term, so short or empty windows are not declared free. Balancing m=tR and

    R approximately N^(1/5)*(M*t)^(-2/5)

gives soft(N^(1/5)*t^(3/5)*M^(-2/5)+t), when these parameters are at least one and lie in the stated coverage range. Otherwise the displayed unoptimized expression, with integer capped parameters, is the contract. This extension is an elementary derivation from the actual arrays, not a theorem attributed to the repository.

For M dividing H=k^2 the current scalar seed beta already supplies the needed local baby separation: ord_R(beta^M)>=ord_R(beta^H)>16H. Apply this only when the chosen m<16H. Powers have O(log N)-bit exponents in the indicated polynomial ranges. No unknown-prime primitive element or arithmetic root oracle is needed.

Recovery should use our licensed scalar consumer rather than importing the source code's special-case treatment of exact matches: check public integer K=aN+b-u, exclude K=0 candidates, and localize nonunit evaluations to actual leaves. Proper gcds factor. A saturated leaf has beta^K=1 globally, with nonzero O(log N)-bit K, so the pinned short-annihilator extractor applies. The covering leaf cannot be excluded on this branch because K=(P-1)(aQ-b), and aQ>b whenever the chosen R<Q. These are explicit guard conditions for this adaptation, not claims about unrestricted implementation parameters. The extractor is the existing `unbalanced-extractor.md`, SHA256 `a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be`.

## Actual native initialization test

At N=Theta(k^6), the attractive formal substitution M=H=k^2 and t=soft(k) would make the batch charge soft(k). The supplied catalogue does NOT provide such an H-residue set.

Indeed a native phase gives

    aP^2+lambda*P+bN=0 mod H,
    lambda^2-4abN=0 mod H.

Even on the favorable odd-adic unit-a branch, this is a double-root equation. For H=k^2 it generally fixes P only modulo k, leaving k lifts modulo H; the prime-2 and nonunit-content cases need their own root counts and do not justify a better uniform list. Hence J=soft(k) row labels can describe soft(J*k) explicit H-residues rather than soft(k). No selection of the correct row has been acquired. This observation is about this attempted advice construction, not a lower bound on all uses of the labels.

The stationary cancellation DOES make the matched weighted sum constant modulo H along its matched P-mod-k class. That is precisely the existing scalar row construction and its h=O(k^(3/2)) window, not a new partial-information acquisition.

Using all residues at a smaller modulus also does not meet the promised short-list input: t approximately M gives the displayed bound N^(1/5)*M^(1/5), so this literal batch is no improvement over ignoring that advice. These scheduled budgets do not exclude early successful factoring.

## Other inspected portions and source pins

`cover_search.py` explicitly calls its offset search heuristic and returns only finite upper-cover witnesses; it does not provide a guaranteed small cover for our correlated b-bands. `farey_cover.py` starts with an actual short interval containing the smaller factor; its exposed position/coverage execution is floating-point. Neither acquires that interval or an exact native advice set. No model floor from either source is imported as a factoring lower bound.

Cached primary files, SHA256:

- `sources/harvey_residue.py`: `1c2a5c13838ceea5f54517d963a2b37305d904000d601fbc1b615596374a7204`.
- `sources/cover_search.py`: `1324dd910db73bc7a9db8f62167f0caea99587c78ab9a5bca4a0fd7499fed1ba`.
- `sources/farey_cover.py`: `1a44eefa5d114ef464f9ace0557a7711e37f4c5445d8761b43436bb9047c66bd`.
- `sources/factorlab-README.md`: `f1807fdbe00518e6ac8cec8273ce23a11c06c1596a4a8c8a9ddf90f5022dd28b`.

No shared or frozen source was changed. The known-zero terminal contract and the current complete soft(k^(5/4)) localization remain unchanged.
