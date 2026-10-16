# Independent proof and integration review B

Verdict: PASS; no correction requested. Read-only mathematical/source/narrative review, not a native build or new Lean certification. All eight references in the two source-pin files match exact prerequisite bytes and hashes.

Final reviewed targets:
- `arbitrary-base-ratio.md`: 8347 bytes; SHA256 `4241ae43992bfba775925e3e0c8fb368e4682324d2d7411a7d658b3d1a204eaf`.
- `arbitrary-base-recurrence.md`: 10847 bytes; SHA256 `586a884f1a679952919af7c97a24456a574bb94f32669a94aa43f6ab97e1523a`.
- `README.md`: 3534 bytes; SHA256 `b68d7d2217c3bbdfef7bd7994b3fd010757770b2b94db4183f1ff7f57cc4f450`.
- `journal-entry.md`: 4053 bytes; SHA256 `54d92d35cbd2972cc6bbbd483c263fc161c683b20a41362ad7fde6d5ad996994`.
- `source-pins.json`: 1063 bytes; SHA256 `89128b52eae2ff773c146a6576dccd62a0bd1f7f0964c5140eb4679874e9b51a`.
- `recurrence-source-pins.json`: 1012 bytes; SHA256 `485a0219177b79cb7f10a3c525800dcf3c7e055e08996c903b38b9104c547a55`.

First-order proof: the cleared frequency identity has the correct scalar q and Q=q^L. Vandermonde grouping is valid with repeated h-powers. Active support retains vertices with either combined coefficient nonzero, even if their net balance is zero. V(1)!=0 makes it nonempty. Because its size is below ord(q), an occupied vertex with missing predecessor exists. Its balance forces both coefficient families present. Its successor cannot be absent because 1-qQ!=0. Comparing ORIGINAL polynomial indices within a family yields bounded a,b with g=h^a,q=h^b. Torsion, composite order and combined coefficients cause no exception. The paid screen then excludes the relation fieldwise for D<=m. The statement about original literal-base inputs correctly requires a separately checked nonalias condition.

Higher-order proof: after clearing the finite q-binomial ratios, the frequencies are g^(-t)q^u h^v in the stated box. Actual aliases with h exponent zero violate the certified g/q relation box; eliminating h from two aliases produces coefficients bounded by2rD. Thus all nonzero aliases are collinear. Formal two-variable coarsening maps every actual class to one monomial, and any merging of distinct classes preserves their zero sums. No primitive saturation or group-algebra division is assumed. The original scalar g,q coefficients are correctly kept distinct from formal running clocks.

The highest-shift pole is genuine under ord(q)>L+r. With nonzero a, the leading coefficient remains a nonzero Laurent polynomial in the independent x variable at the chosen y-root. Lower shifts are regular. Characteristic dividing the substitution exponent can increase pole multiplicity but cannot remove it. With a=0, distinct x powers separate shifts; b!=0 preserves nonzero polynomials and b=0 uses leading regularity at1. No-alias expansion also forces a contradiction.

Nonvacuity and initial singularities are handled correctly. Drop only coefficient FUNCTIONS identically zero on the h-orbit, using the largest remaining effective shift. Do not enlarge the original nominal equation range. A first nonzero value occurs within D indices, whether the orbit is long or short. The shift preserves degrees and leaves at least the claimed nominal sample count. Effective shift0 is contradicted directly by nonzero A_j. All fixed/polylog positive orders and degrees satisfy the displayed bounds eventually; not every nearlinear recurrence is excluded.

The latest all-semiprime setup supplies the explicit strong-order interface on its surviving branch; the inherited square screen arithmetic applies unchanged. Together they either factor or certify BOTH hidden-field relation boxes softly linearly. The conclusions involve arbitrary field-specific advice without enumeration of h, not a transfer of old collision/controller coverage or an acquired long query.

README and journal accurately summarize these proofs, their explicit parameter ranges, and the first report's narrower higher-order limitation. They credit the old coefficient identity, alias/coarsening/collinearity/pole methods, Vandermonde algebra and setup/screen. The new claims are their arbitrary-clock applications and finite-start accounting, not first use of these techniques or an absolute priority claim. The unchanged m^(3/2) query clock and missing soft-m acquisition/Lean bit objective are explicit; no arbitrary circuit or operation lower bound follows.

Planned-layout links check: README reports/arbitrary-base-ratio.md and reports/arbitrary-base-recurrence.md match the two planned reports, reviews/ is the stated planned review directory, and the journal link points to the planned packet README. No integration blocker found.
