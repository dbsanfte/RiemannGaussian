# Independent review: negative same-squareclass pairs

22 October 2026. Verdict: PASS with the explicit unit and squarefree-semiprime hypotheses below. No tests, implementation, or repository changes.

Let N=P Q for distinct odd primes; let m>=17 be an integer, M=m^3, and 0<a_i,a_j<m. Suppose D,s_i,s_j are positive integers and

    v_i^2+M D s_i^2=4a_i N,
    v_j^2+M D s_j^2=4a_j N,

with m,D,s_i,s_j,v_i,v_j units modulo N. These unit hypotheses hold after the existing norm-family gcd screen. Define the two integers

    A_plus=v_i*s_j+v_j*s_i,
    A_minus=v_i*s_j-v_j*s_i.

## Exact integer size bound

Set T=M D. For either sign the following is an exact integer identity:

    16a_i a_j N^2-T*(v_i*s_j +/- v_j*s_i)^2
       =(v_i*v_j -/+ T*s_i*s_j)^2 >=0.

This proves, without numerical square roots,

    T*A_plus^2 <=16a_i a_j N^2,
    T*A_minus^2<=16a_i a_j N^2.

Since D>=1 and a_i a_j<m^2,

    A_plus^2,A_minus^2 <(16/m)*N^2<N^2

for m>=17. Thus each integer has absolute value strictly less than N. No balance condition N~m^6 is used. In fact the same displayed strict estimate suffices at m=16 as well, but the requested m>=17 statement is valid and no constant improvement is needed.

## Nonproportionality equivalence

Eliminate the common T from the two exact norm identities to obtain

    a_i*v_j^2-a_j*v_i^2
       =(T/(4N))*(v_j^2*s_i^2-v_i^2*s_j^2).

This rational equality is exact; multiplication by 4N gives an integer identity if preferred. As T and N are positive, its left side is zero exactly when

    (v_i*s_j)^2=(v_j*s_i)^2,

which over the integers is equivalent to v_i*s_j=+v_j*s_i OR v_i*s_j=-v_j*s_i. Thus the report's condition a_i v_j^2 != a_j v_i^2 is exactly the condition that BOTH A_plus and A_minus are nonzero. It uses actual integers, not equality modulo an unknown prime.

## Proper factors are then forced

The exact difference of the norm relations gives

    A_plus*A_minus
      =v_i^2*s_j^2-v_j^2*s_i^2
      =4N*(a_i*s_j^2-a_j*s_i^2).

Consequently N divides the product. Under nonproportionality both A values are nonzero and have absolute value less than N, so neither is divisible by N. Each hidden prime divides at least one of them. No hidden prime can divide both, since their sum and difference are 2v_i s_j and 2v_j s_i and all those factors are units modulo N. Therefore the two distinct hidden primes divide opposite A values. Both gcd(A_plus,N) and gcd(A_minus,N) are proper, and they are complementary factors P,Q in some order. A hidden-sign-discrepancy premise is unnecessary: the archimedean size bound forces it.

If the integer proportionality holds instead, one A value is zero and the other is plus or minus 2v_i s_j, a unit modulo N. The corresponding gcds are N and 1. This is precisely the globally trivial pair, not an unresolved saturated factor case.

## Consequence and remaining condition

For m>=17, the all-pairs negative-squareclass consumer needs only acquire one class containing two rationally nonproportional normalized roots. Its existing representative screen can test this exactly through a_i v_j^2-a_j v_i^2, and then the two scalar gcds are guaranteed to factor. This removes the previous independent local-sign premise for negative pairs. It does not prove that the canonical family necessarily contains such a class: the remaining universal question is existence and paid acquisition of a negative repeated squareclass with this nonproportionality. All-pairs coprime-base grouping already pays the acquisition if such a pair exists.
