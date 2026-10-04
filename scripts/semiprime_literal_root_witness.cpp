// Copyright (c) 2026 David Sanftenberg. Apache-2.0.
// Resolve reference-field collisions back to their original public packets.
// This search uses private p,q. A Lean control checks the resulting rows.
// It scans the entire literal family without writing a root or pair table.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>

using I = __int128_t;
using U = __uint128_t;
using W = std::uint64_t;

static W residue(I x, W modulus) {
    I r = x % I(modulus);
    return W(r < 0 ? r + modulus : r);
}
static I floor_div(I x, I positive) {
    assert(positive > 0);
    return x / positive - (x % positive < 0);
}
static W inverse(W x, W modulus) {
    I a=x,b=modulus,u=1,v=0;
    while (b) {
        I k=a/b,r=a-k*b,t=u-k*v;
        a=b; b=r; u=v; v=t;
    }
    assert(a==1);
    return residue(u,modulus);
}
static std::vector<W> field_inverses(W prime,W m) {
    std::vector<W> result(m+1);
    result[1]=1;
    for (W k=2;k<=m;++k)
        result[k]=prime-W(U(prime/k)*result[prime%k]%prime);
    return result;
}
static std::string decimal(I value) {
    if (!value) return "0";
    bool negative=value<0;
    U magnitude=negative ? U(-value) : U(value);
    std::string result;
    while (magnitude) {
        result.push_back(char('0'+magnitude%10)); magnitude/=10;
    }
    if (negative) result.push_back('-');
    std::reverse(result.begin(),result.end());
    return result;
}

int main(int argc,char** argv) {
    if (argc<9 || (argc-7)%2) return 2;
    W m=std::stoull(argv[1]),nmod=std::stoull(argv[2]);
    W small=std::stoull(argv[3]),large=std::stoull(argv[4]);
    W p=std::stoull(argv[5]),q=std::stoull(argv[6]),d=m*m;
    assert(1<m && m<(W(1)<<23) && m<p && m<q && p!=q);
    assert(2<p && 2<q && p<(W(1)<<63) && q<(W(1)<<63));
    assert(nmod<d && nmod%m!=0);
    std::vector<std::array<W,2>> queries;
    for (int i=7;i<argc;i+=2) {
        W fp=std::stoull(argv[i]),qc=std::stoull(argv[i+1]);
        assert(fp<=p/2 && qc<q);
        queries.push_back({fp,qc});
    }
    std::vector<W> matches(queries.size());
    auto emit=[&](W ep,W eq,W j,I a,W t,unsigned side,I L,bool known) {
        W np=ep ? p-ep : 0,nq=eq ? q-eq : 0;
        W fp=std::min(ep,np),qc=ep<np ? eq : ep>np ? nq : std::min(eq,nq);
        int sign=ep<np || (ep==np && eq<=nq) ? 1 : -1;
        for (std::size_t k=0;k<queries.size();++k) if (queries[k]==std::array<W,2>{fp,qc}) {
            ++matches[k];
            std::cout << "{\"query\":" << k << ",\"kind\":\"" << (known ? "known" : "shifted")
                << "\",\"residue\":" << j << ",\"numerator\":" << decimal(a)
                << ",\"denominator\":" << t << ",\"larger_center\":" << (side ? "true" : "false")
                << ",\"offset\":" << decimal(L) << ",\"sign\":" << sign
                << ",\"raw_p\":" << ep << ",\"raw_q\":" << eq << "}\n";
        }
    };
    auto ip=field_inverses(p,m),iq=field_inverses(q,m);
    W originals=0,known=0;
    for (W j=0;j<m;++j) {
        emit(residue(-I(j),p),residue(-I(j),q),j,0,0,0,0,true); ++known;
        if (j==0 || std::gcd(j,m)!=1) continue;
        W invj=inverse(j,d),im=invj%m;
        W r0=m,r1=W(U(nmod%m)*im%m*im%m),x=0,y=1;
        bool negative=false;
        auto emit_pair=[&](I a,W t) {
            assert(a!=0 && -I(m)<a && a<I(m) && 0<t && t<=m);
            W r=residue(-a*j-I(nmod)*t*invj,d),aa=W(a<0 ? -a : a);
            W ap=ip[aa],aq=iq[aa];
            if (a<0) { ap=p-ap; aq=q-aq; }
            for (unsigned side=0;side<2;++side) {
                I S=a*(side ? large : small)+I(t)*(side ? small : large);
                I L=I(r)-floor_div(S+2*I(r)+d,2*I(d))*d;
                W ep=residue(I(W(U(residue(-L,p))*ap%p))-j,p);
                W eq=residue(I(W(U(residue(-L,q))*aq%q))-j,q);
                emit(ep,eq,j,a,t,side,L,false); ++originals;
            }
        };
        while (r1) {
            emit_pair(negative ? -I(r1) : I(r1),y);
            W kmax=r0/r1;
            for (W k=1;k<kmax;++k) {
                I a=I(r0)-I(k)*r1;
                emit_pair(negative ? a : -a,x+k*y);
            }
            W rem=r0%r1,new_y=x+kmax*y;
            r0=r1; r1=rem; x=y; y=new_y; negative=!negative;
        }
    }
    std::cout << "{\"original_packets\":" << originals << ",\"known_coordinates\":" << known
        << ",\"matches\":[";
    for (std::size_t k=0;k<matches.size();++k) std::cout << (k ? "," : "") << matches[k];
    std::cout << "]}\n";
}
