// Copyright (c) 2026 David Sanftenberg. Apache-2.0.
// Exact centered scalar carrier. Private fields label signed CRT orbits.
// This is not a public factorizer, bit theorem or Lean machine refinement.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using I=__int128_t;
using U=__uint128_t;
using W=std::uint64_t;
static W residue(I x,W modulus) {
    I r=x%I(modulus);
    return W(r<0 ? r+modulus : r);
}
static I floor_div(I x,I positive) {
    assert(positive>0);
    return x/positive-(x%positive<0);
}
static W inverse(W x,W modulus) {
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
    for (W k=2;k<=m;++k) result[k]=prime-W(U(prime/k)*result[prime%k]%prime);
    return result;
}
struct Writer {
    W p,q,count=0;
    std::ofstream sink;
    std::vector<std::array<W,3>> buffer;
    Writer(W pp,W qq,const std::string& path):p(pp),q(qq),sink(path,std::ios::binary) {
        if (!sink) throw std::runtime_error("cannot open scratch table");
        buffer.reserve(65536);
    }
    void emit(W ep,W eq) {
        W np=ep ? p-ep : 0,nq=eq ? q-eq : 0;
        W fp=std::min(ep,np),fq=std::min(eq,nq);
        W qc=ep<np ? eq : ep>np ? nq : fq;
        buffer.push_back({fp,qc,fq}); ++count;
        if (buffer.size()==65536) flush();
    }
    void flush() {
        sink.write(reinterpret_cast<const char*>(buffer.data()),
            std::streamsize(buffer.size()*sizeof(buffer[0])));
        if (!sink) throw std::runtime_error("scratch write failed");
        buffer.clear();
    }
};

int main(int argc,char** argv) {
    if (argc!=9) return 2;
    W m=std::stoull(argv[1]),nmod=std::stoull(argv[2]);
    W small=std::stoull(argv[3]),large=std::stoull(argv[4]);
    W p=std::stoull(argv[5]),q=std::stoull(argv[6]),mode=std::stoull(argv[7]);
    assert(1<m && m<(W(1)<<23) && nmod<m*m && nmod%m!=0 && mode<=2);
    assert(m<p && m<q && p!=q && p>2 && q>2 && p<(W(1)<<63) && q<(W(1)<<63));
    auto ip=field_inverses(p,m),iq=field_inverses(q,m);
    Writer writer(p,q,argv[8]);
    W square=m*m,originals=0;
    for (W j=1;j<m;++j) {
        W invj=inverse(j,square),im=invj%m;
        W r0=m,r1=W(U(nmod%m)*im%m*im%m),x=0,y=1;
        bool negative=false;
        auto emit=[&](I a,W t) {
            assert(a!=0 && 0<t && (a<0 ? -a : a)+t<=I(m));
            W r=residue(-a*j-I(nmod)*t*invj,square),aa=W(a<0 ? -a : a);
            W ap=ip[aa],aq=iq[aa];
            if (a<0) { ap=p-ap; aq=q-aq; }
            auto normalized=[&](I value) {
                writer.emit(W(U(residue(value,p))*ap%p),W(U(residue(value,q))*aq%q));
            };
            for (unsigned side=0;side<2;++side) {
                I S=a*(side ? large : small)+I(t)*(side ? small : large);
                I L=I(r)-floor_div(S+2*I(r)+square,2*I(square))*square;
                I error=-2*L-S;
                assert(-I(square)<=error && error<=I(square));
                if (mode!=1) normalized(-2*L-a*small-I(t)*large);
                if (mode!=0) normalized(error);
                ++originals;
            }
        };
        while (r1) {
            emit(negative ? -I(r1) : I(r1),y);
            W quotient=r0/r1;
            for (W k=1;k<quotient;++k) {
                I a=I(r0)-I(k)*r1;
                emit(negative ? a : -a,x+k*y);
            }
            W rem=r0%r1,new_y=x+quotient*y;
            r0=r1; r1=rem; x=y; y=new_y; negative=!negative;
        }
    }
    writer.flush(); writer.sink.close();
    assert(writer.count==originals*(mode==2 ? 2 : 1));
    std::cout << "{\"original_packets\":" << originals << ",\"mode\":" << mode
        << ",\"ordinary_records\":" << writer.count
        << ",\"scratch_bytes\":" << writer.count*24 << "}\n";
}
