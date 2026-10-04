// Copyright (c) 2026 David Sanftenberg. Apache-2.0.
// Reference-only field classifier input. This is not a trusted proof or
// an N-only factorizer: p and q are private reference coordinates.
// In-place replay input: store the common whole-N sign orbit in 16 bytes.
// Preserve the literal residue shift before joining original roots.
// Both modes keep all intermediates and centers; mode 1 retains the old family.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
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
    I a = x, b = modulus, u = 1, v = 0;
    while (b) {
        I k = a / b, r = a - k*b, t = u-k*v;
        a = b; b = r; u = v; v = t;
    }
    assert(a == 1);
    return residue(u,modulus);
}
static std::vector<W> field_inverses(W prime, W m) {
    std::vector<W> result(m+1);
    result[1] = 1;
    for (W k = 2; k <= m; ++k)
        result[k] = prime-W(U(prime/k)*result[prime%k]%prime);
    return result;
}

struct Pair { I a; W t; std::array<I,2> L; };
static_assert(sizeof(std::array<W,2>)==16);
struct Writer {
    W p,q,count=0;
    std::ofstream sink;
    std::vector<std::array<W,2>> buffer;
    Writer(W p_,W q_,const std::string& path):p(p_),q(q_),sink(path,std::ios::binary) {
        if (!sink) throw std::runtime_error("cannot open scratch table");
        buffer.reserve(65536);
    }
    void emit(W ep,W eq) {
        W np=ep ? p-ep : 0, nq=eq ? q-eq : 0;
        W fp=std::min(ep,np),fq=std::min(eq,nq);
        W qc=ep<np ? eq : ep>np ? nq : fq;
        buffer.push_back({fp,qc}); ++count;
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
    if (argc != 9 && argc != 11) return 2;
    W m=std::stoull(argv[1]),nmod=std::stoull(argv[2]);
    W small=std::stoull(argv[3]),large=std::stoull(argv[4]);
    W p=std::stoull(argv[5]),q=std::stoull(argv[6]),mode=std::stoull(argv[7]);
    assert(mode<=1);
    // These bounds keep every signed/product intermediate inside 128 bits.
    assert(1<m && m<(W(1)<<23) && m<p && m<q && p!=q);
    assert(2<p && 2<q && p<(W(1)<<63) && q<(W(1)<<63));
    W d=m*m,first=argc==11 ? std::stoull(argv[9]) : 1;
    W last=argc==11 ? std::stoull(argv[10]) : m;
    assert(nmod<d && nmod%m!=0 && 1<=first && first<=last && last<=m);
    auto ip=field_inverses(p,m),iq=field_inverses(q,m);
    Writer writer(p,q,argv[8]);
    writer.emit(0,0);
    W originals=0,companions=0;
    for (W j=first;j<last;++j) {
        writer.emit(residue(-I(j),p),residue(-I(j),q));
        W invj=inverse(j,d),im=invj%m;
        W r0=m,r1=W(U(nmod%m)*im%m*im%m),x=0,y=1;
        bool negative=false,has_previous=false;
        Pair previous{};
        auto emit_pair = [&](I a,W t) {
            assert(a!=0 && -I(m)<a && a<I(m) && 0<t && t<=m);
            W r=residue(-a*j-I(nmod)*t*invj,d);
            Pair current{a,t,{}};
            for (unsigned side=0;side<2;++side) {
                I S=a*(side ? large : small)+I(t)*(side ? small : large);
                current.L[side]=I(r)-floor_div(S+2*I(r)+d,2*I(d))*d;
                W minusP=residue(-current.L[side],p),minusQ=residue(-current.L[side],q);
                W aa=W(a<0 ? -a : a),ap=ip[aa],aq=iq[aa];
                if (a<0) { ap=p-ap; aq=q-aq; }
                W alphaP=W(U(minusP)*ap%p),alphaQ=W(U(minusQ)*aq%q);
                writer.emit(residue(I(alphaP)-j,p),residue(I(alphaQ)-j,q));
                if (mode) {
                    writer.emit(alphaP,alphaQ);
                    writer.emit(W(U(minusP)*ip[t]%p),W(U(minusQ)*iq[t]%q));
                }
                ++originals;
            }
            if (mode && has_previous) {
                I determinant=I(t)*previous.a-I(previous.t)*a;
                assert(determinant==I(m) || determinant==-I(m));
                for (unsigned ls=0;ls<2;++ls) for (unsigned rs=0;rs<2;++rs) {
                    I numerator=-(I(t)*previous.L[ls]-I(previous.t)*current.L[rs]);
                    assert(numerator%determinant==0);
                    I c=numerator/determinant;
                    writer.emit(residue(c,p),residue(c,q)); ++companions;
                }
            }
            previous=current; has_previous=true;
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
    writer.flush(); writer.sink.close();
    assert(companions<=2*originals);
    assert(writer.count==(mode ? 3 : 1)*originals+companions+last-first+1);
    std::cout << "{\"original_packets\":" << originals
        << ",\"companion_packets\":" << companions
        << ",\"mode\":" << mode
        << ",\"literal_shifted_coordinates\":" << originals
        << ",\"known_residue_coordinates\":" << last-first+1
        << ",\"affine_coordinates\":" << (mode ? 2*originals : 0)
        << ",\"ordinary_records\":" << writer.count
        << ",\"scratch_bytes\":" << writer.count*16
        << ",\"first_residue\":" << first << ",\"end_residue\":" << last << "}\n";
}
