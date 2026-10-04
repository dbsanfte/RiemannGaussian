// Copyright (c) 2026 David Sanftenberg. Apache-2.0.
// Complete reference-only anchored slope classification. Private prime fields
// are labels; this is not an N-only factorizer or a Lean execution certificate.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fcntl.h>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <vector>

using I=__int128_t;
using U=__uint128_t;
using W=std::uint64_t;
struct Pair { I a; W t; std::array<I,2> L; };
struct Record { W p,q; };
static_assert(sizeof(Record)==16);

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
static std::vector<Pair> pairs(W m,W nmod,W small,W large,W j) {
    W d=m*m,invj=inverse(j,d),im=invj%m;
    W r0=m,r1=W(U(nmod%m)*im%m*im%m),x=0,y=1;
    bool negative=false;
    std::vector<Pair> rows;
    auto append=[&](I a,W t) {
        assert(a!=0 && 0<t && (a<0 ? -a : a)+t<=I(m));
        W r=residue(-a*j-I(nmod)*t*invj,d);
        Pair current{a,t,{}};
        for (unsigned side=0;side<2;++side) {
            I S=a*(side ? large : small)+I(t)*(side ? small : large);
            current.L[side]=I(r)-floor_div(S+2*I(r)+d,2*I(d))*d;
        }
        rows.push_back(current);
    };
    while (r1) {
        append(negative ? -I(r1) : I(r1),y);
        W quotient=r0/r1;
        for (W k=1;k<quotient;++k) {
            I a=I(r0)-I(k)*r1;
            append(negative ? a : -a,x+k*y);
        }
        W rem=r0%r1,new_y=x+quotient*y;
        r0=r1; r1=rem; x=y; y=new_y; negative=!negative;
    }
    return rows;
}

// One inversion per nonempty residue batch and field. Zero denominators are
// retained as globally singular prefix entries, not silently inverted.
static std::vector<W> batch_inverse(const std::vector<I>& values,W prime) {
    std::vector<W> prefix(values.size()+1,1),result(values.size(),0);
    for (std::size_t i=0;i<values.size();++i)
        prefix[i+1]=values[i] ? W(U(prefix[i])*residue(values[i],prime)%prime) : prefix[i];
    W product_inverse=inverse(prefix.back(),prime);
    for (std::size_t i=values.size();i>0;--i) if (values[i-1]) {
        result[i-1]=W(U(prefix[i-1])*product_inverse%prime);
        product_inverse=W(U(product_inverse)*residue(values[i-1],prime)%prime);
    }
    assert(product_inverse==1);
    return result;
}

struct Writer {
    W count=0;
    std::ofstream sink;
    std::vector<Record> buffer;
    explicit Writer(const std::string& path):sink(path,std::ios::binary) {
        if (!sink) throw std::runtime_error("cannot open scratch table");
        buffer.reserve(65536);
    }
    void emit(W p,W q) {
        buffer.push_back({p,q}); ++count;
        if (buffer.size()==65536) flush();
    }
    void flush() {
        sink.write(reinterpret_cast<const char*>(buffer.data()),
            std::streamsize(buffer.size()*sizeof(Record)));
        if (!sink) throw std::runtime_error("scratch write failed");
        buffer.clear();
    }
};

struct Counts { W whole=0,p=0,q=0; };
static Counts classify(const std::string& path,W records,W p,W q) {
    Counts result;
    if (!records) return result;
    int fd=open(path.c_str(),O_RDWR);
    if (fd<0) throw std::runtime_error("cannot open scratch table");
    struct stat info{};
    if (fstat(fd,&info)!=0) throw std::runtime_error("cannot stat scratch table");
    assert(info.st_size>=0 && W(info.st_size)==records*sizeof(Record));
    void* mapped=mmap(nullptr,std::size_t(info.st_size),PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);
    if (mapped==MAP_FAILED) throw std::runtime_error("cannot map scratch table");
    auto data=static_cast<Record*>(mapped);
    for (W i=0;i<records;++i) assert(data[i].p<p && data[i].q<q);
    std::cerr << "{\"progress\":\"anchored-native-sort-P-start\",\"records\":" << records << "}\n";
    std::sort(data,data+records,[](const Record& a,const Record& b) {
        return a.p<b.p || (a.p==b.p && a.q<b.q);
    });
    for (W i=0;i<records;++i) {
        result.p += i==0 || data[i].p!=data[i-1].p;
        result.whole += i==0 || data[i].p!=data[i-1].p || data[i].q!=data[i-1].q;
    }
    std::vector<W> qvalues;
    qvalues.reserve(std::size_t(result.whole));
    for (W i=0;i<records;++i)
        if (i==0 || data[i].p!=data[i-1].p || data[i].q!=data[i-1].q)
            qvalues.push_back(data[i].q);
    assert(qvalues.size()==result.whole);
    std::cerr << "{\"progress\":\"anchored-native-sort-Q-start\",\"whole_values\":"
        << result.whole << ",\"p_classes\":" << result.p << "}\n";
    std::sort(qvalues.begin(),qvalues.end());
    for (std::size_t i=0;i<qvalues.size();++i) result.q += i==0 || qvalues[i]!=qvalues[i-1];
    assert(result.p<=result.whole && result.q<=result.whole);
    if (munmap(mapped,std::size_t(info.st_size))!=0) throw std::runtime_error("cannot unmap scratch table");
    close(fd);
    return result;
}

int main(int argc,char** argv) {
    if (argc!=9 && argc!=10 && argc!=12) return 2;
    W m=std::stoull(argv[1]),nmod=std::stoull(argv[2]);
    W small=std::stoull(argv[3]),large=std::stoull(argv[4]);
    W p=std::stoull(argv[5]),q=std::stoull(argv[6]),anchor_j=std::stoull(argv[7]);
    bool generate_only=argc>9;
    if (generate_only && std::string(argv[9])!="generate-only") return 2;
    W first=argc==12 ? std::stoull(argv[10]) : 1;
    W last=argc==12 ? std::stoull(argv[11]) : m;
    assert(1<m && m<(W(1)<<23) && nmod<m*m && nmod%m!=0);
    assert(p!=q && m*m<p && m*m<q && p<(W(1)<<63) && q<(W(1)<<63));
    assert(1<=anchor_j && anchor_j<m && 1<=first && first<=last && last<=m);
    auto source=pairs(m,nmod,small,large,anchor_j);
    auto found=std::find_if(source.begin(),source.end(),[](const Pair& z) { return z.a==1 || z.a==-1; });
    assert(found!=source.end());
    Pair anchor=*found;
    W originals=0,singular=0;
    Writer writer(argv[8]);
    for (W j=first;j<last;++j) {
        auto rows=pairs(m,nmod,small,large,j);
        std::vector<I> denominators;
        denominators.reserve(rows.size());
        for (const auto& z:rows) {
            I D=anchor.a*I(z.t)-z.a*I(anchor.t);
            assert((D<0 ? -D : D)<=I(m*m));
            denominators.push_back(D);
        }
        auto ip=batch_inverse(denominators,p),iq=batch_inverse(denominators,q);
        for (std::size_t i=0;i<rows.size();++i) {
            originals+=2;
            if (!denominators[i]) { singular+=2; continue; }
            for (unsigned side=0;side<2;++side) {
                I A=anchor.a*rows[i].L[side]-rows[i].a*anchor.L[1];
                writer.emit(W(U(residue(A,p))*ip[i]%p),W(U(residue(A,q))*iq[i]%q));
            }
        }
    }
    writer.flush(); writer.sink.close();
    assert(writer.count+singular==originals);
    Counts counts=generate_only ? Counts{} : classify(argv[8],writer.count,p,q);
    std::cout << "{\"original_packets\":" << originals
        << ",\"anchor_residue\":" << anchor_j << ",\"anchor_numerator\":" << (anchor.a==1 ? 1 : -1)
        << ",\"anchor_denominator\":" << anchor.t
        << ",\"globally_singular_minor_packets\":" << singular
        << ",\"proper_minor_prefix_hits\":0,\"ordinary_records\":" << writer.count
        << ",\"scratch_bytes\":" << writer.count*sizeof(Record)
        << ",\"first_residue\":" << first << ",\"end_residue\":" << last
        << ",\"both_prime_field_projections_fully_counted\":" << (generate_only ? "false" : "true")
        << ",\"ordinary_whole_values\":" << counts.whole
        << ",\"p_classes\":" << counts.p << ",\"q_classes\":" << counts.q
        << ",\"p_collapsed_values\":" << counts.whole-counts.p
        << ",\"q_collapsed_values\":" << counts.whole-counts.q
        << ",\"chosen_anchor_exhausted\":" << (generate_only ? "null" :
            counts.whole==counts.p && counts.whole==counts.q ? "true" : "false")
        << "}\n";
}
