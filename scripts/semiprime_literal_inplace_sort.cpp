// Copyright (c) 2026 David Sanftenberg. Apache-2.0.
// Reference-field exhaustion test, not an N-only factoring algorithm.
// The two common-sign coordinates identify a whole-N sign orbit exactly.
// Reuse the sorted table for the second field; no extra Q-label vector.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fcntl.h>
#include <iostream>
#include <stdexcept>
#include <string>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

using W = std::uint64_t;
using Pair = std::array<W,2>;
static_assert(sizeof(Pair)==16);

int main(int argc,char** argv) {
    if (argc!=4) return 2;
    W p=std::stoull(argv[2]),q=std::stoull(argv[3]);
    assert(p>2 && q>2 && p!=q && p%2 && q%2);
    int fd=open(argv[1],O_RDWR);
    if (fd<0) throw std::runtime_error("cannot open scratch table");
    struct stat info{};
    if (fstat(fd,&info)) throw std::runtime_error("cannot stat scratch table");
    assert(info.st_size>0 && info.st_size%16==0);
    W count=W(info.st_size)/16;
    void* mapping=mmap(nullptr,std::size_t(info.st_size),PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);
    if (mapping==MAP_FAILED) throw std::runtime_error("cannot map scratch table");
    auto* data=static_cast<Pair*>(mapping);
    std::cerr << "{\"progress\":\"inplace-sort-P-start\",\"rows\":" << count << "}\n";
    std::sort(data,data+count);
    W whole=0,cp=0,last_p=0;
    bool whole_zero=false,p_zero=false,q_zero=false;
    for (W i=0;i<count;++i) {
        Pair point=data[i];
        assert(point[0]<=p/2 && point[1]<q);
        if (whole && point==data[whole-1]) continue;
        if (!whole || point[0]!=last_p) { ++cp; last_p=point[0]; }
        whole_zero=whole_zero || (point[0]==0 && point[1]==0);
        p_zero=p_zero || point[0]==0;
        q_zero=q_zero || point[1]==0;
        data[whole++]=point;
    }
    std::cerr << "{\"progress\":\"inplace-sort-Q-start\",\"global_sign_orbits\":" << whole
        << ",\"folded_p_classes\":" << cp << "}\n";
    for (W i=0;i<whole;++i) {
        W fp=data[i][0],qc=data[i][1],fq=std::min(qc,qc ? q-qc : 0);
        W pc=qc>q/2 && fp ? p-fp : fp;
        data[i]={fq,pc};
    }
    std::sort(data,data+whole);
    W cq=0;
    for (W i=0;i<whole;++i) {
        assert(data[i][0]<=q/2 && data[i][1]<p);
        if (i) assert(data[i]!=data[i-1]);
        if (!i || data[i][0]!=data[i-1][0]) ++cq;
    }
    W sw=2*whole+1-2*W(whole_zero),sp=2*cp+1-2*W(p_zero),sq=2*cq+1-2*W(q_zero);
    assert(sp<=sw && sq<=sw);
    std::cout << "{\"distinct_global_sign_orbits\":" << whole
        << ",\"folded_p_classes\":" << cp << ",\"folded_q_classes\":" << cq
        << ",\"global_zero_in_ordinary_family\":" << (whole_zero ? "true" : "false")
        << ",\"p_zero_in_ordinary_family\":" << (p_zero ? "true" : "false")
        << ",\"q_zero_in_ordinary_family\":" << (q_zero ? "true" : "false")
        << ",\"signed_whole_values_with_zero_anchor\":" << sw
        << ",\"signed_p_classes_with_zero_anchor\":" << sp
        << ",\"signed_q_classes_with_zero_anchor\":" << sq
        << ",\"signed_p_collapsed_values\":" << sw-sp
        << ",\"signed_q_collapsed_values\":" << sw-sq
        << ",\"signed_exhausted\":" << (sw==sp && sw==sq ? "true" : "false")
        << ",\"record_bytes\":16,\"extra_Q_label_bytes\":0}\n";
    if (munmap(mapping,std::size_t(info.st_size))) throw std::runtime_error("cannot unmap scratch table");
    if (close(fd)) throw std::runtime_error("cannot close scratch table");
}
