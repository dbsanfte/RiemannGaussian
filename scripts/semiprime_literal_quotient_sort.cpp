// Copyright (c) 2026 David Sanftenberg. Apache-2.0.
// Exact reference classifier, independently checked against whole-N sets.
// Preserve first proper P/Q collision coordinates for source witness replay.
// This native integer sort is not a Lean proof or a factorizer bit clock.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <fcntl.h>
#include <iostream>
#include <stdexcept>
#include <string>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <vector>

using W=std::uint64_t;
struct Record { W fp,qc,fq; };
struct QRecord { W fq,pc; };
static_assert(sizeof(QRecord)==16);
static_assert(sizeof(Record)==24);
int main(int argc,char** argv) {
    if (argc!=4) return 2;
    W p=std::stoull(argv[2]),q=std::stoull(argv[3]);
    assert(p>2 && q>2 && p!=q && p%2 && q%2);
    int fd=open(argv[1],O_RDWR);
    if (fd<0) throw std::runtime_error("cannot open table");
    struct stat info{};
    if (fstat(fd,&info)!=0) throw std::runtime_error("cannot stat table");
    assert(info.st_size>=0 && info.st_size%24==0);
    W rows=W(info.st_size/24),whole=0,cp=0,cq=0;
    assert(rows<=(W(1)<<40));
    bool pzero=false,qzero=false,globalzero=false;
    bool phit=false,qhit=false;
    W pfirst=0,pqa=0,pqb=0,qfirst=0,qpa=0,qpb=0;
    if (rows) {
        void* mapped=mmap(nullptr,std::size_t(info.st_size),PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);
        if (mapped==MAP_FAILED) throw std::runtime_error("cannot map table");
        auto data=static_cast<Record*>(mapped);
        for (W i=0;i<rows;++i) {
            assert(data[i].fp<=p/2 && data[i].qc<q);
            assert(data[i].fp!=0 || data[i].qc<=q/2);
            assert(data[i].fq==std::min(data[i].qc,data[i].qc ? q-data[i].qc : 0));
        }
        std::cerr << "{\"progress\":\"native-integer-sort-P-start\",\"rows\":" << rows << "}\n";
        std::sort(data,data+rows,[](const Record& a,const Record& b) {
            return a.fp<b.fp || (a.fp==b.fp && a.qc<b.qc);
        });
        for (W i=0;i<rows;++i) {
            cp += i==0 || data[i].fp!=data[i-1].fp;
            whole += i==0 || data[i].fp!=data[i-1].fp || data[i].qc!=data[i-1].qc;
            if (i && !phit && data[i].fp==data[i-1].fp && data[i].qc!=data[i-1].qc) {
                phit=true; pfirst=data[i].fp; pqa=data[i-1].qc; pqb=data[i].qc;
            }
        }
        pzero=data[0].fp==0;
        globalzero=pzero && data[0].qc==0;
        // One Q coordinate per global sign orbit preserves every Q class.
        std::vector<QRecord> qvalues;
        qvalues.reserve(std::size_t(whole));
        for (W i=0;i<rows;++i)
            if (i==0 || data[i].fp!=data[i-1].fp || data[i].qc!=data[i-1].qc) {
                W pc=data[i].qc>q/2 && data[i].fp ? p-data[i].fp : data[i].fp;
                qvalues.push_back({data[i].fq,pc});
            }
        assert(qvalues.size()==whole);
        std::cerr << "{\"progress\":\"native-integer-sort-Q-start\",\"global_sign_orbits\":"
            << whole << ",\"folded_p_classes\":" << cp << "}\n";
        std::sort(qvalues.begin(),qvalues.end(),[](const QRecord& a,const QRecord& b) {
            return a.fq<b.fq || (a.fq==b.fq && a.pc<b.pc);
        });
        for (std::size_t i=0;i<qvalues.size();++i) {
            cq += i==0 || qvalues[i].fq!=qvalues[i-1].fq;
            if (i) assert(qvalues[i].fq!=qvalues[i-1].fq || qvalues[i].pc!=qvalues[i-1].pc);
            if (i && !qhit && qvalues[i].fq==qvalues[i-1].fq) {
                qhit=true; qfirst=qvalues[i].fq; qpa=qvalues[i-1].pc; qpb=qvalues[i].pc;
            }
        }
        qzero=qvalues[0].fq==0;
        if (munmap(mapped,std::size_t(info.st_size))!=0) throw std::runtime_error("cannot unmap table");
    }
    close(fd);
    W signed_whole=2*(whole-globalzero)+1;
    W signed_p=2*(cp-pzero)+1,signed_q=2*(cq-qzero)+1;
    assert(signed_p<=signed_whole && signed_q<=signed_whole);
    std::cout << "{\"distinct_global_sign_orbits\":" << whole
        << ",\"folded_p_classes\":" << cp << ",\"folded_q_classes\":" << cq
        << ",\"global_zero_in_ordinary_family\":" << (globalzero ? "true" : "false")
        << ",\"p_zero_in_ordinary_family\":" << (pzero ? "true" : "false")
        << ",\"q_zero_in_ordinary_family\":" << (qzero ? "true" : "false")
        << ",\"signed_whole_values_with_zero_anchor\":" << signed_whole
        << ",\"signed_p_classes_with_zero_anchor\":" << signed_p
        << ",\"signed_q_classes_with_zero_anchor\":" << signed_q
        << ",\"signed_p_collapsed_values\":" << signed_whole-signed_p
        << ",\"signed_q_collapsed_values\":" << signed_whole-signed_q
        << ",\"signed_exhausted\":" << (signed_whole==signed_p && signed_whole==signed_q ? "true" : "false")
        << ",\"q_label_bytes_per_global_orbit\":16"
        << ",\"first_p_collision\":";
    if (phit) std::cout << "[[" << pfirst << ',' << pqa << "],[" << pfirst << ',' << pqb << "]]";
    else std::cout << "null";
    std::cout << ",\"first_q_collision\":";
    if (qhit) std::cout << "[[" << qpa << ',' << qfirst << "],[" << qpb << ',' << qfirst << "]]";
    else std::cout << "null";
    std::cout << "}\n";
}
