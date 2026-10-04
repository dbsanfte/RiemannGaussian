// Copyright (c) 2026 David Sanftenberg. Apache-2.0.
// Independent private-field exhaustion classifier, not an N-only factorizer.
// Partition whole-N sign pairs by their P label, then count separate Q labels.
// Equal labels always share a bucket; every bucket is scanned completely.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

using W = std::uint64_t;
using U = __uint128_t;
using Pair = std::array<W,2>;
static_assert(sizeof(Pair)==16);

template<class T> struct BucketWriter {
    std::vector<std::ofstream> files;
    std::vector<std::vector<T>> buffers;
    std::vector<W> counts;
    BucketWriter(const std::filesystem::path& dir,const char* prefix,unsigned buckets)
        : buffers(buckets),counts(buckets) {
        for (unsigned i=0;i<buckets;++i) {
            files.emplace_back(dir/(std::string(prefix)+std::to_string(i)),std::ios::binary);
            if (!files.back()) throw std::runtime_error("cannot create bucket");
            buffers[i].reserve(8192);
        }
    }
    void flush(unsigned i) {
        files[i].write(reinterpret_cast<const char*>(buffers[i].data()),
            std::streamsize(buffers[i].size()*sizeof(T)));
        if (!files[i]) throw std::runtime_error("bucket write failed");
        buffers[i].clear();
    }
    void emit(unsigned i,const T& value) {
        assert(i<buffers.size());
        buffers[i].push_back(value); ++counts[i];
        if (buffers[i].size()==8192) flush(i);
    }
    void close() {
        for (unsigned i=0;i<files.size();++i) {
            flush(i); files[i].close();
            if (!files[i]) throw std::runtime_error("bucket close failed");
        }
    }
};

template<class T> struct Mapping {
    int fd;
    std::size_t bytes;
    T* data;
    explicit Mapping(const std::filesystem::path& path,W expected) {
        fd=open(path.c_str(),O_RDWR);
        if (fd<0) throw std::runtime_error("cannot open bucket");
        struct stat info{};
        if (fstat(fd,&info)) throw std::runtime_error("cannot stat bucket");
        assert(info.st_size>0 && W(info.st_size)==expected*sizeof(T));
        bytes=std::size_t(info.st_size);
        // Fail explicitly before classification rather than risk a partial scan.
        if (bytes>(W(32)<<30)) throw std::runtime_error("bucket exceeds 32 GiB guard");
        void* memory=mmap(nullptr,bytes,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);
        if (memory==MAP_FAILED) throw std::runtime_error("cannot map bucket");
        data=static_cast<T*>(memory);
    }
    void close() {
        if (munmap(data,bytes)) throw std::runtime_error("cannot unmap bucket");
        if (::close(fd)) throw std::runtime_error("cannot close bucket");
    }
};

static unsigned bucket(W label,W prime,unsigned buckets) {
    assert(label<=prime/2);
    unsigned index=unsigned(U(label)*buckets/(prime/2+1));
    assert(index<buckets);
    return index;
}

int main(int argc,char** argv) {
    if (argc!=6) return 2;
    W p=std::stoull(argv[2]),q=std::stoull(argv[3]);
    unsigned buckets=unsigned(std::stoul(argv[5]));
    assert(p>2 && q>2 && p!=q && p%2 && q%2 && buckets && buckets<=64);
    std::filesystem::path dir=argv[4];
    assert(std::filesystem::is_directory(dir) && std::filesystem::is_empty(dir));
    auto bytes=std::filesystem::file_size(argv[1]);
    assert(bytes>0 && bytes%sizeof(Pair)==0);
    W raw=bytes/sizeof(Pair),read=0;
    BucketWriter<Pair> ps(dir,"p",buckets);
    BucketWriter<W> qs(dir,"q",buckets);
    std::ifstream input(argv[1],std::ios::binary);
    if (!input) throw std::runtime_error("cannot open source table");
    std::vector<Pair> block(65536);
    while (read<raw) {
        W take=std::min<W>(block.size(),raw-read);
        input.read(reinterpret_cast<char*>(block.data()),std::streamsize(take*sizeof(Pair)));
        if (W(input.gcount())!=take*sizeof(Pair)) throw std::runtime_error("short source read");
        for (W i=0;i<take;++i) {
            assert(block[i][0]<=p/2 && block[i][1]<q);
            ps.emit(bucket(block[i][0],p,buckets),block[i]);
        }
        read+=take;
    }
    input.close(); ps.close();
    assert(std::filesystem::remove(argv[1]));
    std::cerr << "{\"progress\":\"bucket-P-partition-complete\",\"rows\":" << read << "}\n";
    W whole=0,cp=0,cq=0,max_mapping=0;
    bool whole_zero=false,p_zero=false,q_zero=false;
    for (unsigned index=0;index<buckets;++index) {
        W count=ps.counts[index],kept=0;
        auto path=dir/("p"+std::to_string(index));
        if (count) {
            Mapping<Pair> map(path,count);
            max_mapping=std::max<W>(max_mapping,map.bytes);
            auto* data=map.data;
            std::sort(data,data+count);
            for (W i=0;i<count;++i) {
                const Pair point=data[i];
                if (i && point==data[i-1]) continue;
                if (!i || point[0]!=data[i-1][0]) ++cp;
                ++whole; ++kept;
                whole_zero=whole_zero || (point[0]==0 && point[1]==0);
                p_zero=p_zero || point[0]==0;
                q_zero=q_zero || point[1]==0;
                W fq=std::min(point[1],point[1] ? q-point[1] : 0);
                qs.emit(bucket(fq,q,buckets),fq);
            }
            map.close();
        }
        assert(std::filesystem::remove(path));
        std::cerr << "{\"progress\":\"bucket-P-complete\",\"bucket\":" << index
            << ",\"raw_records\":" << count << ",\"global_orbits\":" << kept << "}\n";
    }
    qs.close();
    for (unsigned index=0;index<buckets;++index) {
        W count=qs.counts[index],kept=0;
        auto path=dir/("q"+std::to_string(index));
        if (count) {
            Mapping<W> map(path,count);
            max_mapping=std::max<W>(max_mapping,map.bytes);
            std::sort(map.data,map.data+count);
            for (W i=0;i<count;++i) {
                assert(map.data[i]<=q/2);
                if (!i || map.data[i]!=map.data[i-1]) { ++cq; ++kept; }
            }
            map.close();
        }
        assert(std::filesystem::remove(path));
        std::cerr << "{\"progress\":\"bucket-Q-complete\",\"bucket\":" << index
            << ",\"global_orbits\":" << count << ",\"q_classes\":" << kept << "}\n";
    }
    W sw=2*whole+1-2*W(whole_zero),sp=2*cp+1-2*W(p_zero),sq=2*cq+1-2*W(q_zero);
    assert(cp<=whole && cq<=whole && sp<=sw && sq<=sw);
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
        << ",\"record_bytes\":16,\"raw_records\":" << raw
        << ",\"bucket_count\":" << buckets << ",\"largest_mapped_bucket_bytes\":" << max_mapping
        << ",\"separate_Q_label_bytes\":" << 8*whole << "}\n";
    assert(std::filesystem::is_empty(dir));
}
