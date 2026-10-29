// CPU scalar arithmetic diagnostic, not a CUDA/HIP evaluator or GPU benchmark.
#include <array>
#include <bit>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <limits>
#include <random>

struct Scales { float old_scale, tile_scale; };
Scales original(float old_max, float tile_max, float denominator) {
    const float next = std::fmax(old_max, tile_max);
    return {denominator == 0.0f ? 0.0f : std::exp(old_max - next),
            std::exp(tile_max - next)};
}
Scales candidate(float old_max, float tile_max, float denominator) {
    const float next = std::fmax(old_max, tile_max);
    return {denominator == 0.0f ? 0.0f :
                (old_max == next ? 1.0f : std::exp(old_max - next)),
            tile_max == next ? 1.0f : std::exp(tile_max - next)};
}
bool same(float a, float b) { return std::bit_cast<uint32_t>(a) == std::bit_cast<uint32_t>(b); }
int main() {
    std::mt19937 rng(20261025);
    std::uniform_real_distribution<float> maxima(-100.0f, 100.0f);
    std::uniform_real_distribution<float> value(-500.0f, 500.0f);
    const std::array<float, 11> edges{0.0f, -0.0f,
        std::numeric_limits<float>::denorm_min(), -std::numeric_limits<float>::denorm_min(),
        std::numeric_limits<float>::min(), -std::numeric_limits<float>::min(),
        1.0f, -1.0f, std::numeric_limits<float>::max(),
        -std::numeric_limits<float>::max(), 100.0f};
    uint64_t cases = 0, compared = 0;
    auto check = [&](float a, float b, bool first) {
        if (first) a = -std::numeric_limits<float>::infinity();
        const float den = first ? 0.0f : 1.5f;
        auto x = original(a, b, den), y = candidate(a, b, den);
        if (!same(x.old_scale,y.old_scale) || !same(x.tile_scale,y.tile_scale)) return false;
        compared += 2;
        // Retain the exact multiplication and FMA expression from the producer.
        for (int d=0; d<8; ++d) {
            float prior = first ? 0.0f : value(rng), tile = value(rng);
            if (!same(std::fma(prior,x.old_scale,tile*x.tile_scale),
                      std::fma(prior,y.old_scale,tile*y.tile_scale))) return false;
            ++compared;
        }
        if (!same(std::fma(den,x.old_scale,0.5f*x.tile_scale),
                  std::fma(den,y.old_scale,0.5f*y.tile_scale))) return false;
        ++compared; ++cases; return true;
    };
    for(float a:edges) for(float b:edges) for(bool first:{false,true})
        if(!check(a,b,first)) return 1;
    for(int i=0;i<100000;++i) {
        float a=maxima(rng),b=i%7==0?a:maxima(rng);
        if(!check(a,b,i%11==0)) return 2;
    }
    std::printf("{\"scope\":\"CPU std::exp and preserved FP32 multiplication/FMA; not GPU\","
                "\"cases\":%llu,\"bit_comparisons\":%llu,\"mismatches\":0}\n",
                (unsigned long long)cases,(unsigned long long)compared);
}
