#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

constexpr int types = 225;
constexpr int permutations = 576;
constexpr int words = permutations / 64;
using Caps = std::array<int, types>;
using Bits = std::array<uint64_t, words>;
using Group = std::vector<int>;

int remap(int mask, const std::array<int, 4>& order) {
    int moved = 0;
    for (int i = 0; i < 4; ++i) moved |= ((mask >> i) & 1) << order[i];
    return moved;
}

struct Audit {
    std::array<int, types> masks{};
    std::array<std::array<int, types>, permutations> image{}, preimage{};
    std::array<std::array<Bits, 9>, types> fit{};
    std::array<bool, types> used{};
    std::vector<int> zeros;
    Group permutations_at_root;
    bool symmetry = false;
    uint64_t states = 0;

    Audit() {
        int n = 0;
        std::array<int, 256> index{};
        for (int m = 0; m < 256; ++m) if ((m & 15) && (m >> 4)) {
            masks[n] = m;
            index[m] = n++;
        }
        int p = 0;
        std::array<int, 4> left{0,1,2,3};
        do {
            std::array<int, 4> right{0,1,2,3};
            do {
                for (int j = 0; j < types; ++j) {
                    int v = index[remap(masks[j] & 15, left) | (remap(masks[j] >> 4, right) << 4)];
                    image[p][j] = v;
                    preimage[p][v] = j;
                }
                permutations_at_root.push_back(p++);
            } while (std::next_permutation(right.begin(), right.end()));
        } while (std::next_permutation(left.begin(), left.end()));
    }

    bool singleton_failure(const Bits& possible, int budget, int covered) const {
        int first = -1;
        for (int w = 0; w < words; ++w) if (possible[w]) {
            first = 64 * w + std::countr_zero(possible[w]);
            break;
        }
        if (first < 0) return budget > 0 || covered == 255;
        if (!budget || zeros.empty()) return false;
        if (zeros.size() == 1) {
            // Each surviving permutation forbids exactly one singleton. All
            // distinct forbidden profiles are necessary and sufficient.
            std::array<bool, types> needed{};
            for (int w = 0; w < words; ++w) for (uint64_t word = possible[w]; word; word &= word - 1) {
                int p = 64 * w + std::countr_zero(word);
                int i = preimage[p][zeros[0]];
                if (used[i]) return false;
                if (needed[i]) continue;
                needed[i] = true;
                covered |= masks[i];
                if (--budget < 0) return false;
            }
            return budget > 0 || covered == 255;
        }
        for (int missing : zeros) {
            int i = preimage[first][missing];
            if (used[i]) continue;
            Bits next;
            for (int w = 0; w < words; ++w) next[w] = possible[w] & fit[i][1][w];
            if (singleton_failure(next, budget - 1, covered | masks[i])) return true;
        }
        return false;
    }

    bool repeated_failure(const Bits& possible, int remaining, int limit, int last, int covered, const Group& group) {
        ++states;
        if (singleton_failure(possible, remaining, covered)) return true;
        for (int copies = std::min(remaining, limit); copies >= 2; --copies) {
            int spare = remaining - copies;
            for (int i = copies == limit ? last + 1 : 0; i < types; ++i) {
                if (used[i]) continue;
                int coverage = covered | masks[i];
                if (!spare && coverage != 255) continue;
                Bits next;
                for (int w = 0; w < words; ++w) next[w] = possible[w] & fit[i][copies][w];
                if (next == possible) continue;
                if (std::any_of(group.begin(), group.end(), [&](int p) {
                    const int j = image[p][i];
                    return j < i && (copies < limit || j > last);
                })) continue;
                Group smaller;
                if (spare >= 2) {
                    for (int p : group) if (image[p][i] == i) smaller.push_back(p);
                }
                used[i] = true;
                if (repeated_failure(next, spare, copies, i, coverage, smaller)) return true;
                used[i] = false;
            }
        }
        return false;
    }

    bool verify(const Caps& caps) {
        zeros.clear();
        used.fill(false);
        states = 0;
        for (int i = 0; i < types; ++i) if (!caps[i]) zeros.push_back(i);
        for (int i = 0; i < types; ++i) {
            fit[i] = {};
            for (int p = 0; p < permutations; ++p)
                for (int copies = 1; copies <= caps[image[p][i]]; ++copies)
                    fit[i][copies][p / 64] |= uint64_t{1} << (p % 64);
        }
        Bits all;
        all.fill(~uint64_t{0});
        const Group empty;
        return !repeated_failure(all, 8, 8, -1, 0, symmetry ? permutations_at_root : empty);
    }
};

int main(int argc, char** argv) {
    if (argc != 2 && argc != 4) return 2;
    std::ifstream input(argv[1]);
    Caps caps;
    for (int& c : caps) if (!(input >> c) || c < 0 || c > 8)
        throw std::runtime_error("invalid capacity file");
    Audit audit;
    audit.symmetry = argc == 4;
    auto vertices = [](const Caps& values) { return 32 + std::accumulate(values.begin(), values.end(), 0); };
    if (!audit.verify(caps)) {
        std::cerr << "Coverage failed after " << audit.states << " repeated-demand states\n";
        return 1;
    }
    std::cout << "Coverage passes with " << vertices(caps) << " vertices, " << audit.zeros.size()
              << " missing profiles and " << audit.states << " repeated-demand states\n" << std::flush;
    if (argc == 2) return 0;
    std::mt19937 random(std::stoul(argv[3]));
    std::array<int, types> order;
    std::iota(order.begin(), order.end(), 0);
    auto save = [&] {
        std::ofstream file(argv[2]);
        for (int c : caps) file << c << ' ';
        file << '\n';
    };
    std::shuffle(order.begin(), order.end(), random);
    save();
    for (int i : order) {
        while (caps[i] > 0) {
            --caps[i];
            if (!audit.verify(caps)) {
                ++caps[i];
                break;
            }
            std::cout << vertices(caps) << " vertices (" << audit.zeros.size() << " missing profiles)\n" << std::flush;
            save();
        }
    }
}
