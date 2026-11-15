#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
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
    int relation = 0;
    std::array<int, types> rectangles{};
    std::array<bool, types> allowed{};
    std::vector<int> allowed_types;
    std::array<int, 65536> cover{};
    std::vector<int> maximal_rects;
    std::array<int, 256> profile_index{};
    std::vector<std::pair<int,int>> seeds;
    uint64_t states = 0;

    Audit() {
        int n = 0;
        std::array<int, 256> index{};
        for (int m = 0; m < 256; ++m) if ((m & 15) && (m >> 4)) {
            masks[n] = m;
            for (int i = 0; i < 4; ++i)
                if (m >> i & 1) rectangles[n] |= (m >> 4) << (4 * i);
            profile_index[m] = index[m] = n++;
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
                ++p;
            } while (std::next_permutation(right.begin(), right.end()));
        } while (std::next_permutation(left.begin(), left.end()));
    }

    int completion(int missing) {
        if (cover[missing] >= 0) return cover[missing];
        int best = 8;
        const int first = missing & -missing;
        for (int rect : maximal_rects)
            if (rect & first) best = std::min(best, 1 + completion(missing & ~rect));
        return cover[missing] = best;
    }

    bool singleton_failure(const Bits& possible, int budget, int covered) {
        int first = -1;
        for (int w = 0; w < words; ++w) if (possible[w]) {
            first = 64 * w + std::countr_zero(possible[w]);
            break;
        }
        if (completion(relation & ~covered) > budget) return false;
        if (first < 0) return true;
        if (!budget) return false;
        for (int i : allowed_types) {
            if (used[i] || (fit[i][1][first / 64] >> (first % 64) & 1)) continue;
            Bits next;
            for (int w = 0; w < words; ++w) next[w] = possible[w] & fit[i][1][w];
            if (singleton_failure(next, budget - 1, covered | rectangles[i])) return true;
        }
        return false;
    }

    bool repeated_failure(const Bits& possible, int remaining, int limit, int last, int covered, const Group& group) {
        ++states;
        if (completion(relation & ~covered) > remaining) return false;
        if (singleton_failure(possible, remaining, covered)) return true;
        for (int copies = std::min(remaining, limit); copies >= 2; --copies) {
            int spare = remaining - copies;
            const int start = copies == limit ? last + 1 : 0;
            auto begin = std::lower_bound(allowed_types.begin(), allowed_types.end(), start);
            for (auto at = begin; at != allowed_types.end(); ++at) {
                const int i = *at;
                if (used[i]) continue;
                int coverage = covered | (rectangles[i]);
                if (!spare && coverage != relation) continue;
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

    // Only demands that lost capacity can occur as the seeded demand of a new failure.
    bool audit_relation(int target, const Bits& root) {
        relation = target;
        allowed_types.clear();
        maximal_rects.clear();
        cover.fill(-1);
        cover[0] = 0;
        for (int i = 0; i < types; ++i) {
            allowed[i] = (rectangles[i] & relation) == rectangles[i];
            if (allowed[i]) allowed_types.push_back(i);
        }
        for (int i : allowed_types) {
            int r = rectangles[i];
            if (std::none_of(allowed_types.begin(), allowed_types.end(), [&](int j) {
                return i != j && (r & rectangles[j]) == r;
            })) maximal_rects.push_back(r);
        }
        Group stabilizer;
        for (int g = 0; g < permutations; ++g) {
            bool same = true;
            for (int i = 0; i < types && same; ++i)
                same = allowed[i] == allowed[image[g][i]];
            if (same) stabilizer.push_back(g);
        }
        if (seeds.empty()) return true;
        for (const auto& [i, count] : seeds) {
            Group fixed;
            bool minimal = true;
            for (int g : stabilizer) {
                const int j = image[g][i];
                if (j < i) minimal = false;
                if (j == i) fixed.push_back(g);
            }
            if (!minimal) continue;
            Bits next;
            for (int w = 0; w < words; ++w) next[w] = root[w] & fit[i][count][w];
            used[i] = true;
            const bool failure = repeated_failure(next, 8 - count, 8, -1, rectangles[i], fixed);
            used[i] = false;
            if (failure) return false;
        }
        return true;
    }
};

int main(int argc, char** argv) {
    if (argc != 4) return 2;
    Caps caps{};
    std::ifstream capacity(argv[1]);
    for (int& c : caps) if (!(capacity >> c) || c < 0 || c > 8) return 2;
    const int remove_mask = std::stoi(argv[3]);
    Audit audit;
    if (remove_mask < 0 || remove_mask > 255 || !(remove_mask & 15) || !(remove_mask >> 4)) return 2;
    int& count = caps[audit.profile_index[remove_mask]];
    if (!count) return 2;
    --count;
    std::ifstream input(argv[2]);
    int relation;
    constexpr std::array<int, 4> owners{3,12,3,12};
    std::array<int, 4> colowners{};
    for (int j = 0; j < 4; ++j)
        for (int i = 0; i < 4; ++i)
            if (!(owners[i] >> j & 1)) colowners[j] |= 1 << i;
    Bits root;
    root.fill(~uint64_t{0});
    int cases = 0;
    if (!input) return 2;
    while (input >> relation) {
        if (relation <= 0 || relation >= 65536) return 2;
        ++cases;
        for (auto& row : audit.fit) row = {};
        audit.seeds.clear();
        std::array<std::array<bool,9>,types> seeded{};
        for (int g = 0; g < permutations; ++g) {
            int mapped_relation = 0;
            for (int i = 0; i < 4; ++i)
                for (int j = 0; j < 4; ++j)
                    if (relation >> (4 * i + j) & 1)
                        mapped_relation |= audit.rectangles[audit.image[g][audit.profile_index[(1 << i) | (16 << j)]]];
            std::array<int, 4> missing_column{};
            for (int i = 0; i < 4; ++i)
                for (int j = 0; j < 4; ++j)
                    if (!(mapped_relation >> (4 * i + j) & 1)) missing_column[j] |= 1 << i;
            Caps effective{};
            int lost = -1;
            for (int i = 0; i < types; ++i) if (caps[i] || audit.masks[i] == remove_mask) {
                const int original_down = audit.masks[i] & 15;
                const int original_up = audit.masks[i] >> 4;
                int down = original_down;
                int up = original_up;
                for (int j = 0; j < 4; ++j) {
                    if (owners[j] & original_up & ~(mapped_relation >> (4 * j))) down &= ~(1 << j);
                    if (colowners[j] & original_down & missing_column[j]) up &= ~(1 << j);
                }
                if (down && up) {
                    const int destination = audit.profile_index[down | (16 * up)];
                    effective[destination] += caps[i];
                    if (audit.masks[i] == remove_mask) lost = destination;
                }
            }
            if (lost >= 0 && effective[lost] < 8) {
                const int i = audit.preimage[g][lost];
                const int t = effective[lost] + 1;
                if (!seeded[i][t]) {
                    seeded[i][t] = true;
                    audit.seeds.emplace_back(i,t);
                }
            }
            for (int i = 0; i < types; ++i)
                for (int t = 1; t <= std::min(8, effective[audit.image[g][i]]); ++t)
                    audit.fit[i][t][g / 64] |= uint64_t{1} << (g % 64);
        }
        // When availability depends on the relation, branch using the
        // actual set of singleton profiles missing at each permutation.
        if (!audit.audit_relation(relation, root)) {
            std::cout << "Deletion " << remove_mask << " fails on " << relation << " at orbit " << cases
                      << " after " << audit.states << " states\n";
            return 1;
        }
    }
    if (cases != 179 || !input.eof()) return 2;
    std::cout << "Deletion " << remove_mask << " passes " << cases << " orbits after "
              << audit.states << " states\n";
}
