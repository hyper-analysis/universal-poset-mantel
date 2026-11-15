#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <utility>
#include <vector>

constexpr int types = 240;
constexpr int permutations = 576;
constexpr int words = permutations / 64;
constexpr int top_mask = 15 << 4;
using Caps = std::array<int, types>;
using Bits = std::array<uint64_t, words>;
using Group = std::vector<int>;
using Demand = std::pair<int, int>;
using Witness = std::vector<Demand>;

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
    std::array<int, types> minimum_capacity{};
    std::vector<int> zeros;
    Group permutations_at_root;
    Witness path;
    Witness witness;
    bool symmetry = false;
    uint64_t states = 0;

    Audit() {
        int n = 0;
        std::array<int, 256> index{};
        for (int m = 0; m < 256; ++m) if (m & 15) {
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

    bool singleton_failure(const Bits& possible, int budget, int covered) {
        int first = -1;
        for (int w = 0; w < words; ++w) if (possible[w]) {
            first = 64 * w + std::countr_zero(possible[w]);
            break;
        }
        if (first < 0) {
            // A spare middle slot can always be filled with the full profile.
            if (!budget && (covered & top_mask) != top_mask) return false;
            witness = path;
            return true;
        }
        if (!budget || zeros.empty()) return false;
        if (zeros.size() == 1) {
            // Each surviving permutation forbids exactly one singleton. All
            // distinct forbidden profiles are necessary and sufficient.
            std::array<bool, types> needed{};
            Witness singletons;
            for (int w = 0; w < words; ++w) for (uint64_t word = possible[w]; word; word &= word - 1) {
                int p = 64 * w + std::countr_zero(word);
                int i = preimage[p][zeros[0]];
                if (used[i]) return false;
                if (needed[i]) continue;
                needed[i] = true;
                singletons.emplace_back(i, 1);
                covered |= masks[i];
                if (--budget < 0) return false;
            }
            if (!budget && (covered & top_mask) != top_mask) return false;
            witness = path;
            witness.insert(witness.end(), singletons.begin(), singletons.end());
            return true;
        }
        if (budget == 1) {
            for (int missing : zeros) {
                const int i = preimage[first][missing];
                if (used[i] || ((covered | masks[i]) & top_mask) != top_mask) continue;
                bool eliminated = true;
                for (int w = 0; w < words; ++w) {
                    if (possible[w] & fit[i][1][w]) {
                        eliminated = false;
                        break;
                    }
                }
                if (eliminated) {
                    witness = path;
                    witness.emplace_back(i, 1);
                    return true;
                }
            }
            return false;
        }
        // Every failing completion must knock out first with one singleton.
        for (int missing : zeros) {
            int i = preimage[first][missing];
            if (used[i]) continue;
            Bits next;
            for (int w = 0; w < words; ++w) next[w] = possible[w] & fit[i][1][w];
            path.emplace_back(i, 1);
            if (singleton_failure(next, budget - 1, covered | masks[i])) return true;
            path.pop_back();
        }
        return false;
    }

    bool repeated_failure(const Bits& possible, int remaining, int limit, int last, int covered, const Group& group) {
        ++states;
        if (singleton_failure(possible, remaining, covered)) return true;
        for (int copies = std::min(remaining, limit); copies >= 2; --copies) {
            int spare = remaining - copies;
            for (int i = copies == limit ? last + 1 : 0; i < types; ++i) {
                if (used[i] || copies <= minimum_capacity[i]) continue;
                int coverage = covered | masks[i];
                if (!spare && (coverage & top_mask) != top_mask) continue;
                Bits next;
                for (int w = 0; w < words; ++w) next[w] = possible[w] & fit[i][copies][w];
                if (next == possible) continue;
                if (std::any_of(group.begin(), group.end(), [&](int p) {
                    int other = image[p][i];
                    return other < i && (copies < limit || other > last);
                })) continue;
                Group smaller;
                if (spare >= 2) {
                    for (int p : group) if (image[p][i] == i) smaller.push_back(p);
                }
                used[i] = true;
                path.emplace_back(i, copies);
                if (repeated_failure(next, spare, copies, i, coverage, smaller)) return true;
                used[i] = false;
                path.pop_back();
            }
        }
        return false;
    }

    bool verify(const Caps& caps) {
        zeros.clear();
        path.clear();
        witness.clear();
        used.fill(false);
        states = 0;
        for (int i = 0; i < types; ++i) if (!caps[i]) zeros.push_back(i);
        for (int i = 0; i < types; ++i) {
            fit[i] = {};
            minimum_capacity[i] = 8;
            for (int p = 0; p < permutations; ++p) {
                const int cap = caps[image[p][i]];
                minimum_capacity[i] = std::min(minimum_capacity[i], cap);
                for (int copies = 1; copies <= cap; ++copies)
                    fit[i][copies][p / 64] |= uint64_t{1} << (p % 64);
            }
        }
        Bits all;
        all.fill(~uint64_t{0});
        const Group empty;
        return !repeated_failure(all, 8, 8, -1, 0, symmetry ? permutations_at_root : empty);
    }
};

int vertices(const Caps& values) {
    return 32 + std::accumulate(values.begin(), values.end(), 0);
}

Caps read(const char* path) {
    std::ifstream file(path);
    Caps caps{};
    for (int& c : caps) if (!(file >> c) || c < 0 || c > 8)
        throw std::runtime_error("invalid capacity file");
    return caps;
}

void write(const char* path, const Caps& caps) {
    std::ofstream file(path);
    for (int copies : caps) file << copies << ' ';
    file << '\n';
}

int main(int argc, char** argv) {
    if (argc != 2 && argc != 3) {
        std::cerr << "usage: audit CAPS [REPAIRED_CAPS]\n";
        return 2;
    }
    Caps capacity = read(argv[1]);
    Audit audit;
    audit.symmetry = argc == 3;
    uint64_t repairs = 0;
    while (!audit.verify(capacity)) {
        if (argc == 2) {
            std::cout << "FAIL";
            for (auto [profile, count] : audit.witness) {
                std::cout << ' ' << audit.masks[profile] << ':' << count;
            }
            std::cout << '\n';
            return 1;
        }
        int best = 9;
        int best_stock = -1;
        Caps fixed{};
        for (const auto& permutation : audit.image) {
            Caps trial = capacity;
            int total = 0;
            int stock = 0;
            for (auto [profile, demand] : audit.witness) {
                const int index = permutation[profile];
                const int deficit = std::max(0, demand - capacity[index]);
                total += deficit;
                if (deficit) stock += capacity[index];
                trial[index] += deficit;
            }
            if (total < best || (total == best && stock > best_stock)) {
                best = total;
                best_stock = stock;
                fixed = trial;
            }
        }
        if (best == 0 || best == 9) throw std::logic_error("invalid witness");
        capacity = fixed;
        write(argv[2], capacity);
        std::cout << "Repair " << ++repairs << ", " << vertices(capacity)
                  << " vertices, added " << best << std::endl;
    }
    if (argc == 3) write(argv[2], capacity);
    std::cout << "PASS " << vertices(capacity) << " vertices, "
              << audit.states << " repeated-demand states" << std::endl;
}
