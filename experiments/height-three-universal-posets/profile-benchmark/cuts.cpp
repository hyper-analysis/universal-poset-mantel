#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

constexpr int slots = 16;
constexpr int shapes = 5 * 9 * 5;
constexpr int unoriented_shapes = (shapes + 1) / 2;
constexpr unsigned bottom = 15;
constexpr unsigned middle = 255 << 4;
constexpr unsigned top = 15 << 12;
constexpr unsigned all = (1 << slots) - 1;
constexpr int max_degree = 12;
using Masks = std::array<unsigned, slots>;
using Edge = std::pair<int, int>;

bool same_rank(int a, int b) {
    return (a < 4 && b < 4) || (a >= 4 && a < 12 && b >= 4 && b < 12)
           || (a >= 12 && b >= 12);
}

int shape(unsigned cut) {
    return 45 * std::popcount(cut & bottom) + 5 * std::popcount(cut & middle)
           + std::popcount(cut & top);
}

int deviation_choices(int outside, int degree) {
    int count = 1;
    int choose = 1;
    for (int j = 1; j <= std::min(outside, degree); ++j) {
        choose = choose * (outside - j + 1) / j;
        count += choose;
    }
    return count;
}

int label_count(unsigned cut, int degree) {
    std::array<int, slots> weight{};
    std::array<int, slots> reads{};
    std::array<std::vector<int>, slots> incident;
    std::vector<Edge> edges;
    std::vector<int> owner;
    for (int x = 0; x < slots; ++x) {
        int outside = 0;
        for (int y = 0; y < slots; ++y) {
            if (same_rank(x, y)) continue;
            const bool inside = ((cut >> x) & 1) == ((cut >> y) & 1);
            if (inside) ++outside;
            if (!inside && x < y) {
                incident[x].push_back(edges.size());
                incident[y].push_back(edges.size());
                edges.emplace_back(x, y);
                owner.push_back(-1);
            }
        }
        weight[x] = deviation_choices(outside, degree);
    }
    for (int i = 0; i < static_cast<int>(edges.size()); ++i) {
        const auto [a, b] = edges[i];
        std::array<int, slots> parent;
        parent.fill(-1);
        std::array<int, slots> queue{};
        queue[0] = a;
        queue[1] = b;
        parent[a] = parent[b] = i;
        int tail = 2;
        int best = a;
        for (int head = 0; head < tail; ++head) {
            const int x = queue[head];
            if ((weight[x] << reads[x]) < (weight[best] << reads[best])) best = x;
            for (int j : incident[x]) {
                if (owner[j] != x) continue;
                const auto [from, to] = edges[j];
                const int y = x == from ? to : from;
                if (parent[y] >= 0) continue;
                parent[y] = j;
                queue[tail++] = y;
            }
        }
        // Transfer ownership along an augmenting path. The other loads stay
        // constant, so the only marginal cost is the extra read at best.
        ++reads[best];
        for (int x = best; x >= 0;) {
            const int j = parent[x];
            const int previous = owner[j];
            owner[j] = x;
            x = previous;
        }
    }
    int count = 0;
    for (int x = 0; x < slots; ++x) count += weight[x] << reads[x];
    return count;
}

using Costs = std::array<std::array<int, max_degree + 1>, shapes>;

Costs all_costs() {
    Costs costs{};
    for (int a = 0; a <= 4; ++a) {
        for (int m = 0; m <= 8; ++m) {
            for (int c = 0; c <= 4; ++c) {
                const unsigned cut = ((1 << a) - 1) | (((1 << m) - 1) << 4)
                                     | (((1 << c) - 1) << 12);
                for (int d = 0; d <= max_degree; ++d) costs[shape(cut)][d] = label_count(cut, d);
            }
        }
    }
    return costs;
}

int main() {
    const Costs costs = all_costs();
    if (costs[shape(middle)][4] != 1024) throw std::logic_error("wrong floor cut count");
    std::array<int, 1 << (slots - 1)> cut_shape{};
    for (unsigned cut = 0; cut < cut_shape.size(); ++cut) {
        const int s = shape(cut);
        cut_shape[cut] = std::min(s, shapes - 1 - s);
    }
    for (int s = 0; s < unoriented_shapes; ++s) {
        for (int d = 0; d <= max_degree; ++d) std::cout << costs[s][d] << ' ';
        std::cout << '\n';
    }
    std::string kind;
    while (std::cin >> kind) {
        Masks graph{};
        for (unsigned& row : graph) {
            if (!(std::cin >> row) || row > all) throw std::runtime_error("invalid row");
        }
        int best = std::numeric_limits<int>::max();
        std::array<int, unoriented_shapes> minimum_degree;
        minimum_degree.fill(max_degree);
        for (unsigned cut = 0; cut < cut_shape.size(); ++cut) {
            int d = 0;
            for (int x = 0; x < slots; ++x) {
                const unsigned side = (cut >> x) & 1 ? cut : all ^ cut;
                d = std::max(d, std::popcount(graph[x] & side));
            }
            const int s = cut_shape[cut];
            minimum_degree[s] = std::min(minimum_degree[s], d);
        }
        for (int s = 0; s < unoriented_shapes; ++s) best = std::min(best, costs[s][minimum_degree[s]]);
        int floor_degree = 0;
        for (int x = 0; x < slots; ++x) {
            if (x < 4 || x >= 12) floor_degree = std::max(
                floor_degree, std::popcount(graph[x] & (bottom | top)));
        }
        std::cout << kind << ' ' << best << ' ' << costs[shape(middle)][floor_degree];
        for (int d : minimum_degree) std::cout << ' ' << d;
        std::cout << '\n';
    }
}
