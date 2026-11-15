#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Mask = std::uint32_t;
constexpr int max_slots = 7;

Mask bit(int index) {
    return Mask{1} << index;
}

struct Edge {
    int from;
    int to;
};

struct Profile {
    std::array<int, 4> boundary;
    std::array<Mask, 3> rank_masks{};
    std::vector<Edge> edges;
    std::vector<Mask> triangles;

    Profile(int bottom, int middle, int top)
        : boundary{0, bottom, bottom + middle, bottom + middle + top} {
        int edge_index[max_slots][max_slots]{};
        for (int rank = 0; rank < 3; ++rank) {
            for (int from = boundary[rank]; from < boundary[rank + 1]; ++from) {
                rank_masks[rank] |= bit(from);
                for (int to = boundary[rank + 1]; to < boundary[3]; ++to) {
                    edge_index[from][to] = edges.size();
                    edges.push_back({from, to});
                }
            }
        }
        for (int a = 0; a < boundary[1]; ++a) {
            for (int m = boundary[1]; m < boundary[2]; ++m) {
                for (int c = boundary[2]; c < boundary[3]; ++c) {
                    triangles.push_back(bit(edge_index[a][m]) | bit(edge_index[m][c]) |
                                        bit(edge_index[a][c]));
                }
            }
        }
    }

    std::vector<Mask> triangle_free_graphs() const {
        std::vector<Mask> result;
        for (Mask graph = 0; graph < bit(edges.size()); ++graph) {
            bool triangle_free = true;
            for (Mask triangle : triangles) {
                if ((graph & triangle) == triangle) {
                    triangle_free = false;
                    break;
                }
            }
            if (triangle_free) {
                result.push_back(graph);
            }
        }
        return result;
    }
};

class Decoder {
public:
    Decoder(const Profile& profile, Mask shape, bool reverse_preference)
        : profile(profile) {
        std::vector<Edge> template_edges;
        for (std::size_t i = 0; i < profile.edges.size(); ++i) {
            const auto [from, to] = profile.edges[i];
            if (shape & bit(i)) {
                template_edges.push_back(reverse_preference ? Edge{to, from} : Edge{from, to});
            } else {
                reads[from] |= bit(to);
                reads[to] |= bit(from);
            }
        }

        std::array<std::vector<int>, max_slots> assigned;
        const std::size_t capacity = (profile.boundary[3] + 3) / 4;
        for (std::size_t i = 0; i < template_edges.size(); ++i) {
            Mask seen = 0;
            if (!assign(i, template_edges, assigned, seen, capacity)) {
                throw std::runtime_error("Template edge assignment failed");
            }
        }
        for (int slot = 0; slot < profile.boundary[3]; ++slot) {
            for (int edge : assigned[slot]) {
                const auto [from, to] = template_edges[edge];
                reads[slot] |= bit(slot == from ? to : from);
            }
        }
    }

    void check_embedding(Mask graph) const {
        std::array<Mask, max_slots> positive{};
        for (std::size_t i = 0; i < profile.edges.size(); ++i) {
            if (graph & bit(i)) {
                const auto [from, to] = profile.edges[i];
                positive[from] |= bit(to) & reads[from];
                positive[to] |= bit(from) & reads[to];
            }
        }
        for (std::size_t i = 0; i < profile.edges.size(); ++i) {
            const auto [from, to] = profile.edges[i];
            bool expected = graph & bit(i);
            bool actual;
            if (profile.rank_masks[1] & bit(to)) {
                actual = adjacent(from, positive[from], to, positive[to], profile.rank_masks[2]);
            } else if (profile.rank_masks[1] & bit(from)) {
                actual = adjacent(to, positive[to], from, positive[from], profile.rank_masks[0]);
            } else {
                actual = outer_comparison(from, positive[from], to, positive[to]);
                expected = !expected;
            }
            if (actual != expected) {
                throw std::runtime_error("Induced embedding check failed");
            }
        }
    }

    std::uint64_t check_transitivity() const {
        std::uint64_t paths = 0;
        for (int m = profile.boundary[1]; m < profile.boundary[2]; ++m) {
            for_each_subset(reads[m], [&](Mask middle) {
                for (int a = 0; a < profile.boundary[1]; ++a) {
                    for_each_subset(reads[a], [&](Mask bottom) {
                        if (!adjacent(a, bottom, m, middle, profile.rank_masks[2])) {
                            return;
                        }
                        for (int c = profile.boundary[2]; c < profile.boundary[3]; ++c) {
                            for_each_subset(reads[c], [&](Mask top) {
                                if (adjacent(c, top, m, middle, profile.rank_masks[0])) {
                                    if (!outer_comparison(a, bottom, c, top)) {
                                        throw std::runtime_error("Transitivity check failed");
                                    }
                                    ++paths;
                                }
                            });
                        }
                    });
                }
            });
        }
        return paths;
    }

private:
    const Profile& profile;
    std::array<Mask, max_slots> reads{};

    static bool assign(int edge, const std::vector<Edge>& edges,
                       std::array<std::vector<int>, max_slots>& assigned,
                       Mask& seen, std::size_t capacity) {
        for (int slot : {edges[edge].from, edges[edge].to}) {
            if (seen & bit(slot)) {
                continue;
            }
            seen |= bit(slot);
            if (assigned[slot].size() < capacity) {
                assigned[slot].push_back(edge);
                return true;
            }
            for (int& previous : assigned[slot]) {
                if (assign(previous, edges, assigned, seen, capacity)) {
                    previous = edge;
                    return true;
                }
            }
        }
        return false;
    }

    template <class Check>
    static void for_each_subset(Mask mask, Check check) {
        for (Mask subset = mask;; subset = (subset - 1) & mask) {
            check(subset);
            if (subset == 0) {
                return;
            }
        }
    }

    bool reads_zero(int slot, Mask positive, int other) const {
        return (reads[slot] & bit(other)) && !(positive & bit(other));
    }

    bool adjacent(int outer, Mask outer_bits, int middle, Mask middle_bits,
                  Mask opposite_rank) const {
        return !reads_zero(outer, outer_bits, middle) &&
               !reads_zero(middle, middle_bits, outer) &&
               !(outer_bits & middle_bits & opposite_rank);
    }

    bool outer_comparison(int bottom, Mask bottom_bits, int top, Mask top_bits) const {
        return reads_zero(bottom, bottom_bits, top) || reads_zero(top, top_bits, bottom) ||
               (bottom_bits & top_bits & profile.rank_masks[1]);
    }
};

int main() {
    const std::array<std::array<int, 3>, 4> profiles{{
        {1, 2, 1}, {2, 2, 2}, {2, 3, 2}, {1, 2, 4},
    }};
    std::uint64_t total_embeddings = 0;
    std::uint64_t total_paths = 0;
    for (const auto& [bottom, middle, top] : profiles) {
        const Profile profile(bottom, middle, top);
        const auto graphs = profile.triangle_free_graphs();
        std::uint64_t paths = 0;
        std::uint64_t embeddings = 0;
        for (Mask shape : graphs) {
            for (bool reversed : {false, true}) {
                const Decoder decoder(profile, shape, reversed);
                paths += decoder.check_transitivity();
                for (Mask graph : graphs) {
                    decoder.check_embedding(graph);
                    ++embeddings;
                }
            }
        }
        std::cout << bottom << ',' << middle << ',' << top << ' '
                  << graphs.size() << " templates, " << embeddings << " embeddings, "
                  << paths << " paths\n" << std::flush;
        total_embeddings += embeddings;
        total_paths += paths;
    }
    std::cout << total_embeddings << " embeddings, " << total_paths << " paths overall\n";
}
