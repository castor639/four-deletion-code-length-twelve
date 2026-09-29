#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace {

#ifndef CODE_N
#define CODE_N 12
#endif
#ifndef CODE_T
#define CODE_T 4
#endif
#ifndef TARGET_SIZE
#define TARGET_SIZE 6
#endif

constexpr int n = CODE_N;
constexpr int t = CODE_T;
constexpr int target_size = TARGET_SIZE;
constexpr int descendant_length = n - t;
constexpr int word_count = 1 << n;
constexpr int descendant_count = 1 << descendant_length;

using WordSet = std::bitset<word_count>;

std::vector<int> deletion_descendants(int word) {
  std::set<int> unique;
  std::vector<int> deleted;
  const auto enumerate = [&](const auto& self, int next_position,
                             int deletions_left) -> void {
    if (deletions_left == 0) {
      int descendant = 0;
      std::size_t deleted_index = 0;
      for (int position = 0; position < n; ++position) {
        if (deleted_index < deleted.size() &&
            deleted[deleted_index] == position) {
          ++deleted_index;
          continue;
        }
        descendant = (descendant << 1) |
                     ((word >> (n - position - 1)) & 1);
      }
      unique.insert(descendant);
      return;
    }
    for (int position = next_position;
         position <= n - deletions_left; ++position) {
      deleted.push_back(position);
      self(self, position + 1, deletions_left - 1);
      deleted.pop_back();
    }
  };
  enumerate(enumerate, 0, t);
  return {unique.begin(), unique.end()};
}

std::vector<WordSet> build_conflicts() {
  std::array<std::vector<int>, descendant_count> owners;
  for (int word = 0; word < word_count; ++word) {
    for (int descendant : deletion_descendants(word)) {
      owners[descendant].push_back(word);
    }
  }

  std::vector<WordSet> conflicts(word_count);
  for (int word = 0; word < word_count; ++word) conflicts[word].set(word);
  for (const auto& bucket : owners) {
    WordSet bucket_words;
    for (int word : bucket) bucket_words.set(word);
    for (int word : bucket) conflicts[word] |= bucket_words;
  }
  return conflicts;
}

std::vector<int> members(const WordSet& words) {
  std::vector<int> result;
  result.reserve(words.count());
  for (int word = 0; word < word_count; ++word) {
    if (words.test(word)) result.push_back(word);
  }
  return result;
}

std::vector<int> randomized_greedy(const std::vector<WordSet>& conflicts,
                                   std::mt19937_64& rng) {
  WordSet available;
  available.set();
  std::vector<int> code;

  while (available.any()) {
    auto candidates = members(available);
    std::shuffle(candidates.begin(), candidates.end(), rng);
    if (candidates.size() > 320) candidates.resize(320);

    std::vector<std::pair<std::size_t, int>> scores;
    scores.reserve(candidates.size());
    for (int word : candidates) {
      scores.emplace_back((conflicts[word] & available).count(), word);
    }
    std::sort(scores.begin(), scores.end());
    const std::size_t restricted = std::min<std::size_t>(scores.size(), 8);
    std::uniform_int_distribution<std::size_t> choose(0, restricted - 1);
    const int selected = scores[choose(rng)].second;
    code.push_back(selected);
    available &= ~conflicts[selected];
  }
  return code;
}

bool find_independent_set(const std::vector<WordSet>& conflicts,
                          WordSet candidates, int needed,
                          std::vector<int>& answer,
                          std::uint64_t& nodes_left,
                          std::mt19937_64& rng) {
  if (needed == 0) return true;
  if (static_cast<int>(candidates.count()) < needed || nodes_left == 0) {
    return false;
  }

  auto choices = members(candidates);
  std::shuffle(choices.begin(), choices.end(), rng);
  std::stable_sort(choices.begin(), choices.end(), [&](int x, int y) {
    return (conflicts[x] & candidates).count() <
           (conflicts[y] & candidates).count();
  });

  for (int word : choices) {
    if (!candidates.test(word)) continue;
    if (nodes_left-- == 0) return false;
    answer.push_back(word);
    if (find_independent_set(conflicts, candidates & ~conflicts[word],
                             needed - 1, answer, nodes_left, rng)) {
      return true;
    }
    answer.pop_back();
    candidates.reset(word);
    if (static_cast<int>(candidates.count()) < needed) return false;
  }
  return false;
}

bool improve_by_exchange(const std::vector<WordSet>& conflicts,
                         std::vector<int>& code,
                         int remove_count,
                         std::mt19937_64& rng) {
  const int size = static_cast<int>(code.size());
  std::vector<int> mask(size, 0);
  std::fill(mask.end() - remove_count, mask.end(), 1);

  std::vector<std::vector<int>> removal_masks;
  do {
    removal_masks.push_back(mask);
  } while (std::next_permutation(mask.begin(), mask.end()));
  std::shuffle(removal_masks.begin(), removal_masks.end(), rng);
  const std::size_t attempt_limit =
      remove_count == 1 ? removal_masks.size()
                        : std::min<std::size_t>(30, removal_masks.size());

  for (std::size_t attempt = 0; attempt < attempt_limit; ++attempt) {
    const auto& removal_mask = removal_masks[attempt];
    WordSet candidates;
    candidates.set();
    std::vector<int> retained;
    for (int i = 0; i < size; ++i) {
      if (removal_mask[i]) continue;
      retained.push_back(code[i]);
      candidates &= ~conflicts[code[i]];
    }

    std::vector<int> replacements;
    std::uint64_t nodes_left = remove_count == 1 ? 5000 : 20000;
    if (find_independent_set(conflicts, candidates, remove_count + 1,
                             replacements, nodes_left, rng)) {
      retained.insert(retained.end(), replacements.begin(), replacements.end());
      code = std::move(retained);
      return true;
    }
  }
  return false;
}

bool valid_code(const std::vector<WordSet>& conflicts,
                const std::vector<int>& code) {
  for (std::size_t i = 0; i < code.size(); ++i) {
    for (std::size_t j = i + 1; j < code.size(); ++j) {
      if (conflicts[code[i]].test(code[j])) return false;
    }
  }
  return true;
}

std::vector<int> load_code(const std::string& path) {
  std::ifstream input(path);
  if (!input) throw std::runtime_error("cannot open seed codebook: " + path);
  std::vector<int> code;
  std::string line;
  while (std::getline(input, line)) {
    if (line.empty()) continue;
    if (line.size() != n ||
        line.find_first_not_of("01") != std::string::npos) {
      throw std::runtime_error("invalid seed codeword: " + line);
    }
    code.push_back(std::stoi(line, nullptr, 2));
  }
  return code;
}

bool perturb_or_improve(const std::vector<WordSet>& conflicts,
                        std::vector<int>& code, int remove_count,
                        std::mt19937_64& rng) {
  std::vector<int> indices(code.size());
  std::iota(indices.begin(), indices.end(), 0);
  std::shuffle(indices.begin(), indices.end(), rng);
  indices.resize(remove_count);
  std::sort(indices.begin(), indices.end());

  std::vector<bool> removed(code.size(), false);
  for (int index : indices) removed[index] = true;
  std::vector<int> retained;
  std::vector<int> old_removed;
  WordSet candidates;
  candidates.set();
  for (std::size_t i = 0; i < code.size(); ++i) {
    if (removed[i]) {
      old_removed.push_back(code[i]);
    } else {
      retained.push_back(code[i]);
      candidates &= ~conflicts[code[i]];
    }
  }

  std::vector<int> replacements;
  std::uint64_t improve_nodes = 100000;
  if (find_independent_set(conflicts, candidates, remove_count + 1,
                           replacements, improve_nodes, rng)) {
    retained.insert(retained.end(), replacements.begin(), replacements.end());
    code = std::move(retained);
    return true;
  }

  // Move to a different code of the same size.  Forbidding one randomly
  // removed word prevents the recursive search from simply restoring the
  // identical codebook.
  candidates.reset(old_removed.front());
  replacements.clear();
  std::uint64_t plateau_nodes = 30000;
  if (find_independent_set(conflicts, candidates, remove_count, replacements,
                           plateau_nodes, rng)) {
    retained.insert(retained.end(), replacements.begin(), replacements.end());
    code = std::move(retained);
  }
  return false;
}

void print_code(const std::vector<int>& code) {
  std::vector<int> sorted = code;
  std::sort(sorted.begin(), sorted.end());
  for (int word : sorted) {
    std::cout << std::bitset<n>(word) << '\n';
  }
}

}  // namespace

int main(int argc, char** argv) {
  int seconds = 300;
  std::uint64_t seed = 0xD3E7EULL;
  if (argc >= 2) seconds = std::stoi(argv[1]);
  if (argc >= 3) seed = std::stoull(argv[2]);

  const auto conflicts = build_conflicts();
  std::mt19937_64 rng(seed);
  std::vector<int> best;
  std::uint64_t runs = 0;
  const auto start = std::chrono::steady_clock::now();

  if (argc >= 4) {
    auto code = load_code(argv[3]);
    if (!valid_code(conflicts, code)) {
      std::cerr << "seed codebook is not independent\n";
      return 2;
    }
    best = code;
    std::uniform_int_distribution<int> remove_count(2, 4);
    while (std::chrono::duration_cast<std::chrono::seconds>(
               std::chrono::steady_clock::now() - start)
               .count() < seconds && code.size() < target_size) {
      ++runs;
      perturb_or_improve(conflicts, code, remove_count(rng), rng);
      if (!valid_code(conflicts, code)) {
        std::cerr << "local perturbation produced an invalid code\n";
        return 2;
      }
      if (code.size() > best.size()) {
        best = code;
        const auto elapsed = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start).count();
        std::cerr << "best=" << best.size() << " perturbations=" << runs
                  << " elapsed_seconds=" << elapsed << '\n';
      }
    }
    std::cerr << "final_best=" << best.size() << " perturbations=" << runs
              << " seed=" << seed << '\n';
    print_code(best);
    return best.size() >= target_size ? 0 : 1;
  }

  while (std::chrono::duration_cast<std::chrono::seconds>(
             std::chrono::steady_clock::now() - start)
             .count() < seconds) {
    ++runs;
    auto code = randomized_greedy(conflicts, rng);
    if (code.size() + 2 >= target_size) {
      bool changed = improve_by_exchange(conflicts, code, 1, rng);
      if (changed && code.size() < target_size) {
        changed = improve_by_exchange(conflicts, code, 1, rng);
      }
      if (!changed && code.size() + 1 >= target_size) {
        changed = improve_by_exchange(conflicts, code, 2, rng);
      }
    }

    if (code.size() > best.size()) {
      if (!valid_code(conflicts, code)) {
        std::cerr << "internal conflict-graph validation failed\n";
        return 2;
      }
      best = code;
      const auto elapsed = std::chrono::duration<double>(
          std::chrono::steady_clock::now() - start).count();
      std::cerr << "best=" << best.size() << " runs=" << runs
                << " elapsed_seconds=" << std::fixed << std::setprecision(3)
                << elapsed << '\n';
      if (best.size() >= target_size) break;
    }
  }

  std::cerr << "final_best=" << best.size() << " runs=" << runs
            << " seed=" << seed << '\n';
  print_code(best);
  return best.size() >= target_size ? 0 : 1;
}
