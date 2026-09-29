#!/usr/bin/env python3
"""Discover an exact weighted-clique certificate for A_2(12,4) <= 6.

SciPy/HiGHS is used only to discover cuts and floating-point dual weights.  The
output is rounded upward and accepted only after exact integer checks.  The
standalone proof/verify_upper_certificate.py does not depend on this program or
on SciPy.
"""

from __future__ import annotations

import argparse
import json
import math
from itertools import combinations
from pathlib import Path
from typing import List, Set

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import csr_matrix, lil_matrix, vstack


N = 12
T = 4
WORD_COUNT = 1 << N
DESCENDANT_COUNT = 1 << (N - T)
DENOMINATOR = 1_000_000


def descendants(word: int) -> Set[int]:
    bits = format(word, "0{}b".format(N))
    return {
        int("".join(bits[position] for position in kept), 2)
        for kept in combinations(range(N), N - T)
    }


def incidence_matrix(all_descendants: List[Set[int]]) -> csr_matrix:
    matrix = lil_matrix((DESCENDANT_COUNT, WORD_COUNT), dtype=float)
    for word, values in enumerate(all_descendants):
        for descendant in values:
            matrix[descendant, word] = 1
    return matrix.tocsr()


def clique_row(words: List[int]) -> csr_matrix:
    row = lil_matrix((1, WORD_COUNT), dtype=float)
    row[0, words] = 1
    return row.tocsr()


def maximum_weight_conflict_clique(
    support: np.ndarray, weights: np.ndarray, all_descendants: List[Set[int]]
) -> List[int]:
    # A conflict clique may not contain a compatible pair.  Compatibility here
    # means disjoint four-deletion descendant sets.
    compatible_pairs = []
    for left_index, left in enumerate(support):
        for right_index in range(left_index + 1, len(support)):
            right = support[right_index]
            if all_descendants[left].isdisjoint(all_descendants[right]):
                compatible_pairs.append((left_index, right_index))

    constraints = lil_matrix((len(compatible_pairs), len(support)), dtype=float)
    for row, (left, right) in enumerate(compatible_pairs):
        constraints[row, left] = 1
        constraints[row, right] = 1
    result = milp(
        -weights,
        integrality=np.ones(len(support)),
        bounds=Bounds(0, 1),
        constraints=LinearConstraint(constraints.tocsr(), -np.inf, 1),
        options={"time_limit": 60},
    )
    if result.status != 0 or result.x is None:
        raise RuntimeError("maximum-weight clique subproblem did not solve exactly")
    return [int(support[index]) for index in np.where(result.x > 0.5)[0]]


def exact_check(
    descendant_weights: List[int],
    clique_weights: List[int],
    cliques: List[List[int]],
    all_descendants: List[Set[int]],
) -> tuple[int, int]:
    total = sum(descendant_weights) + sum(clique_weights)
    if total >= 7 * DENOMINATOR:
        raise AssertionError("rounded dual objective is not strictly below 7")

    memberships = [[] for _ in range(WORD_COUNT)]
    for clique_index, clique in enumerate(cliques):
        if len(clique) != len(set(clique)):
            raise AssertionError("duplicate word in clique")
        for left, right in combinations(clique, 2):
            if all_descendants[left].isdisjoint(all_descendants[right]):
                raise AssertionError("purported cut is not a conflict clique")
        for word in clique:
            memberships[word].append(clique_index)

    minimum_coverage = 10**30
    for word, values in enumerate(all_descendants):
        coverage = sum(descendant_weights[value] for value in values)
        coverage += sum(clique_weights[index] for index in memberships[word])
        minimum_coverage = min(minimum_coverage, coverage)
        if coverage < DENOMINATOR:
            raise AssertionError("word {} is under-covered".format(word))
    return total, minimum_coverage


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--max-cuts", type=int, default=100)
    arguments = parser.parse_args()

    all_descendants = [descendants(word) for word in range(WORD_COUNT)]
    base = incidence_matrix(all_descendants)
    cuts: List[List[int]] = []
    rows: List[csr_matrix] = [base]

    for iteration in range(arguments.max_cuts + 1):
        matrix = vstack(rows, format="csr")
        relaxation = linprog(
            -np.ones(WORD_COUNT),
            A_ub=matrix,
            b_ub=np.ones(matrix.shape[0]),
            bounds=(0, 1),
            method="highs",
        )
        if relaxation.status != 0 or relaxation.x is None:
            raise RuntimeError("LP relaxation failed")
        value = -float(relaxation.fun)
        support = np.where(relaxation.x > 1e-8)[0]
        print(
            "iteration={} lp={:.12f} support={} cuts={}".format(
                iteration, value, len(support), len(cuts)
            ),
            flush=True,
        )
        if value < 7:
            break
        if iteration == arguments.max_cuts:
            raise RuntimeError("cut limit reached before LP objective fell below 7")

        clique = maximum_weight_conflict_clique(
            support, relaxation.x[support], all_descendants
        )
        clique_weight = sum(relaxation.x[word] for word in clique)
        if clique_weight <= 1 + 1e-7:
            raise RuntimeError("no violated conflict clique was found")
        print(
            "cut_size={} violation={:.12f}".format(
                len(clique), clique_weight - 1
            ),
            flush=True,
        )
        cuts.append(clique)
        rows.append(clique_row(clique))
    else:
        raise AssertionError("unreachable")

    dual = np.maximum(0, -relaxation.ineqlin.marginals)
    integer_weights = np.ceil(dual * DENOMINATOR - 1e-12).astype(np.int64)
    descendant_weights = [int(value) for value in integer_weights[:DESCENDANT_COUNT]]
    clique_weights = [int(value) for value in integer_weights[DESCENDANT_COUNT:]]
    total, minimum_coverage = exact_check(
        descendant_weights,
        clique_weights,
        cuts,
        all_descendants,
    )

    certificate = {
        "model": "ordinary_ordered_exact_deletions",
        "q": 2,
        "n": N,
        "t": T,
        "claimed_upper_bound": 6,
        "denominator": DENOMINATOR,
        "descendant_weights": {
            format(index, "08b"): weight
            for index, weight in enumerate(descendant_weights)
            if weight
        },
        "clique_cuts": [
            {
                "weight": weight,
                "words": [format(word, "012b") for word in clique],
            }
            for weight, clique in zip(clique_weights, cuts)
            if weight
        ],
        "total_weight_numerator": total,
        "minimum_word_coverage_numerator": minimum_coverage,
    }
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="ascii",
    )
    print("certificate={}".format(arguments.output))
    print("total_weight={}/{}".format(total, DENOMINATOR))
    print("minimum_word_coverage={}/{}".format(minimum_coverage, DENOMINATOR))
    print("EXACT_ROUNDED_CERTIFICATE=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
