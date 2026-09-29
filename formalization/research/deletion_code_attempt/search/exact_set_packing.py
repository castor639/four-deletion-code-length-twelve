#!/usr/bin/env python3
"""CP-SAT set-packing search for binary ordinary deletion codes.

This is a search program, not the independent verifier.  It requires OR-Tools.
"""

from __future__ import annotations

import argparse
import sys
from itertools import combinations
from pathlib import Path
from typing import List, Set

from ortools.sat.python import cp_model


def descendants(word: int, n: int, t: int) -> Set[int]:
    bits = tuple((word >> (n - position - 1)) & 1 for position in range(n))
    result: Set[int] = set()
    for kept_positions in combinations(range(n), n - t):
        descendant = 0
        for position in kept_positions:
            descendant = (descendant << 1) | bits[position]
        result.add(descendant)
    return result


def read_seed(path: Path, n: int) -> List[int]:
    result = []
    for line_number, line in enumerate(path.read_text(encoding="ascii").splitlines(), 1):
        word = line.strip()
        if not word:
            continue
        if len(word) != n or set(word) - {"0", "1"}:
            raise ValueError("invalid seed codeword on line {}".format(line_number))
        result.append(int(word, 2))
    return result


class TargetStopper(cp_model.CpSolverSolutionCallback):
    def __init__(self, variables: List[cp_model.IntVar], target: int) -> None:
        super().__init__()
        self.variables = variables
        self.target = target
        self.best_words: List[int] = []

    def on_solution_callback(self) -> None:
        words = [index for index, var in enumerate(self.variables) if self.Value(var)]
        if len(words) > len(self.best_words):
            self.best_words = words
            print(
                "incumbent_size={} wall_seconds={:.3f}".format(
                    len(words), self.WallTime()
                ),
                file=sys.stderr,
                flush=True,
            )
        if len(words) >= self.target:
            self.StopSearch()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=12)
    parser.add_argument("--t", type=int, default=4)
    parser.add_argument("--target", type=int, default=6)
    parser.add_argument("--seconds", type=float, default=300.0)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--random-seed", type=int, default=489)
    parser.add_argument("--seed-codebook", type=Path)
    arguments = parser.parse_args()

    if not 1 <= arguments.t < arguments.n:
        parser.error("require 1 <= t < n")
    word_count = 1 << arguments.n
    output_count = 1 << (arguments.n - arguments.t)
    owners: List[List[int]] = [[] for _ in range(output_count)]
    for word in range(word_count):
        for descendant in descendants(word, arguments.n, arguments.t):
            owners[descendant].append(word)

    model = cp_model.CpModel()
    selected = [model.NewBoolVar("x{}".format(word)) for word in range(word_count)]
    for bucket in owners:
        model.AddAtMostOne(selected[word] for word in bucket)
    model.Maximize(sum(selected))

    if arguments.seed_codebook:
        seed_words = set(read_seed(arguments.seed_codebook, arguments.n))
        for word, variable in enumerate(selected):
            model.AddHint(variable, int(word in seed_words))

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = arguments.seconds
    solver.parameters.num_search_workers = arguments.workers
    solver.parameters.random_seed = arguments.random_seed
    solver.parameters.symmetry_level = 2
    callback = TargetStopper(selected, arguments.target)
    status = solver.Solve(model, callback)
    words = callback.best_words
    print(
        "status={} best_size={} best_bound={} wall_seconds={:.3f}".format(
            solver.StatusName(status),
            len(words),
            solver.BestObjectiveBound(),
            solver.WallTime(),
        ),
        file=sys.stderr,
    )
    for word in words:
        print(format(word, "0{}b".format(arguments.n)))
    return 0 if len(words) >= arguments.target else 1


if __name__ == "__main__":
    raise SystemExit(main())
