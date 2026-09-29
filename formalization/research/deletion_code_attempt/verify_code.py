#!/usr/bin/env python3
"""Independent exact verifier for an ordinary deletion-correcting codebook."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
from typing import Dict, List, Set, Tuple


def exact_deletion_descendants(word: str, deletions: int) -> Set[str]:
    """Enumerate descendants by a keep/delete recursion, deduplicating strings."""
    descendants: Set[str] = set()

    def visit(position: int, deleted: int, kept: List[str]) -> None:
        if deleted > deletions:
            return
        remaining = len(word) - position
        if deleted + remaining < deletions:
            return
        if position == len(word):
            if deleted == deletions:
                descendants.add("".join(kept))
            return

        visit(position + 1, deleted + 1, kept)
        kept.append(word[position])
        visit(position + 1, deleted, kept)
        kept.pop()

    visit(0, 0, [])
    return descendants


def lcs_length(left: str, right: str) -> int:
    """Independent dynamic-programming check of common subsequence length."""
    previous = [0] * (len(right) + 1)
    for left_symbol in left:
        current = [0]
        for column, right_symbol in enumerate(right, start=1):
            if left_symbol == right_symbol:
                current.append(previous[column - 1] + 1)
            else:
                current.append(max(previous[column], current[-1]))
        previous = current
    return previous[-1]


def parse_codebook(path: Path, q: int, n: int) -> Tuple[bytes, List[str]]:
    raw = path.read_bytes()
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise ValueError("codebook is not ASCII") from error

    words = [line.strip() for line in text.splitlines() if line.strip()]
    if len(words) != len(set(words)):
        raise ValueError("codebook contains duplicate words")
    alphabet = {str(symbol) for symbol in range(q)}
    for line_number, word in enumerate(words, start=1):
        if len(word) != n:
            raise ValueError(
                "line {} has length {}, expected {}".format(
                    line_number, len(word), n
                )
            )
        invalid = set(word) - alphabet
        if invalid:
            raise ValueError(
                "line {} contains symbols outside alphabet: {}".format(
                    line_number, sorted(invalid)
                )
            )
    return raw, words


def verify(path: Path, q: int, n: int, t: int) -> int:
    if q > 10:
        raise ValueError("this fixed one-character encoding supports q <= 10")
    if not 1 <= t < n:
        raise ValueError("require 1 <= t < n")

    raw, words = parse_codebook(path, q, n)
    owners: Dict[str, str] = {}
    descendant_counts: Dict[str, int] = {}
    collisions: List[Tuple[str, str, str]] = []

    for word in words:
        descendants = exact_deletion_descendants(word, t)
        descendant_counts[word] = len(descendants)
        if any(len(descendant) != n - t for descendant in descendants):
            raise AssertionError("internal descendant-length error")
        for descendant in descendants:
            previous_owner = owners.get(descendant)
            if previous_owner is not None and previous_owner != word:
                collisions.append((previous_owner, word, descendant))
            else:
                owners[descendant] = word

    lcs_violations: List[Tuple[str, str, int]] = []
    pair_count = 0
    max_pairwise_lcs = 0
    threshold = n - t
    for left_index, left in enumerate(words):
        for right in words[left_index + 1 :]:
            pair_count += 1
            length = lcs_length(left, right)
            max_pairwise_lcs = max(max_pairwise_lcs, length)
            if length >= threshold:
                lcs_violations.append((left, right, length))

    digest = hashlib.sha256(raw).hexdigest()
    print("VERIFIER_MODEL=ordinary_ordered_exact_deletions")
    print("q={}".format(q))
    print("n={}".format(n))
    print("t={}".format(t))
    print("code_size={}".format(len(words)))
    print("codebook_sha256={}".format(digest))
    print("distinct_descendants={}".format(len(owners)))
    print(
        "descendant_count_range={}:{}".format(
            min(descendant_counts.values(), default=0),
            max(descendant_counts.values(), default=0),
        )
    )
    print("enumeration_collisions={}".format(len(collisions)))
    print("pair_count={}".format(pair_count))
    print("max_pairwise_lcs={}".format(max_pairwise_lcs))
    print("lcs_violations={}".format(len(lcs_violations)))

    if collisions:
        left, right, descendant = collisions[0]
        print(
            "first_collision={} {} {}".format(left, right, descendant)
        )
    if lcs_violations:
        left, right, length = lcs_violations[0]
        print("first_lcs_violation={} {} {}".format(left, right, length))

    if collisions or lcs_violations:
        print("VERIFICATION=FAIL")
        return 1
    print("VERIFICATION=PASS")
    return 0


def main() -> int:
    default_codebook = Path(__file__).with_name("codebook.txt")
    parser = argparse.ArgumentParser()
    parser.add_argument("--codebook", type=Path, default=default_codebook)
    parser.add_argument("--q", type=int, default=2)
    parser.add_argument("--n", type=int, default=12)
    parser.add_argument("--t", type=int, default=4)
    arguments = parser.parse_args()
    try:
        return verify(
            arguments.codebook, arguments.q, arguments.n, arguments.t
        )
    except (OSError, ValueError) as error:
        print("VERIFICATION=ERROR")
        print("error={}".format(error))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
