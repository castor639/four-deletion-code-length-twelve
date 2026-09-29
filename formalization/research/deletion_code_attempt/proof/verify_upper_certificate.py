#!/usr/bin/env python3
"""Dependency-free exact checker for the A_2(12,4) upper certificate."""

from __future__ import annotations

import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path
from typing import Dict, List, Set


def exact_descendants(word: str, deletions: int) -> Set[str]:
    """Independent keep/delete recursion, including repeated-symbol cases."""
    result: Set[str] = set()

    def visit(position: int, deleted: int, kept: List[str]) -> None:
        if deleted > deletions:
            return
        remaining = len(word) - position
        if deleted + remaining < deletions:
            return
        if position == len(word):
            if deleted == deletions:
                result.add("".join(kept))
            return
        visit(position + 1, deleted + 1, kept)
        kept.append(word[position])
        visit(position + 1, deleted, kept)
        kept.pop()

    visit(0, 0, [])
    return result


def parse_word(word: object, length: int, label: str) -> str:
    if not isinstance(word, str) or len(word) != length or set(word) - {"0", "1"}:
        raise ValueError("invalid {} word: {!r}".format(label, word))
    return word


def reject_duplicate_keys(pairs: List[tuple[str, object]]) -> Dict[str, object]:
    result: Dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key: {}".format(key))
        result[key] = value
    return result


def verify(path: Path) -> int:
    raw = path.read_bytes()
    certificate = json.loads(
        raw.decode("ascii"), object_pairs_hook=reject_duplicate_keys
    )
    if certificate.get("model") != "ordinary_ordered_exact_deletions":
        raise ValueError("wrong model")
    q = certificate.get("q")
    n = certificate.get("n")
    t = certificate.get("t")
    upper = certificate.get("claimed_upper_bound")
    denominator = certificate.get("denominator")
    if (q, n, t, upper) != (2, 12, 4, 6):
        raise ValueError("certificate has wrong parameters")
    if not isinstance(denominator, int) or denominator <= 0:
        raise ValueError("invalid denominator")

    descendant_weights = [0] * (1 << (n - t))
    sparse_weights = certificate.get("descendant_weights")
    if not isinstance(sparse_weights, dict):
        raise ValueError("descendant_weights must be an object")
    for raw_descendant, weight in sparse_weights.items():
        descendant = parse_word(raw_descendant, n - t, "descendant")
        if not isinstance(weight, int) or weight < 0:
            raise ValueError("invalid descendant weight")
        descendant_weights[int(descendant, 2)] = weight

    cuts = certificate.get("clique_cuts")
    if not isinstance(cuts, list):
        raise ValueError("clique_cuts must be a list")
    clique_weights: List[int] = []
    cliques: List[List[int]] = []
    for cut in cuts:
        if not isinstance(cut, dict):
            raise ValueError("invalid clique cut")
        weight = cut.get("weight")
        words = cut.get("words")
        if not isinstance(weight, int) or weight < 0 or not isinstance(words, list):
            raise ValueError("invalid clique cut fields")
        parsed = [int(parse_word(word, n, "code"), 2) for word in words]
        if len(parsed) != len(set(parsed)):
            raise ValueError("clique contains duplicate codewords")
        clique_weights.append(weight)
        cliques.append(parsed)

    all_descendants = [
        exact_descendants(format(word, "0{}b".format(n)), t)
        for word in range(1 << n)
    ]

    checked_pairs = 0
    memberships: List[List[int]] = [[] for _ in range(1 << n)]
    for clique_index, clique in enumerate(cliques):
        for left, right in combinations(clique, 2):
            checked_pairs += 1
            if all_descendants[left].isdisjoint(all_descendants[right]):
                raise ValueError(
                    "cut {} is not a conflict clique: {} and {} are compatible".format(
                        clique_index, format(left, "012b"), format(right, "012b")
                    )
                )
        for word in clique:
            memberships[word].append(clique_index)

    minimum_coverage = None
    for word, descendants in enumerate(all_descendants):
        coverage = sum(descendant_weights[int(value, 2)] for value in descendants)
        coverage += sum(clique_weights[index] for index in memberships[word])
        if minimum_coverage is None or coverage < minimum_coverage:
            minimum_coverage = coverage
        if coverage < denominator:
            raise ValueError(
                "word {} has coverage {}, below {}".format(
                    format(word, "012b"), coverage, denominator
                )
            )

    total_weight = sum(descendant_weights) + sum(clique_weights)
    if total_weight >= 7 * denominator:
        raise ValueError("weighted upper bound is not strictly below 7")
    if certificate.get("total_weight_numerator") != total_weight:
        raise ValueError("stored total weight does not match")
    if certificate.get("minimum_word_coverage_numerator") != minimum_coverage:
        raise ValueError("stored minimum coverage does not match")

    print("CERTIFICATE_MODEL=weighted_deletion_packing_with_conflict_cliques")
    print("q={}".format(q))
    print("n={}".format(n))
    print("t={}".format(t))
    print("certificate_sha256={}".format(hashlib.sha256(raw).hexdigest()))
    print("nonzero_descendant_weights={}".format(sum(weight > 0 for weight in descendant_weights)))
    print("clique_cuts={}".format(len(cliques)))
    print("clique_pairs_checked={}".format(checked_pairs))
    print("words_covered={}".format(len(all_descendants)))
    print("minimum_coverage={}/{}".format(minimum_coverage, denominator))
    print("total_weight={}/{}".format(total_weight, denominator))
    print("strictly_below_7={}".format(total_weight < 7 * denominator))
    print("PROVED_UPPER_BOUND=A_2(12,4)<=6")
    print("UPPER_CERTIFICATE=PASS")
    return 0


def main() -> int:
    default = Path(__file__).with_name("upper_certificate.json")
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, default=default)
    arguments = parser.parse_args()
    try:
        return verify(arguments.certificate)
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print("UPPER_CERTIFICATE=ERROR")
        print("error={}".format(error))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
