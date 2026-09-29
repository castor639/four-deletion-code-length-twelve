#!/usr/bin/env python3
"""Adversarial checks that the exact verifier rejects damaged certificates."""

from __future__ import annotations

import copy
import json
import tempfile
from pathlib import Path

from verify_upper_certificate import verify


HERE = Path(__file__).resolve().parent


def expect_rejection(certificate: object, expected: str, label: str) -> None:
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "mutated.json"
        path.write_text(json.dumps(certificate), encoding="ascii")
        try:
            verify(path)
        except ValueError as error:
            if expected not in str(error):
                raise AssertionError(
                    "{} failed for the wrong reason: {}".format(label, error)
                ) from error
            print("{}=REJECTED".format(label))
            print("reason={}".format(error))
            return
    raise AssertionError("{} was incorrectly accepted".format(label))


def main() -> int:
    original = json.loads((HERE / "upper_certificate.json").read_text("ascii"))

    undercovered = copy.deepcopy(original)
    undercovered["descendant_weights"]["00000000"] -= 1
    expect_rejection(undercovered, "below", "UNDERCOVERAGE_MUTATION")

    nonclique = copy.deepcopy(original)
    nonclique["clique_cuts"][0]["words"][0] = "000000000000"
    expect_rejection(nonclique, "not a conflict clique", "NONCLIQUE_MUTATION")

    print("MUTATION_AUDIT=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
