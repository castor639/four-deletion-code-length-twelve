#!/usr/bin/env python3
"""Export the checked JSON certificate as transparent Lean data."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def lean_list(values: list[int], indent: str = "  ") -> str:
    chunks = []
    width = 12
    for start in range(0, len(values), width):
        chunks.append(indent + ", ".join(str(value) for value in values[start:start + width]))
    return "[\n" + ",\n".join(chunks) + "\n]"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("output", type=Path)
    arguments = parser.parse_args()
    data = json.loads(arguments.certificate.read_text(encoding="ascii"))

    weights = [0] * 256
    for descendant, weight in data["descendant_weights"].items():
        weights[int(descendant, 2)] = weight

    cut_lines = []
    for cut in data["clique_cuts"]:
        words = [int(word, 2) for word in cut["words"]]
        cut_lines.append(
            "  ({}, {})".format(cut["weight"], lean_list(words, indent="    "))
        )

    lower_words = [
        int(word, 2)
        for word in Path(arguments.certificate.parent.parent / "codebook.txt")
        .read_text(encoding="ascii")
        .splitlines()
        if word
    ]
    text = """import DeletionCodes.Basic

/-!
# Transparent certificate data for A_2(12,4) = 6

Generated from `research/deletion_code_attempt/proof/upper_certificate.json`.
The theorem module checks these values inside Lean; this file introduces no
axioms and contains no proof.
-/

namespace DeletionCodes.Conjectures.DeletionCode124

def certificateDenominator : Nat := 1000000

def descendantWeights : List Nat := {weights}

def cliqueCuts : List (Nat × List Nat) := [
{cuts}
]

def lowerCode : List Nat := {lower}

end DeletionCodes.Conjectures.DeletionCode124
""".format(
        weights=lean_list(weights),
        cuts=",\n".join(cut_lines),
        lower=lean_list(lower_words),
    )
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
