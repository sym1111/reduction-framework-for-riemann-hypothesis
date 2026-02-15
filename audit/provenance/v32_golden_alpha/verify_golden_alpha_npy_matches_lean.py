#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit-grade check: the stored golden `.npy` alpha artifact matches the Lean literal
in `LeanV32/GoldenAlphaWitness.lean` *bitwise* (complex128 payload).

This avoids "local file is truth" claims by producing:
  - SHA256 hashes of both artifacts
  - exact elementwise equality check (IEEE-754 bits)
  - mismatch location/details (if any)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import struct
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import List, Optional, Tuple

import numpy as np


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


_LEAN_COMPLEX_MK_RE = re.compile(
    r"Complex\.mk\s*"
    r"\(\(\s*([+-]?\d+)\s*:\s*Real\s*\)\s*/\s*([0-9]+)\s*\)\s*"
    r"\(\(\s*([+-]?\d+)\s*:\s*Real\s*\)\s*/\s*([0-9]+)\s*\)",
)


@dataclass(frozen=True)
class LeanComplexRatio:
    re_num: int
    re_den: int
    im_num: int
    im_den: int

    def to_complex128(self) -> np.complex128:
        re_val = float(Fraction(self.re_num, self.re_den))
        im_val = float(Fraction(self.im_num, self.im_den))
        return np.complex128(re_val + 1j * im_val)


def parse_lean_golden_alpha_vec(lean_path: Path) -> List[LeanComplexRatio]:
    text = lean_path.read_text(encoding="utf-8", errors="ignore")
    out: List[LeanComplexRatio] = []
    for m in _LEAN_COMPLEX_MK_RE.finditer(text):
        re_num, re_den, im_num, im_den = (int(m.group(i)) for i in range(1, 5))
        out.append(LeanComplexRatio(re_num=re_num, re_den=re_den, im_num=im_num, im_den=im_den))
    return out


def complex128_bits(z: np.complex128) -> Tuple[int, int]:
    # Returns (re_bits, im_bits) as uint64.
    b = struct.pack("<dd", float(z.real), float(z.imag))
    re_bits, im_bits = struct.unpack("<QQ", b)
    return int(re_bits), int(im_bits)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--npy",
        default=r"audit/provenance/v32_golden_alpha/alphas_golden_R0_scaled_r0.9_M2048_K160_pad1024_theta13.9804951740.npy",
        help="Path to the golden alpha .npy file (complex128, length 160).",
    )
    ap.add_argument(
        "--lean",
        default=r"audit/formalization/lean/LeanV32/GoldenAlphaWitness.lean",
        help="Path to Lean file containing `goldenAlphaVec` literals.",
    )
    ap.add_argument(
        "--json-out",
        default="",
        help="Optional path to write a JSON report.",
    )
    args = ap.parse_args()

    npy_path = Path(args.npy)
    lean_path = Path(args.lean)

    ratios = parse_lean_golden_alpha_vec(lean_path)
    lean_count = len(ratios)

    arr_lean = np.array([r.to_complex128() for r in ratios], dtype=np.complex128)
    arr_npy = np.load(npy_path)
    arr_npy = np.asarray(arr_npy, dtype=np.complex128)

    report = {
        "npy_path": str(npy_path),
        "npy_sha256": sha256_file(npy_path),
        "npy_dtype": str(arr_npy.dtype),
        "npy_shape": list(arr_npy.shape),
        "lean_path": str(lean_path),
        "lean_sha256": sha256_file(lean_path),
        "parsed_complex_mk_count": lean_count,
        "expected_len": 160,
        "all_equal": False,
        "first_mismatch": None,
    }

    ok = True
    if arr_npy.ndim != 1 or arr_npy.shape[0] != 160:
        ok = False
        report["first_mismatch"] = {
            "kind": "shape",
            "npy_shape": list(arr_npy.shape),
            "expected_shape": [160],
        }
    elif lean_count != 160:
        ok = False
        report["first_mismatch"] = {
            "kind": "parse_count",
            "parsed_count": lean_count,
            "expected_count": 160,
        }
    else:
        # Bitwise equality check (IEEE-754 payload).
        for i in range(160):
            a = np.complex128(arr_lean[i])
            b = np.complex128(arr_npy[i])
            if complex128_bits(a) != complex128_bits(b):
                ok = False
                report["first_mismatch"] = {
                    "kind": "value",
                    "index": i,
                    "lean": {
                        "value": f"{a.real:.17g}{a.imag:+.17g}j",
                        "bits": list(complex128_bits(a)),
                    },
                    "npy": {
                        "value": f"{b.real:.17g}{b.imag:+.17g}j",
                        "bits": list(complex128_bits(b)),
                    },
                }
                break

    report["all_equal"] = ok

    out_json = json.dumps(report, indent=2, ensure_ascii=False)
    print(out_json)

    if args.json_out:
        Path(args.json_out).write_text(out_json + "\n", encoding="utf-8")

    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
