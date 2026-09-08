#!/usr/bin/env bash
# Check that the transcription of pasta_curves' AArch64 Pasta Montgomery routines is
# current: the vendored assembly and reference vectors match their recorded hashes, and
# regenerating the Lean files from them reproduces the committed files exactly.
#
# Run from the repository root; exits non-zero on violation.
set -euo pipefail
cd "$(dirname "$0")/.."

(cd CompElliptic/Asm/AArch64/vendor && shasum -a 256 -c SHA256SUMS)

python3 scripts/gen_aarch64_pasta_mul.py
git diff --exit-code -- \
  CompElliptic/Asm/AArch64/PastaMul.lean CompElliptic/Asm/AArch64/PastaMulVectors.lean
echo "AArch64 Pasta transcription: current."
