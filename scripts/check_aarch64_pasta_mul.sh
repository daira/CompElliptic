#!/usr/bin/env bash
# Check that the transcription of pasta_curves' AArch64 Pasta Montgomery routines is
# current: the vendored assembly and reference vectors match their recorded hashes,
# regenerating the Lean files from them reproduces the committed files exactly, and the
# generated parts of the proofs in PastaMulSpec.lean are the ones the generator produces.
#
# Run from the repository root; exits non-zero on violation.
set -euo pipefail
cd "$(dirname "$0")/.."

(cd CompElliptic/Asm/AArch64/vendor && shasum -a 256 -c SHA256SUMS)

python3 scripts/gen_aarch64_pasta_mul.py
git diff --exit-code -- \
  CompElliptic/Asm/AArch64/PastaMul.lean CompElliptic/Asm/AArch64/PastaMulVectors.lean
python3 scripts/gen_aarch64_pasta_mul.py --check-spec CompElliptic/Asm/AArch64/PastaMulSpec.lean
echo "AArch64 Pasta transcription: current."
