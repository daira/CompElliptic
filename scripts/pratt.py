#!/usr/bin/env python3
# Copyright (c) 2026 CompElliptic Contributors.
# Released under the Apache License, Version 2.0, or the MIT license, at your option,
# as described in the files LICENSE-APACHE and LICENSE-MIT.
# Authors: Daira-Emma Hopwood
"""
Common Lucas/Pratt primality-certificate machinery for the `CompElliptic/Fields/*.lean` field
generators (`gen_pasta.py`, `gen_jubjub.py`), in the style of CompPoly's `Fields/Secp256k1.lean`.

Factorization and primitive-root search are done by PARI/GP (fast); the emitted Lean uses
`(by pratt)` for small prime leaves (<= PRATT_MAX, where the in-Lean Pollard-rho factoring is
instant) and explicit recursive certificates for larger prime factors (where `by pratt` would
hang). Modular-exponentiation side-conditions are discharged by `reduce_mod_char; decide`, exactly
as Secp256k1 does for its 256-bit prime.

This module has no entry point of its own; the per-curve generators import `field_block`.
"""
import subprocess

PRATT_MAX = 10**9  # primes <= this are proven by `by pratt`; larger ones recurse explicitly.


def gp_info(n: int):
    """Return (primitive_root_mod_n, [(prime, exp), ...] factoring n-1)."""
    script = "\n".join([
        "default(parisizemax, 8*10^9);",
        f"print(lift(znprimroot({n})))",
        f"f = factor({n} - 1); for(i = 1, matsize(f)[1], print1(f[i,1], \":\", f[i,2], \" \")); print()",
        "quit",
    ]) + "\n"
    res = subprocess.run(["gp", "-q"], input=script, capture_output=True, text=True, timeout=1200)
    lines = [ln.strip() for ln in res.stdout.splitlines() if ln.strip()]
    # Parse defensively: the primitive root is the all-digits line; the factor list is the line with ':'.
    a = int(next(ln for ln in lines if ln.isdigit()))
    fline = next(ln for ln in lines if ":" in ln)
    facts = [(int(t.split(":")[0]), int(t.split(":")[1])) for t in fline.split()]
    return a, facts


def lean_pow(p: int, e: int) -> str:
    return str(p) if e == 1 else f"{p} ^ {e}"


def cert_tactics(n: int, ind: int) -> list[str]:
    """Lean tactics proving `Nat.Prime n` (goal assumed to be `Nat.Prime n`), indented `ind`."""
    a, facts = gp_info(n)
    pad = " " * ind
    powers = ", ".join(lean_pow(p, e) for p, e in facts)
    lines = [
        f"{pad}refine PrattCertificate'.out (p := {n}) ⟨{a}, (by reduce_mod_char), ?_⟩",
        f"{pad}refine .split [{powers}] (fun r hr => ?_) (by norm_num)",
        f"{pad}simp at hr",
        f"{pad}rcases hr with {' | '.join(['hr'] * len(facts))}",
        f"{pad}all_goals rw [hr]",
    ]
    for p, e in facts:
        if p <= PRATT_MAX:
            lines.append(f"{pad}· exact .prime {p} {e} _ (by pratt) "
                         f"(by reduce_mod_char; decide) (by norm_num)")
        else:
            lines.append(f"{pad}· refine .prime {p} {e} _ ?_ "
                         f"(by reduce_mod_char; decide) (by norm_num)")
            lines += cert_tactics(p, ind + 2)
    return lines


def theorem(name: str, card: int) -> str:
    body = "\n".join(cert_tactics(card, 2))
    return f"theorem {name}_is_prime : Nat.Prime {name}_CARD := by\n  unfold {name}_CARD\n{body}"


def field_block(name: str, card: int, fieldabbrev: str, doc: str) -> str:
    return (
        f"\n-- {doc}\n"
        f"@[reducible] def {name}_CARD : Nat := 0x{card:x}\n\n"
        f"abbrev {fieldabbrev} := ZMod {name}_CARD\n\n"
        f"{theorem(name, card)}\n\n"
        f"instance : Fact (Nat.Prime {name}_CARD) := ⟨{name}_is_prime⟩\n"
        f"instance : Field {fieldabbrev} := ZMod.instField {name}_CARD\n"
    )
