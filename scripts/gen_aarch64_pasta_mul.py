#!/usr/bin/env python3
"""Generate the Lean transcription of pasta_curves' AArch64 Pasta Montgomery routines.

Reads the vendored `CompElliptic/Asm/AArch64/vendor/pasta_mul-armv8.S` and writes

- `CompElliptic/Asm/AArch64/PastaMul.lean`: each routine as a Lean definition over the
  instruction semantics of `CompElliptic.Asm.AArch64.Semantics`, one `let` per
  instruction, in the assembly's order, with the instruction as a trailing comment;
- `CompElliptic/Asm/AArch64/PastaMulVectors.lean`: one kernel-checked example per line of
  `vendor/pasta_mul-armv8-vectors.txt`, the outputs of the real routines on an Apple
  M-series machine.

The transcription is deliberately mechanical. Registers become Lean variables of the
same name, rebound by each instruction that writes them. Loads through an argument
pointer become reads of that argument's limbs; stores through the output pointer bind
the result limbs; the stack frame, the return address, and the pointer-authentication
words are not modelled, and the script checks that no instruction depends on them
(a register restored from the frame is treated as unknown, and reading an unknown
register is an error). The `bl` to the shared reduction helper becomes a call of the
helper's own definition, after which the registers the helper clobbers are unknown.

A binding that nothing later reads is not emitted. For a load this records that the
assembly reads a limb it never uses (it hard-codes `p[2] = 0` and `p[3] = 2^62`), and
the dropped load is left as a comment; for a carry flag it is an ordinary unread flag
write. A computed register that is never read would be dead code in the routine and is
reported as an error, since none is expected.

Run from the repository root:

    python3 scripts/gen_aarch64_pasta_mul.py

`scripts/check_aarch64_pasta_mul.sh` regenerates and fails if the output differs from
the committed files. Python 3.9+; stdlib only.
"""
import re
import sys
import textwrap
from pathlib import Path

ASM = Path("CompElliptic/Asm/AArch64/vendor/pasta_mul-armv8.S")
VECTORS = Path("CompElliptic/Asm/AArch64/vendor/pasta_mul-armv8-vectors.txt")
OUT_PROGRAM = Path("CompElliptic/Asm/AArch64/PastaMul.lean")
OUT_VECTORS = Path("CompElliptic/Asm/AArch64/PastaMulVectors.lean")

HEADER = """/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
"""

HELPER_LABEL = "L$pasta_curves_mul_by_1_mont_pasta"

# Code longer than this does not set the instruction-comment column (see `Routine.text`).
COMMENT_COLUMN_MAX = 40

# Registers the helper writes without restoring; after a `bl` they hold nothing the
# caller may read. `x5`-`x8` are also written, to the modulus limbs, and are rebound.
HELPER_CLOBBERS = ["x3", "x9", "x14", "x15", "x17"]

ROUTINES = [
    # (label, Lean name, docstring, pointer arguments in register order, inv register)
    ("_pasta_curves_mul_mont_pasta", "mulMont",
     "`_pasta_curves_mul_mont_pasta`: Montgomery multiplication, `lhs * rhs * 2^-256 mod p`, "
     "with the result stored through `x0`.",
     [("x1", "lhs"), ("x2", "rhs"), ("x3", "modulus")], "x4"),
    ("_pasta_curves_sqr_mont_pasta", "sqrMont",
     "`_pasta_curves_sqr_mont_pasta`: Montgomery squaring, `value^2 * 2^-256 mod p`.",
     [("x1", "value"), ("x2", "modulus")], "x3"),
    ("_pasta_curves_from_mont_pasta", "fromMont",
     "`_pasta_curves_from_mont_pasta`: conversion out of Montgomery form, "
     "`value * 2^-256 mod p`.",
     [("x1", "value"), ("x2", "modulus")], "x3"),
]


def tokenize(rest):
    return re.findall(r"\[[^\]]*\]!?|[^,\s]+", rest)


def parse(path):
    """The instruction list and the label table; directives and comments dropped."""
    ins, labels = [], {}
    for line in path.read_text().splitlines():
        text = line.split("//")[0].strip()
        if not text or text.startswith("."):
            continue
        if text.endswith(":"):
            labels[text[:-1]] = len(ins)
            continue
        m = re.match(r"(\S+)\s*(.*)", text)
        assert m is not None
        ins.append((m.group(1), tokenize(m.group(2)), re.sub(r"\s+", " ", text)))
    return ins, labels


def imm(tok):
    """An immediate operand such as `#62` or `8*1`, as an integer."""
    s = tok.lstrip("#")
    if not re.fullmatch(r"-?[0-9]+(\*[0-9]+)?", s):
        raise ValueError(f"unexpected immediate {tok}")
    return eval(s)


class Emitter:
    """Transcribes one routine, from its label to its `ret`, into Lean `let` bindings."""

    def __init__(self, ins, labels, helper_name):
        self.ins, self.labels, self.helper_name = ins, labels, helper_name
        self.entries = []   # dicts: name, expr, comment, reads, load (bool)
        self.ptrs = {}      # register -> argument name it points to
        self.known = set()  # names holding a value the program may read
        self.outputs = {}   # output limb index -> bound name
        self.cur_reads = set()

    # -- operands ----------------------------------------------------------------

    def read(self, tok):
        if tok == "xzr":
            return "0"
        if tok.startswith("#"):
            return str(imm(tok))
        if tok in self.ptrs:
            raise ValueError(f"{tok} is a pointer, read as a value")
        if tok not in self.known:
            raise ValueError(f"{tok} read before being written")
        self.cur_reads.add(tok)
        return tok

    def bind(self, name, expr, comment, reads=None, load=False):
        if name == "xzr":
            return
        self.ptrs.pop(name, None)
        self.known.add(name)
        self.entries.append(dict(name=name, expr=expr, comment=comment,
                                 reads=set(self.cur_reads) if reads is None else set(reads),
                                 load=load))

    def mem(self, tok):
        """(base register, byte offset) of a memory operand, or None for the frame."""
        inner = tok.strip("!").strip("[]")
        parts = inner.split(",")
        base = parts[0]
        off = imm(parts[1]) if len(parts) > 1 else 0
        if base in ("sp", "x29"):
            return None
        return base, off

    def limb(self, base, off):
        if base not in self.ptrs:
            raise ValueError(f"load through {base}, which is not an argument pointer")
        if off % 8:
            raise ValueError(f"unaligned offset {off}")
        return f"{self.ptrs[base]}.l{off // 8}"

    # -- instructions --------------------------------------------------------------

    def step(self, op, t, text):
        self.cur_reads = set()
        if op in ("ldp", "ldr"):
            if len(t) == 3 and op == "ldr":  # post-indexed frame release
                return
            m = self.mem(t[-1])
            if m is None:  # restore from the frame: the value is not modelled
                for r in t[:-1]:
                    self.known.discard(r)
                    self.ptrs.pop(r, None)
                return
            base, off = m
            for i, r in enumerate(t[:-1]):
                self.bind(r, self.limb(base, off + 8 * i), text, reads=(), load=True)
        elif op in ("stp", "str"):
            m = self.mem(t[-1])
            if m is None:  # spill to the frame
                return
            base, off = m
            if self.ptrs.get(base) != "out":
                raise ValueError(f"store through {base}, which is not the output pointer")
            for i, r in enumerate(t[:-1]):
                idx = off // 8 + i
                self.cur_reads = set()
                self.bind(f"out{idx}", self.read(r), text)
                self.outputs[idx] = f"out{idx}"
        elif op == "add":
            if t[1] == "sp":  # frame pointer setup
                return
            raise ValueError(f"unexpected add: {text}")
        elif op == "mov":
            self.bind(t[0], self.read(t[1]), text)
        elif op == "mul":
            self.bind(t[0], f"mulLo {self.read(t[1])} {self.read(t[2])}", text)
        elif op == "umulh":
            self.bind(t[0], f"umulh {self.read(t[1])} {self.read(t[2])}", text)
        elif op == "lsl":
            self.bind(t[0], f"lsl {self.read(t[1])} {imm(t[2])}", text)
        elif op == "lsr":
            self.bind(t[0], f"lsr {self.read(t[1])} {imm(t[2])}", text)
        elif op in ("adds", "adcs", "adc"):
            cin = "0" if op == "adds" else self.read("c")
            expr = f"addc {self.read(t[1])} {self.read(t[2])} {cin}"
            if op == "adc":
                self.bind(t[0], f"({expr}).1", text)
            else:
                self.bind("s", expr, text)
                self.bind(t[0], "s.1", text, reads=("s",))
                self.bind("c", "s.2", text, reads=("s",))
        elif op in ("subs", "sbcs"):
            cin = "1" if op == "subs" else self.read("c")
            expr = f"subc {self.read(t[1])} {self.read(t[2])} {cin}"
            if t[0] == "xzr":
                self.bind("c", f"({expr}).2", text)
            else:
                self.bind("s", expr, text)
                self.bind(t[0], "s.1", text, reads=("s",))
                self.bind("c", "s.2", text, reads=("s",))
        elif op == "csel":
            if t[3] != "lo":
                raise ValueError(f"unexpected condition: {text}")
            self.bind(t[0], f"cselLo {self.read('c')} {self.read(t[1])} {self.read(t[2])}", text)
        elif op == "bl":
            if t[0] != HELPER_LABEL:
                raise ValueError(f"unexpected call: {text}")
            if self.ptrs.get("x2") != "modulus":
                raise ValueError("helper called without the modulus pointer in x2")
            args = ", ".join(self.read(r) for r in ("x10", "x11", "x12", "x13"))
            self.bind("r", f"{self.helper_name} ⟨{args}⟩ modulus {self.read('x4')}", text)
            for i, r in enumerate(("x10", "x11", "x12", "x13")):
                self.bind(r, f"r.l{i}", "helper output", reads=("r",))
            for i, r in enumerate(("x5", "x6", "x7", "x8")):
                self.bind(r, f"modulus.l{i}", "loaded by the helper", reads=(), load=True)
            for r in HELPER_CLOBBERS:
                self.known.discard(r)
                self.ptrs.pop(r, None)
            self.known.discard("c")
        else:
            raise ValueError(f"unhandled instruction: {text}")

    def run(self, start):
        pc = start
        while True:
            op, t, text = self.ins[pc]
            if op == "ret":
                return
            self.step(op, t, text)
            pc += 1

    # -- output ------------------------------------------------------------------------

    def render(self, result_names):
        """The `let` lines, with bindings that nothing reads dropped (see the module doc)."""
        needed = set(result_names)
        live = [False] * len(self.entries)
        for i in range(len(self.entries) - 1, -1, -1):
            e = self.entries[i]
            if e["name"] in needed:
                live[i] = True
                needed.discard(e["name"])
                needed |= e["reads"]
        lines = []  # (code, comment): a `let` with its instruction, or (None, whole-line comment)
        for e, keep in zip(self.entries, live):
            if keep:
                lines.append((f"  let {e['name']} := {e['expr']}", e["comment"]))
            elif e["load"]:
                lines.append((None, f"  -- {e['comment']}: {e['name']} = {e['expr']} is never read"))
            elif e["name"] != "c":
                raise ValueError(f"dead computation: {e['name']} := {e['expr']} ({e['comment']})")
        return lines


def emit_helper(ins, labels):
    e = Emitter(ins, labels, "mulBy1")
    e.ptrs["x2"] = "modulus"
    for i, r in enumerate(("x10", "x11", "x12", "x13")):
        e.bind(r, f"t.l{i}", "argument", reads=())
    e.bind("x4", "inv", "argument", reads=())
    e.run(labels[HELPER_LABEL])
    e.cur_reads = set()
    result = [e.read(r) for r in ("x10", "x11", "x12", "x13")]
    doc = ("The shared reduction helper (`L$pasta_curves_mul_by_1_mont_pasta`): four Montgomery "
           "cancellation steps on `t`, returning `(t + Q * p) / 2^256` for the `Q` they choose, "
           "without a final conditional subtraction. `x10`-`x13` hold `t` and `x4` holds `inv` on "
           "entry; the modulus limbs are loaded through `x2`.")
    return Routine(doc, "def mulBy1 (t modulus : Limbs) (inv : Nat) : Limbs :=", e.render(result),
                   f"  ⟨{', '.join(result)}⟩")


def emit_routine(ins, labels, label, name, doc, ptr_args, inv_reg):
    e = Emitter(ins, labels, "mulBy1")
    e.ptrs["x0"] = "out"
    for reg, arg in ptr_args:
        e.ptrs[reg] = arg
    e.bind(inv_reg, "inv", "argument", reads=())
    e.run(labels[label])
    if sorted(e.outputs) != [0, 1, 2, 3]:
        raise ValueError(f"{name}: outputs stored: {sorted(e.outputs)}")
    result = [e.outputs[i] for i in range(4)]
    params = " ".join(arg for _, arg in ptr_args)
    return Routine(doc, f"def {name} ({params} : Limbs) (inv : Nat) : Limbs :=", e.render(result),
                   f"  ⟨{', '.join(result)}⟩")


class Routine:
    """A transcribed routine: docstring, signature line, body lines, and result line."""

    def __init__(self, doc, signature, lines, result):
        self.doc, self.signature, self.lines, self.result = doc, signature, lines, result

    def text(self, column):
        """The definition, with the instruction comments aligned at `column`; a line whose code
        reaches the column (an outlier, such as the helper call) gets its comment two spaces
        after the code instead."""
        body = []
        for code, comment in self.lines:
            if code is None:
                body.append(comment)
            else:
                body.append(f"{code.ljust(column) if len(code) + 2 <= column else code + '  '}-- {comment}")
        return f"{docstring(self.doc)}\n{self.signature}\n" + "\n".join(body) + f"\n{self.result}\n"


def docstring(text, width=100):
    """A `/-- ... -/` docstring wrapped to the repository's line width."""
    lines = textwrap.TextWrapper(width=width, break_long_words=False, break_on_hyphens=False,
                                 initial_indent="/-- ").wrap(text)
    if len(lines[-1]) + 3 <= width:
        lines[-1] += " -/"
    else:
        lines.append("-/")
    return "\n".join(lines)


def gen_program(ins, labels):
    parts = [HEADER, "import CompElliptic.Asm.AArch64.Semantics\n", """
/-!
# The Pasta Montgomery routines of `pasta_mul-armv8.S`, transcribed

GENERATED by `scripts/gen_aarch64_pasta_mul.py` from
`CompElliptic/Asm/AArch64/vendor/pasta_mul-armv8.S`; do not edit by hand. Each definition
follows its routine instruction by instruction (the instruction is the trailing comment),
over the semantics of `CompElliptic.Asm.AArch64.Semantics`: registers are rebound by the
instructions that write them, `c` is the carry flag, `s` is the (result, carry) pair of the
instruction that last set both, argument limbs are read where the assembly loads them, and
the output limbs are bound where the assembly stores them. Bindings that nothing reads are
left as comments; the stack frame and the return address are not part of the model. See the
generator's docstring for what it checks.
-/

namespace CompElliptic.Asm.AArch64

"""]
    routines = [emit_helper(ins, labels)]
    for label, name, doc, ptr_args, inv_reg in ROUTINES:
        routines.append(emit_routine(ins, labels, label, name, doc, ptr_args, inv_reg))
    # One comment column for the whole file: two spaces past the widest ordinary `let`. Lines
    # longer than COMMENT_COLUMN_MAX are outliers (the helper call) and do not set the column.
    column = 2 + max(len(code) for r in routines for code, _ in r.lines
                     if code is not None and len(code) <= COMMENT_COLUMN_MAX)
    parts.append("\n".join(r.text(column) for r in routines))
    parts.append("\nend CompElliptic.Asm.AArch64\n")
    return "".join(parts)


FIELDS = {
    "Fp": ("pallasBase", "⟨0x992d30ed00000001, 0x224698fc094cf91b, 0, 0x4000000000000000⟩",
           "0x992d30ecffffffff"),
    "Fq": ("vestaBase", "⟨0x8c46eb2100000001, 0x224698fc0994a8dd, 0, 0x4000000000000000⟩",
           "0x8c46eb20ffffffff"),
}


def gen_vectors(lines):
    out = [HEADER, "import CompElliptic.Asm.AArch64.PastaMul\n", """
/-!
# Reference vectors for the transcribed routines

GENERATED by `scripts/gen_aarch64_pasta_mul.py` from
`CompElliptic/Asm/AArch64/vendor/pasta_mul-armv8-vectors.txt`; do not edit by hand. Each
vector is the output of the real assembly (pasta_curves `8ad85e9fab7929f6236960e472f432a4bd9ccd74`,
run on an Apple M-series machine) on the given operands, and each example asks the kernel
to evaluate the transcription on the same operands. The vectors cover boundary operands
(zero, one, `R`, `R2`, `R3`, `p - 1`, single all-ones limbs), random canonical operands,
and unreduced operands in both positions, so they also record the routines' behaviour
outside their operand contracts.

The modulus limbs and `inv` are the crate's constants for its `Fp` (the Pallas base field)
and `Fq` (the Vesta base field).
-/

namespace CompElliptic.Asm.AArch64

"""]
    for key, (prefix, limbs, inv) in FIELDS.items():
        field = "Pallas" if key == "Fp" else "Vesta"
        out.append(f"/-- The {field} base field modulus, as the crate's `MODULUS` limbs. -/\n")
        out.append(f"def {prefix}Modulus : Limbs := {limbs}\n\n")
        out.append(f"/-- `-p^-1 mod 2^64` for the {field} base field, the crate's `INV`. -/\n")
        out.append(f"def {prefix}Inv : Nat := {inv}\n\n")
    n = 0
    for line in lines:
        parts = line.split()
        if not parts:
            continue
        op, key, *vals = parts
        prefix = FIELDS[key][0]
        vals = [f"(Limbs.ofNat 0x{v})" for v in vals]
        fn = {"MUL": "mulMont", "SQR": "sqrMont", "FROM": "fromMont"}.get(op)
        if fn is None:
            raise ValueError(line)
        *operands, r = vals
        # One operand per line keeps every line within the repository's width.
        out.append(f"example :\n    {fn}\n")
        for v in operands:
            out.append(f"      {v}\n")
        out.append(f"      {prefix}Modulus {prefix}Inv =\n    {r} := by\n  decide +kernel\n\n")
        n += 1
    out.append(f"\n-- {n} vectors.\n\nend CompElliptic.Asm.AArch64\n")
    return "".join(out)


def main():
    ins, labels = parse(ASM)
    OUT_PROGRAM.write_text(gen_program(ins, labels))
    OUT_VECTORS.write_text(gen_vectors(VECTORS.read_text().splitlines()))
    print(f"wrote {OUT_PROGRAM} ({len(ins)} instructions parsed) and {OUT_VECTORS}")


if __name__ == "__main__":
    sys.exit(main())
