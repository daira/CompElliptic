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
the committed files.

The script also generates the mechanical part of each routine's correctness proof in
`CompElliptic/Asm/AArch64/PastaMulSpec.lean`: `--skeleton NAME` prints it (see
`skeleton`), and `--check-spec FILE` checks that FILE contains every routine's skeleton
verbatim once its `-- BEGIN ... -- END` annotation blocks are removed; the check script
runs that too. Python 3.9+; stdlib only.
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

    def bind(self, name, expr, comment, reads=None, load=False, fact=None):
        """Record a binding. `fact` is the skeleton's description of it: a tuple whose head
        names the kind of instruction and whose remaining items are the operand names."""
        if name == "xzr":
            return
        self.ptrs.pop(name, None)
        self.known.add(name)
        self.entries.append(dict(name=name, expr=expr, comment=comment,
                                 reads=set(self.cur_reads) if reads is None else set(reads),
                                 load=load, fact=fact))

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
                self.bind(r, self.limb(base, off + 8 * i), text, reads=(), load=True,
                          fact=("load", self.ptrs[base], (off + 8 * i) // 8))
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
                self.bind(f"out{idx}", self.read(r), text, fact=("out", r))
                self.outputs[idx] = f"out{idx}"
        elif op == "add":
            if t[1] == "sp":  # frame pointer setup
                return
            raise ValueError(f"unexpected add: {text}")
        elif op == "mov":
            a = self.read(t[1])
            self.bind(t[0], a, text, fact=("mov", a))
        elif op == "mul":
            a, b = self.read(t[1]), self.read(t[2])
            self.bind(t[0], f"mulLo {a} {b}", text, fact=("mul", a, b))
        elif op == "umulh":
            a, b = self.read(t[1]), self.read(t[2])
            self.bind(t[0], f"umulh {a} {b}", text, fact=("umulh", a, b))
        elif op == "lsl":
            a, k = self.read(t[1]), imm(t[2])
            self.bind(t[0], f"lsl {a} {k}", text, fact=("lsl", a, k))
        elif op == "lsr":
            a, k = self.read(t[1]), imm(t[2])
            self.bind(t[0], f"lsr {a} {k}", text, fact=("lsr", a, k))
        elif op in ("adds", "adcs", "adc"):
            cin = "0" if op == "adds" else self.read("c")
            a, b = self.read(t[1]), self.read(t[2])
            expr = f"addc {a} {b} {cin}"
            if op == "adc":
                self.bind(t[0], f"({expr}).1", text, fact=("adc", a, b, cin))
            else:
                self.bind("s", expr, text, fact=("adds", a, b, cin))
                self.bind(t[0], "s.1", text, reads=("s",), fact=("fst",))
                self.bind("c", "s.2", text, reads=("s",), fact=("snd",))
        elif op in ("subs", "sbcs"):
            cin = "1" if op == "subs" else self.read("c")
            a, b = self.read(t[1]), self.read(t[2])
            expr = f"subc {a} {b} {cin}"
            if t[0] == "xzr":
                self.bind("c", f"({expr}).2", text, fact=("subs_carry", a, b, cin))
            else:
                self.bind("s", expr, text, fact=("subs", a, b, cin))
                self.bind(t[0], "s.1", text, reads=("s",), fact=("fst",))
                self.bind("c", "s.2", text, reads=("s",), fact=("snd",))
        elif op == "csel":
            if t[3] != "lo":
                raise ValueError(f"unexpected condition: {text}")
            c, a, b = self.read("c"), self.read(t[1]), self.read(t[2])
            self.bind(t[0], f"cselLo {c} {a} {b}", text, fact=("csel", c, a, b))
        elif op == "bl":
            if t[0] != HELPER_LABEL:
                raise ValueError(f"unexpected call: {text}")
            if self.ptrs.get("x2") != "modulus":
                raise ValueError("helper called without the modulus pointer in x2")
            targs = [self.read(r) for r in ("x10", "x11", "x12", "x13")]
            inv = self.read("x4")
            self.bind("r", f"{self.helper_name} ⟨{', '.join(targs)}⟩ modulus {inv}", text,
                      fact=("call", *targs, inv))
            for i, r in enumerate(("x10", "x11", "x12", "x13")):
                self.bind(r, f"r.l{i}", "helper output", reads=("r",), fact=("callout", i))
            for i, r in enumerate(("x5", "x6", "x7", "x8")):
                self.bind(r, f"modulus.l{i}", "loaded by the helper", reads=(), load=True,
                          fact=("load", "modulus", i))
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

    def liveness(self, result_names):
        """Which entries something later reads, by a backward pass from the result names."""
        needed = set(result_names)
        live = [False] * len(self.entries)
        for i in range(len(self.entries) - 1, -1, -1):
            e = self.entries[i]
            if e["name"] in needed:
                live[i] = True
                needed.discard(e["name"])
                needed |= e["reads"]
        return live

    def render(self, result_names):
        """The `let` lines, with bindings that nothing reads dropped (see the module doc)."""
        live = self.liveness(result_names)
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
        e.bind(r, f"t.l{i}", "argument", reads=(), fact=("load", "t", i))
    e.bind("x4", "inv", "argument", reads=(), fact=("inv",))
    e.run(labels[HELPER_LABEL])
    e.cur_reads = set()
    result = [e.read(r) for r in ("x10", "x11", "x12", "x13")]
    doc = ("The shared reduction helper (`L$pasta_curves_mul_by_1_mont_pasta`): four Montgomery "
           "cancellation steps on `t`, returning `(t + Q * p) / 2^256` for the `Q` they choose, "
           "without a final conditional subtraction. `x10`-`x13` hold `t` and `x4` holds `inv` on "
           "entry; the modulus limbs are loaded through `x2`.")
    return Routine(doc, "def mulBy1 (t modulus : Limbs) (inv : Nat) : Limbs :=", e.render(result),
                   f"  ⟨{', '.join(result)}⟩", "mulBy1", e, result)


def emit_routine(ins, labels, label, name, doc, ptr_args, inv_reg):
    e = Emitter(ins, labels, "mulBy1")
    e.ptrs["x0"] = "out"
    for reg, arg in ptr_args:
        e.ptrs[reg] = arg
    e.bind(inv_reg, "inv", "argument", reads=(), fact=("inv",))
    e.run(labels[label])
    if sorted(e.outputs) != [0, 1, 2, 3]:
        raise ValueError(f"{name}: outputs stored: {sorted(e.outputs)}")
    result = [e.outputs[i] for i in range(4)]
    params = " ".join(arg for _, arg in ptr_args)
    return Routine(doc, f"def {name} ({params} : Limbs) (inv : Nat) : Limbs :=", e.render(result),
                   f"  ⟨{', '.join(result)}⟩", name, e, result)


class Routine:
    """A transcribed routine: docstring, signature line, body lines, and result line, plus the
    emitter and result names for the proof skeleton."""

    def __init__(self, doc, signature, lines, result, name, emitter, result_names):
        self.doc, self.signature, self.lines, self.result = doc, signature, lines, result
        self.name, self.emitter, self.result_names = name, emitter, result_names

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
    routines = all_routines(ins, labels)
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


# --- proof skeletons --------------------------------------------------------------------

# Bounds hypotheses the annotated spec theorems must provide, by argument name.
BOUND_HYPS = {"t": "ht", "modulus": "hm", "lhs": "hlhs", "rhs": "hrhs", "value": "hv"}
INV_BOUND_HYP = "hinv_lt"
PROJ = ["1", "2.1", "2.2.1", "2.2.2"]
SKELETON_WIDTH = 100


def ssa_names(entries):
    """Unique names for the live bindings: the first binding of a register keeps its name,
    later ones get `_1`, `_2`, ..."""
    counts, names = {}, []
    for e in entries:
        n = counts.get(e["name"], 0)
        counts[e["name"]] = n + 1
        names.append(e["name"] if n == 0 else f"{e['name']}_{n}")
    return names


def wrap_tactic(head, words, tail, indent="  "):
    """`head w1 w2 ... tail`, broken over lines at SKELETON_WIDTH with a 4-space continuation."""
    lines, cur = [], indent + head
    for w in words:
        if len(cur) + 1 + len(w) > SKELETON_WIDTH:
            lines.append(cur)
            cur = indent + "    " + w
        else:
            cur += " " + w
    lines.append(cur + tail)
    return lines


def skeleton(routine):
    """The generated part of the correctness proof of `routine`: unfold, extract the lets under
    SSA names, record every instruction's defining equation (by `rfl`, in `%`/`/` form), make
    all the locals opaque, then per instruction derive the linear facts from its equation and
    clear the equation. Each derived fact is an instance of one lemma (`Nat.mod_add_div`,
    `Nat.mod_lt`, `Nat.div_lt_of_lt_mul`, or a carry lemma from the spec file's preamble), so a
    step costs nothing wherever it sits and names the facts it rests on; `omega` is left to the
    hand-written annotations, which go after the facts of the group whose marker
    (`-- <register>: <instruction>`) names the register they need.

    The values are cleared in one `clear_value`, last local first: clearing a local reverts
    every later local whose value mentions it, so one call per local is quadratic in the length
    of the chain, and the multiplication routine's chain of 380 locals took over a minute."""
    e = routine.emitter
    live = e.liveness(routine.result_names)
    entries = [en for en, keep in zip(e.entries, live) if keep]
    names = ssa_names(entries)
    ren = {}  # current SSA name of each register at each point: resolved while walking
    bnd = {}  # SSA name -> the fact bounding it below 2^64 (registers) or by 1 (carries)
    narrow = set()  # `lsr` results, whose bound is below 2^64 and needs weakening
    out = [f"  -- generated skeleton for `{routine.name}`: do not edit between the annotations",
           f"  unfold {routine.name} at hr", "  lift_lets at hr"]
    out += wrap_tactic("extract_lets", names, " at hr")
    out.append("  subst hr")
    products, shifts = {}, {}
    eqs = []      # the `have e_… := rfl` lines, emitted before the single `clear_value`
    facts = []    # the derived-fact lines, per group, emitted after it

    def r(op):  # operand as written in the entry, renamed to its SSA name at that point
        return ren.get(op, op)

    def lt64(op):  # a proof that the operand is below 2^64
        if re.fullmatch(r"[0-9]+", op):
            return "(by decide)"
        if op in narrow:
            return f"(lt_of_lt_of_le {bnd[op]} (by norm_num))"
        return bnd[op]

    def le1(op):  # a proof that the carry operand is at most 1
        return "(by decide)" if re.fullmatch(r"[0-9]+", op) else bnd[op]

    def eq(nm, rhs):
        eqs.append(f"  have e_{nm} : {nm} = {rhs} := rfl")

    i = 0
    while i < len(entries):
        en, nm = entries[i], names[i]
        kind, *ops = en["fact"]
        ops = [r(o) if isinstance(o, str) else o for o in ops]
        # The group's marker: the register it writes, then the instruction. Annotation blocks
        # are placed after the group they name.
        label = names[i + 1] if kind in ("adds", "subs") else nm
        lines = [f"  -- {label}: {en['comment']}"]
        # Every step records only facts `omega` handles cheaply later: linear equations, bounds,
        # and at most a disjunction. The `%`/`/` equations are derived by `rfl`, used to prove
        # those facts, and cleared.
        if kind == "load":
            arg, idx = ops
            hyp = BOUND_HYPS[arg]
            eq(nm, f"{arg}.l{idx}")
            lines.append(f"  have b_{nm} : {nm} < 2^64 := by rw [e_{nm}]; exact {hyp}.{PROJ[idx]}")
            bnd[nm] = f"b_{nm}"
        elif kind == "inv":
            eq(nm, "inv")
            lines.append(f"  have b_{nm} : {nm} < 2^64 := by rw [e_{nm}]; exact {INV_BOUND_HYP}")
            bnd[nm] = f"b_{nm}"
        elif kind == "mov":
            (a,) = ops
            eq(nm, a)
            lines.append(f"  have b_{nm} : {nm} < 2^64 := by rw [e_{nm}]; exact {lt64(a)}")
            bnd[nm] = f"b_{nm}"
        elif kind == "mul":
            a, b = ops
            eq(nm, f"{a} * {b} % 2^64")
            lines.append(f"  have b_{nm} : {nm} < 2^64 := by rw [e_{nm}]; exact Nat.mod_lt _ (Nat.two_pow_pos _)")
            bnd[nm] = f"b_{nm}"
            products[(a, b)] = nm  # its `%` equation is cleared at the matching `umulh`
        elif kind == "umulh":
            a, b = ops
            eq(nm, f"{a} * {b} / 2^64")
            lines.append(f"  have p_{nm} : {a} * {b} < 2^64 * 2^64 := Nat.mul_lt_mul'' {lt64(a)} {lt64(b)}")
            lines.append(f"  have b_{nm} : {nm} < 2^64 := by rw [e_{nm}]; exact Nat.div_lt_of_lt_mul p_{nm}")
            bnd[nm] = f"b_{nm}"
            if (a, b) in products:
                lo = products.pop((a, b))
                lines.append(f"  have d_{nm} : {lo} + 2^64 * {nm} = {a} * {b} := by")
                lines.append(f"    rw [e_{lo}, e_{nm}]; exact Nat.mod_add_div _ _")
                lines.append(f"  clear e_{lo} e_{nm}")
            else:
                # The low half is never computed (its cancellation is arranged by `subs`); name
                # it as a ghost so that later steps need no `%`.
                lines.append(f"  obtain ⟨lo_{nm}, b_lo_{nm}, d_{nm}⟩ :")
                lines.append(f"      ∃ lo, lo < 2^64 ∧ lo + 2^64 * {nm} = {a} * {b} :=")
                lines.append(f"    ⟨{a} * {b} % 2^64, Nat.mod_lt _ (Nat.two_pow_pos _),")
                lines.append(f"      by rw [e_{nm}]; exact Nat.mod_add_div _ _⟩")
                lines.append(f"  clear e_{nm}")
        elif kind == "lsl":
            a, k = ops
            eq(nm, f"{a} * 2^{k} % 2^64")
            lines.append(f"  have b_{nm} : {nm} < 2^64 := by rw [e_{nm}]; exact Nat.mod_lt _ (Nat.two_pow_pos _)")
            bnd[nm] = f"b_{nm}"
            shifts[(a, k)] = nm
        elif kind == "lsr":
            a, k = ops
            eq(nm, f"{a} / 2^{k}")
            lines.append(f"  have b_{nm} : {nm} < 2^{64 - k} := by")
            lines.append(f"    rw [e_{nm}]; exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq {lt64(a)} (by norm_num))")
            bnd[nm] = f"b_{nm}"
            narrow.add(nm)
            if (a, 64 - k) in shifts:
                lo = shifts.pop((a, 64 - k))
                if k != 2:
                    raise ValueError(f"lsl/lsr split by {64 - k}/{k}: add a lemma to the spec preamble")
                lines.append(f"  have sh_{nm} : {lo} + 2^64 * {nm} = {a} * 2^{64 - k} := by")
                lines.append(f"    rw [e_{lo}, e_{nm}]; exact lsl62_lsr2_split _")
                lines.append(f"  clear e_{lo} e_{nm}")
        elif kind in ("adds", "subs"):
            a, b, cin = ops
            xn, cn = names[i + 1], names[i + 2]
            if kind == "adds":
                val = f"({a} + {b} + {cin})"
                lin = f"{xn} + 2^64 * {cn} = {a} + {b} + {cin}"
                lin_proof = "Nat.mod_add_div _ _"
                carry_proof = f"addc_carry_le_one _ _ _ {lt64(a)} {lt64(b)} {le1(cin)}"
            else:
                val = f"({a} + 2^64 - {b} - (1 - {cin}))"
                lin = f"{xn} + 2^64 * {cn} + {b} + 1 = {a} + 2^64 + {cin}"
                lin_proof = f"subc_lin _ _ _ {lt64(b)} {le1(cin)}"
                carry_proof = f"subc_carry_le_one _ _ _ {lt64(a)}"
            eq(xn, f"{val} % 2^64")
            eq(cn, f"{val} / 2^64")
            lines.append(f"  have l_{xn} : {lin} := by")
            lines.append(f"    rw [e_{xn}, e_{cn}]; exact {lin_proof}")
            lines.append(f"  have b_{xn} : {xn} < 2^64 := by rw [e_{xn}]; exact Nat.mod_lt _ (Nat.two_pow_pos _)")
            lines.append(f"  have b_{cn} : {cn} ≤ 1 := by")
            lines.append(f"    rw [e_{cn}]; exact {carry_proof}")
            lines.append(f"  clear e_{xn} e_{cn}")
            ren[entries[i + 1]["name"]] = xn
            ren[entries[i + 2]["name"]] = cn
            bnd[xn], bnd[cn] = f"b_{xn}", f"b_{cn}"
            i += 2
        elif kind == "adc":
            a, b, cin = ops
            eq(nm, f"({a} + {b} + {cin}) % 2^64")
            lines.append(f"  have b_{nm} : {nm} < 2^64 := by rw [e_{nm}]; exact Nat.mod_lt _ (Nat.two_pow_pos _)")
            lines.append(f"  obtain ⟨k_{nm}, b_k_{nm}, l_{nm}⟩ :")
            lines.append(f"      ∃ k, k ≤ 1 ∧ {nm} + 2^64 * k = {a} + {b} + {cin} :=")
            lines.append(f"    ⟨({a} + {b} + {cin}) / 2^64, addc_carry_le_one _ _ _ {lt64(a)} {lt64(b)} {le1(cin)},")
            lines.append(f"      by rw [e_{nm}]; exact Nat.mod_add_div _ _⟩")
            lines.append(f"  clear e_{nm}")
            bnd[nm] = f"b_{nm}"
        elif kind == "subs_carry":
            a, b, cin = ops
            eq(nm, f"({a} + 2^64 - {b} - (1 - {cin})) / 2^64")
            lines.append(f"  have b_{nm} : {nm} ≤ 1 := by rw [e_{nm}]; exact subc_carry_le_one _ _ _ {lt64(a)}")
            lines.append(f"  have l_{nm} : ({nm} = 1 ∧ {b} + 1 ≤ {a} + {cin}) ∨ ({nm} = 0 ∧ {a} + {cin} < {b} + 1) :=")
            lines.append(f"    subc_carry_cases _ _ _ _ e_{nm} {lt64(a)} {lt64(b)} {le1(cin)}")
            lines.append(f"  clear e_{nm}")
            bnd[nm] = f"b_{nm}"
        elif kind == "csel":
            c, a, b = ops
            eq(nm, f"(if {c} = 0 then {a} else {b})")
            lines.append(f"  have b_{nm} : {nm} < 2^64 := by")
            lines.append(f"    rw [e_{nm}]; split <;> first | exact {lt64(a)} | exact {lt64(b)}")
            bnd[nm] = f"b_{nm}"
        elif kind == "call":
            *targs, inv = ops
            eq(nm, f"mulBy1 ⟨{', '.join(targs)}⟩ modulus {inv}")
        elif kind == "callout":
            (idx,) = ops
            eq(nm, f"{r('r')}.l{idx}")
            bnd[nm] = f"b_{nm}"  # supplied by the annotation that applies the callee's theorem
        elif kind == "out":
            (x,) = ops
            eq(nm, x)
        else:
            raise ValueError(kind)
        ren[en["name"]] = nm
        facts += lines
        i += 1
    out += eqs
    out += wrap_tactic("clear_value", list(reversed(names)), "")
    out += facts
    return out

def check_spec(path, routines):
    """Verify that each routine's skeleton appears verbatim and contiguously in `path` once its
    `-- BEGIN ... -- END` annotation blocks are removed and blank lines dropped. Text outside the
    skeletons (theorem statements, lemmas, the closing steps) is free; text between two
    skeleton lines must be inside an annotation block."""
    text = Path(path).read_text()
    stripped = re.sub(r"(?ms)^\s*-- BEGIN[^\n]*\n.*?^\s*-- END[^\n]*\n", "", text)
    remaining = [l for l in stripped.splitlines() if l.strip()]
    ok = True
    for rt in routines:
        sk = [l for l in skeleton(rt) if l.strip()]
        n = len(sk)
        if sk[1] not in remaining:  # `unfold <routine> at hr`: the theorem is not in this file
            continue
        for start in range(len(remaining) - n + 1):
            if remaining[start:start + n] == sk:
                del remaining[start:start + n]
                break
        else:
            i = remaining.index(sk[1])
            for j, l in enumerate(sk):
                if i + j >= len(remaining) or remaining[i + j] != l:
                    print(f"{path}: skeleton of {rt.name} diverges at skeleton line {j}:",
                          file=sys.stderr)
                    print(f"  expected: {l}", file=sys.stderr)
                    print(f"  found:    {remaining[i + j] if i + j < len(remaining) else '<eof>'}",
                          file=sys.stderr)
                    break
            ok = False
    return ok


def all_routines(ins, labels):
    routines = [emit_helper(ins, labels)]
    for label, name, doc, ptr_args, inv_reg in ROUTINES:
        routines.append(emit_routine(ins, labels, label, name, doc, ptr_args, inv_reg))
    return routines


def main():
    ins, labels = parse(ASM)
    if len(sys.argv) >= 3 and sys.argv[1] == "--skeleton":
        for rt in all_routines(ins, labels):
            if rt.name == sys.argv[2]:
                print("\n".join(skeleton(rt)))
                return 0
        print(f"no routine {sys.argv[2]}", file=sys.stderr)
        return 1
    if len(sys.argv) >= 3 and sys.argv[1] == "--check-spec":
        ok = check_spec(sys.argv[2], all_routines(ins, labels))
        print(f"{sys.argv[2]}: skeletons {'current' if ok else 'STALE'}")
        return 0 if ok else 1
    OUT_PROGRAM.write_text(gen_program(ins, labels))
    OUT_VECTORS.write_text(gen_vectors(VECTORS.read_text().splitlines()))
    print(f"wrote {OUT_PROGRAM} ({len(ins)} instructions parsed) and {OUT_VECTORS}")


if __name__ == "__main__":
    sys.exit(main())
