#!/usr/bin/env python3
"""Check that native-executing checks are opt-in.

Elaborating a module that (transitively) imports a `precompileModules` lane module
loads the lane's locally compiled dylib, and the interpreter then dispatches calls
into it for any evaluation run during that module's elaboration. Loading is
unavoidable for the lane's own proof modules, so the enforced invariant is one
level up: no module whose import closure reaches a lane module may contain an
evaluation-based check (`#eval`, `#guard`, `native_decide`) unless it is on the
explicit opt-in list below. A check that executes locally compiled native code
trusts the C emitter, the local C toolchain, and the loader, coarse-grained and
with no axiom trace — so it must be a documented decision, never ambient.

The lane is parsed from lakefile.lean (the single source of truth): every
`lean_lib` with `precompileModules := true` contributes its glob entries.
`--print-lane` prints the lane module names, one per line, for consumption by
`scripts/check_native_lane.sh` — so the lakefile is the only place the lane is
stated. Parse failures are violations, not skips.

Scope: textual, non-adversarial (comments and strings are stripped heuristically;
crafted code could evade this). Run from the repository root; exits non-zero on
violation. Requires Python 3.11+ (tomllib).
"""
import re, sys, tomllib
from pathlib import Path

def parse_lane():
    config = tomllib.loads(Path("lakefile.toml").read_text())
    lane = []  # (kind, module-name) with kind in {"one", "andSubmodules"}
    for lib in config.get("lean_lib", []):
        if not lib.get("precompileModules", False):
            continue
        entries = []
        for glob in lib.get("globs", []):
            if glob.endswith(".*"):
                entries.append(("andSubmodules", glob[:-2]))
            elif glob.endswith(".+"):
                print(f"ERROR: submodules-only glob {glob!r} in library "
                      f"{lib.get('name', '?')} is not supported here; extend "
                      f"parse_lane", file=sys.stderr)
                sys.exit(2)
            else:
                entries.append(("one", glob))
        if not entries:
            print(f"ERROR: cannot parse the globs of precompileModules library "
                  f"{lib.get('name', '?')}; extend parse_lane", file=sys.stderr)
            sys.exit(2)
        lane.extend(entries)
    if not lane:
        print("ERROR: no precompileModules library found in lakefile.toml; "
              "if the lane was removed, retire this script", file=sys.stderr)
        sys.exit(2)
    return lane

LANE_ENTRIES = parse_lane()

def is_lane(mod: str) -> bool:
    return any(mod == name or (kind == "andSubmodules" and mod.startswith(name + "."))
               for kind, name in LANE_ENTRIES)
# Modules allowed to contain evaluation-based checks despite reaching a lane
# module. Add a module here only with a comment saying which checks it runs and
# why native execution is intended.
OPT_IN = set()

EVAL_TOKENS = re.compile(r"#eval\b|#guard\b|\bnative_decide\b|\bdecide\s*\+\s*native\b")

def module_name(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)

def strip_code(text: str) -> str:
    # Remove block comments (with nesting), line comments, and string literals.
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        two = text[i:i+2]
        if two == "/-":
            depth += 1; i += 2; continue
        if depth > 0:
            if two == "-/":
                depth -= 1; i += 2
            else:
                i += 1
            continue
        if two == "--":
            j = text.find("\n", i)
            i = n if j == -1 else j
            continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
            continue
        out.append(text[i]); i += 1
    return "".join(out)

if "--print-lane" in sys.argv[1:]:
    for kind, name in LANE_ENTRIES:
        if kind != "one":
            print(f"ERROR: --print-lane only supports .one entries (got .{kind} "
                  f"{name}); teach check_native_lane.sh about prefixes first",
                  file=sys.stderr)
            sys.exit(2)
        print(name)
    sys.exit(0)

files = sorted(p for p in Path(".").glob("*.lean") if p.name != "lakefile.lean") \
    + sorted(Path("CompElliptic").rglob("*.lean"))
imports = {}
for f in files:
    mods = re.findall(r"^import\s+([A-Za-z0-9_.]+)", f.read_text(), re.M)
    imports[module_name(f)] = set(mods)

# Modules whose import closure reaches the lane.
reaches = set()
changed = True
while changed:
    changed = False
    for m, deps in imports.items():
        if m not in reaches and any(is_lane(d) or d in reaches for d in deps):
            reaches.add(m); changed = True

status = 0
for f in files:
    m = module_name(f)
    if m not in reaches or is_lane(m) or m in OPT_IN:
        continue
    code = strip_code(f.read_text())
    hits = sorted(set(EVAL_TOKENS.findall(code)))
    if hits:
        print(f"VIOLATION: {f} reaches a precompiled lane module and contains "
              f"evaluation-based check(s) {hits}; native-executing checks must be "
              f"opt-in — add the module to OPT_IN in this script with a rationale, "
              f"or move the check out of the lane's import cone", file=sys.stderr)
        status = 1

in_cone = sorted(m for m in reaches if not is_lane(m) and m in imports)
print(f"native opt-in: {len(in_cone)} module(s) in the lane import cone, "
      f"{len(OPT_IN)} opted in, no ambient native-executing checks"
      if status == 0 else "native opt-in: violations found", file=sys.stdout)
sys.exit(status)
