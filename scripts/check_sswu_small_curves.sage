# Exact simplified-SWU branch statistics on small curves.
#
# The ironwood book's group-hash page makes three heuristic claims about
# the deployed-shape mapping, confirmed here by exhaustive computation on
# small instances (q ≡ 1 (mod 4), A·B ≠ 0, odd prime order, -A·B a
# nonsquare, Z the first nonsquare ∉ {0, -1}):
#
#   * the images of the two branches f₁ and f₂ coincide, apart from a
#     negligible proportion of exceptional points (the single-branch
#     count is reported, not asserted — we have not proven a bound on
#     the exceptional cases; it is zero at every instance here);
#   * about 3/8 of the group is reached, with about 1/8 of the points
#     having 4 preimages and about 1/4 having 2 (asserted to within
#     3/√q, the Lang–Weil-shaped error; the constants are not
#     optimized);
#   * every reached point other than 𝒪 has exactly 2 or 4 preimages
#     (asserted exactly: a target's quadratic has 1 or 2 realizable
#     roots, each contributing one preimage per branch).
#
# The w = 0 fibre is empty when -A·B is a nonsquare, so the only
# exceptional output is 𝒪 (from the repaired input u = 0).

def sgn0(x):
    return Integer(x) % 2

def find_instance(q):
    F = GF(q)
    for a in range(1, 50):
        for b in range(1, 50):
            A, B = F(a), F(b)
            if 4*A^3 + 27*B^2 == 0:
                continue
            E = EllipticCurve(F, [A, B])
            N = E.order()
            if not (N.is_prime() and N % 2 == 1):
                continue
            if (-A*B).is_square():
                continue
            Z = next(F(z) for z in range(2, q)
                     if not F(z).is_square() and F(z) != F(-1))
            return (F, E, A, B, Z, N)
    return None

def sswu(F, E, A, B, Z, u):
    """The deployed-shape mapping, and which branch produced the point."""
    if u == 0:
        return (E(0), None)             # the zero-repaired exceptional input
    t = Z*u^2
    ta = t^2 + t
    assert ta != 0                      # t = -1 has no solutions for q ≡ 1 (mod 4)
    x1 = B*(ta + 1) / (A*(-ta))
    for branch, x in ((1, x1), (2, t*x1)):
        g = x^3 + A*x + B
        assert g != 0                   # a root would be rational 2-torsion
        if g.is_square():
            y = g.sqrt()
            if sgn0(y) != sgn0(u):
                y = -y
            return (E((x, y)), branch)
    raise AssertionError("neither branch value is a square")

for q in [101, 149, 197, 401, 601, 1009, 10009]:
    assert q % 4 == 1
    inst = find_instance(q)
    assert inst is not None, f"no instance found for q = {q}"
    F, E, A, B, Z, N = inst
    hist = {}
    branches = {}
    for u in F:
        P, branch = sswu(F, E, A, B, Z, u)
        if branch is None:
            continue
        hist[P] = hist.get(P, 0) + 1
        branches.setdefault(P, set()).add(branch)
    assert set(hist.values()) <= {2, 4}, sorted(set(hist.values()))
    reached = len(hist)
    single = sum(1 for s in branches.values() if len(s) == 1)
    four = sum(1 for c in hist.values() if c == 4)
    two = reached - four
    tol = 3/sqrt(q)
    for count, target in [(reached, 3/8), (four, 1/8), (two, 1/4)]:
        assert abs(count/N - target) <= tol, (q, count, N, target)
    print(f"q={q} A={A} B={B} Z={Z} N={N}: reached {reached}/{N} "
          f"(3/8·N ≈ {float(3*N/8):.0f}), 4-preimage {four} (N/8 ≈ {float(N/8):.0f}), "
          f"2-preimage {two} (N/4 ≈ {float(N/4):.0f}), single-branch points {single}")

print("small-curve branch statistics: OK")
