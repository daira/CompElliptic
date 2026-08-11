# Regenerates the generated section of CompElliptic/Isogenies/VeluCertificates.lean:
# everything below the marker line near the top of its namespace. The hand-written
# module doc above the marker is left untouched. See that module's doc-comment for
# the coordinate system and the vocabulary (certificate, cofactor, atom, mass); this
# script is the single source for the theorem statements and proofs.
#
# Method, per certificate:
#   1. Build the identity and its hypotheses in line coordinates (the chord or
#      tangent line substituted for the ordinates; curve coefficients solved out by
#      Vieta; the image-difference blocks as atoms).
#   2. Obtain cofactors with Singular's `lift` over the hypothesis ideal.
#   3. Transport everything through the kernel-centring ring automorphism
#      x ↦ d + x₀ (and, for the chord, the symmetric change e = d₁ + d₂,
#      dd = d₁ − d₂, with the antisymmetric atoms divided by dd).
#   4. Clear denominators by powers of 2 where the symmetric change introduced
#      halves (the tangent transport is integral; its pre-existing factor of 4 comes
#      from the lift's denominators).
#   5. Assert the emitted-form identity by exact polynomial expansion — the
#      hypothesis contributions exactly as `linear_combination` will read them,
#      multiplied by the emitted cofactors, summing to the emitted goal. No
#      Gröbner output is trusted: a wrong lift fails this assert, and Lean's
#      `ring` normalization independently re-checks the same identity on build.
#   6. Emit with a fixed layout (statement polynomials parenthesized, `by` on its
#      own line, tactic arguments strictly deeper) and lint the layout before
#      writing.
import re
import textwrap


def lw(poly, indent):
    s = str(poly)
    body = textwrap.wrap(s, width=96 - indent, break_long_words=False,
                         break_on_hyphens=False)
    pad = " " * indent
    return ("\n" + pad).join(body)


# ---------------------------------------------------------------- chord ----
R = PolynomialRing(QQ, ["x1", "x2", "l", "m", "x0", "nn", "w"], order="degrevlex")
x1, x2, l, m, x0, nn, w = R.gens()
x3 = l^2 - x1 - x2
e2 = x1*x2 + x1*x3 + x2*x3
e3 = x1*x2*x3
a = 2*l*m + e2
b = m^2 - e3
g0 = x0^3 + a*x0 + b
vc = 2*(3*x0^2 + a)
uc = 4*g0
N = lambda s_: s_*(s_ - x0)^2 + vc*(s_ - x0) + uc
M = lambda s_: (s_ - x0)^3 - vc*(s_ - x0) - 2*uc
D = lambda s_: s_ - x0
y = lambda s_: l*s_ + m
hp = 3*x0^4 + 6*a*x0^2 + 12*b*x0 - a^2
NNu = N(x2)*D(x1)^2 - N(x1)*D(x2)^2
Wu = y(x2)*M(x2)*D(x1)^3 - y(x1)*M(x1)*D(x2)^3
goal = (N(x3)*D(x1)^2*D(x2)^2*nn^2
        - (w^2 - (N(x1)*D(x2)^2 + N(x2)*D(x1)^2)*nn^2)*D(x3)^2)
cof = goal.lift(R.ideal([hp, nn - NNu, w - Wu]))
assert cof[0]*hp + cof[1]*(nn - NNu) + cof[2]*(w - Wu) == goal

# Centring + symmetric change; nn and w are antisymmetric, so they carry a factor
# of dd out: the atoms become the quotients ns = nn/dd, ws = w/dd.
A2 = PolynomialRing(QQ, ["e", "dd", "l", "mp", "x0", "ns", "ws"], order="degrevlex")
e_, dd, l2, mp, x02, ns, ws = A2.gens()
sym = R.hom([x02 + (e_ + dd)/2, x02 + (e_ - dd)/2, l2, mp - l2*x02, x02,
             dd*ns, dd*ws], A2)
goal_s = sym(goal)
hp_s = sym(hp)
NNs = sym(NNu) // dd
Wus = sym(Wu) // dd
c_hp = sym(cof[0])
c_nn = sym(cof[1]) // dd
c_w = sym(cof[2]) // dd


def dexp(P):
    d = lcm([c.denominator() for c in P.coefficients()])
    assert d == 2^(d.valuation(2)), d
    return d.valuation(2)


v1 = dexp(hp_s); v2 = dexp(NNs); v3 = dexp(Wus)
v0 = max(dexp(goal_s), v1 + dexp(c_hp), v2 + dexp(c_nn), v3 + dexp(c_w))
hp_i = 2^v1 * hp_s
NNs_i = 2^v2 * NNs
Wus_i = 2^v3 * Wus
goal_i = 2^v0 * goal_s
c1 = 2^(v0 - v1) * c_hp
c2 = dd^2 * 2^(v0 - v2) * c_nn
c3 = dd^2 * 2^(v0 - v3) * c_w
for P in [hp_i, NNs_i, Wus_i, goal_i, c1, c2, c3]:
    assert dexp(P) == 0
# Emitted-form check: hns contributes (2^v2*ns - NNs_i), hws (2^v3*ws - Wus_i).
assert goal_i == c1*hp_i + c2*(2^v2*ns - NNs_i) + c3*(2^v3*ws - Wus_i)
print("chord emitted-form expansion check: PASS")
print("chord sizes: goal", len(goal_i.monomials()), "cofs",
      [len(c.monomials()) for c in [c1, c2, c3]])

chord_tmpl = """\
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The chord case of the homomorphism identity: the two summands have distinct
abscissas. `hp` is the division-polynomial relation `ψ₃(x₀) = 0`; `hns` and `hws`
define the atoms, scaled by the power of 2 that clears the symmetric change's
halves. The goal is the denominator-cleared statement that the image of the
chord's third abscissa is the abscissa the codomain chord computes from the two
image points. -/
theorem chord_x_certificate {{F : Type*}} [CommRing F]
    (e dd l m' x0 ns ws : F)
    (hp : ({hp}) = 0)
    (hns : (2 : F)^{v2} * ns = {nns})
    (hws : (2 : F)^{v3} * ws = {wus}) :
    ({goal})
    = 0 :=
  by
    linear_combination
      ({c1}) * hp
      + ({c2}) * hns
      + ({c3}) * hws"""
chord = chord_tmpl.format(hp=lw(hp_i, 14), v2=v2, v3=v3, nns=lw(NNs_i, 16),
                          wus=lw(Wus_i, 16), goal=lw(goal_i, 6),
                          c1=lw(c1, 8), c2=lw(c2, 8), c3=lw(c3, 8))

# ---------------------------------------------- chord wrapper support ----
# Support lemmas for the chord wrapper, in the same centred-symmetric coordinates
# as the certificate. The geometric input reduces to three hypotheses in those
# coordinates: the two curve-membership relations with the chord line substituted
# for the ordinates (RC1, RC2, cleared of the halves from d = (e ± dd)/2), and
# psi3. Each lemma lifts over that ideal, with a dd-saturation power where the
# Vieta elimination needs one. The targets: the certificate's own hp polynomial;
# the two identities relating the real-coefficient symmetric quotients to the
# certificate's atom polynomials; and the one nonvanishing correction tying the
# slope-free cleared conclusion to the certificate's goal instance (the ws²
# coefficients agree identically, asserted below).
V = PolynomialRing(QQ, ["e", "dd", "l", "mp", "x0", "A", "B"], order="degrevlex")
ve, vdd, vl, vmp, vx0, vA, vB = V.gens()
d1c = (ve + vdd)/2
d2c = (ve - vdd)/2

def clear2(P):
    P = V(P)
    j = lcm([c.denominator() for c in P.coefficients()]).valuation(2)
    return 2^j * P, j

gcub = lambda dv: (vx0 + dv)^3 + vA*(vx0 + dv) + vB
RC1_i, _ = clear2((vl*d1c + vmp)^2 - gcub(d1c))
RC2_i, _ = clear2((vl*d2c + vmp)^2 - gcub(d2c))
psiV = 3*vx0^4 + 6*vA*vx0^2 + 12*vB*vx0 - vA^2
cgens = [RC1_i, RC2_i, psiV]
cnames = ["hR1", "hR2", "hpsi"]

# certificate-side polynomials, coerced into V (they involve no A, B)
toV = A2.hom([ve, vdd, vl, vmp, vx0, V.zero(), V.zero()], V)
hpV = toV(hp_i)
NNsV = toV(NNs_i)
WusV = toV(Wus_i)

# real-coefficient symmetric quotients (antisymmetric numerators divided by dd)
vAc = 2*(3*vx0^2 + vA)
uAc = 4*(vx0^3 + vA*vx0 + vB)
NAc = lambda dv: (vx0 + dv)*dv^2 + vAc*dv + uAc
MAc = lambda dv: dv^3 - vAc*dv - 2*uAc
yln = lambda dv: vl*dv + vmp
NN_num, jN = clear2(NAc(d2c)*d1c^2 - NAc(d1c)*d2c^2)
WA_num, jW = clear2(yln(d2c)*MAc(d2c)*d1c^3 - yln(d1c)*MAc(d1c)*d2c^3)
NNA_i = NN_num // vdd
WA_i = WA_num // vdd

# the correction Cns: atom- and ordinate-free, then transported to V
Wc = PolynomialRing(QQ, ["x1", "x2", "l", "mp", "x0", "A", "B", "ns", "ws"],
                    order="degrevlex")
cx1, cx2, cl, cmp_, cx0, cA, cB, cns, cws = Wc.gens()
instc = A2.hom([(cx1 - cx0) + (cx2 - cx0), cx1 - cx2, cl, cmp_, cx0, cns, cws], Wc)
GpolyC = instc(goal_i)
vAc2 = 2*(3*cx0^2 + cA)
uAc2 = 4*(cx0^3 + cA*cx0 + cB)
NA3 = lambda s_: s_*(s_ - cx0)^2 + vAc2*(s_ - cx0) + uAc2
x3c = cl^2 - cx1 - cx2
d3c = x3c - cx0
FinalPolyC = (NA3(x3c)*(cx1 - cx0)^2*(cx2 - cx0)^2*cns^2
              - (cws^2 - (NA3(cx1)*(cx2 - cx0)^2
                          + NA3(cx2)*(cx1 - cx0)^2)*cns^2)*d3c^2)
DeltaC = 2^v0 * (cx1 - cx2)^2 * FinalPolyC - GpolyC
CnsC = DeltaC.coefficient({cns: 2, cws: 0})
CwsC = DeltaC.coefficient({cns: 0, cws: 2})
assert DeltaC == CnsC*cns^2 + CwsC*cws^2
assert CwsC == 0, "the ws^2 correction no longer vanishes"
CnsC = CnsC // (cx1 - cx2)^2
cenC = Wc.hom([vx0 + d1c, vx0 + d2c, vl, vmp, vx0, vA, vB, V.zero(), V.zero()], V)
Cns_i, _ = clear2(cenC(CnsC))

support_parts = []
support_docs = {
    "chord_psi3_bridge": """\
/-- The certificate's `hp` input, derived from the geometry: modulo the two
line-substituted curve relations and `ψ₃(x₀) = 0`, the polynomial that
`chord_x_certificate` takes as `hp` vanishes. Carries one saturation factor of
`dd` —the Vieta elimination of the curve coefficients through the line holds only
after saturating by the abscissa difference— and a 2-power from clearing, both
cancelled by the consumer. -/""",
    "chord_ns_semantics": """\
/-- The meaning of the `ns` atom: the symmetric quotient of the image-abscissa
difference numerator, written with the true curve coefficients `A` and `B`,
agrees with the certificate's atom polynomial, which has the coefficients
eliminated through the line. Scaled by one `dd` and by 2-powers, both cancelled
by the consumer. -/""",
    "chord_ws_semantics": """\
/-- The meaning of the `ws` atom: the symmetric quotient of the image-ordinate
difference numerator, written with the true curve coefficients, agrees with the
certificate's atom polynomial. Scaled like `chord_ns_semantics`. -/""",
    "chord_final_correction": """\
/-- The correction closing the wrapper's final step: the slope-free cleared form
of the target equation differs from the certificate's goal instance by
`dd² · C · ns²`, where `C` is the polynomial here and the matching `ws²` gap
vanishes identically (asserted by the generator). This lemma proves `C` vanishes
modulo the same relations, after one `dd` saturation factor and a 2-power from
clearing. -/""",
}
support_tmpl = """\
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
{doc}
theorem {name} {{F : Type*}} [CommRing F]
    (e dd l m' x0 A B : F)
{binders} :
    {goal} :=
  by
    linear_combination
      {combo}"""
hyp_lines = {
    "hR1": "    (hR1 : (" + lw(RC1_i, 12) + ") = 0)",
    "hR2": "    (hR2 : (" + lw(RC2_i, 12) + ") = 0)",
    "hpsi": "    (hpsi : 3*x0^4 + 6*A*x0^2 + 12*B*x0 - A^2 = 0)",
}
for name, lhs_poly, lhs_pow, rhs_poly, rhs_pow in [
        ("chord_psi3_bridge", hpV, 0, None, 0),
        ("chord_ns_semantics", NNA_i, v2, NNsV, jN),
        ("chord_ws_semantics", WA_i, v3, WusV, jW),
        ("chord_final_correction", Cns_i, 0, None, 0)]:
    T0 = lhs_poly * 2^lhs_pow - (rhs_poly * 2^rhs_pow if rhs_poly is not None else 0)
    for k in range(4):
        T = vdd^k * T0
        try:
            lift = T.lift(V.ideal(cgens))
        except ValueError:
            continue
        assert sum(c*g for c, g in zip(lift, cgens)) == T
        break
    else:
        raise AssertionError(name + " not in ideal")
    # scale the whole identity by the cofactors' 2-denominator so the emitted
    # coefficients are integers; the consumer cancels with (2 : F) ≠ 0
    dens = [lcm([q.denominator() for q in c.coefficients()]) for c in lift if c != 0]
    for d in dens:
        assert d == 2^(d.valuation(2)), (name, d)
    dj = max([0] + [d.valuation(2) for d in dens])
    lift = [2^dj * c for c in lift]
    T = 2^dj * T
    assert sum(c*g for c, g in zip(lift, cgens)) == T
    assert all(all(q in ZZ for q in c.coefficients()) for c in lift)
    lhs_pow += dj
    if rhs_poly is not None:
        rhs_pow += dj
    mass = sum(len(c.monomials())*len(g.monomials()) for c, g in zip(lift, cgens))
    print(name, ": saturation", k, "; cofactors",
          [len(c.monomials()) for c in lift], "; mass", mass)
    used = [(nm, c) for nm, c in zip(cnames, lift) if c != 0]
    combo = "\n      + ".join("(" + lw(c, 8) + ") * " + nm for nm, c in used)
    sat = "" if k == 0 else ("dd * " if k == 1 else "dd^" + str(k) + " * ")
    p2 = lambda j: "" if j == 0 else "(2 : F)^" + str(j) + " * "
    if rhs_poly is None:
        goal = sat + p2(lhs_pow) + "(" + lw(lhs_poly, 6) + ")\n    = 0"
    else:
        goal = (sat + p2(lhs_pow) + "(" + lw(lhs_poly, 6) + ")\n    = "
                + sat + p2(rhs_pow) + "(" + lw(rhs_poly, 8) + ")")
    support_parts.append(support_tmpl.format(
        name=name, doc=support_docs[name],
        binders="\n".join(hyp_lines[nm] for nm, _ in used),
        goal=goal, combo=combo))

support = "\n\n".join(support_parts)

# --------------------------------------------------------------- tangent ----
S = PolynomialRing(QQ, ["z1", "u", "v", "z0", "k", "t"], order="degrevlex")
z1, u, v, z0, k, t = S.gens()
z3 = u^2 - 2*z1
za = 2*u*v + z1^2 + 2*z1*z3
zb = v^2 - z1^2*z3
zg0 = z0^3 + za*z0 + zb
zvc = 2*(3*z0^2 + za)
zuc = 4*zg0
zN = lambda s_: s_*(s_ - z0)^2 + zvc*(s_ - z0) + zuc
zM = lambda s_: (s_ - z0)^3 - zvc*(s_ - z0) - 2*zuc
zD = lambda s_: s_ - z0
zy1 = u*z1 + v
zhp = 3*z0^4 + 6*za*z0^2 + 12*zb*z0 - za^2
zAcod = za - 10*(3*z0^2 + za)
T1x = 3*zN(z1)^2 + zAcod*zD(z1)^4
K1x = 2*zy1*zM(z1)*zD(z1)
GXD = zN(z3)*k^2*zD(z1)^2 - (t^2*zD(z1)^2 - 2*zN(z1)*k^2)*zD(z3)^2
# The lift has cofactor denominators of 4; scale the identity by 4 so the emitted
# certificate is integral (the consumer cancels the 4 with (2 : F) ≠ 0).
tcof = [4*c for c in GXD.lift(S.ideal([zhp, k - K1x, t - T1x]))]
GXD4 = 4*GXD
assert tcof[0]*zhp + tcof[1]*(k - K1x) + tcof[2]*(t - T1x) == GXD4

S2 = PolynomialRing(QQ, ["d", "u", "vp", "x0", "k", "t"], order="degrevlex")
d2_, u2, vp, x03, k2, t2 = S2.gens()
cen = S.hom([d2_ + x03, u2, vp - u2*x03, x03, k2, t2], S2)
goal_t = cen(GXD4)
zhp_c = cen(zhp)
K1x_c = cen(K1x)
T1x_c = cen(T1x)
tcof_c = [cen(c) for c in tcof]
assert tcof_c[0]*zhp_c + tcof_c[1]*(k2 - K1x_c) + tcof_c[2]*(t2 - T1x_c) == goal_t
assert all(all(cc in ZZ for cc in f.coefficients())
           for f in [goal_t, zhp_c, K1x_c, T1x_c] + tcof_c)
print("tangent emitted-form expansion check: PASS")
print("tangent sizes: goal", len(goal_t.monomials()), "cofs",
      [len(c.monomials()) for c in tcof_c])

tang_tmpl = """\
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The tangent case of the homomorphism identity: doubling. `hp` is the
division-polynomial relation `ψ₃(x₀) = 0`; the atoms `k` and `t` are the
numerators of `2·y'` and `3·x'² + A'` —the parts of the codomain doubling
slope— over their `d`-power denominators. The whole identity carries the
factor of 4 that made the cofactors integral. -/
theorem tangent_x_certificate {{F : Type*}} [CommRing F]
    (d u v' x0 k t : F)
    (hp : ({hp}) = 0)
    (hk : k = ({k1x}))
    (ht : t = ({t1x})) :
    ({goal})
    = 0 :=
  by
    linear_combination
      ({c0}) * hp
      + ({c1}) * hk
      + ({c2}) * ht"""
tang = tang_tmpl.format(hp=lw(zhp_c, 14), k1x=lw(K1x_c, 16), t1x=lw(T1x_c, 16),
                        goal=lw(goal_t, 6), c0=lw(tcof_c[0], 8),
                        c1=lw(tcof_c[1], 8), c2=lw(tcof_c[2], 8))

text = chord + "\n\n" + support + "\n\n" + tang + "\n"
# The Sage ring names `mp` and `vp` stand for the primed intercepts; rename to the
# Lean identifiers m' and v' (whole words only).
text = re.sub(r"\bmp\b", "m'", text)
text = re.sub(r"\bvp\b", "v'", text)


def indent(s_):
    return len(s_) - len(s_.lstrip())


flat = text.split("\n")
in_comment = False
for i, line in enumerate(flat):
    stripped = line.strip()
    if in_comment:
        if stripped.endswith("-/"):
            in_comment = False
        continue
    if stripped.startswith("/--") or stripped.startswith("/-!"):
        if not stripped.endswith("-/"):
            in_comment = True
        continue
    if stripped == "by" or stripped.endswith(" by"):
        nxt = next((l2 for l2 in flat[i+1:] if l2.strip()), "")
        assert indent(nxt) > indent(line), (i + 1, line[:40], nxt[:40])
print("layout lint clean")

module_path = "CompElliptic/Isogenies/VeluCertificates.lean"
marker = "-- The declarations below are generated by `scripts/gen_velu_certificates.sage`;"
src = open(module_path).read()
assert marker in src, "marker line not found in " + module_path
head = src[:src.index(marker)]
out = (head + marker + "\n"
       + "-- edit and re-run that script rather than editing them here.\n\n"
       + text + "\nend CompElliptic.Isogenies\n")
with open(module_path, "w") as f:
    f.write(out)
print("regenerated " + module_path)
