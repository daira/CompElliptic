# Symbolic checks for design/weil-constant-derivation.md
R0 = PolynomialRing(QQ, ['a', 'b', 'z'])
(a, b, z) = R0.gens()
K = R0.fraction_field()
R = PolynomialRing(K, 'u')
u = R.gen()
t = z*u^2
ta = t^2 + t
x1 = b*(ta + 1) / (a * -ta)
x2 = t*x1
g = lambda x: x^3 + a*x + b

# x₂ simplifies to denominator z·u² + 1:
assert x2 == -b*(ta + 1)/(a*(z*u^2 + 1))
print("x₂ simplification: OK")

# The shared degree-12 core:
Phi = b^2*(ta + 1)^3 + a^3*ta^2
assert Phi == b^2*(ta + 1)^3 + a^3*z^2*u^4*(z*u^2 + 1)^2
assert Phi.degree() == 12
print("Φ identity and degree: OK")

# r_j = g(x_j) factorizations:
r1 = g(x1)
r2 = g(x2)
assert r1 == -b*Phi/(a^3*ta^3)
assert r2 == -b*Phi/(a^3*(z*u^2 + 1)^3)
print("r_j factorizations: OK")

# Hyperelliptic models: Y² = r_j re-scales to W² = H_j = d_j·(z·u² + 1)·Φ
# with d₁ = −a³·b·z³ and d₂ = −a³·b, via W = Y·s_j(u):
assert ta == z*u^2*(z*u^2 + 1)
s1 = a^3*z^3*u^3*(z*u^2 + 1)^2
s2 = a^3*(z*u^2 + 1)^2
H1 = (-a^3*b*z^3)*(z*u^2 + 1)*Phi
H2 = (-a^3*b)*(z*u^2 + 1)*Phi
assert r1*s1^2 == H1
assert r2*s2^2 == H2
print("hyperelliptic models and twist constants: OK")

# Φ is coprime to u and to z·u² + 1 (values b² at both loci):
assert Phi(0) == b^2
# at z·u² = −1: ta = 0, so Φ = b²:
S = PolynomialRing(K, 'v')
v = S.gen()
Phi_v = b^2*((v^2 + v) + 1)^3 + a^3*(v^2 + v)^2   # Φ in t = z·u² = v
assert Phi_v(-1) == b^2
print("Φ coprimality at u = 0 and t = −1: OK")

# The squarefreeness lemma: Φ = φ(ta) for a cubic φ whose discriminant
# and critical values reduce to a·b ≠ 0 and ellipticity:
ST = PolynomialRing(K, 'T')
T = ST.gen()
phi = b^2*(T + 1)^3 + a^3*T^2
assert phi == b^2*T^3 + (a^3 + 3*b^2)*T^2 + 3*b^2*T + b^2
assert Phi == phi(ta)
assert phi.discriminant() == -a^6*b^2*(4*a^3 + 27*b^2)
assert ta.derivative() == 2*z*u*(2*z*u^2 + 1)
assert phi(0) == b^2
assert 64*phi(-1/QQ(4)) == 4*a^3 + 27*b^2
print("φ composition, discriminant, and critical values: OK")

# The certificates transcribed in Hashing/WeilSupport.lean: φ's Bézout
# cofactors, the re-expansion 64·Φ = Ψ(2·z·u² + 1), and the coprimality
# decomposition of Φ against z·u² + 1:
s3 = (6*a^3*b^2 + 36*b^4)*T + (4*a^6 + 36*a^3*b^2 + 63*b^4)
t3 = (-2*a^3*b^2 - 12*b^4)*T^2 + (-2*a^6 - 18*a^3*b^2 - 33*b^4)*T \
    + (-3*a^3*b^2 - 21*b^4)
assert s3*phi + t3*phi.derivative() == a^3*b^2*(4*a^3 + 27*b^2)
Psi = b^2*T^6 + (4*a^3 + 9*b^2)*T^4 + (27*b^2 - 8*a^3)*T^2 \
    + (4*a^3 + 27*b^2)
assert 64*Phi == Psi(2*z*u^2 + 1)
assert Psi(0) == 4*a^3 + 27*b^2
assert Phi == ta*(b^2*ta^2 + (3*b^2 + a^3)*ta + 3*b^2) + b^2
print("WeilSupport certificates: OK")

# g(−b/a) = −(b/a)³, so its square class is that of −a·b:
assert g(-b/a) == -(b/a)^3
print("Eisenstein-fibre ordinate identity: OK")

# Boundary bookkeeping: values of the models at u = 0 and their leading
# coefficients (square classes d_j and d_j·z respectively):
assert H1.degree() == 14 and H2.degree() == 14
assert H1(0) == (-a^3*b*z^3)*b^2 and H2(0) == (-a^3*b)*b^2
assert Phi.leading_coefficient() == b^2*z^6
assert H1.leading_coefficient() == (-a^3*b*z^3)*b^2*z^7
assert H2.leading_coefficient() == (-a^3*b)*b^2*z^7
print("boundary values and leading coefficients: OK")

# Boundary images: x₁ has a pole at u = 0 and tends to −b/a at
# infinity; x₂(0) = −b/a and x₂ has a pole at infinity:
n1, e1 = b*(ta + 1), a*-ta
n2, e2 = -b*(ta + 1), a*(z*u^2 + 1)
assert x1 == n1/e1 and x2 == n2/e2
assert e1(0) == 0 and n1(0) == b
assert n1.degree() == e1.degree()
assert n1.leading_coefficient() / e1.leading_coefficient() == -b/a
assert n2(0) / e2(0) == -b/a
assert n2.degree() > e2.degree()
print("boundary images of x_j: OK")
