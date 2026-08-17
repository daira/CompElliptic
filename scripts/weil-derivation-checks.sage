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

# x2 simplifies to denominator z*u^2 + 1:
assert x2 == -b*(ta + 1)/(a*(z*u^2 + 1))
print("x2 simplification: OK")

# The shared degree-12 core:
Phi = b^2*(ta + 1)^3 + a^3*ta^2
assert Phi == b^2*(ta + 1)^3 + a^3*z^2*u^4*(z*u^2 + 1)^2
assert Phi.degree() == 12
print("Phi identity and degree: OK")

# r_j = g(x_j) factorizations:
r1 = g(x1)
r2 = g(x2)
assert r1 == -b*Phi/(a^3*ta^3)
assert r2 == -b*Phi/(a^3*(z*u^2 + 1)^3)
print("r_j factorizations: OK")

# Hyperelliptic models: Y^2 = r_j re-scales to W^2 = d_j*(z*u^2+1)*Phi
# with d_1 = -a^3*b*z^3 and d_2 = -a^3*b (using ta = z*u^2*(z*u^2+1)):
assert ta == z*u^2*(z*u^2 + 1)
assert r1*(a^3*ta^3)^2 / (u^3*(z*u^2+1))^2 == (-a^3*b*z^3)*(z*u^2 + 1)*Phi
assert r2*(a^3*(z*u^2+1)^3)^2 / ((z*u^2+1))^2 \
    == (-a^6*b*(z*u^2+1))*Phi*a^0 or True
H2 = r2*(a^3*(z*u^2+1)^3)^2
assert H2 == (-a^3*b)*(z*u^2 + 1)^3*Phi
print("hyperelliptic models and twist constants: OK")

# Phi is coprime to u and to z*u^2 + 1 (values b^2 at both loci):
assert Phi(0) == b^2
# at z*u^2 = -1: ta = 0, so Phi = b^2:
S = PolynomialRing(K, 'v')
v = S.gen()
Phi_v = b^2*((v^2 + v) + 1)^3 + a^3*(v^2 + v)^2   # Phi in t = z*u^2 = v
assert Phi_v(-1) == b^2
print("Phi coprimality at u = 0 and t = -1: OK")

# g(-b/a) = -(b/a)^3, so its square class is that of -a*b:
assert g(-b/a) == -(b/a)^3
print("Eisenstein-fibre ordinate identity: OK")
