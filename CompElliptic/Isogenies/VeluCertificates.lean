/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Mathlib.Tactic.LinearCombination

/-!
# Certificates for the 3-isogeny homomorphism property

This module proves the two polynomial identities behind the homomorphism property
of `ThreeIsogeny.map`: the abscissa of the image of a sum agrees with the abscissa
the codomain group law computes from the images. `chord_x_certificate` covers
adding points with distinct abscissas; `tangent_x_certificate` covers doubling.
Both are generic commutative-ring algebra with no geometric content; the geometry
lives in `Isogenies/ThreeIsogeny.lean`.

## Certificates, cofactors, atoms, and mass

Each theorem is a *certificate*. The goal is a polynomial equation `G = 0`, and
each hypothesis is an equation `⟨poly⟩ = 0` or `atom = ⟨poly⟩`. Write `hᵢ` for the
difference of the two sides of hypothesis `i`. The proof supplies *cofactor*
polynomials `c₁, …, cₖ` with `G = c₁·h₁ + ⋯ + cₖ·hₖ`. That equation is exactly what
`linear_combination` checks, by normalizing both sides with `ring`; the cofactors
are the entire proof input. They were computed in Sage by
`scripts/gen_velu_certificates.sage`, which re-verifies the emitted identity by
exact polynomial expansion before writing the Lean text, and Lean re-checks the
same identity on every build — so no Gröbner-basis output is trusted.

An *atom* is a variable standing for a named subexpression, with a defining
hypothesis such as `hns` below. Atoms keep the statement small: the goal and the
cofactors refer to the subexpression by name instead of expanding through it.
Size is what makes these proofs feasible: the running time of `ring` is driven by
the number of monomials in the statement, and secondarily by the certificate's
*mass* `Σᵢ |cᵢ|·|hᵢ|` (counting monomials). The coordinates below reduce the chord
certificate's mass roughly sevenfold and bring its goal from 151 monomials to 66,
which is the difference between an infeasible proof and one that elaborates in
under a minute.

## Kernel-centred coordinates

Both statements use the translation that puts the kernel abscissa at the origin.
For a point abscissa `x` the certificate sees `d = x - x₀`, and a line
`y = l·x + m` becomes `y = l·d + m'` with the centred intercept `m' = m + l·x₀`;
the slope is unchanged. The translation is a ring automorphism, so a certificate
in the original variables transports term-for-term.

Centring shrinks everything because the isogeny is built around `x₀`. Its
denominators are `x - x₀`, which become bare `d`. Vélu's numerators written in `d`
are short: `xnum = d³ + x₀·d² + 2p·d + 4g₀` and `ynum = d³ - 2p·d - 8g₀`, where
`p = 3x₀² + A` and `g₀ = x₀³ + A·x₀ + B` are the derivative and the value of the
curve cubic at the kernel. The powers of `x - x₀` never expand into `x, x₀`
cross-terms, which were most of the bulk in the original variables. The curve
cubic near the kernel becomes `d³ + 3x₀·d² + p·d + g₀` —its coefficients are the
Taylor coefficients at `x₀`— and the division-polynomial relation `ψ₃(x₀) = 0`
becomes the two-term relation `p² = 12·x₀·g₀`.

## Symmetric variables and the atoms

The chord statement also works in symmetric variables for the two summands:
`e = d₁ + d₂` and `dd = d₁ - d₂`. Over the common denominators, the difference of
the image abscissas has numerator `xnum(x₂)·d₁² - xnum(x₁)·d₂²`, and the
difference of the image ordinates has numerator
`y(x₂)·ynum(x₂)·d₁³ - y(x₁)·ynum(x₁)·d₂³`. Both are antisymmetric under swapping
the points, so `dd` divides them; the atoms `ns` and `ws` are those quotients.
The goal and the `ψ₃` hypothesis are symmetric, the atoms and their cofactors are
antisymmetric, and every product in the certificate is even in `dd`. The halves
from `d₁ = (e + dd)/2` are cleared by powers of 2 —visible as the `(2 : F)^k`
factors in the atom hypotheses and an overall scaling of the goal— which a
consumer cancels using `(2 : F) ≠ 0`. The tangent statement has one point and no
symmetry; its atoms `k` and `t` are described at the theorem.

The `s`-scaling of the isogeny stays out of both certificates: the scaled
identity is a power of `s` times the unscaled one, reintroduced by the consumer.

## Support lemmas for the wrapper

The generated section also carries support lemmas for the chord wrapper, in the
same coordinates. Their hypotheses are the two curve-membership relations with the
chord line substituted for the ordinates (`hR1`, `hR2`) and the
division-polynomial relation (`hpsi`). `chord_psi3_bridge` derives the
certificate's `hp` input. `chord_ns_semantics` and `chord_ws_semantics` relate the
certificate's atom polynomials to the same quotients written with the true curve
coefficients. `chord_final_correction` ties the slope-free cleared form of the
target equation to the certificate's goal. Each carries one factor of `dd` —the
Vieta elimination of the curve coefficients through the line holds only after
saturating by the abscissa difference— and 2-power factors from clearing, all
cancelled by the consumer.
-/

namespace CompElliptic.Isogenies

-- The declarations below are generated by `scripts/gen_velu_certificates.sage`;
-- edit and re-run that script rather than editing them here.

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The chord case of the homomorphism identity: the two summands have distinct
abscissas. `hp` is the division-polynomial relation `ψ₃(x₀) = 0`; `hns` and `hws`
define the atoms, scaled by the power of 2 that clears the symmetric change's
halves. The goal is the denominator-cleared statement that the image of the
chord's third abscissa is the abscissa the codomain chord computes from the two
image points. -/
theorem chord_x_certificate {F : Type*} [CommRing F]
    (e dd l m' x0 ns ws : F)
    (hp : (-16*e^2*l^4 + 24*e^3*l^2 + 8*e*dd^2*l^2 - 64*e*l^3*m' + 48*e^2*l^2*x0 +
              48*dd^2*l^2*x0 - 9*e^4 - 6*e^2*dd^2 - dd^4 + 48*e^2*l*m' + 16*dd^2*l*m' -
              64*l^2*m'^2 - 24*e^3*x0 - 72*e*dd^2*x0 + 192*e*l*m'*x0 - 144*dd^2*x0^2 +
              192*m'^2*x0) = 0)
    (hns : (2 : F)^4 * ns = -8*e^3*l^2 + 8*e*dd^2*l^2 + 9*e^4 - 10*e^2*dd^2 + dd^4 + 16*e^2*l*m' -
                16*dd^2*l*m' + 24*e^3*x0 - 24*e*dd^2*x0 + 64*e*m'^2)
    (hws : (2 : F)^6 * ws = 24*e^5*l^3 - 48*e^3*dd^2*l^3 + 24*e*dd^4*l^3 - 27*e^6*l + 57*e^4*dd^2*l -
                33*e^2*dd^4*l + 3*dd^6*l + 48*e^4*l^2*m' - 48*dd^4*l^2*m' - 72*e^5*l*x0 +
                144*e^3*dd^2*l*x0 - 72*e*dd^4*l*x0 - 72*e^5*m' + 48*e^3*dd^2*m' + 24*e*dd^4*m' -
                192*e^3*l*m'^2 + 192*e*dd^2*l*m'^2 - 192*e^4*m'*x0 + 96*e^2*dd^2*m'*x0 +
                96*dd^4*m'*x0 - 384*e^2*m'^3 - 128*dd^2*m'^3) :
    (64*e^4*dd^2*l^6*ns^2 - 640*e^2*dd^4*l^6*ns^2 + 576*dd^6*l^6*ns^2 + 128*e^5*dd^2*l^4*ns^2 +
      1280*e^3*dd^4*l^4*ns^2 - 1408*e*dd^6*l^4*ns^2 + 1024*e^3*dd^2*l^5*m'*ns^2 -
      1024*e*dd^4*l^5*m'*ns^2 - 384*e^4*dd^2*l^4*x0*ns^2 + 5376*e^2*dd^4*l^4*x0*ns^2 -
      4992*dd^6*l^4*x0*ns^2 - 480*e^6*dd^2*l^2*ns^2 - 544*e^4*dd^4*l^2*ns^2 +
      992*e^2*dd^6*l^2*ns^2 + 32*dd^8*l^2*ns^2 - 1792*e^4*dd^2*l^3*m'*ns^2 +
      1536*e^2*dd^4*l^3*m'*ns^2 + 256*dd^6*l^3*m'*ns^2 + 2048*e^2*dd^2*l^4*m'^2*ns^2 +
      2048*dd^4*l^4*m'^2*ns^2 - 1152*e^5*dd^2*l^2*x0*ns^2 - 6912*e^3*dd^4*l^2*x0*ns^2 +
      8064*e*dd^6*l^2*x0*ns^2 - 6144*e^3*dd^2*l^3*m'*x0*ns^2 + 6144*e*dd^4*l^3*m'*x0*ns^2 +
      576*e^4*dd^2*l^2*x0^2*ns^2 - 14976*e^2*dd^4*l^2*x0^2*ns^2 + 14400*dd^6*l^2*x0^2*ns^2 +
      288*e^7*dd^2*ns^2 - 96*e^5*dd^4*ns^2 - 160*e^3*dd^6*ns^2 - 32*e*dd^8*ns^2 +
      768*e^5*dd^2*l*m'*ns^2 - 512*e^3*dd^4*l*m'*ns^2 - 256*e*dd^6*l*m'*ns^2 -
      4096*e^3*dd^2*l^2*m'^2*ns^2 - 4096*e*dd^4*l^2*m'^2*ns^2 + 1632*e^6*dd^2*x0*ns^2 +
      1248*e^4*dd^4*x0*ns^2 - 2784*e^2*dd^6*x0*ns^2 - 96*dd^8*x0*ns^2 +
      5376*e^4*dd^2*l*m'*x0*ns^2 - 4608*e^2*dd^4*l*m'*x0*ns^2 - 768*dd^6*l*m'*x0*ns^2 -
      12288*e^2*dd^2*l^2*m'^2*x0*ns^2 - 12288*dd^4*l^2*m'^2*x0*ns^2 + 2304*e^5*dd^2*x0^2*ns^2 +
      9216*e^3*dd^4*x0^2*ns^2 - 11520*e*dd^6*x0^2*ns^2 + 9216*e^3*dd^2*l*m'*x0^2*ns^2 -
      9216*e*dd^4*l*m'*x0^2*ns^2 + 13824*e^2*dd^4*x0^3*ns^2 - 13824*dd^6*x0^3*ns^2 +
      2304*e^4*dd^2*m'^2*ns^2 + 1536*e^2*dd^4*m'^2*ns^2 + 256*dd^6*m'^2*ns^2 +
      12288*e^3*dd^2*m'^2*x0*ns^2 + 12288*e*dd^4*m'^2*x0*ns^2 + 18432*e^2*dd^2*m'^2*x0^2*ns^2 +
      18432*dd^4*m'^2*x0^2*ns^2 - 1024*dd^2*l^4*ws^2 + 2048*e*dd^2*l^2*ws^2 +
      6144*dd^2*l^2*x0*ws^2 - 1024*e^2*dd^2*ws^2 - 6144*e*dd^2*x0*ws^2 - 9216*dd^2*x0^2*ws^2)
    = 0 :=
  by
    linear_combination
      (-24*e^4*dd^2*l^3*m'*ns + 48*e^2*dd^4*l^3*m'*ns - 24*dd^6*l^3*m'*ns -
        120*e^5*dd^2*l^2*x0*ns + 240*e^3*dd^4*l^2*x0*ns - 120*e*dd^6*l^2*x0*ns +
        24*e^5*dd^2*l*m'*ns - 48*e^3*dd^4*l*m'*ns + 24*e*dd^6*l*m'*ns - 64*e^3*dd^2*l^2*m'^2*ns
        + 64*e*dd^4*l^2*m'^2*ns + 135*e^6*dd^2*x0*ns - 285*e^4*dd^4*x0*ns + 165*e^2*dd^6*x0*ns -
        15*dd^8*x0*ns + 312*e^4*dd^2*l*m'*x0*ns - 624*e^2*dd^4*l*m'*x0*ns + 312*dd^6*l*m'*x0*ns
        + 360*e^5*dd^2*x0^2*ns - 720*e^3*dd^4*x0^2*ns + 360*e*dd^6*x0^2*ns + 48*e^4*dd^2*m'^2*ns
        - 32*e^2*dd^4*m'^2*ns - 16*dd^6*m'^2*ns + 1152*e^3*dd^2*m'^2*x0*ns -
        1152*e*dd^4*m'^2*x0*ns + 32*e^2*dd^2*l^2*ns^2 - 32*dd^4*l^2*ns^2 + 32*e^2*dd^2*l^2*m'*ws
        - 32*dd^4*l^2*m'*ws - 32*e^3*dd^2*ns^2 + 32*e*dd^4*ns^2 - 336*e^2*dd^2*x0*ns^2 +
        336*dd^4*x0*ns^2 - 32*e^3*dd^2*m'*ws + 32*e*dd^4*m'*ws - 96*e^2*dd^2*m'*x0*ws +
        96*dd^4*m'*x0*ws) * hp
      + (36*e^4*dd^2*l^6*ns - 72*e^2*dd^4*l^6*ns + 36*dd^6*l^6*ns - 72*e^5*dd^2*l^4*ns +
        144*e^3*dd^4*l^4*ns - 72*e*dd^6*l^4*ns + 192*e^3*dd^2*l^5*m'*ns - 192*e*dd^4*l^5*m'*ns -
        456*e^4*dd^2*l^4*x0*ns + 672*e^2*dd^4*l^4*x0*ns - 216*dd^6*l^4*x0*ns +
        36*e^6*dd^2*l^2*ns - 72*e^4*dd^4*l^2*ns + 36*e^2*dd^6*l^2*ns - 336*e^4*dd^2*l^3*m'*ns +
        288*e^2*dd^4*l^3*m'*ns + 48*dd^6*l^3*m'*ns + 256*e^2*dd^2*l^4*m'^2*ns +
        576*e^5*dd^2*l^2*x0*ns - 672*e^3*dd^4*l^2*x0*ns + 96*e*dd^6*l^2*x0*ns -
        2112*e^3*dd^2*l^3*m'*x0*ns + 2112*e*dd^4*l^3*m'*x0*ns + 1044*e^4*dd^2*l^2*x0^2*ns -
        648*e^2*dd^4*l^2*x0^2*ns - 396*dd^6*l^2*x0^2*ns + 144*e^5*dd^2*l*m'*ns -
        96*e^3*dd^4*l*m'*ns - 48*e*dd^6*l*m'*ns - 384*e^3*dd^2*l^2*m'^2*ns -
        128*e*dd^4*l^2*m'^2*ns - 135*e^6*dd^2*x0*ns + 45*e^4*dd^4*x0*ns + 75*e^2*dd^6*x0*ns +
        15*dd^8*x0*ns + 1728*e^4*dd^2*l*m'*x0*ns - 1344*e^2*dd^4*l*m'*x0*ns -
        384*dd^6*l*m'*x0*ns - 2496*e^2*dd^2*l^2*m'^2*x0*ns + 960*dd^4*l^2*m'^2*x0*ns -
        360*e^5*dd^2*x0^2*ns - 720*e^3*dd^4*x0^2*ns + 1080*e*dd^6*x0^2*ns +
        4608*e^3*dd^2*l*m'*x0^2*ns - 4608*e*dd^4*l*m'*x0^2*ns - 2160*e^2*dd^4*x0^3*ns +
        2160*dd^6*x0^3*ns - 48*e^2*dd^2*l^5*ws + 48*dd^4*l^5*ws + 144*e^4*dd^2*m'^2*ns +
        96*e^2*dd^4*m'^2*ns + 16*dd^6*m'^2*ns + 1152*e^3*dd^2*m'^2*x0*ns + 384*e*dd^4*m'^2*x0*ns
        + 5184*e^2*dd^2*m'^2*x0^2*ns - 2880*dd^4*m'^2*x0^2*ns + 96*e^3*dd^2*l^3*ws -
        96*e*dd^4*l^3*ws - 128*e*dd^2*l^4*m'*ws + 288*e^2*dd^2*l^3*x0*ws - 288*dd^4*l^3*x0*ws -
        48*e^4*dd^2*l*ws + 48*e^2*dd^4*l*ws + 224*e^2*dd^2*l^2*m'*ws + 32*dd^4*l^2*m'*ws -
        288*e^3*dd^2*l*x0*ws + 288*e*dd^4*l*x0*ws + 768*e*dd^2*l^2*m'*x0*ws -
        432*e^2*dd^2*l*x0^2*ws + 432*dd^4*l*x0^2*ws - 96*e^3*dd^2*m'*ws - 32*e*dd^4*m'*ws -
        672*e^2*dd^2*m'*x0*ws - 96*dd^4*m'*x0*ws - 1152*e*dd^2*m'*x0^2*ws) * hns
      + (12*e^2*dd^2*l^5*ns - 12*dd^4*l^5*ns - 24*e^3*dd^2*l^3*ns + 24*e*dd^4*l^3*ns +
        32*e*dd^2*l^4*m'*ns - 72*e^2*dd^2*l^3*x0*ns + 72*dd^4*l^3*x0*ns + 12*e^4*dd^2*l*ns -
        12*e^2*dd^4*l*ns - 56*e^2*dd^2*l^2*m'*ns - 8*dd^4*l^2*m'*ns + 72*e^3*dd^2*l*x0*ns -
        72*e*dd^4*l*x0*ns - 192*e*dd^2*l^2*m'*x0*ns + 108*e^2*dd^2*l*x0^2*ns -
        108*dd^4*l*x0^2*ns + 24*e^3*dd^2*m'*ns + 8*e*dd^4*m'*ns + 168*e^2*dd^2*m'*x0*ns +
        24*dd^4*m'*x0*ns + 288*e*dd^2*m'*x0^2*ns - 16*dd^2*l^4*ws + 32*e*dd^2*l^2*ws +
        96*dd^2*l^2*x0*ws - 16*e^2*dd^2*ws - 96*e*dd^2*x0*ws - 144*dd^2*x0^2*ws) * hws

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The certificate's `hp` input, derived from the geometry: modulo the two
line-substituted curve relations and `ψ₃(x₀) = 0`, the polynomial that
`chord_x_certificate` takes as `hp` vanishes. Carries one saturation factor of
`dd` —the Vieta elimination of the curve coefficients through the line holds only
after saturating by the abscissa difference— and a 2-power from clearing, both
cancelled by the consumer. -/
theorem chord_psi3_bridge {F : Type*} [CommRing F]
    (e dd l m' x0 A B : F)
    (hR1 : (2*e^2*l^2 + 4*e*dd*l^2 + 2*dd^2*l^2 - e^3 - 3*e^2*dd - 3*e*dd^2 - dd^3 + 8*e*l*m' +
            8*dd*l*m' - 6*e^2*x0 - 12*e*dd*x0 - 6*dd^2*x0 - 12*e*x0^2 - 12*dd*x0^2 - 8*x0^3 +
            8*m'^2 - 4*e*A - 4*dd*A - 8*x0*A - 8*B) = 0)
    (hR2 : (2*e^2*l^2 - 4*e*dd*l^2 + 2*dd^2*l^2 - e^3 + 3*e^2*dd - 3*e*dd^2 + dd^3 + 8*e*l*m' -
            8*dd*l*m' - 6*e^2*x0 + 12*e*dd*x0 - 6*dd^2*x0 - 12*e*x0^2 + 12*dd*x0^2 - 8*x0^3 +
            8*m'^2 - 4*e*A + 4*dd*A - 8*x0*A - 8*B) = 0)
    (hpsi : 3*x0^4 + 6*A*x0^2 + 12*B*x0 - A^2 = 0) :
    dd * (2 : F)^1 * (-16*e^2*l^4 + 24*e^3*l^2 + 8*e*dd^2*l^2 - 64*e*l^3*m' + 48*e^2*l^2*x0 + 48*dd^2*l^2*x0 -
      9*e^4 - 6*e^2*dd^2 - dd^4 + 48*e^2*l*m' + 16*dd^2*l*m' - 64*l^2*m'^2 - 24*e^3*x0 -
      72*e*dd^2*x0 + 192*e*l*m'*x0 - 144*dd^2*x0^2 + 192*m'^2*x0)
    = 0 :=
  by
    linear_combination
      (-4*e*l^2 + 3*e^2 + dd^2 - 8*l*m' - 12*e*x0 + 24*dd*x0 - 12*x0^2 - 4*A) * hR1
      + (4*e*l^2 - 3*e^2 - dd^2 + 8*l*m' + 12*e*x0 + 24*dd*x0 + 12*x0^2 + 4*A) * hR2
      + (32*dd) * hpsi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The meaning of the `ns` atom: the symmetric quotient of the image-abscissa
difference numerator, written with the true curve coefficients `A` and `B`,
agrees with the certificate's atom polynomial, which has the coefficients
eliminated through the line. Scaled by one `dd` and by 2-powers, both cancelled
by the consumer. -/
theorem chord_ns_semantics {F : Type*} [CommRing F]
    (e dd l m' x0 A B : F)
    (hR1 : (2*e^2*l^2 + 4*e*dd*l^2 + 2*dd^2*l^2 - e^3 - 3*e^2*dd - 3*e*dd^2 - dd^3 + 8*e*l*m' +
            8*dd*l*m' - 6*e^2*x0 - 12*e*dd*x0 - 6*dd^2*x0 - 12*e*x0^2 - 12*dd*x0^2 - 8*x0^3 +
            8*m'^2 - 4*e*A - 4*dd*A - 8*x0*A - 8*B) = 0)
    (hR2 : (2*e^2*l^2 - 4*e*dd*l^2 + 2*dd^2*l^2 - e^3 + 3*e^2*dd - 3*e*dd^2 + dd^3 + 8*e*l*m' -
            8*dd*l*m' - 6*e^2*x0 + 12*e*dd*x0 - 6*dd^2*x0 - 12*e*x0^2 + 12*dd*x0^2 - 8*x0^3 +
            8*m'^2 - 4*e*A + 4*dd*A - 8*x0*A - 8*B) = 0) :
    dd * (2 : F)^4 * (-e^4 + 2*e^2*dd^2 - dd^4 + 24*e^2*x0^2 - 24*dd^2*x0^2 + 64*e*x0^3 + 8*e^2*A - 8*dd^2*A +
      64*e*x0*A + 64*e*B)
    = dd * (2 : F)^4 * (-8*e^3*l^2 + 8*e*dd^2*l^2 + 9*e^4 - 10*e^2*dd^2 + dd^4 + 16*e^2*l*m' - 16*dd^2*l*m' +
        24*e^3*x0 - 24*e*dd^2*x0 + 64*e*m'^2) :=
  by
    linear_combination
      (48*e^2 - 64*e*dd + 16*dd^2) * hR1
      + (-48*e^2 - 64*e*dd - 16*dd^2) * hR2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The meaning of the `ws` atom: the symmetric quotient of the image-ordinate
difference numerator, written with the true curve coefficients, agrees with the
certificate's atom polynomial. Scaled like `chord_ns_semantics`. -/
theorem chord_ws_semantics {F : Type*} [CommRing F]
    (e dd l m' x0 A B : F)
    (hR1 : (2*e^2*l^2 + 4*e*dd*l^2 + 2*dd^2*l^2 - e^3 - 3*e^2*dd - 3*e*dd^2 - dd^3 + 8*e*l*m' +
            8*dd*l*m' - 6*e^2*x0 - 12*e*dd*x0 - 6*dd^2*x0 - 12*e*x0^2 - 12*dd*x0^2 - 8*x0^3 +
            8*m'^2 - 4*e*A - 4*dd*A - 8*x0*A - 8*B) = 0)
    (hR2 : (2*e^2*l^2 - 4*e*dd*l^2 + 2*dd^2*l^2 - e^3 + 3*e^2*dd - 3*e*dd^2 + dd^3 + 8*e*l*m' -
            8*dd*l*m' - 6*e^2*x0 + 12*e*dd*x0 - 6*dd^2*x0 - 12*e*x0^2 + 12*dd*x0^2 - 8*x0^3 +
            8*m'^2 - 4*e*A + 4*dd*A - 8*x0*A - 8*B) = 0) :
    dd * (2 : F)^6 * (-e^6*l + 3*e^4*dd^2*l - 3*e^2*dd^4*l + dd^6*l - 24*e^4*l*x0^2 + 48*e^2*dd^2*l*x0^2 -
      24*dd^4*l*x0^2 - 128*e^3*l*x0^3 + 128*e*dd^2*l*x0^3 - 96*e^3*m'*x0^2 + 96*e*dd^2*m'*x0^2 -
      384*e^2*m'*x0^3 - 128*dd^2*m'*x0^3 - 8*e^4*l*A + 16*e^2*dd^2*l*A - 8*dd^4*l*A -
      128*e^3*l*x0*A + 128*e*dd^2*l*x0*A - 32*e^3*m'*A + 32*e*dd^2*m'*A - 384*e^2*m'*x0*A -
      128*dd^2*m'*x0*A - 128*e^3*l*B + 128*e*dd^2*l*B - 384*e^2*m'*B - 128*dd^2*m'*B)
    = dd * (2 : F)^6 * (24*e^5*l^3 - 48*e^3*dd^2*l^3 + 24*e*dd^4*l^3 - 27*e^6*l + 57*e^4*dd^2*l - 33*e^2*dd^4*l
        + 3*dd^6*l + 48*e^4*l^2*m' - 48*dd^4*l^2*m' - 72*e^5*l*x0 + 144*e^3*dd^2*l*x0 -
        72*e*dd^4*l*x0 - 72*e^5*m' + 48*e^3*dd^2*m' + 24*e*dd^4*m' - 192*e^3*l*m'^2 +
        192*e*dd^2*l*m'^2 - 192*e^4*m'*x0 + 96*e^2*dd^2*m'*x0 + 96*dd^4*m'*x0 - 384*e^2*m'^3 -
        128*dd^2*m'^3) :=
  by
    linear_combination
      (-448*e^4*l + 512*e^3*dd*l + 384*e^2*dd^2*l - 512*e*dd^3*l + 64*dd^4*l - 1280*e^3*m' +
        1536*e^2*dd*m' - 768*e*dd^2*m' + 512*dd^3*m') * hR1
      + (448*e^4*l + 512*e^3*dd*l - 384*e^2*dd^2*l - 512*e*dd^3*l - 64*dd^4*l + 1280*e^3*m' +
        1536*e^2*dd*m' + 768*e*dd^2*m' + 512*dd^3*m') * hR2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The correction closing the wrapper's final step: the slope-free cleared form
of the target equation differs from the certificate's goal instance by
`dd² · C · ns²`, where `C` is the polynomial here and the matching `ws²` gap
vanishes identically (asserted by the generator). This lemma proves `C` vanishes
modulo the same relations, after one `dd` saturation factor and a 2-power from
clearing. -/
theorem chord_final_correction {F : Type*} [CommRing F]
    (e dd l m' x0 A B : F)
    (hR1 : (2*e^2*l^2 + 4*e*dd*l^2 + 2*dd^2*l^2 - e^3 - 3*e^2*dd - 3*e*dd^2 - dd^3 + 8*e*l*m' +
            8*dd*l*m' - 6*e^2*x0 - 12*e*dd*x0 - 6*dd^2*x0 - 12*e*x0^2 - 12*dd*x0^2 - 8*x0^3 +
            8*m'^2 - 4*e*A - 4*dd*A - 8*x0*A - 8*B) = 0)
    (hR2 : (2*e^2*l^2 - 4*e*dd*l^2 + 2*dd^2*l^2 - e^3 + 3*e^2*dd - 3*e*dd^2 + dd^3 + 8*e*l*m' -
            8*dd*l*m' - 6*e^2*x0 + 12*e*dd*x0 - 6*dd^2*x0 - 12*e*x0^2 + 12*dd*x0^2 - 8*x0^3 +
            8*m'^2 - 4*e*A + 4*dd*A - 8*x0*A - 8*B) = 0)
    (hpsi : 3*x0^4 + 6*A*x0^2 + 12*B*x0 - A^2 = 0) :
    dd * (512*e^2*dd^2*l^6 - 512*dd^4*l^6 - 256*e^5*l^4 - 1024*e^3*dd^2*l^4 + 1280*e*dd^4*l^4 -
      1024*e^3*l^5*m' + 1024*e*dd^2*l^5*m' - 4608*e^2*dd^2*l^4*x0 + 4608*dd^4*l^4*x0 +
      1536*e^3*l^4*x0^2 - 1536*e*dd^2*l^4*x0^2 + 2048*e^2*l^4*x0^3 + 2048*dd^2*l^4*x0^3 +
      544*e^6*l^2 + 416*e^4*dd^2*l^2 - 928*e^2*dd^4*l^2 - 32*dd^6*l^2 + 1792*e^4*l^3*m' -
      1536*e^2*dd^2*l^3*m' - 256*dd^4*l^3*m' - 2048*e^2*l^4*m'^2 - 2048*dd^2*l^4*m'^2 +
      1536*e^5*l^2*x0 + 6144*e^3*dd^2*l^2*x0 - 7680*e*dd^4*l^2*x0 + 6144*e^3*l^3*m'*x0 -
      6144*e*dd^2*l^3*m'*x0 - 2688*e^4*l^2*x0^2 + 16128*e^2*dd^2*l^2*x0^2 - 13440*dd^4*l^2*x0^2
      - 13312*e^3*l^2*x0^3 + 5120*e*dd^2*l^2*x0^3 - 12288*e^2*l^2*x0^4 - 12288*dd^2*l^2*x0^4 +
      512*e^3*l^4*A - 512*e*dd^2*l^4*A + 2048*e^2*l^4*x0*A + 2048*dd^2*l^4*x0*A - 288*e^7 +
      96*e^5*dd^2 + 160*e^3*dd^4 + 32*e*dd^6 - 768*e^5*l*m' + 512*e^3*dd^2*l*m' +
      256*e*dd^4*l*m' + 4096*e^3*l^2*m'^2 + 4096*e*dd^2*l^2*m'^2 - 1632*e^6*x0 -
      1248*e^4*dd^2*x0 + 2784*e^2*dd^4*x0 + 96*dd^6*x0 - 5376*e^4*l*m'*x0 +
      4608*e^2*dd^2*l*m'*x0 + 768*dd^4*l*m'*x0 + 12288*e^2*l^2*m'^2*x0 + 12288*dd^2*l^2*m'^2*x0
      - 1152*e^5*x0^2 - 9984*e^3*dd^2*x0^2 + 11136*e*dd^4*x0^2 - 9216*e^3*l*m'*x0^2 +
      9216*e*dd^2*l*m'*x0^2 + 10368*e^4*x0^3 - 19200*e^2*dd^2*x0^3 + 12928*dd^4*x0^3 +
      26112*e^3*x0^4 - 1536*e*dd^2*x0^4 + 18432*e^2*x0^5 + 18432*dd^2*x0^5 - 896*e^4*l^2*A +
      768*e^2*dd^2*l^2*A + 128*dd^4*l^2*A - 7168*e^3*l^2*x0*A - 1024*e*dd^2*l^2*x0*A -
      12288*e^2*l^2*x0^2*A - 12288*dd^2*l^2*x0^2*A + 2048*e^2*l^4*B + 2048*dd^2*l^4*B -
      2304*e^4*m'^2 - 1536*e^2*dd^2*m'^2 - 256*dd^4*m'^2 - 12288*e^3*m'^2*x0 -
      12288*e*dd^2*m'^2*x0 - 18432*e^2*m'^2*x0^2 - 18432*dd^2*m'^2*x0^2 + 384*e^5*A -
      256*e^3*dd^2*A - 128*e*dd^4*A + 4992*e^4*x0*A - 768*e^2*dd^2*x0*A - 128*dd^4*x0*A +
      16896*e^3*x0^2*A + 7680*e*dd^2*x0^2*A + 18432*e^2*x0^3*A + 18432*dd^2*x0^3*A -
      4096*e^3*l^2*B - 4096*e*dd^2*l^2*B - 12288*e^2*l^2*x0*B - 12288*dd^2*l^2*x0*B + 2304*e^4*B
      + 1536*e^2*dd^2*B + 256*dd^4*B + 12288*e^3*x0*B + 12288*e*dd^2*x0*B + 18432*e^2*x0^2*B +
      18432*dd^2*x0^2*B)
    = 0 :=
  by
    linear_combination
      (128*e*dd^2*l^4 - 128*dd^3*l^4 - 32*e^4*l^2 - 64*e^2*dd^2*l^2 + 96*dd^4*l^2 -
        128*e^2*l^3*m' + 128*dd^2*l^3*m' - 768*e*dd^2*l^2*x0 + 768*dd^3*l^2*x0 +
        192*e^2*l^2*x0^2 - 192*dd^2*l^2*x0^2 + 256*e*l^2*x0^3 + 56*e^5 - 24*e^4*dd - 48*e^3*dd^2
        + 112*e^2*dd^3 - 136*e*dd^4 + 40*dd^5 + 256*e^3*l*m' - 128*e^2*dd*l*m' + 256*e*dd^2*l*m'
        - 384*dd^3*l*m' + 256*e*l^2*m'^2 - 512*dd*l^2*m'^2 + 96*e^4*x0 + 192*e^2*dd^2*x0 -
        288*dd^4*x0 + 384*e^2*l*m'*x0 - 384*dd^2*l*m'*x0 - 384*e^3*x0^2 + 192*e^2*dd*x0^2 +
        768*e*dd^2*x0^2 - 576*dd^3*x0^2 - 1536*e*l*m'*x0^2 + 1536*dd*l*m'*x0^2 - 896*e^2*x0^3 +
        128*dd^2*x0^3 - 512*l*m'*x0^3 + 64*e^2*l^2*A - 64*dd^2*l^2*A + 256*e*l^2*x0*A +
        320*e^2*m'^2 + 448*dd^2*m'^2 + 512*l*m'^3 + 768*e*m'^2*x0 - 768*m'^2*x0^2 - 128*e^3*A +
        64*e^2*dd*A - 128*e*dd^2*A + 192*dd^3*A - 512*e*l*m'*A + 512*dd*l*m'*A - 512*e^2*x0*A -
        256*dd^2*x0*A - 512*l*m'*x0*A - 768*e*x0^2*A + 1536*dd*x0^2*A - 512*x0^3*A + 256*e*l^2*B
        - 256*m'^2*A + 256*e*A^2 - 512*dd*A^2 + 512*x0*A^2 - 320*e^2*B - 448*dd^2*B - 512*l*m'*B
        - 2304*e*x0*B + 4608*dd*x0*B - 2304*x0^2*B + 256*A*B) * hR1
      + (-128*e*dd^2*l^4 - 128*dd^3*l^4 + 32*e^4*l^2 + 64*e^2*dd^2*l^2 - 96*dd^4*l^2 +
        128*e^2*l^3*m' - 128*dd^2*l^3*m' + 768*e*dd^2*l^2*x0 + 768*dd^3*l^2*x0 -
        192*e^2*l^2*x0^2 + 192*dd^2*l^2*x0^2 - 256*e*l^2*x0^3 - 56*e^5 - 24*e^4*dd + 48*e^3*dd^2
        + 112*e^2*dd^3 + 136*e*dd^4 + 40*dd^5 - 256*e^3*l*m' - 128*e^2*dd*l*m' - 256*e*dd^2*l*m'
        - 384*dd^3*l*m' - 256*e*l^2*m'^2 - 512*dd*l^2*m'^2 - 96*e^4*x0 - 192*e^2*dd^2*x0 +
        288*dd^4*x0 - 384*e^2*l*m'*x0 + 384*dd^2*l*m'*x0 + 384*e^3*x0^2 + 192*e^2*dd*x0^2 -
        768*e*dd^2*x0^2 - 576*dd^3*x0^2 + 1536*e*l*m'*x0^2 + 1536*dd*l*m'*x0^2 + 896*e^2*x0^3 -
        128*dd^2*x0^3 + 512*l*m'*x0^3 - 64*e^2*l^2*A + 64*dd^2*l^2*A - 256*e*l^2*x0*A -
        320*e^2*m'^2 - 448*dd^2*m'^2 - 512*l*m'^3 - 768*e*m'^2*x0 + 768*m'^2*x0^2 + 128*e^3*A +
        64*e^2*dd*A + 128*e*dd^2*A + 192*dd^3*A + 512*e*l*m'*A + 512*dd*l*m'*A + 512*e^2*x0*A +
        256*dd^2*x0*A + 512*l*m'*x0*A + 768*e*x0^2*A + 1536*dd*x0^2*A + 512*x0^3*A - 256*e*l^2*B
        + 256*m'^2*A - 256*e*A^2 - 512*dd*A^2 - 512*x0*A^2 + 320*e^2*B + 448*dd^2*B + 512*l*m'*B
        + 2304*e*x0*B + 4608*dd*x0*B + 2304*x0^2*B - 256*A*B) * hR2
      + (-512*e^2*dd*l^2 - 1536*dd^3*l^2 + 2048*e*dd*l^2*x0 + 2048*e*dd^3 - 4096*e*dd*l*m' +
        4096*dd^3*x0 + 4096*dd*l*m'*x0 - 6144*dd*m'^2 + 2048*e*dd*A + 4096*dd*x0*A + 6144*dd*B) * hpsi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The tangent case of the homomorphism identity: doubling. `hp` is the
division-polynomial relation `ψ₃(x₀) = 0`; the atoms `k` and `t` are the
numerators of `2·y'` and `3·x'² + A'` —the parts of the codomain doubling
slope— over their `d`-power denominators. The whole identity carries the
factor of 4 that made the cofactors integral. -/
theorem tangent_x_certificate {F : Type*} [CommRing F]
    (d u v' x0 k t : F)
    (hp : (-4*d^2*u^4 + 12*d^3*u^2 - 8*d*u^3*v' + 12*d^2*u^2*x0 - 9*d^4 + 12*d^2*u*v' -
              4*u^2*v'^2 - 12*d^3*x0 + 24*d*u*v'*x0 + 12*v'^2*x0) = 0)
    (hk : k = (8*d^4*u^3 - 18*d^5*u - 24*d^4*u*x0 - 18*d^4*v' - 24*d^2*u*v'^2 - 24*d^3*v'*x0 -
                16*d*v'^3))
    (ht : t = (-18*d^5*u^2 + 54*d^6 + 54*d^4*u*v' + 48*d^2*u^2*v'^2 + 72*d^5*x0 +
                24*d^3*u*v'*x0 + 72*d^3*v'^2 + 96*d*u*v'^3 + 24*d^2*v'^2*x0 + 48*v'^4)) :
    (4*d^2*u^6*k^2 + 16*d^3*u^4*k^2 + 32*d*u^5*v'*k^2 - 24*d^2*u^4*x0*k^2 - 120*d^4*u^2*k^2 -
      112*d^2*u^3*v'*k^2 + 32*u^4*v'^2*k^2 - 144*d^3*u^2*x0*k^2 - 192*d*u^3*v'*x0*k^2 +
      36*d^2*u^2*x0^2*k^2 - 4*d^2*u^4*t^2 + 144*d^5*k^2 + 96*d^3*u*v'*k^2 - 128*d*u^2*v'^2*k^2 +
      408*d^4*x0*k^2 + 336*d^2*u*v'*x0*k^2 - 192*u^2*v'^2*x0*k^2 + 288*d^3*x0^2*k^2 +
      288*d*u*v'*x0^2*k^2 + 16*d^3*u^2*t^2 + 24*d^2*u^2*x0*t^2 + 144*d^2*v'^2*k^2 +
      384*d*v'^2*x0*k^2 + 288*v'^2*x0^2*k^2 - 16*d^4*t^2 - 48*d^3*x0*t^2 - 36*d^2*x0^2*t^2)
    = 0 :=
  by
    linear_combination
      (-48*d^3*u^4*v'*k - 120*d^4*u^3*x0*k + 36*d^6*u*k + 240*d^4*u^2*v'*k + 40*d^2*u^3*v'^2*k
        + 324*d^5*u*x0*k + 288*d^3*u^2*v'*x0*k + 360*d^4*u*x0^2*k + 120*d^5*u^2*t -
        16*d^3*u^3*v'*t - 72*d^4*u^2*x0*t - 126*d^5*v'*k + 240*d^3*u*v'^2*k + 208*d*u^2*v'^3*k -
        36*d^4*v'*x0*k + 744*d^2*u*v'^2*x0*k + 144*d^3*v'*x0^2*k - 390*d^6*t - 400*d^4*u*v'*t -
        376*d^2*u^2*v'^2*t - 360*d^5*x0*t - 96*d^3*u*v'*x0*t + 216*d^4*x0^2*t + 48*d^2*v'^3*k +
        144*u*v'^4*k + 480*d*v'^3*x0*k - 616*d^3*v'^2*t - 816*d*u*v'^3*t - 168*d^2*v'^2*x0*t -
        432*v'^4*t - u^2*k^2 - 7*d*k^2 + 18*x0*k^2 + 9*t^2) * hp
      + (24*d*u^5*v'*k + 60*d^2*u^4*x0*k - 45*d^4*u^2*k - 156*d^2*u^3*v'*k + 28*u^4*v'^2*k -
        288*d^3*u^2*x0*k - 24*d*u^3*v'*x0*k - 180*d^2*u^2*x0^2*k + 12*d^3*u^3*t + 8*d*u^4*v'*t +
        36*d^2*u^3*x0*t + 81*d^5*k + 180*d^3*u*v'*k - 156*d*u^2*v'^2*k + 486*d^4*x0*k +
        288*d^2*u*v'*x0*k - 108*u^2*v'^2*x0*k + 504*d^3*x0^2*k - 144*d*u*v'*x0^2*k - 21*d^4*u*t
        + 20*d^2*u^2*v'*t + 12*u^3*v'^2*t - 108*d^3*u*x0*t + 24*d*u^2*v'*x0*t - 108*d^2*u*x0^2*t
        + 144*d^2*v'^2*k + 468*d*v'^2*x0*k + 72*v'^2*x0^2*k - 48*d^3*v'*t - 168*d^2*v'*x0*t -
        36*u*v'^2*x0*t - 144*d*v'*x0^2*t) * hk
      + (-12*d^3*u^3*k - 8*d*u^4*v'*k - 36*d^2*u^3*x0*k + 32*d^2*u^4*t + 21*d^4*u*k -
        20*d^2*u^2*v'*k - 12*u^3*v'^2*k + 108*d^3*u*x0*k - 24*d*u^2*v'*x0*k + 108*d^2*u*x0^2*k -
        92*d^3*u^2*t + 72*d*u^3*v'*t - 84*d^2*u^2*x0*t + 48*d^3*v'*k + 168*d^2*v'*x0*k +
        36*u*v'^2*x0*k + 144*d*v'*x0^2*k + 65*d^4*t - 108*d^2*u*v'*t + 36*u^2*v'^2*t +
        60*d^3*x0*t - 216*d*u*v'*x0*t - 36*d^2*x0^2*t - 108*v'^2*x0*t) * ht

end CompElliptic.Isogenies
