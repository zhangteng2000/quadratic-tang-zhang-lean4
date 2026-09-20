# Additional proof details used in the formalization

This document records the steps needed to pass from the manuscript to the Lean proofs.
Completion is determined by actual compilation; these notes do not replace the Lean
theorems. Stages A-N have all passed Lean checks, and all 6,593 certificate records have
been verified by the kernel. The final main theorem, complete equality classification,
and corollary for real exponents `λ ≥ 2` require no unproved inputs.

## A: Centered remainder

First, for an arbitrary centered family `w : Fin m → ℂ` with `sum w = 0`, prove

```text
sum |D-c*w_j|² = m*|D|² + c²*sum |w_j|².
```

This identity gives a uniform second-moment bound along the entire interpolation path
`D-c*theta*w_j`, without requiring any individual factor to be nonzero. The AM-GM bound
for a product with one factor deleted follows from

```text
(m/(m-1))^(m-1) ≤ exp(1) < (5/3)².
```

Apply the proved division-free differentiation identity to the polynomial
`P(theta) = product(D-c*theta*w_j)`. Take norms of the derivative and integrate using the
fundamental theorem of calculus on a real interval. The only quantity divided by is
`|D|`. With `D = 1-at*mean(q)`, the inequalities `|mean(q)| ≤ 1` and `0 ≤ at < 1` imply
`D ≠ 0`. Integrating `theta` contributes a factor of `1/2`, changing `5/3` to `5/6`.

Files: `DeletedProducts.lean`, `CenteredRemainder.lean`.

## B: Centered scalar inequality

Write the manuscript's integral formula for the centered power in a division-free form:

```text
b*(m+1)*integral_0^1 (1-b*t)^m dt = 1-(1-b)^(m+1).
```

This step therefore does not require a nonzero mean. Control the denominator using
`Re(D) ≤ |D|` and `1-a*x*t > 0`, and control the power using `beta_s ≤ beta`. Combining
these with the norm bound for the first origin channel gives the scalar inequality.
The origin integral bound is an explicit premise of `centered_scalar_inequality`;
it is subsequently supplied by the communication identity for the actual polynomial.

File: `CenteredScalar.lean`.

## C: Direct scalar inequality

Evaluation and interval integration of the proved polynomial differentiation identity
give the full differential origin identity. Bound the remainder using the deleted-factor
estimate from stage A and `sum |q_j|² ≤ m`. The first origin channel gives
`|integral F| ≤ 1/(m+1)`, yielding the manuscript's factor `m*a/(m+1)`.

File: `DirectScalar.lean`.

## D: Abstract rectangle exclusion

Separate the actual scalar quantities `C, E, F, R, T` from their rectangle bounds.
For every `0 ≤ r ≤ 1`, the expression `a*r+C*r*(1-r²)` is monotone in `a` and `C`.
A numerical check can exclude the entire rectangle by establishing any one of four tests,
together with the correctness of all upper bounds. The boundary test explicitly requires
a uniform bound for `E/(1-a²)`; a fixed upper bound for `E` alone is insufficient.

File: `RectangleExclusion.lean`.

## E: Algebraic proof of convexity for the quotient

For `u, v ≥ 0` and `d, e > 0`, if `u*d+v*e > 0`, then

```text
(u*x+v*y)²/(u*d+v*e) ≤ u*x²/d + v*y²/e.
```

After clearing denominators, the difference is exactly `u*v*(e*x-d*y)²`. Thus `f²/g`
is convex whenever `f` is nonnegative and convex and `g` is positive and affine.
Taking `f = b^(r/2)`, composition preserves convexity for `r ≥ 2` and a nonnegative
convex quadratic function `b`, giving convexity of `b^r/(1-d*t)`. This avoids a separate
second-derivative argument at `b = 0`.

The weighted quadrature bounds follow by multiplying the secant function by `t` or `t²`
and integrating the resulting cubic polynomial exactly. The weights obtained in Lean
agree exactly with those in the manuscript.

File: `ConvexQuadrature.lean`.

## F-J: Rounding, individual records, and coverage

`DyadicSoundness.lean` proves correctness of rounding down and up, exponentiation by
squaring, square roots, and half-integer power enclosures on the 160-bit fixed-point grid.
`RectangleGap.lean` and `RectangleBounds.lean` prove the polar gap test and function
enclosures on rectangles, respectively. `BoundaryTail.lean` proves the monotonicity of
the power-function quotient used by the boundary test. `FiniteQuadrature.lean` proves
the error bound for the complete quadrature grid by adding integrals over adjacent
intervals. The theorems `one_record_verifier_sound` and `verifyRecord_sound` in
`CertificateVerifier.lean` have passed Lean checks. `CertificateCoverage.lean` proves
complete coverage when degree blocks and parameter intervals meet.

The original JSON is preserved byte-for-byte as `verification/certificate.json`, with
SHA-256 `8384d62a377b4fcac4080d0e05979d7a6fcf90437b7e4911927a5403d4052709`.
`Certificate/Data.lean` contains all 6,593 records. `Certificate/DataFacts.lean` verifies
the 6,593 records, 430 degree blocks, and complete coverage in the kernel. Individual
exclusion checks use `decide +kernel`, and all 43 batches have passed. The grid uses
structurally recursive insertion sort so that the kernel can evaluate it directly.

## Additional analysis for large degrees

`ScalarBridge.lean` proves that an actual polynomial counterexample supplies
`ScalarConditions`, including the first origin integral bound.
`ExponentialIntegrals.lean` proves two exponential integral bounds using explicit
antiderivatives. Its pointwise decomposition also applies when the minimizer of beta
lies outside the interval. `LogGrowth.lean` derives the logarithmic growth bound over
the entire unbounded degree range from `log(u) ≤ u - 1`.
`NearPowerTails.lean` and `NearEndpointBounds.lean` establish the power-tail and endpoint
estimates near the boundary. `LargeNear.lean` proves exclusion for large degrees near
the boundary. Here the coefficient bound is relaxed to `6001/m`; for `m ≥ 1000000`
it remains strictly smaller than `a/2`, preserving the manuscript's conclusion.

The analysis away from the boundary is complete. For `a ≥ 1/2`, split delta into the
three intervals `[1/10, 1/2]`, `[1/2, 5/8]`, and `[5/8, 3/4]`. The exponents `7/4`,
`3/2`, and `21/16` give weaker but sufficient remainder bounds. These rational-power
constants are checked in `PowerTailBounds.lean`. This avoids the sharper auxiliary-function
monotonicity argument in the manuscript while still covering the entire parameter range.

`AwayScalarBounds.lean` splits the integral into an exponentially decaying part and an
endpoint power term. `AwayIncreasingBounds.lean` handles the power term separately for
small and large `a`. In both cases, `LargeAway.lean` derives a contradiction to the direct
scalar inequality. `LargeDegreeResult.large_degree_interior` proves the result for every
`n ≥ 1000001` without an additional unproved hypothesis.

`Certificate/Verified.lean` assembles the kernel proofs for all records.
`FinalAssembly.lean` joins the finite and infinite degree ranges. `MainTheorem.lean`
provides stages K, M, and N, the complete equality classification, and the power corollary,
without a certificate-acceptance hypothesis. Some certificate batches use a separate
namespace containing only computational definitions to reduce memory use.
`CertificateKernel/Bridge.lean` proves equality with the original verifier for every
input, and `CertificateKernel/Tagged.lean` proves sufficiency of the selected tests.
