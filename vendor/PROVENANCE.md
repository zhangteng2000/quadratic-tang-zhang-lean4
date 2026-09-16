# Vendored proof provenance

Upstream: https://github.com/teorth/sendov

Commit: `1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d`

License: Apache-2.0; see `LICENSE.sendov`. Copyright and author notices remain in the files.

The following files were copied without proof changes:

- `Sendov/Counterexample/Factor.lean`
- `Sendov/Counterexample/Identities.lean`
- `Sendov/Analytic/Maclaurin.lean`
- `Sendov/Common/Sinh.lean`

`Sendov/Analytic/PolarBase.lean` contains lines 1--205 of upstream
`Sendov/Analytic/Polar.lean`, with `import Sendov.Reduction.Setup` replaced by
`import Mathlib.Tactic`, and a closing `end Sendov` appended. The retained
results concern the communication identity, norms of products, and AM--GM.

`Sendov/Reduction/BetaBound.lean` retains the upstream proof text. Its import
of `Sendov.Reduction.Polar` is replaced with targeted mathlib imports; it has
no dependency on the Sendov counterexample reduction.

`QuadraticTangZhang/Polar.lean` adapts the AM--GM proof from upstream
`Sendov/Analytic/Polar.lean`, retaining the exact second moment instead of
assuming each reciprocal critical point has norm at most one. The new
moment hypothesis is stated explicitly and is derived from the quadratic
energy bound in `LowDegreeResult.lean`.

`QuadraticTangZhang/BetaBounds.lean` deduces the manuscript's weaker strict
bound `beta(1) < alpha/(1+alpha)` from the upstream proven estimate
`beta(1) <= alpha/(3+alpha)`. The exponential reduction here uses the exact
second moment and does not assume the Sendov pointwise hypothesis.

No upstream challenge file, admitted main theorem, or native certificate
oracle is imported. The general Sendov theorem is neither asserted nor
used as a substitute for the stronger quadratic Tang--Zhang inequality.

The upstream commit and the local project both use Lean 4.34.0-rc1 and
mathlib revision `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.
