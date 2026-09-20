# Quadratic Tang-Zhang: Lean 4 formalization

This project formalizes the main theorem, the complete equality classification, and the
corollary for every real exponent `λ ≥ 2` in *Beyond Sendov's conjecture: the quadratic
Tang-Zhang inequality*.

Let `p` be a complex polynomial of degree `n ≥ 2` whose zeros all lie in the closed unit
disk. For each zero `a`, let `ζ₁, …, ζₙ₋₁` be the critical points, counted with multiplicity.
Then

$$
\sum_{j=1}^{n-1}\frac{1}{|a-\zeta_j|^2}\ge n-1.
$$

Equality holds if and only if `p(z) = c(zⁿ - ω)`, where `c ≠ 0` and `|ω| = 1`.
Terms with a zero denominator are represented by positive infinity in `ENNReal`.
`criticalEnergy` uses the multiset of critical points, preserving all multiplicities.

## Theorem entry points

All declarations are in the `QuadraticTangZhang` namespace; see
[`MainTheorem.lean`](QuadraticTangZhang/MainTheorem.lean).

| Theorem | Conclusion |
|---|---|
| `mainStatement : MainStatement` | The quadratic Tang-Zhang inequality in every degree |
| `equalityStatement : EqualityStatement` | The complete necessary and sufficient condition for equality in every degree |
| `main_theorem` | The quadratic inequality together with the equality classification |
| `strict_interior` | Strict inequality at every zero in the open unit disk |
| `powers_ge_two` | The inequality and equality classification for every real exponent `λ ≥ 2` |
| `remainingInterior : RemainingInteriorStatement` | The normalized interior result for degrees at least 6 |

These final theorems require no additional certificate-acceptance hypothesis or assumed
interior result. `reciprocalEnergy_rpow` proves that the power-energy definition agrees
with the usual expression `1/|a - ζ|^λ`.

## Correspondence between stages A-N and the code

| Stage | Main files and theorems |
|---|---|
| A | `CenteredRemainder.lean`: `centered_remainder_estimate` |
| B | `CenteredScalar.lean`: `centered_scalar_inequality` |
| C | `DirectScalar.lean`: `direct_scalar_inequality` |
| D | `RectangleExclusion.lean`: `abstract_rectangle_exclusion` |
| E | `ConvexQuadrature.lean`, `FiniteQuadrature.lean`: convexity and quadrature bounds for the complete grid |
| F | `DyadicSoundness.lean`: `halfPower_sound` and correctness of rounding down and up |
| G | `CertificateVerifier.lean`: `one_record_verifier_sound`, `verifyRecord_sound` |
| H | `CertificateCoverage.lean`: `certificate_coverage_sound` |
| I | `Certificate/Data.lean`, `DataFacts.lean`: 6,593 records and 430 degree blocks |
| J | `Certificate/Verified.lean`: `full_certificate_evaluates_successfully` |
| K | `MainTheorem.lean`: `finite_degree_interior`, `6 ≤ n ≤ 1000000` |
| L | `LargeDegreeResult.lean`: `large_degree_interior`, `n ≥ 1000001` |
| M | `MainTheorem.lean`: `remainingInterior` |
| N | `MainTheorem.lean`: `mainStatement` |

`ScalarBridge.lean` derives all scalar conditions from an actual polynomial counterexample.
`FinalAssembly.lean` combines the finite and infinite degree ranges. Other proved modules
handle low degrees, the origin, the unit-circle boundary, rotation, and the equality
classification. Mathematical details supplied during formalization are recorded in
[`PROOF-NOTES.md`](PROOF-NOTES.md).

## Certificates and trusted foundations

The original input is [`verification/certificate.json`](verification/certificate.json),
with SHA-256:

```text
8384d62a377b4fcac4080d0e05979d7a6fcf90437b7e4911927a5403d4052709
```

Coordinates are exact values on a 100-bit binary fixed-point grid. Enclosures of powers,
square roots, and quotients use a 160-bit grid. All computations use integers and rational
numbers. The Lean verifier checks parameter constraints, gap estimates, quadrature grids,
and exclusion tests. The coverage theorem joins adjacent parameter intervals and degree
blocks.

The numerical proof for each record uses `decide +kernel`. Some batches are checked through
`CertificateKernel` modules that import only computational definitions.
`CertificateKernel/Bridge.lean` proves agreement with the original verifier on every input.
The final acceptance proposition for the original verifier is proved in
`Certificate/Verified.lean`. `CertificateKernel/Tagged.lean` proves that selecting a
sufficient exclusion test by its tag also implies acceptance by the original verifier.

The final axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
The project uses no `sorry`, `admit`, additional axioms, or `native_decide`.
Python scripts perform encoding and build scheduling; their output is not used as a Lean proof.

## Reproduction

The project pins Lean to `v4.34.0-rc1` and mathlib to commit
`de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`. Other dependencies are listed in
[`lake-manifest.json`](lake-manifest.json).

After installing the dependencies, run from the project root:

```powershell
lake exe cache get
.\verify.ps1
```

`verify.ps1` builds the certificate batches, then builds the final main theorem and audits
its axioms. Computing all certificates from scratch can take several hours; Lake reuses
successful existing builds. You can also run `python verification/build_certificate_proofs.py`
to build the certificates in advance with bounded concurrency.

Results are recorded in [`verification/build.log`](verification/build.log),
[`verification/axioms.log`](verification/axioms.log), and
[`verification/summary.json`](verification/summary.json).
[`verification/source-sha256.json`](verification/source-sha256.json) records source-file hashes.
`python verification/check_encoding.py` checks every integer in both Lean data encodings,
all 430 degree blocks, and their record references.

## Provenance

The communication identities and some auxiliary results reuse complete Lean proofs from
[teorth/sendov](https://github.com/teorth/sendov). The pinned upstream commit, scope of local
changes, and Apache-2.0 license are documented in
[`vendor/PROVENANCE.md`](vendor/PROVENANCE.md) and
[`vendor/LICENSE.sendov`](vendor/LICENSE.sendov).
