# Verification records

[`summary.json`](summary.json) records successful verification of all stages A-N, the
equality classification, and the power corollary. [`build.log`](build.log) and
[`axioms.log`](axioms.log) contain the final build and axiom-audit logs.

`certificate-kernel/Checked00.log` through `Checked42.log` cover all 43 batches.
Successful cache reuse in these logs comes from previously completed Lean kernel computations.

[`encoding.json`](encoding.json) checks the 6,593 integer records and all 430 degree
blocks in the original certificate against both Lean data encodings.
[`source-sha256.json`](source-sha256.json) records the source-file hashes.

Run `./verify.ps1` from the project root to rebuild the project and repeat the axiom audit.
