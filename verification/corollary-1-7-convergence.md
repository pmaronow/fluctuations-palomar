# Corollary 1.7: explicit pressure convergence

This revision addresses Palomar's statement-fidelity request for Corollary 1.7.
The base release is `77de1ff2421efc9dccb34f3da19cd3ac0bb33250`.

## Compared statement

`LowerUpperBounds.corollary_1_7`, in both `Challenge.lean` and
`Solution.lean`, now proves the conjunction of:

1. For every real beta > 1, `countingPressure beta` tends along `atTop` to
   `limitingPressure beta`.
2. The original `OAI.SKFluctuations.MeanBias.LowerBoundStatement`, including
   every positive exponent slack, a positive constant, and an eventual threshold.

Convergence is a conclusion, not an additional hypothesis. The definition
`limitingPressure beta = limUnder atTop (countingPressure beta)` is unchanged;
its name or definition alone is not being used as evidence of convergence.
The independent Challenge continues to import only Mathlib. The other four
compared claims, all inherited proof sources, and all four build/comparison
controls are unchanged. No result number or written mathematical corollary changes.

## Proof

The inequality is the existing
`OAI.SKFluctuations.LaplaceWindowFormalization.mean_bias_lower_bound_unconditional`.
The new convergence conjunct uses the existing pressure identities
`MeanBias.countingPressure_eq_pressure` and
`QuantitativePaper.pressure_eq_finiteSKFreeEnergy` to identify the sequence
with `Paper.finiteSKFreeEnergy beta 0`. The existing
`Paper.physicalParisiFormula` proves convergence of that sequence for beta > 0.
`MeanBias.limitingPressure_eq_parisiPDEValue` identifies its limit with
`limitingPressure beta`. The condition beta > 1 supplies beta > 0.

## Validation status

The [machine-readable record](corollary-1-7-convergence.json) binds these
checks to the revised interface and control hashes.

- Independent source and statement-correspondence review: PASS.
- Fresh pinned Lean elaboration of the revised Challenge: PASS, exit 0; five
  intentional `sorry` warnings and 20 existing redundant-`@[expose]` warnings,
  with no errors.
- Fresh default package build: running from source; no final result yet.
- Strict five-export axiom audit: pending completion of the package build.
- Fresh protected canonical Comparator and three-kernel replay: pending;
  no new acceptance is asserted.

The local workspace initially contained no Lean toolchain or compiled package
objects. The pinned Lean toolchain and trusted Mathlib cache are installed
outside the submitted source tree. Local namespace setup for the protected
runner fails with `bwrap: setting up uid map: Read-only file system`, so a
protected replay is not claimed on the strength of local source checks.

The historical records in this directory remain unchanged and are bound to
proof-source commit `5551e62264a270fd5dcd396f36389eaf77eddebc`. Their Corollary
1.7 export contains the original lower-bound predicate, without the new
explicit convergence conjunct. They do not certify the strengthened type.
