# Verification record

> This is the historical record for proof-source commit `5551e62264a270fd5dcd396f36389eaf77eddebc`.
> For the strengthened Corollary 1.7 interface, its fresh build, strict audit,
> and still-pending protected replay, see the [current record](corollary-1-7-convergence.md).
> Historical receipts below remain unchanged.

Local checks of this five-claim package completed on October 20, 2026. The verified public
root content commit is `5551e62264a270fd5dcd396f36389eaf77eddebc`. The records commit preserves all
10,695 Lean sources and all four build/comparison controls byte for byte.
[Source identities](source-checks.json) and [provenance](../PROVENANCE.json)
bind these checks to the released proof sources.

| Check | UTC date | Result | Evidence |
| --- | --- | --- | --- |
| Bubblewrap namespace test | 2026-10-20 | PASS: Bubblewrap 0.12.0, exit 0 | [Source and environment receipt](source-checks.json) |
| Official source, configuration, header, and technical metadata requirements | 2026-10-20 | PASS: 10,695 Lean files and compiler-parsed headers; valid metadata; five intentional Challenge placeholders and zero proof holes elsewhere | [Source receipt](source-checks.json) |
| Plain default `lake build` using retained objects | 2026-10-20 | PASS: 19,626 jobs, exit 0; 10,694 reused package objects; zero rebuilt package modules | [Build receipt](build-result.json) |
| Strict `Audit.lean` | 2026-10-20 | PASS: five exports, only the three standard axioms; zero warnings or errors | [Audit receipt](axiom-audit-result.json), [log](axiom-audit.log) |
| Official protected Comparator statement, reachable-helper, and axiom comparison | 2026-10-20 | PASS: five claims; no definition-hole exemptions | [Replay receipt](comparator/result.json) |
| Independent kernel replay | 2026-10-20 | PASS: con-ron, NanoDa, and Lean default accepted the Solution export | [Transcript](comparator/comparator.log) |

All 10,694 non-Challenge Lean files and all four controls match the prior local
clean-build inputs. The current build reuses those objects and permits existing
infrastructure linter warnings. The separate Audit
uses `-j1 -DautoImplicit=false -DwarningAsError=true` and permits only
`propext`, `Quot.sound`, and `Classical.choice`. Challenge is 358 lines and
16,289 bytes, within its hard caps; its size exceeds the advisory 300-line
threshold.

## Protected comparison

The replay uses the official PalomarSubmission verifier at
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, Lean `v4.35.0-rc2`
(`11acb17ec6b07a8f9e9173e6845197929540936b`), Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, and Bubblewrap 0.12.0 with
a successful namespace test.

The runner calls the pinned verifier's canonical-Challenge compiler, export
functions, and protected export judge. A random alias identifies the fresh
Challenge compiled against only canonical dependencies and Lean core. The
Comparator checks all five statement types and the complete reachable helper
closure, with no definition exemptions, then replays the Solution through
con-ron (`--jobs=2`), NanoDa, and Lean default. Its matching, mismatched, and
ill-typed preflight controls and filesystem-confinement controls passed.

The [accepted receipt](comparator/result.json) records commands, real exit
codes, protected configuration, 38 export roots, source and executable digests,
dependency revisions, and export hashes. con-ron reports 163,246 verified declarations.
Proof inputs and
tools remained unchanged during the replay. Large exports and full compilation
logs remain outside the repository at the paths recorded in the receipts.

## Challenge identity continuity

| Snapshot | SHA-256 | Change |
| --- | --- | --- |
| Early statement review | `4480c5a0610abe28f0e7987b80b63f117583a92a38c61dcc0d1bb78ed086a587` | Original reviewed interface |
| After authored-comment scrub | `43cd24bf2da6478304a30433cc0bd0b2667a3765df82bf97c26d831ca56590a2` | Comments and blank lines only |
| Prior local three-kernel verification | `f4d2c6444591c6a33e1367d47b9f956ead148895e3ac8e31edb8885c63b90e2e` | Two auxiliary-proof cache reset commands; mathematical declarations unchanged |
| Current interface | `cfb9e89f1163f844b1632ad7ad603dcf42c16d8a43ade763d85c2e0425e8e688` | Two-line explanatory comment above the first reset; removing these exact lines recovers the prior locally verified Challenge byte for byte. |

The only final Challenge change is the exact two-line auxiliary-cache comment
above the first of four resets. Removing these two comment lines recovers the
prior locally verified Challenge byte for byte.
The prior local verification is identified by content hashes. The published
history consists of the public root content commit and its records commit;
earlier local package history is not required.

## Reproduction and scope

From a fresh checkout using the pinned toolchain and manifest:

```sh
lake exe cache get
lake build
lake env lean -j1 -DautoImplicit=false -DwarningAsError=true Audit.lean
```

Protected replay additionally requires the pinned official verifier and the
canonical-Challenge/export/judge sequence recorded in the replay receipt.
The local reproduction runner and complete final-commit source-check receipt
are retained with `/home/ubuntu/work/reports/pkg/PKG3/report-final.md`.

This run reused unchanged Solution/package objects and performed a new full
protected replay, including fresh canonical Challenge compilation and all three
kernels. It does not claim a new clean package rebuild, public registry intake, production-capacity
qualification, registration, human review, or Palomar acceptance. Historical
manuscript checks remain scoped to their named source revisions.
