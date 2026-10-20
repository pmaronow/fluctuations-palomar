# Lower and Upper Bounds for Glauber Dynamics from Typical States of the Low-Temperature Sherrington–Kirkpatrick Model

The [`fluctuations-palomar`](https://github.com/pmaronow/fluctuations-palomar)
repository contains the manuscript and a Palomar submission package for five
result groups. The independent statements are in `Challenge.lean`, their
proofs are in `Solution.lean`, and `comparator.json` selects exactly the five
advertised claims. The [manuscript](manuscript/main.pdf) and its buildable
source accompany the formalization.

| Manuscript result | Formal scope |
| --- | --- |
| Theorem 1.1 | For every fixed β > 1, a positive coefficient Aβ, chosen before the threshold, gives the exponent 7/30 barrier for both continuous time and discrete update attempts, at every fixed threshold 0 < τ < 1/2. The same coefficient serves both clocks and all these thresholds. |
| Corollary 1.2 | Both clocks and every fixed threshold 0 < τ < 1/2, with coefficient one for every exponent 0 < κ < 7/30. Coefficient one at 7/30 is not asserted. |
| Theorem 1.3 | The continuous-time typical-start upper bound for every fixed β > 1 and 0 < ω < 1/4: the joint probability of distance greater than 1/4 at exp(n^(1−ω)) tends to zero. Each site has rate one. The endpoint ω = 1/4 is excluded. |
| Theorem 1.6 | The standard-deviation and variance exponents 1/6 and 1/3, and the typical centered-fluctuation exponent 1/6, with every positive exponent slack. The positive-Laplace-window input is proved internally. |
| Corollary 1.7 | For every fixed β > 1, the finite-volume counting pressures converge to the defined limiting pressure; the mean-pressure bias is at least cβ,ε n^(−5/6−ε) for every ε > 0, with a positive constant and an eventual size threshold. Both conclusions are part of the compared claim. |

In the dynamics statements, the initial configuration is sampled once from
the Gibbs law and then held fixed when its transition law and total variation
distance are formed. Probability averages over the disorder and this sampled
configuration. The upper-bound formalization uses a completed GOE matrix;
its diagonal adds a configuration-independent constant to the Hamiltonian
and cancels from the Gibbs probabilities and transition rates. For Theorem
1.6 the formal log partition function uses uniform rather than counting
measure, subtracting the deterministic term n log 2; centered fluctuations
and variance agree. Corollary 1.7 uses the counting-measure pressure and its
actual thermodynamic limit. Its exported statement now explicitly conjoins
pressure convergence with the unchanged lower-bound predicate. The convergence
proof uses the retained `Paper.physicalParisiFormula` and pressure-identification
theorems. The manuscript's formal-verification chapter explains these
correspondences.

Corollaries 1.4 and 1.5 (the discrete upper bound and the combined two-sided
statement) are not separately formalized or advertised Comparator claims.
The stronger quantitative, almost-sure, Metropolis, general bounded-rate,
and relaxation-time barrier conclusions are not formalized. The sharper
local expansion, a fluctuation limit law or positive variance prefactor,
and the mean-bias bound without exponent slack are also outside the five
formal claims.

`Challenge.lean` imports only Mathlib and defines the mathematical objects
directly. Its five deliberate theorem placeholders specify the claims to
compare; they are not solution proofs. `Solution.lean` connects these
statements to the included proof developments. `Audit.lean` checks the five
exports and permits only `propext`, `Classical.choice`, and `Quot.sound` in
their transitive axiom dependencies. There is no external literature premise
in the five exported theorem types; their quantified model and parameter
conditions remain part of the statements.

The retained Lean files form the import closure of `Challenge`, `Solution`,
and `Audit`. The proof sources combine the barrier, optimized upper-bound,
and fluctuation developments, including their required vendored foundations.
Licenses and source notices are retained in `NOTICE`, `LICENSES/`, and the
vendor directories. [Provenance](PROVENANCE.json) records source identities,
module counts, adaptations, and the status of final file hashes. The
[claim map](submission/claims.json) connects the manuscript statements to the
five compared declarations and their proof endpoints. The historical
[verification record](verification/README.md) records the successful build check,
strict audit, and protected three-kernel replay of proof-source commit
`5551e62264a270fd5dcd396f36389eaf77eddebc`. That interface exported only the
lower-bound predicate for Corollary 1.7. At proof-source commit
`2fd7036fa3435aaacef2801c35ae95082d3f6806`, the fresh default build reported
`Build completed successfully (19626 jobs).`, and a strict audit of all five
exports passed using Lake's generated artifact setup. The original standalone
audit failed while loading a compiled module; that failure is retained alongside
the successful setup-based invocation. A **fresh protected canonical Comparator
and three-kernel replay remain pending**; see the
[Corollary 1.7 verification record](verification/corollary-1-7-convergence.md).
The other four compared statements and the retained proof development are
unchanged. Historical receipts remain evidence for their named source
revisions and do not certify the strengthened interface. No registry
acceptance is asserted.

## Build and verify

Install Elan and Python 3.11 or later. The project pins Lean `v4.35.0-rc2`
and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`; keep the included
toolchain and manifest.

```sh
lake exe cache get
lake build
lake build Challenge
lake env lean -j1 -DautoImplicit=false -DwarningAsError=true --setup .lake/build/ir/Audit.setup.json Audit.lean
```

The default targets are `Solution` and `Audit`; building `Challenge` checks
the independent statement surface. The strict command uses the artifact setup
generated by `lake build`, retaining both strict flags. Its recorded invocation
exited zero; the earlier invocation without `--setup` exited one during module
loading. The build's successful completion marker is preserved, but its original
parent-process exit code could not be recovered. To validate the metadata,
obtain the pinned official verifier outside this repository:

```sh
git clone https://github.com/PalomarRegistry/PalomarSubmission.git ../PalomarSubmission
git -C ../PalomarSubmission checkout d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44
python3 -m venv ../palomar-venv
../palomar-venv/bin/python -m pip install --require-hashes --no-deps -r ../PalomarSubmission/requirements.txt
PYTHONPATH=../PalomarSubmission ../palomar-venv/bin/python -c 'from pathlib import Path; from scripts.submission_contract import load_formalization_metadata; load_formalization_metadata(Path("formalization.yaml"))'
```

For a local statement and proof replay, use the toolchain-bundled Comparator
with Linux bubblewrap 0.12.0 available:

```sh
lake comparator --config comparator.json
```

Local building and the axiom audit alone do not establish independent
statement equality or acceptance by the external kernels. Official
verification uses a fresh canonical Challenge
against trusted Mathlib and checks the proof dependencies with Lean, NanoDa,
and con-ron. Use `comparator.json` for the eventual submission at an immutable
commit; the Palomar intake workflow is separate from local checks.

## Supporting manuscript

With TeX, BibTeX, and `latexmk` installed:

```sh
cd manuscript
latexmk -pdf -interaction=nonstopmode -halt-on-error -no-shell-escape main.tex
```

`manuscript/main.pdf` is the PDF of the accompanying revised manuscript. The
source includes the bibliography and a `.bbl`; TeX build byproducts are ignored.
The supplied authors' note and funding acknowledgement are preserved. The
formal-verification chapter records the strengthened Corollary 1.7 interface's
completed local build and strict audit, with historical protected checks scoped
to their named source revisions. Current protected-replay status is maintained
in the repository's verification records.

The repository retains the verified proof-source commit
`5551e62264a270fd5dcd396f36389eaf77eddebc`, verification-records commit
`351cc102439ff1d741d240391dfb62258605b4d2`, and manuscript-update commit
`6229df2fda534abfd64eb75027e99e5f83a706ea` in its history. The repository
transfer and manuscript-link update preserved every Lean source, the four
build/comparison controls, `formalization.yaml`, and the verification records
byte for byte. The subsequent Corollary 1.7 strengthening changes only the
two Lean interfaces; its compilation and replay status is recorded separately
above. The historical receipts are unchanged.

For Palomar intake, use the immutable release commit with `comparator.json`
and ensure the repository is public, as required by the
[pinned submission instructions](https://github.com/PalomarRegistry/PalomarSubmission/blob/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44/README.md).
The retained verification records do not constitute registry submission or
acceptance.
