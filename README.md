# Entropy and large deviations for Latin squares — Lean formalization

Juan Pablo Traverso Gianini · Preprint 1.0 · Apache-2.0

[Read the paper on alphaXiv](https://www.alphaxiv.org/abs/2611.latin-squares-entropy-large-deviations) ·
[Bilingual manuscript, companion, original Lean archive and audit](https://github.com/jtraverso/latinon-entropy-ldp/releases/tag/latinon-v1.0)

This repository contains the substantive Lean development for the Latinon
large deviation principle and its finite-pattern counting consequence. It is
prepared for Palomar's independent comparison and kernel checks. The published
preprint archive remains unchanged; `evidence/PACKAGING.json` records the source
archive hash and every module-system adapter in this repository.

`Challenge.lean` is the standalone, Mathlib-only statement interface.
`Solution.lean` re-exports the proved declarations through the canonical
`LatinonFormalization` entry point. It never imports Challenge. All mathematical
definitions on the statement side have concrete values; none is an unspecified
definition supplied merely to make a theorem hold.

## Compared claims

The nine principal declarations are:

| Declaration in `LatinonEntropy` | Meaning |
| --- | --- |
| `closed_uniform_latinon_upper` | The global closed-set LDP upper bound at speed n², with a nonstrict extended-rate floor. |
| `open_uniform_latinon_lower` | The global open-set LDP lower bound with a finite-rate witness. |
| `latinon_rate_lowerSemicontinuous` | Lower semicontinuity of the extended KL rate in the full ordered cut topology. |
| `latinon_full_cut_compact` | Compactness of the full ordered Latinon space. |
| `latinon_rate_sublevels_compact` | Compactness of rate sublevels, hence goodness of the rate. |
| `finite_rate_standard_pattern_log_count` | Bilateral logarithmic counts for any finite family of strict order patterns and any finite-rate target. |
| `empty_standard_pattern_fiber_eventually_zero` | Infeasible exact Latinon fibers have eventually empty finite neighborhoods. |
| `finite_latin_tensor_lower_bound` | A common lower-counting threshold over bounded positive tristochastic profiles. |
| `correction_lemma_five` | Exact-support transportation correction with entry bounds and coefficient 5/2 in total margin defect. |

Six additional compared declarations establish the three pseudometric identities
and the three uniform pair marginals of the finite-square embedding. They permit
the Challenge to define its actual topology and uniform finite law explicitly
without importing project proofs. Every hole in Challenge is named in
`comparator.json`; the proved Solution may use only `propext`, `Classical.choice`
and `Quot.sound`.

The distance includes independent row and column alignments, both order terms,
and measurable row/column cuts tested on symbol intervals. The finite law is the
uniform law on labeled Latin squares pushed forward by the grid embedding. The
rate is KL relative to uniform cube volume, retaining infinity for singular
measures. The entropy convention is Ent = -KL.

Pattern densities use increasing row and column samples and the product of
binomial coefficients. The patterns have distinct ranks. For every finite-rate
target, accuracy and a maximum radius are fixed first; a target-dependent radius
is chosen next, before the threshold for the order. This supplies local
asymptotic counts, not exact prescribed finite-n densities. The connection with
GHHS Conjecture 12.4 (arXiv v3), including its entropy-sign correction and the
model comparison, is detailed in Sections 1–2 of the paper. Infinite-rate
closed-set upper bounds and empty fibers retain their separate quantifiers.

The correction coefficient 5/2 is a proved refinement under the original
hypotheses. It is not claimed to be optimal. CDR and bipartite-factorization
applications are included in the source but are not separate claims in this
Comparator configuration. The CDR family assumes a supplied completed base and
keeps its residue fixed.

## Proof architecture and provenance

The lower construction exposes rows successively. Transportation correction on
the available regular support controls margin defects, permanental estimates
control the corrected row law, and a stopped recursion yields the entropy loss
of two units per cell. Finite-partition entropy gives the matching upper bound.
Approximation, full-distance compactness and contraction produce the LDP and
the local pattern formula. The paper gives the written proofs and a bilingual
ledger of 23 core steps and eight application steps.

Nine Graphon modules originate from Cameron Freer's development at
`9f7be59fa754d260a544b4cfd83d6a5b94f7552e`. Original credits and compatibility
edits are preserved in `evidence/GRAPHON_PROVENANCE.json` and
`licenses/graphon-Apache-2.0.txt`. The finite CDR source cut and its representation
adapters are recorded in `evidence/series_cdr_provenance.json`. Their historical
hashes describe the published inputs before this package's documented module
header and visibility changes.

The [published audit](https://github.com/jtraverso/latinon-entropy-ldp/blob/4bf8be21e0dfe72afe7039d649098ebfd5265b73/publication/LATINON_RELEASE_AUDIT.json)
distinguishes the complete 309-module reconstruction from the subsequent cached
incremental check of the final 310-module archive. It is historical evidence for
the published source, not a build claim about this repackaged commit.
The [scoped literature review](https://github.com/jtraverso/latinon-entropy-ldp/blob/4bf8be21e0dfe72afe7039d649098ebfd5265b73/publication/audit/LITERATURE_REVIEW.md)
records the priority search and its limits. The internal review is distinct from
journal peer review and exhaustive priority certification.

## GitHub preflight

No local Lean or Lake build is performed during this submission preparation.
The manually dispatched `palomar-preflight.yml` calls Palomar's official full
workflow at a pinned revision, including Comparator and independent kernel
checks. Its report must say `pass` for the exact submitted commit before intake.
Running the workflow is not itself a Palomar submission or registration.

The substantive source and mathematical responsibility belong to Juan Pablo
Traverso Gianini. AI assistance in proof implementation and editing is disclosed
in `formalization.yaml`.
