# Machine-checked results on measuring advanced AI systems

This repository holds the machine-checked proofs cited in The Uncontainability Project's public comment on the U.S. Treasury's proposed rule 31 CFR Part 851 (Outbound Investment Security Program; docket [TREAS-DO-2026-0595](https://www.regulations.gov/docket/TREAS-DO-2026-0595), RIN 1505-AC94). It contains only those results, so that a reader can check each one against its source.

**Status: unreviewed.** Every proof here compiles in Lean 4 with Mathlib, with no unfinished steps and no axioms beyond Lean's standard three (checked by machine in [`Submission/Axioms.lean`](Submission/Axioms.lean)). A Lean proof shows that a precisely stated claim is true. It does not show that the Lean statement says exactly what its source says; that independent review has not yet been done. Nor does it show that a mathematical model describes any deployed system.

## The claims

| Claim | What a Lean proof shows | Source | Lean |
| --- | --- | --- | --- |
| DHAR-2 | 738 independent task scores estimate a mean score within 5 points at 95% confidence | Dhar, Oldenburg & Søgaard 2025 | [`DharEstimator.lean`](UncontainabilityLean/Targets/DharEstimator.lean#L88), [`Examples.lean`](Submission/Examples.lean#L49) |
| DHAR-4 (corrected form) | The published 1/√(nm) error rate does not hold in general; more runs per task cannot replace more tasks | Dhar, Oldenburg & Søgaard 2025 | [`DharEstimator.lean`](UncontainabilityLean/Targets/DharEstimator.lean#L354), [`DharSharp.lean`](UncontainabilityLean/Targets/DharSharp.lean#L266) |
| NFL-1 | Search agents perform alike exactly when the weighting of tasks is unchanged by relabelling | Igel & Toussaint 2004; Schumacher, Vose & Whitley 2001 | [`Sharp.lean`](Vendor/AISafetyAtlas/Learning/Sharp.lean#L822), [`NFLEscape.lean`](UncontainabilityLean/Targets/NFLEscape.lean#L182) |
| NFL-4 (corrected form) | Agents can be ranked exactly when the weighting breaks relabelling symmetry | The project's survey, from the same results | [`NFLEscape.lean`](UncontainabilityLean/Targets/NFLEscape.lean#L263) |
| METR-5 | Overall reliability r holds over n steps of per-step failure ε exactly when n ≤ log r / log(1 − ε) | Kwa et al. 2025 | [`MetrHorizon.lean`](UncontainabilityLean/Targets/MetrHorizon.lean#L136) |
| METR-6 | n steps each failing with probability at most ε fail together with probability at most nε, with no independence assumed | Kwa et al. 2025 | [`MetrHorizon.lean`](UncontainabilityLean/Targets/MetrHorizon.lean#L171) |
| MTH-C1, MTH-C3 | No computable procedure decides a non-trivial alignment property for every program | Melo, Máximo, Soma & Castro 2025 | Zach Schlosser's repository (below) |
| GEN-7 | The spread of the generality metric is always defined and non-negative; the step curve is the most general | Hernández-Orallo et al. 2021 | [`Extremal.lean`](UncontainabilityLean/Generality/Extremal.lean#L146) |
| GEN-13 | Spread is zero only for a step curve | Project's own result, on Hernández-Orallo et al. 2021 | [`Extremal.lean`](UncontainabilityLean/Generality/Extremal.lean#L166) |
| GEN-16 | A system with spread S fails on at most S/√2 difficulty-units of the tasks below its capability; the bound is attained | Project's own result, on Hernández-Orallo et al. 2021 | [`Transitivity.lean`](UncontainabilityLean/Generality/Transitivity.lean#L200) |

Each claim's full entry (the source's words, every Lean declaration, the verdict) is in [`CLAIMS.md`](CLAIMS.md).

## Sources

- Dhar, Oldenburg & Søgaard 2025, *On the Measure of a Model*: [arXiv 2511.11773](https://arxiv.org/abs/2511.11773)
- Kwa et al. 2025, *Measuring AI Ability to Complete Long Software Tasks*: [arXiv 2503.14499](https://arxiv.org/abs/2503.14499)
- Igel & Toussaint 2004, *A No-Free-Lunch Theorem for Non-Uniform Distributions of Target Functions*, Journal of Mathematical Modelling and Algorithms 3: [doi 10.1023/B:JMMA.0000049381.24625.f7](https://doi.org/10.1023/B:JMMA.0000049381.24625.f7)
- Schumacher, Vose & Whitley 2001, *The No Free Lunch and Problem Description Length*, Proceedings of GECCO 2001
- Brčić 2026, AI Safety Formalization Atlas (Lean formalization of the no-free-lunch characterization, rung CT-10): [github.com/mbrcic/ai-safety-formalization-atlas](https://github.com/mbrcic/ai-safety-formalization-atlas/tree/ecf4c4eda25963fc77bf6fe65f8e409b564ed0b4)
- Melo, Máximo, Soma & Castro 2025, *Machines that halt resolve the undecidability of artificial intelligence alignment*, Scientific Reports 15, 15591: [doi 10.1038/s41598-025-99060-2](https://doi.org/10.1038/s41598-025-99060-2). Lean formalization by Zach Schlosser: [github.com/ZachSchlosser/machines-that-halt-lean](https://github.com/ZachSchlosser/machines-that-halt-lean/tree/6aa93b4f5010b64d4377af97ca97994c319d46d2) (claims C1 and C3 of its [ledger](https://github.com/ZachSchlosser/machines-that-halt-lean/blob/6aa93b4f5010b64d4377af97ca97994c319d46d2/CLAIMS-VERIFIED-2026-11-14.md))
- Hernández-Orallo, Loe, Cheke, Martínez-Plumed & Ó hÉigeartaigh 2021, *General intelligence disentangled via a generality metric for natural and artificial intelligence*, Scientific Reports 11, 22822: [doi 10.1038/s41598-021-01997-7](https://doi.org/10.1038/s41598-021-01997-7) (properties and proofs in its Supplementary Information, §E–F)

The research results the comment cites without a Lean proof (Benton et al. 2024; Greenblatt et al. 2024; Hackenburg et al. 2025; Zhou et al. 2025) are listed with links in the comment's Annex B.

## Checking the proofs

Install Lean with [elan](https://github.com/leanprover/elan), then from this directory:

```bash
lake exe cache get
```

```bash
lake build
```

A successful build means every proof here checks, and [`Submission/Axioms.lean`](Submission/Axioms.lean) confirms that each cited theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

- `UncontainabilityLean/` is copied unchanged from The Uncontainability Project's working repository (private), commit `4620c3d`. Comments in these files that mention `papers/`, `policy/` or `NOTES.md` refer to that repository.
- `Vendor/AISafetyAtlas/` holds three files copied unchanged from the AI Safety Formalization Atlas at commit `ecf4c4e` (Apache-2.0; licence in that folder).
- `Submission/Examples.lean` copies the worked example for DHAR-2 from the project's repository unchanged; `Submission/Axioms.lean` is generated for this repository.
- Statements were drafted with Claude (Anthropic); the proofs were written by Claude Fable, an AI prover, and checked by Lean.

## Licence

Apache License 2.0 ([`LICENSE`](LICENSE)). The Uncontainability Project, [agiuncontainability.org](https://agiuncontainability.org).
