# Machine-checked results on measuring advanced AI systems

This repository holds the machine-checked proofs cited in The Uncontainability Project's public comment on the U.S. Treasury's proposed rule 31 CFR Part 851 (Outbound Investment Security Program; docket [TREAS-DO-2026-0595](https://www.regulations.gov/docket/TREAS-DO-2026-0595), RIN 1505-AC94). It contains only those results, so that a reader can check each one against its source.

**Status: unreviewed.** Every proof here compiles in Lean 4 with Mathlib, with no unfinished steps and no axioms beyond Lean's standard three (checked by machine in [`Submission/Axioms.lean`](Submission/Axioms.lean)). A Lean proof shows that a precisely stated claim is true. It does not show that the Lean statement says exactly what its source says; that independent review has not yet been done. Nor does it show that a mathematical model describes any deployed system.

## The claims

| Claim | Tier | What a Lean proof shows | Source | Lean |
| --- | --- | --- | --- | --- |
| DHAR-2 | 4 | 738 independent task scores estimate a mean score within 5 points at 95% confidence | Dhar, Oldenburg & Søgaard 2025 | [`DharEstimator.lean`](UncontainabilityLean/Targets/DharEstimator.lean#L90), [`Examples.lean`](Submission/Examples.lean#L49) |
| DHAR-4 (corrected form) | 4 | The published 1/√(nm) error rate does not hold in general; more runs per task cannot replace more tasks | Dhar, Oldenburg & Søgaard 2025 | [`DharEstimator.lean`](UncontainabilityLean/Targets/DharEstimator.lean#L367), [`DharSharp.lean`](UncontainabilityLean/Targets/DharSharp.lean#L266) |
| NFL-1 | 4 | Search agents perform alike exactly when the weighting of tasks is unchanged by relabelling | Igel & Toussaint 2004; Schumacher, Vose & Whitley 2001 | [`Sharp.lean`](Vendor/AISafetyAtlas/Learning/Sharp.lean#L822), [`NFLEscape.lean`](UncontainabilityLean/Targets/NFLEscape.lean#L182) |
| NFL-4 (corrected form) | 4 | Agents can be ranked exactly when the weighting breaks relabelling symmetry | The project's survey, from the same results | [`NFLEscape.lean`](UncontainabilityLean/Targets/NFLEscape.lean#L263) |
| METR-5 | 2 | Overall reliability r holds over n steps of per-step failure ε exactly when n ≤ log r / log(1 − ε) | Kwa et al. 2025 | [`MetrHorizon.lean`](UncontainabilityLean/Targets/MetrHorizon.lean#L152) |
| METR-6 | 2 | n steps each failing with probability at most ε fail together with probability at most nε, with no independence assumed | Kwa et al. 2025 | [`MetrHorizon.lean`](UncontainabilityLean/Targets/MetrHorizon.lean#L196) |
| MTH-C1, MTH-C3 | 4, 4 | No computable procedure decides a non-trivial alignment property for every program | Melo, Máximo, Soma & Castro 2025 | [`Aligned.lean`](Vendor/MachinesThatHalt/AlignmentUndecidability/Aligned.lean#L189), [`Adversary.lean`](Vendor/MachinesThatHalt/AlignmentUndecidability/Adversary.lean#L100) |
| GEN-7 | 5 | The spread of the generality metric is always defined and non-negative; the step curve is the most general | Hernández-Orallo et al. 2021 | [`Extremal.lean`](UncontainabilityLean/Generality/Extremal.lean#L146) |
| GEN-13 | 5 | Spread is zero only for a step curve | Project's own result, on Hernández-Orallo et al. 2021 | [`Extremal.lean`](UncontainabilityLean/Generality/Extremal.lean#L166) |
| GEN-16 | 5 | A system with spread S fails on at most S/√2 difficulty-units of the tasks below its capability; the bound is attained | Project's own result, on Hernández-Orallo et al. 2021 | [`Transitivity.lean`](UncontainabilityLean/Generality/Transitivity.lean#L200) |

Each claim's full entry (the source's words, every Lean declaration, the verdict, the tier and why) is in [`CLAIMS.md`](CLAIMS.md). The tier rates how much mathematics the proof carries, from an internal content review: 1 definitional, 2 elementary, 3 premises carry the claim, 4 standard result re-applied, 5 real content. It is not a measure of correctness or usefulness.

## Sources

- Dhar, Oldenburg & Søgaard 2025, *On the Measure of a Model*: [arXiv 2511.11773](https://arxiv.org/abs/2511.11773)
- Kwa et al. 2025, *Measuring AI Ability to Complete Long Software Tasks*: [arXiv 2503.14499](https://arxiv.org/abs/2503.14499)
- Igel & Toussaint 2004, *A No-Free-Lunch Theorem for Non-Uniform Distributions of Target Functions*, Journal of Mathematical Modelling and Algorithms 3: [doi 10.1023/B:JMMA.0000049381.24625.f7](https://doi.org/10.1023/B:JMMA.0000049381.24625.f7)
- Schumacher, Vose & Whitley 2001, *The No Free Lunch and Problem Description Length*, Proceedings of GECCO 2001
- Brčić 2026, AI Safety Formalization Atlas (Lean formalization of the no-free-lunch characterization, rung CT-10): [github.com/mbrcic/ai-safety-formalization-atlas](https://github.com/mbrcic/ai-safety-formalization-atlas/tree/ecf4c4eda25963fc77bf6fe65f8e409b564ed0b4)
- Melo, Máximo, Soma & Castro 2025, *Machines that halt resolve the undecidability of artificial intelligence alignment*, Scientific Reports 15, 15591: [doi 10.1038/s41598-025-99060-2](https://doi.org/10.1038/s41598-025-99060-2)
- Hernández-Orallo, Loe, Cheke, Martínez-Plumed & Ó hÉigeartaigh 2021, *General intelligence disentangled via a generality metric for natural and artificial intelligence*, Scientific Reports 11, 22822: [doi 10.1038/s41598-021-01997-7](https://doi.org/10.1038/s41598-021-01997-7) (properties and proofs in its Supplementary Information, §E–F)

The research results the comment cites without a Lean proof (Benton et al. 2024; Greenblatt et al. 2024; Hackenburg et al. 2025; Zhou et al. 2025) are listed with links in the comment's Annex B.

## Ratings for the research brief

The folder [`brief-ratings/`](brief-ratings/) holds the ratings behind the project's research brief *Can Advanced AI Systems Be Told Apart by Measurement?*. The brief rates 55 ways of classifying AI systems on six tests, and the folder gives each rating with its reason and a source link.

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

- `UncontainabilityLean/` is copied unchanged from The Uncontainability Project's working repository (private), commit `062e4d7`. Comments in these files that mention `papers/`, `policy/` or `NOTES.md` refer to that repository.
- `Vendor/AISafetyAtlas/` holds three files copied unchanged from the AI Safety Formalization Atlas at commit `ecf4c4e` (Apache-2.0; licence in that folder).
- `Vendor/MachinesThatHalt/` holds the formalization of Melo et al. 2025 used for MTH-C1 and MTH-C3, with its claims ledger and licence, copied unchanged from the project's working repository (upstream commit `6aa93b4`, Apache-2.0). The copyright notices in its files are kept as the licence requires.
- `Submission/Examples.lean` copies the worked example for DHAR-2 from the project's repository unchanged; `Submission/Axioms.lean` is generated for this repository.
- The statements in `UncontainabilityLean/` were drafted with Claude (Anthropic) and proved by Claude Fable, an AI prover; those in `Vendor/MachinesThatHalt/` were produced with GLM-5.3 and Claude. Every proof is checked by Lean.

## Licence

Apache License 2.0 ([`LICENSE`](LICENSE)). The Uncontainability Project, [agiuncontainability.org](https://agiuncontainability.org).
