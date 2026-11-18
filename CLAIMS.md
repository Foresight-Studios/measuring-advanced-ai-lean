# Claims cited in the comment, with their Lean proofs

The entries below are copied from the claims ledger of The Uncontainability Project, one per claim the comment cites. Each gives the source's words, the Lean declarations that bear on it (linked to the line in this repository), and the proposed verdict.

**Status of every verdict: proposed, not independently reviewed.** A Lean proof shows that the Lean statement is true. Whether the Lean statement says exactly what its source says is a separate check (statement-fidelity review), which has not yet been done for any claim here.

Tiers (from an internal content review, 2026-11-18) rate how much mathematics each proof carries, not whether it is correct: **1** definitional, **2** elementary, **3** premises carry the claim, **4** standard result re-applied, **5** real content.

Statuses: **CONFIRMED** (proved as stated) · **CONFIRMED IN CORRECTED FORM** (the source's statement is false or overstated as written; the corrected statement is the one proved) · **AMBIGUITY RESOLVED** (the proof fixes one reading of an ambiguous source and says why).

Some entries quote "the project sheet" or "the project survey": these are the project's working summaries of the papers. The papers themselves are linked in the README.

## Undecidability of alignment verification (MTH-C1, MTH-C3)

From the claims ledger of the Machines That Halt formalization, included in full at [`Vendor/MachinesThatHalt/CLAIMS-VERIFIED-2026-11-14.md`](Vendor/MachinesThatHalt/CLAIMS-VERIFIED-2026-11-14.md); its claim IDs C1 and C3 are cited here as MTH-C1 and MTH-C3.

### MTH-C1. Deciding alignment is undecidable
**Paper (Abstract; restated in Introduction and Background):** "The inner alignment problem, which asserts whether an arbitrary artificial intelligence (AI) model satisfices a non-trivial alignment function of its outputs given its inputs, is undecidable." · "We demonstrate that deciding whether an arbitrary AI system will always satisfice such a judge function is undecidable." · "By the reasoning of Rice's theorem, the property of perfect alignment of the AI should be undecidable in general, since it is a non-trivial semantic condition on the program's behavior."
**Lean:** `alignedVac_undecidable` ([`Aligned.lean:189`](Vendor/MachinesThatHalt/AlignmentUndecidability/Aligned.lean#L189)), `alignedTot_undecidable` ([`Aligned.lean:238`](Vendor/MachinesThatHalt/AlignmentUndecidability/Aligned.lean#L238)), `alignedVac_undecidable_by_reduction` ([`Reduction.lean:160`](Vendor/MachinesThatHalt/AlignmentUndecidability/Reduction.lean#L160)), `alignedTot_undecidable_by_reduction` ([`Reduction.lean:242`](Vendor/MachinesThatHalt/AlignmentUndecidability/Reduction.lean#L242)), `T2'_undecidable` ([`Reduction.lean:319`](Vendor/MachinesThatHalt/AlignmentUndecidability/Reduction.lean#L319)).
**Verdict:** The build proves the claim under both readings of "aligned," by three independent routes — Rice's theorem, an explicit reduction to the halting problem, and the diagonal adversary of entry C3. Both theorems take as their hypothesis that the alignment property is non-trivial — some system aligned, another not, the paper's Background framing. For the vacuous reading that condition is exactly the judge rejecting some pair (alignedVac_nontrivial_iff, Aligned.lean:171); for the totality reading it holds under the judge-level conditions (alignedTot_nontrivial_of_judge, Aligned.lean:208) and needs no computability beyond them.  
**Tier 4:** `alignedVac_undecidable` and `alignedTot_undecidable` are Mathlib's Rice theorem applied (11 and 12 lines, after a 2-line extensionality lemma); the second route builds explicit halting gadgets (25 and 31 lines). Low to middle of the tier, like CBF-23.

### MTH-C3. The informal adversary argument
**Paper (Informal proof):** "If we had such a verifier, we could build an adversarial model that fools the verifier." · "there would be at least one input i, if the verifier V had evaluated the bytes B_M′ of the model to be aligned, for which M′ would return a misaligned output o−, thus fooling the verifier. The complementary fooling example can also be constructed: if the verifier had evaluated the bytes B_M′ of the model to be misaligned, M′ would return an aligned output o+, thus also fooling the verifier." · "Thus, the only resolution to this apparent contradiction is the non-computability of the verifier V itself."
**Lean:** `T1_adversary` ([`Adversary.lean:100`](Vendor/MachinesThatHalt/AlignmentUndecidability/Adversary.lean#L100)), `T1_no_verifier_vac` ([`Adversary.lean:147`](Vendor/MachinesThatHalt/AlignmentUndecidability/Adversary.lean#L147)), `T1_no_verifier_tot` ([`Adversary.lean:159`](Vendor/MachinesThatHalt/AlignmentUndecidability/Adversary.lean#L159)); self-reference via `Nat.Partrec.Code.fixed_point₂`; the missing computation step via `partrec_approved_select` ([`Aligned.lean:128`](Vendor/MachinesThatHalt/AlignmentUndecidability/Aligned.lean#L128)); the base-model form of the paper's narrative — the adversary "would behave as the initial model M for most of its inputs and outputs" — as `T1_adversary_param` ([`Adversary.lean:251`](Vendor/MachinesThatHalt/AlignmentUndecidability/Adversary.lean#L251)).
**Verdict:** The build proves the argument: every computable verifier faces one code that fools it in one direction or the other, so no computable verifier decides alignment under either reading. The formalization supplies one step the paper leaves implicit — under the per-input reading of the non-triviality condition the adversary must compute an approved output for each input, which `Nat.rfind` delivers. The self-reference the paper justifies by appeal to quines and "Turing's Proof" is Kleene's recursion theorem, which Mathlib provides. `T1_adversary_param` restores the paper's framing with an arbitrary base model `m`: the constructed code follows `m` at every input other than the designated fooling input when the verifier says aligned, and is aligned at every input when the verifier says misaligned, so "behave as the initial model M for most of its inputs and outputs" holds verbatim in the aligned-verdict branch.  
**Tier 4:** `T1_adversary` (41 lines) builds the diagonal program with Mathlib's recursion theorem (`fixed_point₂`) and an unbounded search for an approved output; the form that agrees with a given model off one input is 94 lines. The technique is the standard proof of Rice's theorem; upper end of the tier.

## The other cited claims

### DHAR-2. The sample-size certificate
**Status:** CONFIRMED  
**Source (Project sheet, row "Dhar estimator bounds"):** "a battery of n tasks, with n at least ln(2/delta) over 2 epsilon squared, estimates the generality score to accuracy epsilon at confidence delta."  
**Lean:** `sample_size_certificate` ([`DharEstimator.lean:90`](UncontainabilityLean/Targets/DharEstimator.lean#L90)), `sample_size_certificate_original` ([`DharEstimator.lean:108`](UncontainabilityLean/Targets/DharEstimator.lean#L108)), `sample_size_certificate_proposed` ([`DharEstimator.lean:122`](UncontainabilityLean/Targets/DharEstimator.lean#L122)), `sample_size_738` ([`Examples.lean:49`](Submission/Examples.lean#L49))  
**Verdict:** Confirmed for a fixed model. Content review, 2026-11-18: the hypothesis δ < 1 is not needed and `sample_size_certificate` no longer carries it (drafted statement kept as `sample_size_certificate_original`). At ε = δ = 0.05 the smallest admissible n is 738 (`sample_size_738`).  
**Tier 4:** DHAR-1 plus algebra to solve for n; the 738 figure is a numeric check.

### DHAR-4. The multi-task rate 1/√(mn), eq. (14) and Theorem 1
**Status:** CONFIRMED IN CORRECTED FORM  
**Source (Paper, p. 7, Theorem 1; p. 8, eq. (14) and the sentence after it):** Theorem 1: "the generalization bound is reduced by approximately a factor of √n in the multi-task case." Eq. (14): "L_Q(h) ≤ (1/n) Σ_i L̂_{P_i}(h) + O(√((C + ln(1/δ))/(nm)))". After it: "for multi-task environments, the error decays much faster at a rate of 1/√(mn)".  
**Lean:** `eq14_single_term_fails` ([`DharEstimator.lean:367`](UncontainabilityLean/Targets/DharEstimator.lean#L367)), `two_level_bound_sharp` ([`DharSharp.lean:208`](UncontainabilityLean/Targets/DharSharp.lean#L208)), `two_level_bound_sharp_delta` ([`DharSharp.lean:266`](UncontainabilityLean/Targets/DharSharp.lean#L266))  
**Verdict:** Eq. (14) does not follow from eq. (12). `eq14_single_term_fails` gives an environment (two equally likely tasks with losses 0 and 1, one task drawn) in which, for every constant K, every estimate from more than 4K samples misses by more than √(K/(nm)). The corrected form: the within-task error does decay at √(ln(4/δ)/(2nm)) when all samples are jointly independent (`two_level_bound_sharp_delta`), and the between-task term √(ln(4/δ)/(2n)) remains, whatever m is. More samples per task cannot replace more tasks.  
**Tier 4:** Substantive correction. The counterexample is elementary (two tasks with constant losses 0 and 1); the corrected rate (`two_level_bound_sharp`) is Hoeffding under joint independence of all samples, a stronger assumption than DHAR-3 uses.

### NFL-1. Performance is algorithm-independent exactly when the prior is closed under relabelling
**Status:** CONFIRMED  
**Source (Project sheet, row "No-free-lunch escape"; Atlas CT-10):** "Performance is algorithm-independent exactly when the task distribution is closed under relabelling the search space"  
**Lean:** `nfl_adaptive_iff_permInvariant` ([`Sharp.lean:822`](Vendor/AISafetyAtlas/Learning/Sharp.lean#L822)), `orderedAgents_iff_not_permInvariant` ([`NFLEscape.lean:182`](UncontainabilityLean/Targets/NFLEscape.lean#L182))  
**Verdict:** Confirmed by the Atlas theorem, vendored unchanged and compiled with this build, for arbitrary real weights on a finite search space and non-revisiting adaptive agents. `orderedAgents_iff_not_permInvariant` restates it in the "ordered agents" form used below.  
**Tier 4:** The vendored Atlas theorem CT-10 carries the claim; the local restatement is an 11-line rearrangement.

### NFL-4. Rankings exist precisely inside the difficulty-restricted regime
**Status:** CONFIRMED IN CORRECTED FORM  
**Source (Project sheet, row "No-free-lunch escape"):** "so rankings exist precisely inside the difficulty-restricted regime."  
**Lean:** `orderedAgents_iff_not_permInvariant` ([`NFLEscape.lean:182`](UncontainabilityLean/Targets/NFLEscape.lean#L182)), `c2_pointMass_orderedAgents` ([`NFLEscape.lean:263`](UncontainabilityLean/Targets/NFLEscape.lean#L263))  
**Verdict:** "Precisely" is too strong: any weighting that is not relabelling-invariant gives ordered agents, whether or not it is based on difficulty (`c2_pointMass_orderedAgents`, a point mass on one task). Corrected form: rankings exist exactly where the weighting breaks relabelling symmetry; difficulty weighting is one way to break it.  
**Tier 4:** An 11-line logical rearrangement of Atlas CT-10 plus a point-mass example. Substantive correction of the project's own sheet ("precisely" is too strong), with no new mathematics.

### METR-5. Compounding, product form
**Status:** CONFIRMED  
**Source (Project sheet, row "METR horizon calculus"):** "a per-step failure rate epsilon holds reliability r only up to log(r)/log(1-epsilon) steps."  
**Lean:** `compound_product` ([`MetrHorizon.lean:152`](UncontainabilityLean/Targets/MetrHorizon.lean#L152)), `compound_product_original` ([`MetrHorizon.lean:161`](UncontainabilityLean/Targets/MetrHorizon.lean#L161)), `compound_product_proposed` ([`MetrHorizon.lean:172`](UncontainabilityLean/Targets/MetrHorizon.lean#L172)), `compound_product_floor_proposed` ([`MetrHorizon.lean:186`](UncontainabilityLean/Targets/MetrHorizon.lean#L186))  
**Verdict:** Confirmed as arithmetic: r ≤ (1 − ε)^n if and only if n ≤ log r / log(1 − ε). That (1 − ε)^n is the success probability of n independent steps is the reader's interpretation and is not part of the statement. Content review, 2026-11-18: the sheet's hypothesis r ≤ 1 is not needed and `compound_product` no longer carries it (the drafted statement is kept as `compound_product_original`). The monitor form with a floor, `compound_product_floor_proposed`, does need r ≤ 1.  
**Tier 2:** Log algebra; the unused hypothesis r ≤ 1 was removed in the content review. Independence of steps is the reader's interpretation, not in the statement.

### METR-6. Compounding, union-bound form
**Status:** CONFIRMED  
**Source (Project sheet, row "METR horizon calculus"):** "both compounding forms (the product form and the union bound)"  
**Lean:** `compound_union` ([`MetrHorizon.lean:196`](UncontainabilityLean/Targets/MetrHorizon.lean#L196))  
**Verdict:** Confirmed, more generally than stated: the measure need not be a probability measure, the failure events need not be measurable, and no independence is assumed.  
**Tier 2:** The union bound: finite subadditivity of a measure and a sum.

### GEN-7. Property 3 / Corollary 8: at fixed capability the step curve has the smallest expected difficulty and the largest generality
**Status:** CONFIRMED  
**Source (SI Corollary 8, PDF p. 36):** "given a fixed capability Ψ, the minimum expected difficulty H and the maximum generality Γ are obtained with a step agent characteristic function on h = Ψ."  
**Lean:** `spreadSq_nonneg` ([`Extremal.lean:146`](UncontainabilityLean/Generality/Extremal.lean#L146)), `spread_sq` ([`Extremal.lean:278`](UncontainabilityLean/Generality/Extremal.lean#L278)), `generality_le_step` ([`Extremal.lean:300`](UncontainabilityLean/Generality/Extremal.lean#L300)), `half_capability_le_expectedDifficulty` ([`Extremal.lean:308`](UncontainabilityLean/Generality/Extremal.lean#L308))  
**Verdict:** Confirmed, by a proof that is not the supplement's. A Lean proof shows that, for the generality metric as defined by Hernández-Orallo et al., every curve has 2M − Ψ² ≥ 0 (so spread is always defined), expected difficulty at least Ψ/2, and generality at most that of the step curve at Ψ. The supplement's exchange argument (from Proposition 7) does not establish a maximum; the Lean proof writes 2M − Ψ² as 2∫(h − Ψ)(ψ − σ) dh with σ the step curve, whose integrand is non-negative. Integrability of ψ and h·ψ(h) is assumed.  
**Tier 5:** `spreadSq_nonneg` is an original 14-line argument (2M − Ψ² = 2∫(h − Ψ)(ψ − σ) ≥ 0) that replaces the supplement's incomplete one. `generality_le_step` itself is `le_top`, since the step curve's generality is ⊤ by GEN-2.

### GEN-13. Project's own result (not in the paper): the extremal curves are unique; spread is 0 only for a step curve
**Status:** CONFIRMED  
**Source (Not stated in the paper. The step case is used without proof in the proof of SI Proposition 14, PDF p. 38, and in property 6, PDF p. 35):** "It is sufficient to see that both agents will have step functions." (proof of Prop. 14); "Agents with maximum generality Γ = ∞ are s-saturated with s = Ψ" (property 6)  
**Lean:** `spreadSq_eq_zero_iff` ([`Extremal.lean:166`](UncontainabilityLean/Generality/Extremal.lean#L166)), `spread_eq_zero_iff` ([`Extremal.lean:284`](UncontainabilityLean/Generality/Extremal.lean#L284)), `generality_eq_top_iff_step` ([`Extremal.lean:292`](UncontainabilityLean/Generality/Extremal.lean#L292)), `spreadSq_eq_max_iff` ([`Extremal.lean:228`](UncontainabilityLean/Generality/Extremal.lean#L228))  
**Verdict:** The project's own result. A Lean proof shows that a curve has S = 0 (equivalently Γ = ∞) if and only if it equals the step curve at its capability at almost every difficulty, and that a curve vanishing beyond q attains S² = 2Ψ(q − Ψ) if and only if it equals the reversed step almost everywhere. "Almost every" cannot be removed: changing a curve at a single difficulty changes no integral. So infinite generality gives saturation up to Ψ only outside a null set of difficulties.  
**Tier 5:** An original equality case: zero spread exactly for step curves, maximal spread exactly for reversed steps, almost everywhere (25 and 31 lines).

### GEN-16. Project's own result (not in the paper): failure below capability is at most S/√2
**Status:** CONFIRMED  
**Source (Not in the paper. First derived, unchecked, in `policy/bridge/08-generality-metric-proofs.md`):** With D = ∫₀^Ψ (1 − ψ(h)) dh the failure on tasks easier than the agent's capability: "S² ≥ 2D², that is, D ≤ S/√2."  
**Lean:** `deficit` ([`Transitivity.lean:132`](UncontainabilityLean/Generality/Transitivity.lean#L132)), `two_mul_deficit_sq_le_spreadSq` ([`Transitivity.lean:178`](UncontainabilityLean/Generality/Transitivity.lean#L178)), `deficit_le` ([`Transitivity.lean:200`](UncontainabilityLean/Generality/Transitivity.lean#L200)), `deficit_le_of_spread_le` ([`Transitivity.lean:211`](UncontainabilityLean/Generality/Transitivity.lean#L211)), `deficit_eq_excess` ([`Transitivity.lean:165`](UncontainabilityLean/Generality/Transitivity.lean#L165)), `deficit_bound_sharp` ([`Transitivity.lean:234`](UncontainabilityLean/Generality/Transitivity.lean#L234))  
**Verdict:** The project's own result. A Lean proof shows that, for the generality metric as defined by Hernández-Orallo et al., every curve with capability Ψ and spread S has D ≤ S/√2, that D also equals the success on tasks harder than Ψ, and that the bound is attained (for 0 < D ≤ Ψ) by the curve equal to 1 on [0, Ψ − D] and [Ψ, Ψ + D]. It is a statement about a curve, in units of difficulty. It does not say which tasks are failed, and nothing here shows that it applies to a measured system or relates to harm.  
**Tier 5:** An original, short result (D ≤ S/√2) with a sharpness example (34 lines). A statement about a curve, not about a measured system.
