/-
# Axiom check for every theorem the comment cites

Each block runs `#print axioms` inside `#guard_msgs`: `lake build` fails if a proof depends on
anything beyond Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), such as
`sorryAx` (an unfinished proof) or `Lean.ofReduceBool` (`native_decide`). This checks that the proofs
are complete. It does not check that each statement says what its source says.
-/
import UncontainabilityLean
import AlignmentUndecidability
import AISafetyAtlas.Learning.Sharp
import Submission.Examples

/-- info: 'UncontainabilityLean.DharEstimator.sample_size_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.DharEstimator.sample_size_certificate

/-- info: 'UncontainabilityLean.Review.PaperExamples.sample_size_738' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.Review.PaperExamples.sample_size_738

/-- info: 'UncontainabilityLean.DharEstimator.eq14_single_term_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.DharEstimator.eq14_single_term_fails

/-- info: 'UncontainabilityLean.DharEstimator.two_level_bound_sharp_delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.DharEstimator.two_level_bound_sharp_delta

/-- info: 'AISafetyAtlas.Learning.nfl_adaptive_iff_permInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AISafetyAtlas.Learning.nfl_adaptive_iff_permInvariant

/-- info: 'UncontainabilityLean.NFLEscape.orderedAgents_iff_not_permInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.NFLEscape.orderedAgents_iff_not_permInvariant

/-- info: 'UncontainabilityLean.NFLEscape.c2_pointMass_orderedAgents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.NFLEscape.c2_pointMass_orderedAgents

/-- info: 'UncontainabilityLean.MetrHorizon.compound_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.MetrHorizon.compound_product

/-- info: 'UncontainabilityLean.MetrHorizon.compound_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.MetrHorizon.compound_union

/-- info: 'UncontainabilityLean.Generality.spreadSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.Generality.spreadSq_nonneg

/-- info: 'UncontainabilityLean.Generality.generality_le_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.Generality.generality_le_step

/-- info: 'UncontainabilityLean.Generality.spreadSq_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.Generality.spreadSq_eq_zero_iff

/-- info: 'UncontainabilityLean.Generality.spread_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.Generality.spread_eq_zero_iff

/-- info: 'UncontainabilityLean.Generality.deficit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.Generality.deficit_le

/-- info: 'UncontainabilityLean.Generality.deficit_bound_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UncontainabilityLean.Generality.deficit_bound_sharp

/-- info: 'AlignmentUndecidability.alignedVac_undecidable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlignmentUndecidability.alignedVac_undecidable

/-- info: 'AlignmentUndecidability.alignedTot_undecidable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlignmentUndecidability.alignedTot_undecidable

/-- info: 'AlignmentUndecidability.alignedVac_undecidable_by_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlignmentUndecidability.alignedVac_undecidable_by_reduction

/-- info: 'AlignmentUndecidability.alignedTot_undecidable_by_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlignmentUndecidability.alignedTot_undecidable_by_reduction

/-- info: 'AlignmentUndecidability.T2'_undecidable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlignmentUndecidability.T2'_undecidable

/-- info: 'AlignmentUndecidability.T1_adversary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlignmentUndecidability.T1_adversary

/-- info: 'AlignmentUndecidability.T1_no_verifier_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlignmentUndecidability.T1_no_verifier_vac

/-- info: 'AlignmentUndecidability.T1_no_verifier_tot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlignmentUndecidability.T1_no_verifier_tot
