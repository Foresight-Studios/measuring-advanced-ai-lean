/-
# No-free-lunch escape  (new construction on AISFA — no index ID; original theorem)

Fable block 3 · priority 4 (stretch).

Sheet row: "Performance is algorithm-independent exactly when the task distribution is
closed under relabelling the search space, and almost no distribution is, so over
unweighted distributions no breadth ranking exists. The escape runs the other way: under
any difficulty-weighted distribution on a finite task space, ordered agents exist, so
rankings exist precisely inside the difficulty-restricted regime."

SOURCE (located 2026-11-15). "AISFA" is the AI Safety Formalization Atlas (Brčić, 2026,
Apache-2.0): https://github.com/mbrcic/ai-safety-formalization-atlas , pinned at commit
ecf4c4eda25963fc77bf6fe65f8e409b564ed0b4 (v0.8.0, Lean v4.33.0). The characterization
being consumed is its rung CT-10:

  * `AISafetyAtlas.Learning.Sharp.nfl_adaptive_iff_permInvariant` (Learning/Sharp.lean):
    for any real weight `P : (X → Y) → ℝ` on a finite search space, every pair of
    non-revisiting adaptive algorithms has the same weighted performance under every
    performance measure `Ψ` and every sample length `m`  ↔  `PermInvariant P`
    (`∀ π f, P (f ∘ π) = P f`). Igel–Toussaint 2004; Schumacher–Vose–Whitley 2001.
  * `AISafetyAtlas.Combinatorics.card_closedUnderPermutation_nonempty`
    (Combinatorics/PermInvariance.lean): the count behind "almost no prior is closed".
  Dependencies: those two files plus `AISafetyAtlas/Learning.lean`; Mathlib only.

WHERE THE CLAIM COMES FROM. The Atlas supplies only CT-10 (above). It contains no
difficulty-weighted "escape": the escape is item 6 of the project survey "Formal Approaches
to Uncontainability", which labels it "new construction, not yet proved". Its author is not
confirmed (not Zach, per the project owner). So there is no owner definition to wait for:
the statement below is Claude's best reading, chosen because the corrected claim follows
rigorously from CT-10. Every statement stays `-- STATEMENT UNREVIEWED`; the reviewer checks
the adaptations listed here.

SPEC (best reading).
  Setting: the Atlas's `X Y` (finite), `AdaptiveRule X Y m`, `ruleVisit`, `weightedTrace`.
  Non-revisiting:  `∀ c, Function.Injective (ruleVisit r c)`  (the Atlas's hypothesis).

  def  difficulty-weighted:  `d : (X → Y) → ℕ` (difficulty of a task) and `w : ℕ → ℝ` with
       `StrictAnti w` (harder tasks get less weight); the weight is `P f = w (d f)`.
  def  label-sensitive difficulty:  `∃ (π : Equiv.Perm X) (f : X → Y), d (f ∘ π) ≠ d f`.
  def  ordered agents:  `m`, a performance measure `Ψ`, and non-revisiting
       `r₁ r₂ : AdaptiveRule X Y m` with `weightedTrace P Ψ r₁ < weightedTrace P Ψ r₂`.

  T1 (escape)      StrictAnti w ∧ label-sensitive d  ⇒  ordered agents exist.
  T2 (boundary)    d label-blind (∀ π f, d (f ∘ π) = d f)  ⇒  for every w, all
                   non-revisiting agents tie under every Ψ and m.
  T3 (iff)         for StrictAnti w: ordered agents exist  ↔  d is label-sensitive.
  T4 (general)     for any w (not necessarily monotone): ordered agents exist
                   ↔  ∃ π f, w (d (f ∘ π)) ≠ w (d f).
  T5 (example)     a concrete structural difficulty on `X = Fin n` (for instance the number
                   of positions i with f i ≠ f (i+1)), a proof that it is label-sensitive,
                   and a computed pair of agents with different performance.

ADAPTATIONS FROM THE SURVEY WORDING (each is a review item).
  A1. "distribution" → any real weight `w ∘ d`. The Atlas theorem holds for arbitrary real
      weights; normalizing to a probability distribution changes nothing.
  A2. "difficulty-weighted" → `w ∘ d` with `w` strictly decreasing. A non-strict `w` is
      covered by T4.
  A3. "ordered agents" → one strictly better/worse pair. A ranking over a named family of
      agents, or a best agent, is a stronger claim and is not stated.
  A4. "free lunch" → a performance gap for SOME performance measure Ψ and SOME length m
      (in the Atlas's proof, an indicator measure at m = |X| with fixed-order agents). It
      does not say the gap appears under the measure a given evaluation uses.

CORRECTIONS TO THE SURVEY AND SHEET (each proved, not just asserted).
  C1. "under any difficulty-weighted distribution, ordered agents exist" is false as
      written: T2 gives a counterexample whenever difficulty ignores labelling (constant
      difficulty gives the uniform prior, where no-free-lunch holds). The claim needs a
      label-sensitive difficulty measure (T3).
  C2. "rankings exist precisely inside the difficulty-restricted regime" is also too
      strong: by CT-10, ANY weighting that is not relabelling-invariant gives ordered
      agents, difficulty-based or not. Difficulty weighting is one way to break the
      symmetry, not the only one.
  C3. "almost no prior is closed under relabelling": the Atlas count is for SETS of tasks
      (indicator weights), not for real-valued priors. Cite it as such.

RISK. T1–T4 are short corollaries of CT-10. The substantive content is the corrections and
T5. If the project wants a stronger contribution, the next step is a quantitative
escape (a lower bound on the performance gap in terms of how unevenly w ∘ d weights a
relabelling orbit), which is not specified here.
-/
import Mathlib
import AISafetyAtlas.Learning.Sharp

/-
## Formalization (session 2, block C2)

-- STATEMENT UNREVIEWED: every definition and theorem statement below was written by Fable
-- from the SPEC in the header above (which is itself "Claude's best reading" of item 6 of
-- the project survey "Formal Approaches to Uncontainability"; the survey is not in
-- `papers/`). The no-free-lunch characterization that everything rests on is vendored from
-- the AI Safety Formalization Atlas (`Vendor/AISafetyAtlas/`, see its README) and is
-- consumed as given. A reviewer must check the statements, the adaptations A1–A4 and the
-- corrections C1–C3 against `STATEMENT_REVIEW.md` before anything here is called certified.

Map from the SPEC to Lean names (all in `UncontainabilityLean.NFLEscape`):

  difficulty-weighted weight `P f = w (d f)`     `diffWeight w d`
  label-sensitive difficulty                      `LabelSensitive d`
  label-blind difficulty                          `LabelBlind d`
  ordered agents                                  `OrderedAgents P`
  T1 (escape)                                     `escape`
  T2 (boundary)                                   `boundary`, `boundary_not_orderedAgents`
  T3 (iff)                                        `orderedAgents_iff_labelSensitive`
  T4 (general)                                    `orderedAgents_diffWeight_iff`
  T5 (example)                                    `flips`, `flips_labelSensitive`,
                                                  `flipsExample`, `flipsExample_orderedAgents`
  C1 (survey claim false as written)              `c1_constant_difficulty_no_ordering`
  C2 (difficulty is not the only escape)          `orderedAgents_iff_not_permInvariant`,
                                                  `c2_pointMass_orderedAgents`
  C3 (the Atlas count is for sets)                `c3_count_is_for_sets`
  quantitative escape (block C3, stretch)         `exists_agents_gap_eq`,
                                                  `exists_agents_gap_eq_diffWeight`
-/

open AISafetyAtlas.Learning AISafetyAtlas.Combinatorics Function
open Classical

namespace UncontainabilityLean.NFLEscape

universe uX uY

variable {X : Type uX} {Y : Type uY}

/-! ### Definitions -/

-- STATEMENT UNREVIEWED. Source: SPEC, "def difficulty-weighted" (header of this file);
-- adaptations A1, A2.
/-- The difficulty-weighted weight on tasks: task `f : X → Y` has difficulty `d f : ℕ` and
receives weight `w (d f)`. For "harder tasks get less weight", `w` is `StrictAnti`. The
weight is an arbitrary real function of the difficulty: it is not required to be
nonnegative or to sum to one (adaptation A1). -/
def diffWeight (w : ℕ → ℝ) (d : (X → Y) → ℕ) : ObjectiveWeight X Y := fun f => w (d f)

-- STATEMENT UNREVIEWED. Source: SPEC, "def label-sensitive difficulty".
/-- A difficulty measure is label-sensitive if relabelling the search space changes the
difficulty of at least one task. -/
def LabelSensitive (d : (X → Y) → ℕ) : Prop :=
  ∃ (π : Equiv.Perm X) (f : X → Y), d (f ∘ π) ≠ d f

-- STATEMENT UNREVIEWED. Source: SPEC, T2, "d label-blind (∀ π f, d (f ∘ π) = d f)".
/-- A difficulty measure is label-blind if relabelling the search space never changes the
difficulty of a task. -/
def LabelBlind (d : (X → Y) → ℕ) : Prop :=
  ∀ (π : Equiv.Perm X) (f : X → Y), d (f ∘ π) = d f

-- STATEMENT UNREVIEWED. Source: SPEC, "def ordered agents"; adaptations A3, A4.
/-- Ordered agents exist under the weight `P`: there are a sample length `m`, a performance
measure `Ψ` on length-`m` cost sequences, and two non-revisiting adaptive rules, one with
strictly smaller weighted performance than the other. Non-revisiting is the Atlas's
hypothesis `∀ c, Injective (ruleVisit r c)`. -/
def OrderedAgents [Fintype X] [Fintype Y] (P : ObjectiveWeight X Y) : Prop :=
  ∃ (m : ℕ) (Ψ : (Fin m → Y) → ℝ) (r₁ r₂ : AdaptiveRule X Y m),
    (∀ c, Injective (ruleVisit r₁ c)) ∧ (∀ c, Injective (ruleVisit r₂ c)) ∧
    weightedTrace P Ψ r₁ < weightedTrace P Ψ r₂

theorem labelSensitive_iff_not_labelBlind (d : (X → Y) → ℕ) :
    LabelSensitive d ↔ ¬LabelBlind d := by
  unfold LabelSensitive LabelBlind
  push Not
  rfl

/-- The difficulty-weighted weight is relabelling-invariant exactly when no relabelling
changes the weight of a task. -/
theorem permInvariant_diffWeight_iff (w : ℕ → ℝ) (d : (X → Y) → ℕ) :
    PermInvariant (diffWeight w d) ↔ ∀ (π : Equiv.Perm X) (f : X → Y), w (d (f ∘ π)) = w (d f) :=
  Iff.rfl

/-! ### The engine: CT-10 in "ordered agents" form -/

section Finite

variable [Fintype X] [Fintype Y]

-- STATEMENT UNREVIEWED. Source: Atlas rung CT-10,
-- `AISafetyAtlas.Learning.nfl_adaptive_iff_permInvariant` (vendored), restated with a strict
-- inequality. This is correction C2 of the SPEC in general form.
/-- **Ordered agents exist exactly when the weight is not relabelling-invariant** (CT-10,
contrapositive, with the inequality oriented). Nothing here mentions difficulty: ANY
weighting that is not invariant under relabelling the search space gives ordered agents
(correction C2). -/
theorem orderedAgents_iff_not_permInvariant (P : ObjectiveWeight X Y) :
    OrderedAgents P ↔ ¬PermInvariant P := by
  rw [← nfl_adaptive_iff_permInvariant P]
  constructor
  · rintro ⟨m, Ψ, r₁, r₂, h₁, h₂, hlt⟩ hall
    exact absurd (hall m Ψ r₁ r₂ h₁ h₂) hlt.ne
  · intro h
    push Not at h
    obtain ⟨m, Ψ, r₁, r₂, h₁, h₂, hne⟩ := h
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨m, Ψ, r₁, r₂, h₁, h₂, hlt⟩
    · exact ⟨m, Ψ, r₂, r₁, h₂, h₁, hgt⟩

/-! ### T1–T4 -/

-- STATEMENT UNREVIEWED. Source: SPEC, T4 (general).
/-- **T4 (general).** For any weight function `w` (not necessarily monotone), ordered
agents exist under the difficulty-weighted weight iff some relabelling changes the weight of
some task. -/
theorem orderedAgents_diffWeight_iff (w : ℕ → ℝ) (d : (X → Y) → ℕ) :
    OrderedAgents (diffWeight w d) ↔
      ∃ (π : Equiv.Perm X) (f : X → Y), w (d (f ∘ π)) ≠ w (d f) := by
  rw [orderedAgents_iff_not_permInvariant, permInvariant_diffWeight_iff]
  push Not
  rfl

-- STATEMENT UNREVIEWED. Source: SPEC, T1 (escape).
/-- **T1 (escape).** If harder tasks get strictly less weight and the difficulty measure is
label-sensitive, ordered agents exist. -/
theorem escape {w : ℕ → ℝ} (hw : StrictAnti w) {d : (X → Y) → ℕ} (hd : LabelSensitive d) :
    OrderedAgents (diffWeight w d) := by
  obtain ⟨π, f, hne⟩ := hd
  exact (orderedAgents_diffWeight_iff w d).mpr ⟨π, f, fun h => hne (hw.injective h)⟩

-- STATEMENT UNREVIEWED. Source: SPEC, T2 (boundary).
/-- **T2 (boundary).** If the difficulty measure is label-blind then, for every weight
function `w`, all non-revisiting agents tie under every performance measure `Ψ` and every
sample length `m`. -/
theorem boundary {d : (X → Y) → ℕ} (hd : LabelBlind d) (w : ℕ → ℝ) (m : ℕ)
    (Ψ : (Fin m → Y) → ℝ) (r₁ r₂ : AdaptiveRule X Y m)
    (h₁ : ∀ c, Injective (ruleVisit r₁ c)) (h₂ : ∀ c, Injective (ruleVisit r₂ c)) :
    weightedTrace (diffWeight w d) Ψ r₁ = weightedTrace (diffWeight w d) Ψ r₂ :=
  (nfl_adaptive_iff_permInvariant (diffWeight w d)).mpr
    (fun π f => congrArg w (hd π f)) m Ψ r₁ r₂ h₁ h₂

-- STATEMENT UNREVIEWED. Source: SPEC, T2, in "ordered agents" form.
/-- T2 restated: under a label-blind difficulty, no weight function gives ordered agents. -/
theorem boundary_not_orderedAgents {d : (X → Y) → ℕ} (hd : LabelBlind d) (w : ℕ → ℝ) :
    ¬OrderedAgents (diffWeight w d) := by
  rintro ⟨m, Ψ, r₁, r₂, h₁, h₂, hlt⟩
  exact absurd (boundary hd w m Ψ r₁ r₂ h₁ h₂) hlt.ne

-- STATEMENT UNREVIEWED. Source: SPEC, T3 (iff).
/-- **T3 (iff).** For a strictly decreasing weight function, ordered agents exist iff the
difficulty measure is label-sensitive. -/
theorem orderedAgents_iff_labelSensitive {w : ℕ → ℝ} (hw : StrictAnti w)
    (d : (X → Y) → ℕ) : OrderedAgents (diffWeight w d) ↔ LabelSensitive d := by
  constructor
  · intro h
    by_contra hns
    rw [labelSensitive_iff_not_labelBlind, not_not] at hns
    exact boundary_not_orderedAgents hns w h
  · exact escape hw

/-! ### Corrections C1–C3 to the survey -/

-- STATEMENT UNREVIEWED. Source: SPEC, correction C1.
/-- **Correction C1.** The survey's "under any difficulty-weighted distribution, ordered
agents exist" is false as written: for a constant difficulty (every task equally hard), a
strictly decreasing `w` gives the uniform weight, and no ordered agents exist. -/
theorem c1_constant_difficulty_no_ordering (k : ℕ) :
    ∃ w : ℕ → ℝ, StrictAnti w ∧
      ¬OrderedAgents (diffWeight w (fun _ : X → Y => k)) :=
  ⟨fun n => -(n : ℝ), fun a b hab => by simpa using hab,
    boundary_not_orderedAgents (fun _ _ => rfl) _⟩

-- STATEMENT UNREVIEWED. Source: SPEC, correction C2.
/-- **Correction C2.** "Rankings exist precisely inside the difficulty-restricted regime" is
too strong: a weight that has nothing to do with difficulty, the point mass on a single
non-constant-under-relabelling task `f₀`, also gives ordered agents. (The general statement
is `orderedAgents_iff_not_permInvariant`.) -/
theorem c2_pointMass_orderedAgents (f₀ : X → Y) (π : Equiv.Perm X) (h : f₀ ∘ π ≠ f₀) :
    OrderedAgents (fun f : X → Y => if f = f₀ then (1 : ℝ) else 0) := by
  rw [orderedAgents_iff_not_permInvariant]
  intro hP
  have := hP π f₀
  simp [h] at this

-- STATEMENT UNREVIEWED. Source: SPEC, correction C3; Atlas
-- `AISafetyAtlas.Combinatorics.card_closedUnderPermutation_nonempty` (vendored).
/-- **Correction C3.** The Atlas count behind "almost no prior is closed under relabelling"
counts SETS of tasks `F : Set (X → Y)` (indicator weights) that are closed under
permutation: there are `2 ^ C(|X| + |Y| − 1, |X|) − 1` nonempty ones. It is not a count, or
a measure, of real-valued priors. This theorem is the Atlas statement, restated here so the
citation is checked by the build. -/
theorem c3_count_is_for_sets [DecidableEq X] [DecidableEq Y] :
    Nat.card {F : Set (X → Y) // ClosedUnderPermutation F ∧ F.Nonempty} + 1
      = 2 ^ ((Fintype.card Y + Fintype.card X - 1).choose (Fintype.card X)) :=
  card_closedUnderPermutation_nonempty

/-! ### Quantitative escape (block C3, stretch) -/

/-- A full-length fixed-order agent under the indicator measure of a cost sequence `c` reads
off the weight of the single task that produces `c` in that order (the Atlas's probe
`weightedPerformance_indicator`, in adaptive form). The indicator is described by its two
defining properties so that the statement does not depend on a choice of decidability
instance. -/
theorem weightedTrace_scheduleRule_indicator (P : ObjectiveWeight X Y)
    (e : Fin (Fintype.card X) ≃ X) (c : Fin (Fintype.card X) → Y)
    (Ψ : (Fin (Fintype.card X) → Y) → ℝ) (hc : Ψ c = 1) (hne : ∀ d, d ≠ c → Ψ d = 0) :
    weightedTrace P Ψ (scheduleRule e.toEmbedding) = P (fun x => c (e.symm x)) := by
  have hΨ : Ψ = fun d => if d = c then (1 : ℝ) else 0 := by
    funext d
    by_cases h : d = c
    · simp [h, hc]
    · simp [h, hne d h]
  rw [hΨ, ← weightedPerformance_eq_adaptive]
  exact weightedPerformance_indicator P e c

-- STATEMENT UNREVIEWED. Source: SPEC, RISK paragraph ("a quantitative escape (a lower bound
-- on the performance gap in terms of how unevenly w ∘ d weights a relabelling orbit)");
-- statement drafted in NOTES.md, session 2, block C3.
/-- **Quantitative escape.** For every task `f` and relabelling `π` there are a performance
measure `Ψ` with values in `{0, 1}` and two non-revisiting agents whose performance gap is
exactly the difference of the weights of `f` and of its relabelling `f ∘ π`. So the gap
achievable with a 0/1-valued measure is at least the spread of the weight over any
relabelling orbit. -/
theorem exists_agents_gap_eq (P : ObjectiveWeight X Y) (π : Equiv.Perm X) (f : X → Y) :
    ∃ (Ψ : (Fin (Fintype.card X) → Y) → ℝ) (r₁ r₂ : AdaptiveRule X Y (Fintype.card X)),
      (∀ c, Ψ c = 0 ∨ Ψ c = 1) ∧
      (∀ c, Injective (ruleVisit r₁ c)) ∧ (∀ c, Injective (ruleVisit r₂ c)) ∧
      weightedTrace P Ψ r₂ - weightedTrace P Ψ r₁ = P f - P (f ∘ π) := by
  let e₀ : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let e₁ : Fin (Fintype.card X) ≃ X := e₀.trans π.symm
  let c : Fin (Fintype.card X) → Y := fun i => f (e₀ i)
  refine ⟨fun d => if d = c then (1 : ℝ) else 0, scheduleRule e₁.toEmbedding,
    scheduleRule e₀.toEmbedding, fun d => ?_, injective_ruleVisit_scheduleRule _,
    injective_ruleVisit_scheduleRule _, ?_⟩
  · by_cases h : d = c <;> simp [h]
  · rw [weightedTrace_scheduleRule_indicator P e₀ c _ (by simp) (fun d hd => by simp [hd]),
      weightedTrace_scheduleRule_indicator P e₁ c _ (by simp) (fun d hd => by simp [hd])]
    have h₀ : (fun x => c (e₀.symm x)) = f := by
      funext x; simp [c]
    have h₁ : (fun x => c (e₁.symm x)) = f ∘ π := by
      funext x; simp [c, e₁]
    rw [h₀, h₁]

-- STATEMENT UNREVIEWED. Source: as for `exists_agents_gap_eq`, specialized to `w ∘ d`.
/-- Quantitative escape for a difficulty-weighted weight: the gap `w (d f) − w (d (f ∘ π))`
is achieved, for every task `f` and relabelling `π`. -/
theorem exists_agents_gap_eq_diffWeight (w : ℕ → ℝ) (d : (X → Y) → ℕ) (π : Equiv.Perm X)
    (f : X → Y) :
    ∃ (Ψ : (Fin (Fintype.card X) → Y) → ℝ) (r₁ r₂ : AdaptiveRule X Y (Fintype.card X)),
      (∀ c, Ψ c = 0 ∨ Ψ c = 1) ∧
      (∀ c, Injective (ruleVisit r₁ c)) ∧ (∀ c, Injective (ruleVisit r₂ c)) ∧
      weightedTrace (diffWeight w d) Ψ r₂ - weightedTrace (diffWeight w d) Ψ r₁
        = w (d f) - w (d (f ∘ π)) :=
  exists_agents_gap_eq (diffWeight w d) π f

end Finite

/-! ### T5: a concrete structural difficulty -/

section Example

-- STATEMENT UNREVIEWED. Source: SPEC, T5 ("for instance the number of positions i with
-- f i ≠ f (i+1)").
/-- A structural difficulty on tasks `f : Fin (n + 1) → Y`: the number of adjacent positions
`i, i + 1` at which `f` changes value. Constant tasks have difficulty `0`. -/
noncomputable def flips {n : ℕ} (f : Fin (n + 1) → Y) : ℕ :=
  (Finset.univ.filter fun i : Fin n => f i.castSucc ≠ f i.succ).card

/-- The task that is `a` at position `0` and `b` elsewhere changes value once. -/
theorem flips_spike_zero {n : ℕ} {a b : Y} (hab : a ≠ b) :
    flips (fun x : Fin (n + 3) => if x = 0 then a else b) = 1 := by
  unfold flips
  have : (Finset.univ.filter fun i : Fin (n + 2) =>
      (if i.castSucc = 0 then a else b) ≠ (if i.succ = 0 then a else b)) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.succ_ne_zero, ite_false]
    constructor
    · intro h
      by_contra hi
      have : i.castSucc ≠ 0 := fun h0 => hi (Fin.castSucc_eq_zero_iff.mp h0)
      simp [this] at h
    · rintro rfl
      simpa using hab
  rw [this, Finset.card_singleton]

/-- The task that is `a` at position `1` and `b` elsewhere changes value twice. -/
theorem flips_spike_one {n : ℕ} {a b : Y} (hab : a ≠ b) :
    flips (fun x : Fin (n + 3) => if x = 1 then a else b) = 2 := by
  unfold flips
  have : (Finset.univ.filter fun i : Fin (n + 2) =>
      (if i.castSucc = 1 then a else b) ≠ (if i.succ = 1 then a else b)) = {0, 1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    have h1 : i.castSucc = 1 ↔ i = 1 := by
      rw [Fin.ext_iff, Fin.ext_iff]; simp
    have h2 : i.succ = 1 ↔ i = 0 := by
      rw [Fin.ext_iff, Fin.ext_iff]; simp
    simp only [h1, h2]
    by_cases hi0 : i = 0
    · subst hi0
      simpa using hab.symm
    · by_cases hi1 : i = 1
      · subst hi1
        simpa using hab
      · simp [hi0, hi1]
  rw [this, Finset.card_pair (by simp)]

-- STATEMENT UNREVIEWED. Source: SPEC, T5 ("a proof that it is label-sensitive").
/-- **T5, label-sensitivity.** On a search space with at least three points and a value
type with at least two values, `flips` is label-sensitive: swapping positions `0` and `1`
turns a one-change task into a two-change task. -/
theorem flips_labelSensitive {n : ℕ} {a b : Y} (hab : a ≠ b) :
    LabelSensitive (flips : (Fin (n + 3) → Y) → ℕ) := by
  refine ⟨Equiv.swap 0 1, fun x => if x = 0 then a else b, ?_⟩
  have hcomp : (fun x : Fin (n + 3) => if x = 0 then a else b) ∘ (Equiv.swap 0 1)
      = fun x => if x = 1 then a else b := by
    funext x
    simp only [comp_apply]
    by_cases h0 : x = 0
    · subst h0; simp
    · by_cases h1 : x = 1
      · subst h1; simp
      · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]; simp [h0, h1]
  rw [hcomp, flips_spike_one hab, flips_spike_zero hab]
  norm_num

-- STATEMENT UNREVIEWED. Source: SPEC, T5 ("a computed pair of agents with different
-- performance").
/-- **T5, computed pair of agents.** Tasks `Fin 3 → Bool`, difficulty `flips`, weight
`w k = (1/2)^k` (harder tasks get less weight). The performance measure is the indicator of
the cost sequence `(true, false, false)`. The agent that queries the positions in the order
`0, 1, 2` has weighted performance `1/2` (it sees that sequence only on the task
`(true, false, false)`, of difficulty 1); the agent that queries in the order `1, 0, 2` has
weighted performance `1/4` (only on `(false, true, false)`, of difficulty 2). -/
theorem flipsExample :
    ∃ (Ψ : (Fin (Fintype.card (Fin 3)) → Bool) → ℝ)
      (r₁ r₂ : AdaptiveRule (Fin 3) Bool (Fintype.card (Fin 3))),
      (∀ c, Injective (ruleVisit r₁ c)) ∧ (∀ c, Injective (ruleVisit r₂ c)) ∧
      weightedTrace (diffWeight (fun k => (1 / 2 : ℝ) ^ k) flips) Ψ r₁ = 1 / 4 ∧
      weightedTrace (diffWeight (fun k => (1 / 2 : ℝ) ^ k) flips) Ψ r₂ = 1 / 2 := by
  let e₀ : Fin (Fintype.card (Fin 3)) ≃ Fin 3 := finCongr (Fintype.card_fin 3)
  let e₁ : Fin (Fintype.card (Fin 3)) ≃ Fin 3 := e₀.trans (Equiv.swap 0 1)
  let c : Fin (Fintype.card (Fin 3)) → Bool := fun i => decide (e₀ i = 0)
  refine ⟨fun d => if d = c then (1 : ℝ) else 0,
    scheduleRule e₁.toEmbedding, scheduleRule e₀.toEmbedding,
    injective_ruleVisit_scheduleRule _, injective_ruleVisit_scheduleRule _, ?_, ?_⟩
  · rw [weightedTrace_scheduleRule_indicator _ e₁ c _ (by simp) (fun d hd => by simp [hd])]
    have h : (fun x => c (e₁.symm x)) = fun x : Fin 3 => if x = 1 then true else false := by
      funext x
      fin_cases x <;> simp [c, e₁, Equiv.swap_apply_def]
    rw [h]
    show (1 / 2 : ℝ) ^ flips (fun x : Fin (0 + 3) => if x = 1 then true else false) = 1 / 4
    rw [flips_spike_one (by decide)]
    norm_num
  · rw [weightedTrace_scheduleRule_indicator _ e₀ c _ (by simp) (fun d hd => by simp [hd])]
    have h : (fun x => c (e₀.symm x)) = fun x : Fin 3 => if x = 0 then true else false := by
      funext x
      fin_cases x <;> simp [c]
    rw [h]
    show (1 / 2 : ℝ) ^ flips (fun x : Fin (0 + 3) => if x = 0 then true else false) = 1 / 2
    rw [flips_spike_zero (by decide)]
    norm_num

-- STATEMENT UNREVIEWED. Source: SPEC, T5 with T1.
/-- The T5 example gives ordered agents, directly from the computed pair (and, independently,
from T1 `escape` with `flips_labelSensitive`). -/
theorem flipsExample_orderedAgents :
    OrderedAgents (diffWeight (fun k => (1 / 2 : ℝ) ^ k)
      (flips : (Fin 3 → Bool) → ℕ)) := by
  obtain ⟨Ψ, r₁, r₂, h₁, h₂, e₁, e₂⟩ := flipsExample
  exact ⟨_, Ψ, r₁, r₂, h₁, h₂, by rw [e₁, e₂]; norm_num⟩

end Example

end UncontainabilityLean.NFLEscape
