/-
# The generality metric: transitivity, and a bound at finite generality
(index ID 125; Tier 4, package D)

Source: Hernández-Orallo et al. 2021, Supplementary Information §E.2 (properties 6 and 7,
PDF p. 35) and §F.1 (Propositions 13 and 14, PDF pp. 37–38):
`papers/index/files/125_supplementary_information.pdf`. Page numbers are PDF pages.

CONTENTS.

  1. THE PROJECT'S OWN RESULT (not in the paper). With `D = ∫₀^Ψ (1 − ψ(h)) dh`, the
     failure on tasks easier than the agent's capability `Ψ` (`deficit`):

         2·D² ≤ S²,   that is   D ≤ S/√2      (`deficit_le`),

     attained by the curve that is 1 on `[0, Ψ − D]`, 0 on `(Ψ − D, Ψ)`, 1 on `[Ψ, Ψ + D]`
     (`deficit_bound_sharp`). `D` also equals the success on tasks harder than `Ψ`
     (`deficit_eq_excess`). A two-agent form, also the project's own: if `Ψ_a ≤ Ψ_b`, the
     area by which agent a's curve exceeds agent b's is at most `(S_a + S_b)/√2`
     (`excess_area_le`). These are statements about curves. They say nothing about which
     individual tasks an agent solves, and nothing about harm.

  2. Property 6, second sentence ("Agents with maximum generality Γ = ∞ are s-saturated
     with s = Ψ", PDF p. 35). FALSE pointwise (`saturated_of_generality_eq_top_literal_false`:
     a step curve changed at one difficulty); TRUE at almost every difficulty
     (`saturated_ae_of_generality_eq_top_corrected`).

  3. Proposition 13 (task transitivity), with its hypotheses explicit (`task_transitivity`).

  4. Proposition 14 (agent transitivity). As literally stated it fails, but only through a
     null set of difficulties (`agent_transitivity_literal_false`). It holds when both
     curves are step curves at every difficulty, which is what the supplement's proof uses
     (`agent_transitivity_corrected`), and at the level of curves it holds almost
     everywhere (`curve_le_ae_of_generality_eq_top`).

MODELLING CHOICES, in addition to those of the earlier files.

  D15. The paper's curve is `ψ(h) = P(A = 1 | difficulty = h)` over tasks. Propositions 13
       and 14 are about individual tasks, so they need a link between a curve and task
       results, which the paper leaves implicit. `TaskLink d A ψ` states the link used:
       difficulties are non-negative; if `ψ` is 1 at a task's difficulty the task is
       accomplished; if a task is accomplished `ψ` is positive at its difficulty. Both hold
       when `ψ(h)` is the share of accomplished tasks among finitely many tasks of
       difficulty `h`.
  D16. `deficit ψ` is an interval integral from 0 to the capability.
  D17. "The area by which curve a exceeds curve b" is `∫ max(ψ_a − ψ_b, 0)`.

Every statement stays `-- STATEMENT UNREVIEWED` until a human reviewer signs off.
-/
import UncontainabilityLean.Generality.Compactness

open MeasureTheory Set
open scoped ENNReal

namespace UncontainabilityLean.Generality

/-! ## Splitting a curve at a difficulty `k` -/

theorem IsCurve.intervalIntegrable {ψ : ℝ → ℝ} (hψ : IsCurve ψ) {k : ℝ} (hk : 0 ≤ k) :
    IntervalIntegrable ψ volume 0 k :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hk).2
    (hψ.integrable.mono_set Ioc_subset_Ioi_self)

theorem IsCurve.intervalIntegrable_mul {ψ : ℝ → ℝ} (hψ : IsCurve ψ) {k : ℝ} (hk : 0 ≤ k) :
    IntervalIntegrable (fun h => h * ψ h) volume 0 k :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hk).2
    (hψ.integrable_mul.mono_set Ioc_subset_Ioi_self)

/-- Capability is the area up to `k` plus the capability of the part beyond `k`. -/
theorem capability_split {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ) :
    capability ψ = (∫ h in (0 : ℝ)..k, ψ h) + capability (translateLeft k ψ) := by
  have key := (piecewise_Ioi (F := ψ) (G := translateLeft k ψ) hk (hψ.intervalIntegrable hk)
    (isCurve_translateLeft hk hψ).integrable).2
  unfold capability at key ⊢
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  by_cases hlt : h < k <;> simp [hlt, translateLeft]

/-- The moment, split in the same way. -/
theorem effort_split {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ) :
    effort ψ = (∫ h in (0 : ℝ)..k, h * ψ h) + effort (translateLeft k ψ)
      + k * capability (translateLeft k ψ) := by
  have hg := isCurve_translateLeft hk hψ
  have hG : IntegrableOn (fun u => (u + k) * translateLeft k ψ u) (Ioi 0) := by
    refine (hg.integrable_mul.add (hg.integrable.const_mul k)).congr_fun (fun u _ => ?_)
      measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  have key := (piecewise_Ioi (F := fun h => h * ψ h)
    (G := fun u => (u + k) * translateLeft k ψ u) hk (hψ.intervalIntegrable_mul hk) hG).2
  have s : ∫ u in Ioi (0 : ℝ), (u + k) * translateLeft k ψ u
      = effort (translateLeft k ψ) + k * capability (translateLeft k ψ) := by
    unfold effort capability
    rw [← integral_const_mul, ← integral_add hg.integrable_mul (hg.integrable.const_mul k)]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [add_assoc, ← s, ← key]
  unfold effort
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  by_cases hlt : h < k <;> simp [hlt, translateLeft]

/-- The curve cut off beyond difficulty `k`. -/
noncomputable def truncate (k : ℝ) (ψ : ℝ → ℝ) : ℝ → ℝ := (Iic k).indicator ψ

theorem mul_truncate (k : ℝ) (ψ : ℝ → ℝ) (h : ℝ) :
    h * truncate k ψ h = (Iic k).indicator (fun h => h * ψ h) h := by
  unfold truncate; by_cases hh : h ∈ Iic k <;> simp [hh]

theorem isCurve_truncate (k : ℝ) {ψ : ℝ → ℝ} (hψ : IsCurve ψ) : IsCurve (truncate k ψ) := by
  refine ⟨fun h h0 => ?_, fun h h0 => ?_, hψ.integrable.indicator measurableSet_Iic, ?_⟩
  · unfold truncate; by_cases hh : h ∈ Iic k <;> simp [hh, hψ.nonneg h h0]
  · unfold truncate; by_cases hh : h ∈ Iic k <;> simp [hh, hψ.le_one h h0]
  · simp_rw [mul_truncate]
    exact hψ.integrable_mul.indicator measurableSet_Iic

theorem capability_truncate {k : ℝ} (hk : 0 ≤ k) (ψ : ℝ → ℝ) :
    capability (truncate k ψ) = ∫ h in (0 : ℝ)..k, ψ h := by
  unfold capability truncate
  rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, intervalIntegral.integral_of_le hk]

theorem effort_truncate {k : ℝ} (hk : 0 ≤ k) (ψ : ℝ → ℝ) :
    effort (truncate k ψ) = ∫ h in (0 : ℝ)..k, h * ψ h := by
  unfold effort
  simp_rw [mul_truncate]
  rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, intervalIntegral.integral_of_le hk]

/-! ## The project's own result: failure below capability is at most `S/√2` -/

-- STATEMENT UNREVIEWED
/-- **Project's own definition (not in the paper).** The deficit `D = ∫₀^Ψ (1 − ψ(h)) dh`:
the amount of failure on tasks easier than the agent's capability `Ψ`, in units of
difficulty. -/
noncomputable def deficit (ψ : ℝ → ℝ) : ℝ := ∫ h in (0 : ℝ)..capability ψ, (1 - ψ h)

theorem deficit_eq {ψ : ℝ → ℝ} (hψ : IsCurve ψ) :
    deficit ψ = capability ψ - ∫ h in (0 : ℝ)..capability ψ, ψ h := by
  unfold deficit
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (hψ.intervalIntegrable (capability_nonneg hψ))]
  simp

-- STATEMENT UNREVIEWED
/-- **Project's own result.** The deficit is non-negative. -/
theorem deficit_nonneg {ψ : ℝ → ℝ} (hψ : IsCurve ψ) : 0 ≤ deficit ψ :=
  intervalIntegral.integral_nonneg (capability_nonneg hψ) fun h hh =>
    sub_nonneg.2 (hψ.le_one h hh.1)

-- STATEMENT UNREVIEWED
/-- **Project's own result.** The deficit is at most the capability. -/
theorem deficit_le_capability {ψ : ℝ → ℝ} (hψ : IsCurve ψ) : deficit ψ ≤ capability ψ := by
  rw [deficit_eq hψ]
  have := intervalIntegral.integral_nonneg (capability_nonneg hψ)
    (fun h hh => hψ.nonneg h hh.1) (μ := volume)
  linarith

/-- The capability of the part of the curve beyond `Ψ` is the deficit. -/
theorem capability_translateLeft_capability {ψ : ℝ → ℝ} (hψ : IsCurve ψ) :
    capability (translateLeft (capability ψ) ψ) = deficit ψ := by
  have := capability_split (capability_nonneg hψ) hψ
  rw [deficit_eq hψ]; linarith

-- STATEMENT UNREVIEWED
/-- **Project's own result.** Because capability is the whole area, the failure on tasks
easier than `Ψ` equals the success on tasks harder than `Ψ`:
`∫₀^Ψ (1 − ψ) = ∫_Ψ^∞ ψ`. -/
theorem deficit_eq_excess {ψ : ℝ → ℝ} (hψ : IsCurve ψ) :
    deficit ψ = ∫ h in Ioi (capability ψ), ψ h := by
  rw [← capability_translateLeft_capability hψ]
  unfold capability translateLeft
  rw [← setIntegral_Ioi_shift (fun u => ψ (u + (∫ h in Ioi (0 : ℝ), ψ h)))
    (∫ h in Ioi (0 : ℝ), ψ h)]
  simp

-- STATEMENT UNREVIEWED
/-- **Project's own result (not in the paper): `2·D² ≤ S²`.** For the generality metric as
defined by Hernández-Orallo et al., a curve with deficit `D` has squared spread at least
`2D²`. Proof: split the curve at `Ψ`; the part below and the part above each satisfy the
left inequality of the extremal theorem (`spreadSq_nonneg`). -/
theorem two_mul_deficit_sq_le_spreadSq {ψ : ℝ → ℝ} (hψ : IsCurve ψ) :
    2 * deficit ψ ^ 2 ≤ spreadSq ψ := by
  have hΨ := capability_nonneg hψ
  have c := capability_split hΨ hψ
  have e := effort_split hΨ hψ
  have t1 := spreadSq_nonneg (isCurve_truncate (capability ψ) hψ)
  have t2 := spreadSq_nonneg (isCurve_translateLeft hΨ hψ)
  have d := deficit_eq hψ
  unfold spreadSq at t1 t2 ⊢
  rw [capability_truncate hΨ, effort_truncate hΨ] at t1
  have hcg : capability (translateLeft (capability ψ) ψ)
      = capability ψ - ∫ h in (0 : ℝ)..capability ψ, ψ h := by linarith
  rw [hcg] at t2 e
  rw [d, e]
  nlinarith [t1, t2]

-- STATEMENT UNREVIEWED
/-- **Project's own result (not in the paper): `D ≤ S/√2`.** For the generality metric as
defined by Hernández-Orallo et al.: an agent with capability `Ψ` and spread `S` fails on
at most `S/√2` difficulty-units' worth of the tasks easier than `Ψ`. This is a statement
about the curve; it does not say which tasks are failed, and it is not a statement about
any real system or about harm. -/
theorem deficit_le {ψ : ℝ → ℝ} (hψ : IsCurve ψ) : deficit ψ ≤ spread ψ / Real.sqrt 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [le_div_iff₀ h2]
  unfold spread
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  linarith [two_mul_deficit_sq_le_spreadSq hψ]

-- STATEMENT UNREVIEWED
/-- **Project's own result.** The same bound from a bound on spread: if `S ≤ s` then
`D ≤ s/√2`. (In terms of generality `Γ = 1/S`: if `Γ ≥ 1/s` then `D ≤ s/√2`.) -/
theorem deficit_le_of_spread_le {ψ : ℝ → ℝ} (hψ : IsCurve ψ) {s : ℝ} (hs : spread ψ ≤ s) :
    deficit ψ ≤ s / Real.sqrt 2 :=
  (deficit_le hψ).trans (div_le_div_of_nonneg_right hs (Real.sqrt_nonneg 2))

/-- The curve attaining the bound: 1 on `[0, Ψ − D]`, 0 on `(Ψ − D, Ψ)`, 1 on
`[Ψ, Ψ + D]`, 0 after. -/
noncomputable def deficitCurve (Ψ D : ℝ) : ℝ → ℝ :=
  fun h => box 1 0 (Ψ - D) h + box 1 Ψ (Ψ + D) h

theorem isCurve_deficitCurve {Ψ D : ℝ} (hD : 0 < D) : IsCurve (deficitCurve Ψ D) := by
  refine ⟨fun h _ => ?_, fun h _ => ?_,
    (integrableOn_box _ _ _).add (integrableOn_box _ _ _), ?_⟩
  · unfold deficitCurve box; simp only [indicator, mem_Icc]; split_ifs <;> norm_num
  · unfold deficitCurve box; simp only [indicator, mem_Icc]
    split_ifs with h1 h2 <;> first | (exfalso; linarith [h1.2, h2.1]) | norm_num
  · refine ((integrableOn_mul_box 1 0 (Ψ - D)).add (integrableOn_mul_box 1 Ψ (Ψ + D))).congr_fun
      (fun h _ => ?_) measurableSet_Ioi
    simp only [deficitCurve, Pi.add_apply]; ring

-- STATEMENT UNREVIEWED
/-- **Project's own result: the bound `D ≤ S/√2` is attained.** For `0 < D ≤ Ψ` the curve
`deficitCurve Ψ D` is an agent characteristic curve with capability `Ψ`, deficit `D` and
squared spread exactly `2D²`, so its deficit equals `S/√2`. -/
theorem deficit_bound_sharp {Ψ D : ℝ} (hD : 0 < D) (hDΨ : D ≤ Ψ) :
    IsCurve (deficitCurve Ψ D) ∧ capability (deficitCurve Ψ D) = Ψ ∧
      deficit (deficitCurve Ψ D) = D ∧ spreadSq (deficitCurve Ψ D) = 2 * D ^ 2 ∧
      deficit (deficitCurve Ψ D) = spread (deficitCurve Ψ D) / Real.sqrt 2 := by
  have hΨ : 0 ≤ Ψ := by linarith
  have hc := isCurve_deficitCurve (Ψ := Ψ) hD
  have hcap : capability (deficitCurve Ψ D) = Ψ := by
    unfold deficitCurve
    rw [capability_add (integrableOn_box _ _ _) (integrableOn_box _ _ _),
      capability_box _ le_rfl (by linarith), capability_box _ hΨ (by linarith)]
    ring
  have heff : effort (deficitCurve Ψ D) = (Ψ - D) ^ 2 / 2 + ((Ψ + D) ^ 2 - Ψ ^ 2) / 2 := by
    unfold deficitCurve
    rw [effort_add (integrableOn_mul_box _ _ _) (integrableOn_mul_box _ _ _),
      effort_box _ le_rfl (by linarith), effort_box _ hΨ (by linarith)]
    ring
  have hsq : spreadSq (deficitCurve Ψ D) = 2 * D ^ 2 := by
    unfold spreadSq; rw [hcap, heff]; ring
  have hdef : deficit (deficitCurve Ψ D) = D := by
    rw [deficit_eq hc, hcap, intervalIntegral.integral_of_le hΨ, ← integral_Icc_eq_integral_Ioc]
    have : ∫ h in Icc 0 Ψ, deficitCurve Ψ D h = Ψ - D := by
      have := partialArea_add (ψ := box 1 0 (Ψ - D)) (φ := box 1 Ψ (Ψ + D)) 0 Ψ
        (integrable_box _ _ _).integrableOn (integrable_box _ _ _).integrableOn
      unfold partialArea at this
      unfold deficitCurve
      rw [this]
      have a := partialArea_box 1 0 (Ψ - D) 0 Ψ
      have b := partialArea_box 1 Ψ (Ψ + D) 0 Ψ
      unfold partialArea at a b
      rw [a, b, min_eq_right (by linarith), max_self, min_eq_left (by linarith),
        max_eq_right hΨ, sub_self, max_self, sub_zero, max_eq_left (by linarith)]
      ring
    rw [this]; ring
  refine ⟨hc, hcap, hdef, hsq, ?_⟩
  unfold spread
  rw [hdef, hsq, Real.sqrt_mul (by norm_num), Real.sqrt_sq hD.le]
  field_simp

/-! ## Property 6, second sentence: infinite generality and saturation -/

-- STATEMENT UNREVIEWED
/-- **SI §E.2, property 6, second sentence, corrected** (PDF p. 35: "Agents with maximum
generality Γ = ∞ are s-saturated with s = Ψ"): a curve of infinite generality equals 1 at
ALMOST EVERY difficulty in `(0, Ψ]`. The words "almost every" are the correction (see
`saturated_of_generality_eq_top_literal_false`). Uses the project's own
`generality_eq_top_iff_step`. -/
theorem saturated_ae_of_generality_eq_top_corrected {ψ : ℝ → ℝ} (hψ : IsCurve ψ)
    (hΓ : generality ψ = ⊤) :
    ∀ᵐ h ∂(volume.restrict (Ioc 0 (capability ψ))), ψ h = 1 := by
  have h1 := ae_restrict_of_ae_restrict_of_subset (s := Ioc 0 (capability ψ)) (t := Ioi 0)
    Ioc_subset_Ioi_self ((generality_eq_top_iff_step hψ).1 hΓ)
  filter_upwards [h1, ae_restrict_mem measurableSet_Ioc] with x hx hm
  rw [hx, step_of_le hm.1.le hm.2]

/-- The step curve at 1, changed to 0 at the single difficulty 1/2. -/
noncomputable def puncturedStep : ℝ → ℝ := fun h => if h = 1 / 2 then 0 else step 1 h

theorem puncturedStep_ae : puncturedStep =ᵐ[volume.restrict (Ioi 0)] step 1 := by
  filter_upwards [ae_restrict_ne (1 / 2)] with h hne
  show (if h = 1 / 2 then 0 else step 1 h) = step 1 h
  rw [ite_eq_right_iff]
  exact fun h' => absurd h' hne

theorem isCurve_puncturedStep : IsCurve puncturedStep := by
  refine ⟨fun h h0 => ?_, fun h h0 => ?_,
    Integrable.congr (isCurve_step 1).integrable puncturedStep_ae.symm,
    Integrable.congr (isCurve_step 1).integrable_mul ?_⟩
  · unfold puncturedStep; split_ifs
    · exact le_rfl
    · exact (isCurve_step 1).nonneg h h0
  · unfold puncturedStep; split_ifs
    · exact zero_le_one
    · exact (isCurve_step 1).le_one h h0
  · filter_upwards [puncturedStep_ae] with h hh
    rw [hh]

theorem capability_puncturedStep : capability puncturedStep = 1 := by
  rw [capability_congr_ae puncturedStep_ae, capability_step zero_le_one]

theorem generality_puncturedStep : generality puncturedStep = ⊤ := by
  rw [generality_eq_top_iff_step isCurve_puncturedStep, capability_puncturedStep]
  exact puncturedStep_ae

-- STATEMENT UNREVIEWED
/-- **SI §E.2, property 6, second sentence is false as literally stated** (PDF p. 35):
there is an agent characteristic curve with infinite generality that is not saturated up
to its capability. The curve is the step curve at 1 with the single difficulty 1/2
failed. The failure is confined to a null set of difficulties: see
`saturated_ae_of_generality_eq_top_corrected`. -/
theorem saturated_of_generality_eq_top_literal_false :
    ∃ ψ : ℝ → ℝ, IsCurve ψ ∧ generality ψ = ⊤ ∧ ¬ Saturated (capability ψ) ψ := by
  refine ⟨puncturedStep, isCurve_puncturedStep, generality_puncturedStep, fun hs => ?_⟩
  have := hs (1 / 2) (by norm_num) (by rw [capability_puncturedStep]; norm_num)
  simp [puncturedStep] at this

/-! ## Task transitivity (SI Proposition 13, PDF p. 37) -/

-- STATEMENT UNREVIEWED
/-- The link between an agent's results on individual tasks and its curve, which the
source leaves implicit (modelling choice D15). `d` is the difficulty of a task, `A t` says
that the agent accomplishes task `t`, and `ψ` is the agent's curve. Source: SI §E.1, PDF
p. 33 ("ψ(h) = P(A = 1 | h(μ) = h), or equivalently, the mean of the accomplishment of
agent j on all problems of difficulty h"; "a difficulty function h, mapping each task μ to
a real value h(μ) ≥ 0"). -/
structure TaskLink {T : Type*} (d : T → ℝ) (A : T → Prop) (ψ : ℝ → ℝ) : Prop where
  difficulty_nonneg : ∀ t, 0 ≤ d t
  accomplished_of_one : ∀ t, ψ (d t) = 1 → A t
  pos_of_accomplished : ∀ t, A t → 0 < ψ (d t)

-- STATEMENT UNREVIEWED
/-- **SI Proposition 13** (PDF p. 37): "if an agent is s-saturated then for every task μ_b
such that A_b = 1 in the saturated area then for all other tasks a with h(μ_a) ≤ h(μ_b) we
have that A_a = 1." The hypothesis that task `b` is accomplished (`_hAb`) is in the source
and is not used: saturation alone gives the conclusion (`accomplished_of_saturated`). -/
theorem task_transitivity {T : Type*} {d : T → ℝ} {A : T → Prop} {ψ : ℝ → ℝ} {s : ℝ}
    (L : TaskLink d A ψ) (hs : Saturated s ψ) {a b : T} (hb : d b ≤ s) (_hAb : A b)
    (hab : d a ≤ d b) : A a :=
  L.accomplished_of_one a (hs _ (L.difficulty_nonneg a) (hab.trans hb))

-- STATEMENT UNREVIEWED
/-- What the proof of SI Proposition 13 shows (PDF p. 37: "If an agent is s-saturated then
A_b = 1 for all tasks such that h(μ_b) ≤ s"): an `s`-saturated agent accomplishes every
task of difficulty at most `s`. -/
theorem accomplished_of_saturated {T : Type*} {d : T → ℝ} {A : T → Prop} {ψ : ℝ → ℝ} {s : ℝ}
    (L : TaskLink d A ψ) (hs : Saturated s ψ) {a : T} (ha : d a ≤ s) : A a :=
  L.accomplished_of_one a (hs _ (L.difficulty_nonneg a) ha)

/-- The task–curve link holds in the Guttman (deterministic) model: tasks are the
non-negative reals, each its own difficulty, the agent accomplishes exactly the tasks of
difficulty at most `l`, and its curve is the step curve at `l`. -/
theorem taskLink_step (l : ℝ) :
    TaskLink (fun t : NNReal => (t : ℝ)) (fun t => (t : ℝ) ≤ l) (step l) :=
  ⟨fun t => t.2, fun t ht => by
      by_contra hgt
      have h0 : step l (t : ℝ) = 0 := step_of_gt (not_le.1 hgt)
      have h1 : step l (t : ℝ) = 1 := ht
      rw [h0] at h1
      exact zero_ne_one h1,
    fun t ht => by
      have h1 : step l (t : ℝ) = 1 := step_of_le t.2 ht
      show 0 < step l (t : ℝ)
      rw [h1]; exact zero_lt_one⟩

/-! ## Agent transitivity (SI Proposition 14, PDF pp. 37–38) -/

-- STATEMENT UNREVIEWED
/-- **SI Proposition 14, corrected** (PDF p. 37: "if two agents π_a and π_b have maximum
generality Γ_a = Γ_b = ∞ and Ψ_a ≤ Ψ_b then for every task μ_i such that A_i^a = 1 then
A_i^b = 1"). The hypothesis here is that both curves ARE step curves at every difficulty,
which is the supplement's proof ("It is sufficient to see that both agents will have step
functions"); infinite generality gives that only almost everywhere
(`agent_transitivity_literal_false`). -/
theorem agent_transitivity_corrected {T : Type*} {d : T → ℝ} {Aa Ab : T → Prop}
    {ψa ψb : ℝ → ℝ} (La : TaskLink d Aa ψa) (Lb : TaskLink d Ab ψb)
    (ha : ∀ h, 0 ≤ h → ψa h = step (capability ψa) h)
    (hb : ∀ h, 0 ≤ h → ψb h = step (capability ψb) h)
    (hab : capability ψa ≤ capability ψb) : ∀ t, Aa t → Ab t := by
  intro t hA
  have h0 := La.difficulty_nonneg t
  have hpos := La.pos_of_accomplished t hA
  rw [ha _ h0] at hpos
  have hle : d t ≤ capability ψa := by
    by_contra hgt
    rw [step_of_gt (not_le.1 hgt)] at hpos
    exact lt_irrefl _ hpos
  exact Lb.accomplished_of_one t (by rw [hb _ h0, step_of_le h0 (hle.trans hab)])

-- STATEMENT UNREVIEWED
/-- **SI Proposition 14 at the level of curves** (PDF p. 37): if two agents have infinite
generality and `Ψ_a ≤ Ψ_b`, then agent b's curve is at least agent a's at almost every
difficulty. Uses the project's own `generality_eq_top_iff_step`. -/
theorem curve_le_ae_of_generality_eq_top {ψa ψb : ℝ → ℝ} (hψa : IsCurve ψa) (hψb : IsCurve ψb)
    (ha : generality ψa = ⊤) (hb : generality ψb = ⊤)
    (hab : capability ψa ≤ capability ψb) : ψa ≤ᵐ[volume.restrict (Ioi 0)] ψb := by
  filter_upwards [(generality_eq_top_iff_step hψa).1 ha, (generality_eq_top_iff_step hψb).1 hb,
    ae_restrict_mem measurableSet_Ioi] with h h1 h2 hm
  rw [h1, h2]
  rcases le_or_gt h (capability ψa) with hle | hgt
  · rw [step_of_le (le_of_lt hm) hle, step_of_le (le_of_lt hm) (hle.trans hab)]
  · rw [step_of_gt hgt]; exact (isCurve_step _).nonneg h (le_of_lt hm)

-- STATEMENT UNREVIEWED
/-- **SI Proposition 14 as literally stated** (PDF p. 37), with the task–curve link of
modelling choice D15. -/
def AgentTransitivityLiteral : Prop :=
  ∀ (T : Type) (d : T → ℝ) (Aa Ab : T → Prop) (ψa ψb : ℝ → ℝ),
    IsCurve ψa → IsCurve ψb → TaskLink d Aa ψa → TaskLink d Ab ψb →
    generality ψa = ⊤ → generality ψb = ⊤ → capability ψa ≤ capability ψb →
    ∀ t, Aa t → Ab t

-- STATEMENT UNREVIEWED
/-- **SI Proposition 14 is false as literally stated** (PDF p. 37), for a reason confined
to a null set of difficulties. Tasks are the non-negative reals, each its own difficulty.
Agent a has the step curve at 1 and accomplishes every task of difficulty at most 1.
Agent b has the same curve except at difficulty 1/2, where it fails. Both have infinite
generality and capability 1; agent a accomplishes the task of difficulty 1/2 and agent b
does not. The integrals that define generality cannot see a single difficulty. -/
theorem agent_transitivity_literal_false : ¬ AgentTransitivityLiteral := by
  intro H
  have La : TaskLink (fun t : NNReal => (t : ℝ)) (fun t => (t : ℝ) ≤ 1) (step 1) :=
    ⟨fun t => t.2, fun t ht => by
        by_contra hgt
        have h0 : step 1 (t : ℝ) = 0 := step_of_gt (not_le.1 hgt)
        have h1 : step 1 (t : ℝ) = 1 := ht
        rw [h0] at h1
        exact zero_ne_one h1,
      fun t ht => by
        have h1 : step 1 (t : ℝ) = 1 := step_of_le t.2 ht
        show 0 < step 1 (t : ℝ)
        rw [h1]; exact zero_lt_one⟩
  have Lb : TaskLink (fun t : NNReal => (t : ℝ)) (fun t => puncturedStep (t : ℝ) = 1)
      puncturedStep :=
    ⟨fun t => t.2, fun _ ht => ht, fun t ht => by
      have h1 : puncturedStep (t : ℝ) = 1 := ht
      show 0 < puncturedStep (t : ℝ)
      rw [h1]; exact zero_lt_one⟩
  have := H NNReal _ _ _ (step 1) puncturedStep (isCurve_step 1) isCurve_puncturedStep La Lb
    (generality_step zero_le_one) generality_puncturedStep
    (by rw [capability_step zero_le_one, capability_puncturedStep]) (1 / 2)
    (by norm_num)
  simp [puncturedStep] at this

/-! ## The project's own two-agent bound at finite generality -/

-- STATEMENT UNREVIEWED
/-- **Project's own result (not in the paper).** For two agents with `Ψ_a ≤ Ψ_b`, the area
by which agent a's curve exceeds agent b's, `∫ max(ψ_a − ψ_b, 0)`, is at most
`D_a + D_b ≤ (S_a + S_b)/√2`. When both spreads are 0 this is the curve-level form of SI
Proposition 14. It is a statement about curves: turning it into a statement about tasks
needs an assumption about WHICH tasks of a given difficulty each agent accomplishes (for
example that, at each difficulty, the tasks accomplished by one agent include those
accomplished by the other), which the supplement points out after Proposition 14 (PDF
p. 38). -/
theorem excess_area_le {ψa ψb : ℝ → ℝ} (hψa : IsCurve ψa) (hψb : IsCurve ψb)
    (hab : capability ψa ≤ capability ψb) :
    ∫ h in Ioi (0 : ℝ), max (ψa h - ψb h) 0 ≤ deficit ψa + deficit ψb ∧
      ∫ h in Ioi (0 : ℝ), max (ψa h - ψb h) 0 ≤ (spread ψa + spread ψb) / Real.sqrt 2 := by
  have hΨa := capability_nonneg hψa
  have hΨb := capability_nonneg hψb
  -- the comparison function
  have i1 : IntegrableOn (fun h => 1 - ψb h) (Ioc 0 (capability ψb)) :=
    (integrableOn_const (by simp)).sub (hψb.integrable.mono_set Ioc_subset_Ioi_self)
  have i1a : IntegrableOn (fun h => 1 - ψb h) (Ioc 0 (capability ψa)) :=
    i1.mono_set (Ioc_subset_Ioc_right hab)
  have i2 : IntegrableOn ψa (Ioi (capability ψa)) :=
    hψa.integrable.mono_set (Ioi_subset_Ioi hΨa)
  have iF : IntegrableOn (fun h => (Ioc 0 (capability ψa)).indicator (fun h => 1 - ψb h) h
      + (Ioi (capability ψa)).indicator ψa h) (Ioi 0) :=
    (((integrable_indicator_iff measurableSet_Ioc).2 i1a).integrableOn).add
      (((integrable_indicator_iff measurableSet_Ioi).2 i2).integrableOn)
  have hmono : ∫ h in Ioi (0 : ℝ), max (ψa h - ψb h) 0
      ≤ ∫ h in Ioi (0 : ℝ), ((Ioc 0 (capability ψa)).indicator (fun h => 1 - ψb h) h
        + (Ioi (capability ψa)).indicator ψa h) := by
    refine setIntegral_mono_on (hψa.integrable.sub hψb.integrable).pos_part iF measurableSet_Ioi
      fun h hh => ?_
    have a0 := hψa.nonneg h (le_of_lt hh)
    have a1 := hψa.le_one h (le_of_lt hh)
    have b0 := hψb.nonneg h (le_of_lt hh)
    have b1 := hψb.le_one h (le_of_lt hh)
    rcases le_or_gt h (capability ψa) with hle | hgt
    · have m1 : h ∈ Ioc 0 (capability ψa) := ⟨hh, hle⟩
      have m2 : h ∉ Ioi (capability ψa) := not_lt.2 hle
      simp only [indicator_of_mem m1, indicator_of_notMem m2, add_zero]
      exact max_le (by linarith) (by linarith)
    · have m1 : h ∉ Ioc 0 (capability ψa) := fun hm => not_le.2 hgt hm.2
      have m2 : h ∈ Ioi (capability ψa) := hgt
      simp only [indicator_of_notMem m1, indicator_of_mem m2, zero_add]
      exact max_le (by linarith) (by linarith)
  have hsplit : ∫ h in Ioi (0 : ℝ), ((Ioc 0 (capability ψa)).indicator (fun h => 1 - ψb h) h
        + (Ioi (capability ψa)).indicator ψa h)
      = (∫ h in Ioc 0 (capability ψa), (1 - ψb h)) + ∫ h in Ioi (capability ψa), ψa h := by
    rw [integral_add (((integrable_indicator_iff measurableSet_Ioc).2 i1a).integrableOn)
      (((integrable_indicator_iff measurableSet_Ioi).2 i2).integrableOn),
      setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.2 Ioc_subset_Ioi_self, inter_eq_right.2 (Ioi_subset_Ioi hΨa)]
  have hb' : ∫ h in Ioc 0 (capability ψa), (1 - ψb h) ≤ deficit ψb := by
    unfold deficit
    rw [intervalIntegral.integral_of_le hΨb]
    refine setIntegral_mono_set i1 ?_ (Ioc_subset_Ioc_right hab).eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    exact sub_nonneg.2 (hψb.le_one h hh.1.le)
  have hfirst : ∫ h in Ioi (0 : ℝ), max (ψa h - ψb h) 0 ≤ deficit ψa + deficit ψb := by
    rw [hsplit, ← deficit_eq_excess hψa] at hmono
    linarith
  refine ⟨hfirst, hfirst.trans ?_⟩
  rw [add_div]
  linarith [deficit_le hψa, deficit_le hψb]

end UncontainabilityLean.Generality
