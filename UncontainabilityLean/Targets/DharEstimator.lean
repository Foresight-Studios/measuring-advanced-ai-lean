/-
# Dhar estimator bounds  (Dhar, Oldenburg & Søgaard 2025, arXiv 2511.11773 — index ID 3)

Fable block 2 · priority 3.

Sheet row: task-level bound n ≥ ln(2/δ)/(2ε²) ⇒ accuracy ε at confidence δ; two-level bound
adds the between-task term; the paper's eq. (14) does not follow from its own eq. (12).

What the paper says (Theorem 1, pp. 7–8):
  eq. (12): sup_h |L_Q(h) − (1/n)Σ L̂_{P_i}(h)| ≤ O( √((C+ln(n/δ))/m) + √((C+ln(1/δ))/n) )
  eq. (14): L_Q(h) ≤ (1/n)Σ L̂_{P_i}(h) + O( √((C+ln(1/δ))/(nm)) )        ← does NOT follow
The between-task term √(·/n) does not shrink with m, so (14) overstates the rate.
A faithful formalization proves (12)'s structure for a fixed hypothesis and records the
correction in the README.

Mathlib support: `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` (Hoeffding for
sub-Gaussian sums) and `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (Hoeffding's
lemma) in `Mathlib/Probability/Moments/SubGaussian.lean`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Real

namespace UncontainabilityLean.DharEstimator

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Helper (one-sided Hoeffding): `n` independent centred variables, each with range inside an
interval of length one, have sum at least `n * ε` with probability at most `exp (-2 n ε²)`. -/
theorem one_sided_hoeffding (n : ℕ) (hn : 0 < n) (Y : Fin n → Ω → ℝ)
    (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i)) (a : ℝ)
    (hbd : ∀ i ω, Y i ω ∈ Set.Icc a (a + 1)) (hmean : ∀ i, μ[Y i] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | n * ε ≤ ∑ i, Y i ω} ≤ exp (-2 * n * ε ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (Y i) ((‖(a + 1) - a‖₊ / 2) ^ 2) μ := fun i _ =>
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hmeas i).aemeasurable
      (ae_of_all _ (hbd i)) (hmean i)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub
    (ε := n * ε) (by positivity)
  refine h.trans (le_of_eq ?_)
  congr 1
  simp
  field_simp

/-- Task-level Hoeffding bound: n independent task scores in [0,1] with common mean `m`. -/
theorem task_level_hoeffding (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hbd : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (m : ℝ) (hmean : ∀ i, μ[X i] = m)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ |(∑ i, X i ω) / n - m|} ≤ 2 * exp (-2 * n * ε ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hint : ∀ i, Integrable (X i) μ := fun i =>
    Integrable.of_mem_Icc 0 1 (hmeas i).aemeasurable (ae_of_all _ (hbd i))
  -- upper tail
  have hU := one_sided_hoeffding μ n hn (fun i ω => X i ω - m)
    (hind.comp (fun _ x => x - m) (fun _ => measurable_id.sub_const m))
    (fun i => (hmeas i).sub_const m) (-m)
    (fun i ω => ⟨by linarith [(hbd i ω).1], by linarith [(hbd i ω).2]⟩)
    (fun i => by simp [integral_sub (hint i) (integrable_const m), hmean i]) hε
  -- lower tail
  have hL := one_sided_hoeffding μ n hn (fun i ω => m - X i ω)
    (hind.comp (fun _ x => m - x) (fun _ => measurable_const.sub measurable_id))
    (fun i => (hmeas i).const_sub m) (m - 1)
    (fun i ω => ⟨by linarith [(hbd i ω).2], by linarith [(hbd i ω).1]⟩)
    (fun i => by simp [integral_sub (integrable_const m) (hint i), hmean i]) hε
  have hsubset : {ω | ε ≤ |(∑ i, X i ω) / n - m|} ⊆
      {ω | n * ε ≤ ∑ i, (X i ω - m)} ∪ {ω | n * ε ≤ ∑ i, (m - X i ω)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hω ⊢
    have hdiv : (∑ i, X i ω) / n - m = ((∑ i, X i ω) - n * m) / n := by field_simp
    rw [hdiv, abs_div, abs_of_pos hn', le_div_iff₀ hn', le_abs] at hω
    rcases hω with h | h
    · left; linarith
    · right; linarith
  calc μ.real {ω | ε ≤ |(∑ i, X i ω) / n - m|}
      ≤ μ.real ({ω | n * ε ≤ ∑ i, (X i ω - m)} ∪ {ω | n * ε ≤ ∑ i, (m - X i ω)}) :=
        measureReal_mono hsubset
    _ ≤ μ.real {ω | n * ε ≤ ∑ i, (X i ω - m)} + μ.real {ω | n * ε ≤ ∑ i, (m - X i ω)} :=
        measureReal_union_le _ _
    _ ≤ exp (-2 * n * ε ^ 2) + exp (-2 * n * ε ^ 2) := add_le_add hU hL
    _ = 2 * exp (-2 * n * ε ^ 2) := by ring

/-- Sample-size certificate: n ≥ ln(2/δ)/(2ε²) tasks suffice for accuracy ε with
failure probability at most δ. -/
theorem sample_size_certificate (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hbd : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (m : ℝ) (hmean : ∀ i, μ[X i] = m)
    {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsize : log (2 / δ) / (2 * ε ^ 2) ≤ n) :
    μ.real {ω | ε ≤ |(∑ i, X i ω) / n - m|} ≤ δ := by
  refine (task_level_hoeffding μ n hn X hind hmeas hbd m hmean hε).trans ?_
  have hε2 : (0 : ℝ) < 2 * ε ^ 2 := by positivity
  have hlog : log (2 / δ) ≤ 2 * n * ε ^ 2 := by
    have := (div_le_iff₀ hε2).mp hsize
    linarith
  have hexp : exp (-2 * n * ε ^ 2) ≤ δ / 2 := by
    have h1 : exp (-2 * n * ε ^ 2) ≤ exp (-log (2 / δ)) := exp_le_exp.mpr (by linarith)
    rwa [exp_neg, exp_log (by positivity), inv_div] at h1
  linarith

-- STATEMENT UNREVIEWED (written by Fable, session 2, block A4).
-- Source: project sheet, row Dhar, "task-level bound n ≥ ln(2/δ)/(2ε²) ⇒ accuracy ε at
-- confidence δ"; derived from eq. (11), p. 8 of arXiv 2511.11773 for a fixed hypothesis.
/-- Proposed replacement for `sample_size_certificate` without its unused hypothesis
`δ < 1`. -/
theorem sample_size_certificate_proposed (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hbd : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (m : ℝ) (hmean : ∀ i, μ[X i] = m)
    {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ)
    (hsize : log (2 / δ) / (2 * ε ^ 2) ≤ n) :
    μ.real {ω | ε ≤ |(∑ i, X i ω) / n - m|} ≤ δ := by
  refine (task_level_hoeffding μ n hn X hind hmeas hbd m hmean hε).trans ?_
  have hε2 : (0 : ℝ) < 2 * ε ^ 2 := by positivity
  have hlog : log (2 / δ) ≤ 2 * n * ε ^ 2 := by
    have := (div_le_iff₀ hε2).mp hsize
    linarith
  have hexp : exp (-2 * n * ε ^ 2) ≤ δ / 2 := by
    have h1 : exp (-2 * n * ε ^ 2) ≤ exp (-log (2 / δ)) := exp_le_exp.mpr (by linarith)
    rwa [exp_neg, exp_log (by positivity), inv_div] at h1
  linarith

/-
TODO (Fable writes the statement, reviewer checks it): two-level bound for a FIXED
hypothesis. n tasks P_i ~ Q i.i.d.; within each task m i.i.d. samples with losses in [0,1].
Target shape, with probability ≥ 1 − δ:
  |L_Q − (1/n) Σ_i L̂_{P_i}| ≤ √(ln(4n/δ)/(2m)) + √(ln(4/δ)/(2n))
(exact constants to be fixed by the proof; the point is the two separate terms).
Then a remark-level lemma showing the single-term √(·/(nm)) rate of eq. (14) fails in
general (e.g. m → ∞ with n fixed leaves the between-task deviation nonzero).
-/

/-
## Two-level bound (added in the Fable window)

-- STATEMENT UNREVIEWED: the statements and definitions in this section were written by
-- Fable from the TODO above and pp. 7–8 of the paper. A human reviewer must check them
-- against `STATEMENT_REVIEW.md` before they are called certified.

Model, for a FIXED hypothesis h. Task `i` is a random element `T i` of a task space `𝒯`
with law `Q`. Sample `j` of task `i` has loss `ℓ (T i) (U i j)`, where `U i j` is sampling
noise with law `ρ` on `𝒰` and `ℓ : 𝒯 → 𝒰 → [0,1]` is jointly measurable. (Any task-indexed
family of data distributions on a standard Borel space can be written this way with
`𝒰 = [0,1]`, `ρ` uniform.) Independence assumed: the tasks are independent; within each
task the noise variables are independent of each other and of that task. Nothing is
assumed about dependence between the noise of different tasks.

  L_P(h)  = `taskLoss ρ ℓ τ`      L_Q(h) = `envLoss Q ρ ℓ`      L̂_P(h) = `empLoss ℓ τ u`

`two_level_bound` gives, for all ε₁, ε₂ > 0,
  P( |L_Q − (1/n) Σ_i L̂_{P_i}| ≥ ε₁ + ε₂ ) ≤ 2n·exp(−2mε₁²) + 2·exp(−2nε₂²),
`two_level_bound_delta` the confidence form with the two separate terms of eq. (12), and
`eq14_single_term_fails` shows the single √(·/(nm)) term of eq. (14) cannot hold.
-/

section TwoLevel

variable {𝒯 𝒰 : Type*} [MeasurableSpace 𝒯] [MeasurableSpace 𝒰]

/-- True loss of the fixed hypothesis on task `τ`: the mean of the per-sample loss `ℓ τ u`
over the sampling noise `u ~ ρ`. This is the paper's `L_P(h)`. -/
noncomputable def taskLoss (ρ : Measure 𝒰) (ℓ : 𝒯 → 𝒰 → ℝ) (τ : 𝒯) : ℝ := ∫ u, ℓ τ u ∂ρ

/-- Environment-average loss `L_Q(h) = E_{P∼Q} L_P(h)`. -/
noncomputable def envLoss (Q : Measure 𝒯) (ρ : Measure 𝒰) (ℓ : 𝒯 → 𝒰 → ℝ) : ℝ :=
  ∫ τ, taskLoss ρ ℓ τ ∂Q

/-- Empirical loss on one task from `m` samples: the paper's `L̂_P(h)`, eq. (8). -/
noncomputable def empLoss {m : ℕ} (ℓ : 𝒯 → 𝒰 → ℝ) (τ : 𝒯) (u : Fin m → 𝒰) : ℝ :=
  (∑ j, ℓ τ (u j)) / m

theorem measurable_taskLoss (ρ : Measure 𝒰) [IsProbabilityMeasure ρ] (ℓ : 𝒯 → 𝒰 → ℝ)
    (hℓ : Measurable (Function.uncurry ℓ)) : Measurable (taskLoss ρ ℓ) :=
  (hℓ.stronglyMeasurable.integral_prod_right').measurable

theorem taskLoss_mem_Icc (ρ : Measure 𝒰) [IsProbabilityMeasure ρ] (ℓ : 𝒯 → 𝒰 → ℝ)
    (hℓ : Measurable (Function.uncurry ℓ)) (hbd : ∀ τ u, ℓ τ u ∈ Set.Icc (0 : ℝ) 1) (τ : 𝒯) :
    taskLoss ρ ℓ τ ∈ Set.Icc (0 : ℝ) 1 := by
  have hm : Measurable (ℓ τ) := hℓ.comp measurable_prodMk_left
  have hint : Integrable (ℓ τ) ρ :=
    Integrable.of_mem_Icc 0 1 hm.aemeasurable (ae_of_all _ (hbd τ))
  constructor
  · exact integral_nonneg fun u => (hbd τ u).1
  · calc taskLoss ρ ℓ τ ≤ ∫ _u, (1 : ℝ) ∂ρ :=
        integral_mono hint (integrable_const 1) fun u => (hbd τ u).2
      _ = 1 := by simp

/-- Within-task step for a fixed task `τ`, on the sample space `(Fin m → 𝒰, ρ^m)`. -/
theorem within_task_fixed (ρ : Measure 𝒰) [IsProbabilityMeasure ρ] (m : ℕ) (hm : 0 < m)
    (ℓ : 𝒯 → 𝒰 → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hbd : ∀ τ u, ℓ τ u ∈ Set.Icc (0 : ℝ) 1) (τ : 𝒯) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi fun _ : Fin m => ρ).real {u | ε ≤ |empLoss ℓ τ u - taskLoss ρ ℓ τ|}
      ≤ 2 * exp (-2 * m * ε ^ 2) := by
  have hmℓ : Measurable (ℓ τ) := hℓ.comp measurable_prodMk_left
  exact task_level_hoeffding (Measure.pi fun _ : Fin m => ρ) m hm (fun j u => ℓ τ (u j))
    (iIndepFun_pi (X := fun _ : Fin m => ℓ τ) fun _ => hmℓ.aemeasurable)
    (fun j => hmℓ.comp (measurable_pi_apply j)) (fun j u => hbd τ (u j)) (taskLoss ρ ℓ τ)
    (fun j => integral_comp_eval (μ := fun _ : Fin m => ρ) (i := j)
      hmℓ.aestronglyMeasurable) hε

/-- Within-task step: a task `T` drawn at random, then `m` samples whose noise `U j` is
i.i.d. `ρ` and independent of the task. -/
theorem within_task_bound (ρ : Measure 𝒰) [IsProbabilityMeasure ρ] (m : ℕ) (hm : 0 < m)
    (T : Ω → 𝒯) (U : Fin m → Ω → 𝒰) (hT : Measurable T) (hU : ∀ j, Measurable (U j))
    (hUlaw : ∀ j, μ.map (U j) = ρ) (hUind : iIndepFun U μ)
    (hTU : IndepFun T (fun ω j => U j ω) μ)
    (ℓ : 𝒯 → 𝒰 → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hbd : ∀ τ u, ℓ τ u ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ |empLoss ℓ (T ω) (fun j => U j ω) - taskLoss ρ ℓ (T ω)|}
      ≤ 2 * exp (-2 * m * ε ^ 2) := by
  set Pm : Measure (Fin m → 𝒰) := Measure.pi fun _ : Fin m => ρ with hPm
  have hUvec : Measurable fun ω j => U j ω := Measurable.of_eval hU
  have hlawU : μ.map (fun ω j => U j ω) = Pm := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun j => (hU j).aemeasurable).mp hUind]
    simp only [hUlaw, hPm]
  have hlaw : μ.map (fun ω => (T ω, fun j => U j ω)) = (μ.map T).prod Pm := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable hUvec.aemeasurable).mp hTU,
      hlawU]
  set A : Set (𝒯 × (Fin m → 𝒰)) := {p | ε ≤ |empLoss ℓ p.1 p.2 - taskLoss ρ ℓ p.1|} with hA
  have hemp : Measurable fun p : 𝒯 × (Fin m → 𝒰) => empLoss ℓ p.1 p.2 := by
    unfold empLoss
    refine Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _
    exact hℓ.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hAmeas : MeasurableSet A :=
    measurableSet_le measurable_const
      ((hemp.sub ((measurable_taskLoss ρ ℓ hℓ).comp measurable_fst)).abs)
  have hc : (0 : ℝ) ≤ 2 * exp (-2 * m * ε ^ 2) := by positivity
  have hpre : {ω | ε ≤ |empLoss ℓ (T ω) (fun j => U j ω) - taskLoss ρ ℓ (T ω)|}
      = (fun ω => (T ω, fun j => U j ω)) ⁻¹' A := rfl
  rw [hpre, measureReal_def, ← Measure.map_apply (hT.prodMk hUvec) hAmeas, hlaw,
    Measure.prod_apply hAmeas]
  refine ENNReal.toReal_le_of_le_ofReal hc ?_
  calc ∫⁻ τ, Pm (Prod.mk τ ⁻¹' A) ∂(μ.map T)
      ≤ ∫⁻ _τ, ENNReal.ofReal (2 * exp (-2 * m * ε ^ 2)) ∂(μ.map T) := by
        refine lintegral_mono fun τ => ?_
        have h := within_task_fixed ρ m hm ℓ hℓ hbd τ hε
        rw [measureReal_def] at h
        exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc).mpr h
    _ = ENNReal.ofReal (2 * exp (-2 * m * ε ^ 2)) := by
        have : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map_iff hT.aemeasurable |>.mpr inferInstance
        simp

/-- **Two-level bound for a fixed hypothesis** (the structure of the paper's eq. (12)). -/
theorem two_level_bound (Q : Measure 𝒯) (ρ : Measure 𝒰) [IsProbabilityMeasure ρ]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (T : Fin n → Ω → 𝒯) (U : Fin n → Fin m → Ω → 𝒰)
    (hT : ∀ i, Measurable (T i)) (hU : ∀ i j, Measurable (U i j))
    (hTlaw : ∀ i, μ.map (T i) = Q) (hUlaw : ∀ i j, μ.map (U i j) = ρ)
    (hTind : iIndepFun T μ) (hUind : ∀ i, iIndepFun (U i) μ)
    (hTU : ∀ i, IndepFun (T i) (fun ω j => U i j ω) μ)
    (ℓ : 𝒯 → 𝒰 → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hbd : ∀ τ u, ℓ τ u ∈ Set.Icc (0 : ℝ) 1)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    μ.real {ω | ε₁ + ε₂ ≤
        |envLoss Q ρ ℓ - (∑ i, empLoss ℓ (T i ω) (fun j => U i j ω)) / n|}
      ≤ 2 * n * exp (-2 * m * ε₁ ^ 2) + 2 * exp (-2 * n * ε₂ ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hg := measurable_taskLoss ρ ℓ hℓ
  -- between-task step: Hoeffding over the n task losses
  have hB := task_level_hoeffding μ n hn (fun i ω => taskLoss ρ ℓ (T i ω))
    (hTind.comp (fun _ => taskLoss ρ ℓ) fun _ => hg) (fun i => hg.comp (hT i))
    (fun i ω => taskLoss_mem_Icc ρ ℓ hℓ hbd (T i ω)) (envLoss Q ρ ℓ)
    (fun i => by
      rw [envLoss, ← hTlaw i, integral_map (hT i).aemeasurable hg.aestronglyMeasurable]) hε₂
  -- within-task step, one task at a time
  have hW : ∀ i, μ.real {ω | ε₁ ≤
      |empLoss ℓ (T i ω) (fun j => U i j ω) - taskLoss ρ ℓ (T i ω)|}
      ≤ 2 * exp (-2 * m * ε₁ ^ 2) := fun i =>
    within_task_bound μ ρ m hm (T i) (U i) (hT i) (hU i) (hUlaw i) (hUind i) (hTU i) ℓ hℓ hbd hε₁
  have hsubset : {ω | ε₁ + ε₂ ≤
        |envLoss Q ρ ℓ - (∑ i, empLoss ℓ (T i ω) (fun j => U i j ω)) / n|} ⊆
      {ω | ε₂ ≤ |(∑ i, taskLoss ρ ℓ (T i ω)) / n - envLoss Q ρ ℓ|} ∪
      ⋃ i ∈ (Finset.univ : Finset (Fin n)), {ω | ε₁ ≤
        |empLoss ℓ (T i ω) (fun j => U i j ω) - taskLoss ρ ℓ (T i ω)|} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_univ,
      exists_true_left, not_or, not_exists, not_le] at hcon
    obtain ⟨h2, h1⟩ := hcon
    have hsum : |∑ i, (empLoss ℓ (T i ω) (fun j => U i j ω) - taskLoss ρ ℓ (T i ω))|
        < n * ε₁ := by
      calc |∑ i, (empLoss ℓ (T i ω) (fun j => U i j ω) - taskLoss ρ ℓ (T i ω))|
          ≤ ∑ i, |empLoss ℓ (T i ω) (fun j => U i j ω) - taskLoss ρ ℓ (T i ω)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ < ∑ _i : Fin n, ε₁ := by
            have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
            exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => h1 i
        _ = n * ε₁ := by simp
    have hdecomp : envLoss Q ρ ℓ - (∑ i, empLoss ℓ (T i ω) (fun j => U i j ω)) / n
        = -((∑ i, taskLoss ρ ℓ (T i ω)) / n - envLoss Q ρ ℓ)
          - (∑ i, (empLoss ℓ (T i ω) (fun j => U i j ω) - taskLoss ρ ℓ (T i ω))) / n := by
      rw [Finset.sum_sub_distrib]; ring
    have hdiv : |(∑ i, (empLoss ℓ (T i ω) (fun j => U i j ω) - taskLoss ρ ℓ (T i ω))) / n|
        < ε₁ := by
      rw [abs_div, abs_of_pos hn', div_lt_iff₀ hn']; linarith
    have : |envLoss Q ρ ℓ - (∑ i, empLoss ℓ (T i ω) (fun j => U i j ω)) / n| < ε₁ + ε₂ := by
      rw [hdecomp]
      calc _ ≤ |-((∑ i, taskLoss ρ ℓ (T i ω)) / n - envLoss Q ρ ℓ)|
            + |(∑ i, (empLoss ℓ (T i ω) (fun j => U i j ω) - taskLoss ρ ℓ (T i ω))) / n| :=
            abs_sub _ _
        _ < ε₁ + ε₂ := by rw [abs_neg]; linarith
    exact absurd hω (not_le.mpr this)
  calc _ ≤ μ.real ({ω | ε₂ ≤ |(∑ i, taskLoss ρ ℓ (T i ω)) / n - envLoss Q ρ ℓ|} ∪
        ⋃ i ∈ (Finset.univ : Finset (Fin n)), {ω | ε₁ ≤
          |empLoss ℓ (T i ω) (fun j => U i j ω) - taskLoss ρ ℓ (T i ω)|}) :=
        measureReal_mono hsubset
    _ ≤ 2 * exp (-2 * n * ε₂ ^ 2) + ∑ _i : Fin n, 2 * exp (-2 * m * ε₁ ^ 2) :=
        (measureReal_union_le _ _).trans (add_le_add hB
          ((measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i _ => hW i)))
    _ = 2 * n * exp (-2 * m * ε₁ ^ 2) + 2 * exp (-2 * n * ε₂ ^ 2) := by
        simp; ring

/-- **Two-level bound, confidence form.** With probability at least `1 − δ`,
`|L_Q − (1/n) Σ_i L̂_{P_i}| < √(ln(4n/δ)/(2m)) + √(ln(4/δ)/(2n))`.
The second (between-task) term does not depend on `m`. -/
theorem two_level_bound_delta (Q : Measure 𝒯) (ρ : Measure 𝒰) [IsProbabilityMeasure ρ]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (T : Fin n → Ω → 𝒯) (U : Fin n → Fin m → Ω → 𝒰)
    (hT : ∀ i, Measurable (T i)) (hU : ∀ i j, Measurable (U i j))
    (hTlaw : ∀ i, μ.map (T i) = Q) (hUlaw : ∀ i j, μ.map (U i j) = ρ)
    (hTind : iIndepFun T μ) (hUind : ∀ i, iIndepFun (U i) μ)
    (hTU : ∀ i, IndepFun (T i) (fun ω j => U i j ω) μ)
    (ℓ : 𝒯 → 𝒰 → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hbd : ∀ τ u, ℓ τ u ∈ Set.Icc (0 : ℝ) 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | √(log (4 * n / δ) / (2 * m)) + √(log (4 / δ) / (2 * n)) ≤
        |envLoss Q ρ ℓ - (∑ i, empLoss ℓ (T i ω) (fun j => U i j ω)) / n|} ≤ δ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h4 : 1 < 4 / δ := by rw [lt_div_iff₀ hδ0]; linarith
  have h4n : 1 < 4 * n / δ := by rw [lt_div_iff₀ hδ0]; nlinarith
  have hl1 : 0 < log (4 * n / δ) / (2 * m) := div_pos (log_pos h4n) (by positivity)
  have hl2 : 0 < log (4 / δ) / (2 * n) := div_pos (log_pos h4) (by positivity)
  refine (two_level_bound μ Q ρ n m hn hm T U hT hU hTlaw hUlaw hTind hUind hTU ℓ hℓ hbd
    (sqrt_pos.mpr hl1) (sqrt_pos.mpr hl2)).trans ?_
  rw [sq_sqrt hl1.le, sq_sqrt hl2.le]
  have e1 : -2 * (m : ℝ) * (log (4 * n / δ) / (2 * m)) = -log (4 * n / δ) := by
    field_simp
  have e2 : -2 * (n : ℝ) * (log (4 / δ) / (2 * n)) = -log (4 / δ) := by
    field_simp
  rw [e1, e2, exp_neg, exp_neg, exp_log (by positivity), exp_log (by positivity)]
  have : 2 * (n : ℝ) * (4 * n / δ)⁻¹ + 2 * (4 / δ)⁻¹ = δ := by
    field_simp; ring
  exact this.le

/-- **Remark: the single-term rate of eq. (14) fails.** For every constant `K` (standing for
`c² (C + ln(1/δ))`) there is a task environment — two equally likely tasks, one with loss
always 0 and one with loss always 1 — in which, with `n = 1` task, the estimate misses
`L_Q` by more than `√(K / (n m))` for *every* drawn task and *every* sample, as soon as
`m > 4K`. Taking more samples per task cannot repair the between-task term. -/
theorem eq14_single_term_fails (K : ℝ) :
    ∃ (Q : Measure Bool) (_ : IsProbabilityMeasure Q) (ℓ : Bool → Unit → ℝ),
      Measurable (Function.uncurry ℓ) ∧ (∀ τ u, ℓ τ u ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ m : ℕ, 4 * K < m → ∀ (τ : Bool) (u : Fin m → Unit),
        √(K / ((1 : ℕ) * m)) < |envLoss Q (Measure.dirac ()) ℓ - empLoss ℓ τ u| := by
  let ℓ : Bool → Unit → ℝ := fun τ _ => if τ then 1 else 0
  let Q : Measure Bool :=
    (2⁻¹ : ENNReal) • Measure.dirac true + (2⁻¹ : ENNReal) • Measure.dirac false
  have hQ : IsProbabilityMeasure Q := ⟨by simp [Q, ENNReal.inv_two_add_inv_two]⟩
  refine ⟨Q, hQ, ℓ, measurable_of_countable _, fun τ u => ?_, fun m hmK τ u => ?_⟩
  · cases τ <;> simp [ℓ]
  have henv : envLoss Q (Measure.dirac ()) ℓ = 1 / 2 := by
    have hint : ∀ ν : Measure Bool, IsFiniteMeasure ν →
        Integrable (fun τ : Bool => if τ then (1 : ℝ) else 0) ν := fun ν _ => .of_finite
    simp only [envLoss, taskLoss, Q, ℓ, integral_dirac]
    have hfin : ∀ b : Bool, IsFiniteMeasure ((2⁻¹ : ENNReal) • Measure.dirac b) := fun b =>
      Measure.smul_finite _ (by simp)
    rw [integral_add_measure (hint _ (hfin true)) (hint _ (hfin false)),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    simp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [henv, empLoss]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hemp : empLoss ℓ τ u = if τ then 1 else 0 := by
    simp only [empLoss, ℓ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have habs : |envLoss Q (Measure.dirac ()) ℓ - empLoss ℓ τ u| = 1 / 2 := by
    rw [henv, hemp]
    cases τ <;> norm_num [abs_of_neg, abs_of_pos]
  rw [habs, Nat.cast_one, one_mul]
  by_cases hK : 0 ≤ K
  · rw [show (1 : ℝ) / 2 = √(1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    refine sqrt_lt_sqrt (by positivity) ?_
    rw [div_lt_iff₀ hm']
    linarith
  · rw [sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hK) hm'.le)]
    norm_num

end TwoLevel

end UncontainabilityLean.DharEstimator
