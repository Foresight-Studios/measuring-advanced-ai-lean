/-
# Dhar estimator bounds: the sharper within-task term  (session 2, block B2)

Source: Dhar, Oldenburg & Søgaard 2025, arXiv 2511.11773, Theorem 1, p. 8.
  eq. (12):  sup_h |L_Q(h) − (1/n)Σ L̂_{P_i}(h)| ≤ O( √((C+ln(n/δ))/m) + √((C+ln(1/δ))/n) )
  eq. (14):  L_Q(h) ≤ (1/n)Σ L̂_{P_i}(h) + O( √((C+ln(1/δ))/(nm)) )

Session 1 (`two_level_bound_delta`) proved, for a fixed hypothesis,
  √(ln(4n/δ)/(2m)) + √(ln(4/δ)/(2n)),
whose within-task term comes from a union bound over the n tasks. This file sharpens the
within-task term to the √(·/(nm)) rate of eq. (14):

  with probability ≥ 1 − δ,
    |L_Q − (1/n)Σ_i L̂_{P_i}| < √(ln(4/δ)/(2nm)) + √(ln(4/δ)/(2n)).

So eq. (14)'s rate IS correct for the within-task part of the error, and the between-task
term √(ln(4/δ)/(2n)) is the only one that does not improve with m. Together with
`eq14_single_term_fails` this locates the paper's error exactly: (14) drops the second term.

How it is proved, and what that costs. Conditionally on the tasks, the n·m centred sample
losses are independent, so Hoeffding's inequality applies to all of them at once (no union
bound over tasks). The conditioning is done by a product-measure (Fubini) argument, as in
session 1's `within_task_bound`. This needs a STRONGER independence hypothesis than
`two_level_bound`: all n·m noise variables are jointly independent (`hUind`) and the whole
task vector is independent of the whole noise array (`hTU`). `two_level_bound` assumed
independence only within each task.

The conditional Hoeffding lemma of `ForMathlib/ConditionalHoeffding.lean` is NOT used here.
A martingale (Azuma–Hoeffding) proof with that lemma would also cover samples chosen
adaptively; it is not attempted (see NOTES.md).

-- STATEMENT UNREVIEWED: every statement in this file was written by Fable (session 2).
-- A reviewer must check them against `STATEMENT_REVIEW.md` before they are called certified.
-/
import UncontainabilityLean.Targets.DharEstimator

open MeasureTheory ProbabilityTheory Real

namespace UncontainabilityLean.DharEstimator

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

-- STATEMENT UNREVIEWED. Source: Hoeffding's inequality, cited by the paper on p. 8
-- ("by Hoeffding's inequality"); the paper gives no statement of it.
/-- Helper (two-sided Hoeffding over a finite index type): independent centred variables
`Y i`, each with range inside its own interval `[a i, a i + 1]` of length one, have
`|∑ i, Y i| ≥ N ε` with probability at most `2 exp (-2 N ε²)`, where `N` is the number of
variables. Unlike `one_sided_hoeffding`, the intervals may differ between variables. -/
theorem hoeffding_fintype {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι) (Y : ι → Ω → ℝ)
    (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i)) (a : ι → ℝ)
    (hbd : ∀ i ω, Y i ω ∈ Set.Icc (a i) (a i + 1)) (hmean : ∀ i, μ[Y i] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | Fintype.card ι * ε ≤ |∑ i, Y i ω|}
      ≤ 2 * exp (-2 * Fintype.card ι * ε ^ 2) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  have one : ∀ (Z : ι → Ω → ℝ), iIndepFun Z μ → (∀ i, Measurable (Z i)) → ∀ b : ι → ℝ,
      (∀ i ω, Z i ω ∈ Set.Icc (b i) (b i + 1)) → (∀ i, μ[Z i] = 0) →
      μ.real {ω | Fintype.card ι * ε ≤ ∑ i, Z i ω} ≤ exp (-2 * Fintype.card ι * ε ^ 2) := by
    intro Z hZind hZmeas b hZbd hZmean
    have hsub : ∀ i ∈ (Finset.univ : Finset ι),
        HasSubgaussianMGF (Z i) ((‖(1 : ℝ)‖₊ / 2) ^ 2) μ := fun i _ => by
      have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hZmeas i).aemeasurable
        (ae_of_all _ (hZbd i)) (hZmean i)
      rwa [add_sub_cancel_left] at h
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hZind hsub
      (ε := Fintype.card ι * ε) (by positivity)
    refine h.trans (le_of_eq ?_)
    congr 1
    simp
    field_simp
  have hU := one Y hind hmeas a hbd hmean
  have hL := one (fun i ω => -Y i ω) (hind.comp (fun _ x => -x) fun _ => measurable_neg)
    (fun i => (hmeas i).neg) (fun i => -(a i + 1))
    (fun i ω => ⟨by linarith [(hbd i ω).2], by linarith [(hbd i ω).1]⟩)
    (fun i => by rw [integral_neg, hmean i, neg_zero])
  have hsubset : {ω | Fintype.card ι * ε ≤ |∑ i, Y i ω|} ⊆
      {ω | Fintype.card ι * ε ≤ ∑ i, Y i ω} ∪ {ω | Fintype.card ι * ε ≤ ∑ i, -Y i ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.sum_neg_distrib] at hω ⊢
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc _ ≤ μ.real ({ω | Fintype.card ι * ε ≤ ∑ i, Y i ω} ∪
        {ω | Fintype.card ι * ε ≤ ∑ i, -Y i ω}) := measureReal_mono hsubset
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ exp (-2 * Fintype.card ι * ε ^ 2) + exp (-2 * Fintype.card ι * ε ^ 2) :=
        add_le_add hU hL
    _ = 2 * exp (-2 * Fintype.card ι * ε ^ 2) := by ring

section Sharp

variable {𝒯 𝒰 : Type*} [MeasurableSpace 𝒯] [MeasurableSpace 𝒰]

-- STATEMENT UNREVIEWED. Source: arXiv 2511.11773, p. 8, the within-task part of the proof
-- of Theorem 1 (eq. (10)), here for all tasks at once and for fixed tasks.
/-- Within-task step for FIXED tasks `t 0, …, t (n-1)`, all tasks at once, on the noise
space `(Fin n × Fin m → 𝒰, ρ^{n·m})`: the average over tasks of (empirical loss − true loss)
exceeds `ε` in absolute value with probability at most `2 exp (-2 n m ε²)`. -/
theorem within_all_tasks_fixed (ρ : Measure 𝒰) [IsProbabilityMeasure ρ] (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (ℓ : 𝒯 → 𝒰 → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hbd : ∀ τ u, ℓ τ u ∈ Set.Icc (0 : ℝ) 1) (t : Fin n → 𝒯) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi fun _ : Fin n × Fin m => ρ).real
        {u | ε ≤ |(∑ i, (empLoss ℓ (t i) (fun j => u (i, j)) - taskLoss ρ ℓ (t i))) / n|}
      ≤ 2 * exp (-2 * n * m * ε ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hcard : Fintype.card (Fin n × Fin m) = n * m := by simp
  have hmℓ : ∀ τ, Measurable (ℓ τ) := fun τ => hℓ.comp measurable_prodMk_left
  have hintℓ : ∀ τ, Integrable (ℓ τ) ρ := fun τ =>
    Integrable.of_mem_Icc 0 1 (hmℓ τ).aemeasurable (ae_of_all _ (hbd τ))
  have hmX : ∀ p : Fin n × Fin m, Measurable fun x => ℓ (t p.1) x - taskLoss ρ ℓ (t p.1) :=
    fun p => (hmℓ _).sub_const _
  have key := hoeffding_fintype (Measure.pi fun _ : Fin n × Fin m => ρ)
    (ι := Fin n × Fin m) (by rw [hcard]; positivity)
    (fun p u => ℓ (t p.1) (u p) - taskLoss ρ ℓ (t p.1))
    (iIndepFun_pi (X := fun (p : Fin n × Fin m) x => ℓ (t p.1) x - taskLoss ρ ℓ (t p.1))
      fun p => (hmX p).aemeasurable)
    (fun p => (hmX p).comp (measurable_pi_apply p)) (fun p => -taskLoss ρ ℓ (t p.1))
    (fun p u => ⟨by linarith [(hbd (t p.1) (u p)).1], by linarith [(hbd (t p.1) (u p)).2]⟩)
    (fun p => by
      rw [integral_comp_eval (μ := fun _ : Fin n × Fin m => ρ) (i := p)
        (hmX p).aestronglyMeasurable, integral_sub (hintℓ _) (integrable_const _)]
      simp [taskLoss]) hε
  rw [hcard] at key
  push_cast at key
  refine (measureReal_mono ?_).trans (key.trans (le_of_eq (by ring_nf)))
  intro u hu
  simp only [Set.mem_ofPred_eq] at hu ⊢
  have hsum : ∑ p : Fin n × Fin m, (ℓ (t p.1) (u p) - taskLoss ρ ℓ (t p.1))
      = m * ∑ i, (empLoss ℓ (t i) (fun j => u (i, j)) - taskLoss ρ ℓ (t i)) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [empLoss, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsum, abs_mul, abs_of_pos hm']
  rw [abs_div, abs_of_pos hn', le_div_iff₀ hn'] at hu
  nlinarith

-- STATEMENT UNREVIEWED. Source: as for `within_all_tasks_fixed`, with the tasks random.
/-- Within-task step with random tasks: `T` is the vector of tasks, `U` the array of noise
variables, i.i.d. `ρ`, jointly independent, and independent of `T`. -/
theorem within_all_tasks_bound (ρ : Measure 𝒰) [IsProbabilityMeasure ρ] (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (T : Fin n → Ω → 𝒯) (U : Fin n → Fin m → Ω → 𝒰)
    (hT : ∀ i, Measurable (T i)) (hU : ∀ i j, Measurable (U i j))
    (hUlaw : ∀ i j, μ.map (U i j) = ρ)
    (hUind : iIndepFun (fun p : Fin n × Fin m => U p.1 p.2) μ)
    (hTU : IndepFun (fun ω i => T i ω) (fun ω (p : Fin n × Fin m) => U p.1 p.2 ω) μ)
    (ℓ : 𝒯 → 𝒰 → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hbd : ∀ τ u, ℓ τ u ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ |(∑ i, (empLoss ℓ (T i ω) (fun j => U i j ω)
        - taskLoss ρ ℓ (T i ω))) / n|} ≤ 2 * exp (-2 * n * m * ε ^ 2) := by
  set Pnm : Measure (Fin n × Fin m → 𝒰) := Measure.pi fun _ : Fin n × Fin m => ρ with hPnm
  have hTvec : Measurable fun ω i => T i ω := Measurable.of_eval hT
  have hUarr : Measurable fun ω (p : Fin n × Fin m) => U p.1 p.2 ω :=
    Measurable.of_eval fun p => hU p.1 p.2
  have hlawU : μ.map (fun ω (p : Fin n × Fin m) => U p.1 p.2 ω) = Pnm := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map (f := fun p : Fin n × Fin m => U p.1 p.2)
      fun p => (hU p.1 p.2).aemeasurable).mp hUind
    rw [h]
    simp only [hUlaw, hPnm]
  have hlaw : μ.map (fun ω => ((fun i => T i ω), fun p : Fin n × Fin m => U p.1 p.2 ω))
      = (μ.map fun ω i => T i ω).prod Pnm := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hTvec.aemeasurable hUarr.aemeasurable).mp hTU,
      hlawU]
  set A : Set ((Fin n → 𝒯) × (Fin n × Fin m → 𝒰)) :=
    {q | ε ≤ |(∑ i, (empLoss ℓ (q.1 i) (fun j => q.2 (i, j)) - taskLoss ρ ℓ (q.1 i))) / n|}
    with hA
  have hterm : ∀ i : Fin n, Measurable fun q : (Fin n → 𝒯) × (Fin n × Fin m → 𝒰) =>
      empLoss ℓ (q.1 i) (fun j => q.2 (i, j)) - taskLoss ρ ℓ (q.1 i) := by
    intro i
    refine Measurable.sub ?_
      ((measurable_taskLoss ρ ℓ hℓ).comp ((measurable_pi_apply i).comp measurable_fst))
    unfold empLoss
    refine Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _
    have hpair : Measurable fun q : (Fin n → 𝒯) × (Fin n × Fin m → 𝒰) =>
        (q.1 i, q.2 (i, j)) := by fun_prop
    exact hℓ.comp hpair
  have hAmeas : MeasurableSet A :=
    measurableSet_le measurable_const
      ((Finset.measurable_sum _ fun i _ => hterm i).div_const _).abs
  have hc : (0 : ℝ) ≤ 2 * exp (-2 * n * m * ε ^ 2) := by positivity
  have hpre : {ω | ε ≤ |(∑ i, (empLoss ℓ (T i ω) (fun j => U i j ω)
        - taskLoss ρ ℓ (T i ω))) / n|}
      = (fun ω => ((fun i => T i ω), fun p : Fin n × Fin m => U p.1 p.2 ω)) ⁻¹' A := rfl
  rw [hpre, measureReal_def, ← Measure.map_apply (hTvec.prodMk hUarr) hAmeas, hlaw,
    Measure.prod_apply hAmeas]
  refine ENNReal.toReal_le_of_le_ofReal hc ?_
  calc ∫⁻ t, Pnm (Prod.mk t ⁻¹' A) ∂(μ.map fun ω i => T i ω)
      ≤ ∫⁻ _t, ENNReal.ofReal (2 * exp (-2 * n * m * ε ^ 2)) ∂(μ.map fun ω i => T i ω) := by
        refine lintegral_mono fun t => ?_
        have h := within_all_tasks_fixed ρ n m hn hm ℓ hℓ hbd t hε
        rw [measureReal_def] at h
        exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc).mpr h
    _ = ENNReal.ofReal (2 * exp (-2 * n * m * ε ^ 2)) := by
        have : IsProbabilityMeasure (μ.map fun ω i => T i ω) :=
          Measure.isProbabilityMeasure_map_iff hTvec.aemeasurable |>.mpr inferInstance
        simp

-- STATEMENT UNREVIEWED. Source: arXiv 2511.11773, p. 8, eqs. (12) and (14), fixed
-- hypothesis; the within-task term has the √(·/(nm)) rate of (14), the between-task term
-- of (12) is kept.
/-- **Two-level bound with the sharp within-task term, tail form.** For a fixed
hypothesis, `n` i.i.d. tasks and `m` i.i.d. samples per task, all noise jointly independent
and independent of the tasks:
`P(|L_Q − (1/n) Σ_i L̂_{P_i}| ≥ ε₁ + ε₂) ≤ 2 exp(−2 n m ε₁²) + 2 exp(−2 n ε₂²)`.
Compare `two_level_bound`, whose first term is `2 n exp(−2 m ε₁²)`. -/
theorem two_level_bound_sharp (Q : Measure 𝒯) (ρ : Measure 𝒰) [IsProbabilityMeasure ρ]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (T : Fin n → Ω → 𝒯) (U : Fin n → Fin m → Ω → 𝒰)
    (hT : ∀ i, Measurable (T i)) (hU : ∀ i j, Measurable (U i j))
    (hTlaw : ∀ i, μ.map (T i) = Q) (hUlaw : ∀ i j, μ.map (U i j) = ρ)
    (hTind : iIndepFun T μ)
    (hUind : iIndepFun (fun p : Fin n × Fin m => U p.1 p.2) μ)
    (hTU : IndepFun (fun ω i => T i ω) (fun ω (p : Fin n × Fin m) => U p.1 p.2 ω) μ)
    (ℓ : 𝒯 → 𝒰 → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hbd : ∀ τ u, ℓ τ u ∈ Set.Icc (0 : ℝ) 1)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    μ.real {ω | ε₁ + ε₂ ≤
        |envLoss Q ρ ℓ - (∑ i, empLoss ℓ (T i ω) (fun j => U i j ω)) / n|}
      ≤ 2 * exp (-2 * n * m * ε₁ ^ 2) + 2 * exp (-2 * n * ε₂ ^ 2) := by
  have hg := measurable_taskLoss ρ ℓ hℓ
  -- between-task step: Hoeffding over the n task losses
  have hB := task_level_hoeffding μ n hn (fun i ω => taskLoss ρ ℓ (T i ω))
    (hTind.comp (fun _ => taskLoss ρ ℓ) fun _ => hg) (fun i => hg.comp (hT i))
    (fun i ω => taskLoss_mem_Icc ρ ℓ hℓ hbd (T i ω)) (envLoss Q ρ ℓ)
    (fun i => by
      rw [envLoss, ← hTlaw i, integral_map (hT i).aemeasurable hg.aestronglyMeasurable]) hε₂
  -- within-task step, all tasks at once
  have hW := within_all_tasks_bound μ ρ n m hn hm T U hT hU hUlaw hUind hTU ℓ hℓ hbd hε₁
  have hsubset : {ω | ε₁ + ε₂ ≤
        |envLoss Q ρ ℓ - (∑ i, empLoss ℓ (T i ω) (fun j => U i j ω)) / n|} ⊆
      {ω | ε₂ ≤ |(∑ i, taskLoss ρ ℓ (T i ω)) / n - envLoss Q ρ ℓ|} ∪
      {ω | ε₁ ≤ |(∑ i, (empLoss ℓ (T i ω) (fun j => U i j ω)
        - taskLoss ρ ℓ (T i ω))) / n|} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
    obtain ⟨h2, h1⟩ := hcon
    have hdecomp : envLoss Q ρ ℓ - (∑ i, empLoss ℓ (T i ω) (fun j => U i j ω)) / n
        = -((∑ i, taskLoss ρ ℓ (T i ω)) / n - envLoss Q ρ ℓ)
          - (∑ i, (empLoss ℓ (T i ω) (fun j => U i j ω) - taskLoss ρ ℓ (T i ω))) / n := by
      rw [Finset.sum_sub_distrib]; ring
    have : |envLoss Q ρ ℓ - (∑ i, empLoss ℓ (T i ω) (fun j => U i j ω)) / n| < ε₁ + ε₂ := by
      rw [hdecomp]
      calc _ ≤ |-((∑ i, taskLoss ρ ℓ (T i ω)) / n - envLoss Q ρ ℓ)|
            + |(∑ i, (empLoss ℓ (T i ω) (fun j => U i j ω) - taskLoss ρ ℓ (T i ω))) / n| :=
            abs_sub _ _
        _ < ε₁ + ε₂ := by rw [abs_neg]; linarith
    exact absurd hω (not_le.mpr this)
  calc _ ≤ μ.real ({ω | ε₂ ≤ |(∑ i, taskLoss ρ ℓ (T i ω)) / n - envLoss Q ρ ℓ|} ∪
        {ω | ε₁ ≤ |(∑ i, (empLoss ℓ (T i ω) (fun j => U i j ω)
          - taskLoss ρ ℓ (T i ω))) / n|}) := measureReal_mono hsubset
    _ ≤ 2 * exp (-2 * n * ε₂ ^ 2) + 2 * exp (-2 * n * m * ε₁ ^ 2) :=
        (measureReal_union_le _ _).trans (add_le_add hB hW)
    _ = 2 * exp (-2 * n * m * ε₁ ^ 2) + 2 * exp (-2 * n * ε₂ ^ 2) := by ring

-- STATEMENT UNREVIEWED. Source: arXiv 2511.11773, p. 8, eqs. (12) and (14), fixed
-- hypothesis, confidence form.
/-- **Two-level bound with the sharp within-task term, confidence form.** With probability
at least `1 − δ`,
`|L_Q − (1/n) Σ_i L̂_{P_i}| < √(ln(4/δ)/(2 n m)) + √(ln(4/δ)/(2 n))`.
The first term has the `1/√(n m)` rate of the paper's eq. (14); the second, between-task
term does not depend on `m` and is the only one that does not improve with more samples per
task. -/
theorem two_level_bound_sharp_delta (Q : Measure 𝒯) (ρ : Measure 𝒰) [IsProbabilityMeasure ρ]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (T : Fin n → Ω → 𝒯) (U : Fin n → Fin m → Ω → 𝒰)
    (hT : ∀ i, Measurable (T i)) (hU : ∀ i j, Measurable (U i j))
    (hTlaw : ∀ i, μ.map (T i) = Q) (hUlaw : ∀ i j, μ.map (U i j) = ρ)
    (hTind : iIndepFun T μ)
    (hUind : iIndepFun (fun p : Fin n × Fin m => U p.1 p.2) μ)
    (hTU : IndepFun (fun ω i => T i ω) (fun ω (p : Fin n × Fin m) => U p.1 p.2 ω) μ)
    (ℓ : 𝒯 → 𝒰 → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hbd : ∀ τ u, ℓ τ u ∈ Set.Icc (0 : ℝ) 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | √(log (4 / δ) / (2 * n * m)) + √(log (4 / δ) / (2 * n)) ≤
        |envLoss Q ρ ℓ - (∑ i, empLoss ℓ (T i ω) (fun j => U i j ω)) / n|} ≤ δ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h4 : 1 < 4 / δ := by rw [lt_div_iff₀ hδ0]; linarith
  have hl1 : 0 < log (4 / δ) / (2 * n * m) := div_pos (log_pos h4) (by positivity)
  have hl2 : 0 < log (4 / δ) / (2 * n) := div_pos (log_pos h4) (by positivity)
  refine (two_level_bound_sharp μ Q ρ n m hn hm T U hT hU hTlaw hUlaw hTind hUind hTU ℓ hℓ
    hbd (sqrt_pos.mpr hl1) (sqrt_pos.mpr hl2)).trans ?_
  rw [sq_sqrt hl1.le, sq_sqrt hl2.le]
  have e1 : -2 * (n : ℝ) * m * (log (4 / δ) / (2 * n * m)) = -log (4 / δ) := by
    field_simp
  have e2 : -2 * (n : ℝ) * (log (4 / δ) / (2 * n)) = -log (4 / δ) := by
    field_simp
  rw [e1, e2, exp_neg, exp_log (by positivity)]
  have : 2 * (4 / δ)⁻¹ + 2 * (4 / δ)⁻¹ = δ := by
    field_simp; ring
  exact this.le

end Sharp

end UncontainabilityLean.DharEstimator
