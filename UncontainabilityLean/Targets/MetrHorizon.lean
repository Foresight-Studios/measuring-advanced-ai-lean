/-
# METR horizon calculus  (Kwa et al. 2025, arXiv 2503.14499 — index ID 1)

Fable block 1 · priority 1.

Source model (paper eq. 1, Appendix):
  p_success(agent, task) = σ((log h_agent − log t_task) · β_agent)
where h is the 50%-horizon and β the agent's slope.

Targets (from "Lean Formalization Practical Benefits", row METR):
  * horizon-at-reliability law: h_r = h · odds(r)^(−1/β), odds(r) = r/(1−r)
  * 80-versus-50 ratio law:     h_0.8 = h · 4^(−1/β)
  * two sides of the threshold: t < h_r ⇒ success > r ; t > h_r ⇒ success < r
  * compounding, product form:  r ≤ (1−ε)^n ↔ n ≤ log r / log(1−ε)
  * compounding, union bound:   P(any of n steps fails) ≤ n·ε
Out of scope by design: the growth trend (that stays estimation).

STATUS: statements drafted by Opus from the paper and the sheet. Every `sorry` is a
Fable task. Statement fidelity must be checked by a human reviewer before "certified".
-/
import Mathlib

open Real MeasureTheory

namespace UncontainabilityLean.MetrHorizon

/-- The logistic function σ(x) = 1 / (1 + e^{−x}). -/
noncomputable def logistic (x : ℝ) : ℝ := 1 / (1 + exp (-x))

/-- Success probability of an agent with 50%-horizon `h` and slope `β` on a task of
human-baseline length `t` (paper eq. 1). -/
noncomputable def pSuccess (h β t : ℝ) : ℝ := logistic ((log h - log t) * β)

/-- odds(r) = r / (1 − r). -/
noncomputable def odds (r : ℝ) : ℝ := r / (1 - r)

/-- Horizon at reliability `r`: h · odds(r)^(−1/β). -/
noncomputable def horizonAt (h β r : ℝ) : ℝ := h * odds r ^ (-(1 / β))

/-- Sanity: at t = h the model predicts 50%. -/
theorem pSuccess_self (h β : ℝ) : pSuccess h β h = 1 / 2 := by
  simp [pSuccess, logistic]
  norm_num

-- STATEMENT UNREVIEWED (written by Fable, session 2, block A4).
-- Source: Kwa et al., arXiv 2503.14499, p. 25, item 2 below eq. (1): "when h_agent = t_task,
-- our model predicts a success probability of σ(0 · β_agent) = σ(0) = 0.5".
/-- Proposed replacement for `pSuccess_self`: the same conclusion under the hypothesis
`0 < h` that the paper's model needs. `pSuccess_self` holds for every real `h` only because
Lean's `log` is total; the guarded form says what the paper says. -/
theorem pSuccess_self_proposed {h β : ℝ} (_hh : 0 < h) : pSuccess h β h = 1 / 2 :=
  pSuccess_self h β

/-- Helper: the logistic function is strictly increasing. -/
theorem logistic_strictMono : StrictMono logistic := by
  intro a b hab
  unfold logistic
  have ha : 0 < exp (-a) := exp_pos _
  have hb : 0 < exp (-b) := exp_pos _
  have : exp (-b) < exp (-a) := exp_lt_exp.mpr (by linarith)
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-- Helper: odds are positive on (0, 1). -/
theorem odds_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : 0 < odds r :=
  div_pos hr0 (by linarith)

/-- Helper: the logistic function inverts log-odds. -/
theorem logistic_log_odds {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    logistic (log (odds r)) = r := by
  unfold logistic
  rw [exp_neg, exp_log (odds_pos hr0 hr1)]
  unfold odds
  have h1 : (1 - r) ≠ 0 := by linarith
  field_simp
  ring

/-- Helper: the r-horizon is a positive task length. -/
theorem horizonAt_pos {h β r : ℝ} (hh : 0 < h) (hr0 : 0 < r) (hr1 : r < 1) :
    0 < horizonAt h β r :=
  mul_pos hh (rpow_pos_of_pos (odds_pos hr0 hr1) _)

/-- Helper: at the r-horizon the logit equals the log-odds of r. -/
theorem logit_horizonAt {h β r : ℝ} (hh : 0 < h) (hβ : 0 < β) (hr0 : 0 < r) (hr1 : r < 1) :
    (log h - log (horizonAt h β r)) * β = log (odds r) := by
  have ho := odds_pos hr0 hr1
  unfold horizonAt
  rw [log_mul hh.ne' (rpow_pos_of_pos ho _).ne', log_rpow ho]
  field_simp
  ring

/-- Horizon-at-reliability law: the agent succeeds with probability exactly `r` on a task
of length `horizonAt h β r`. -/
theorem pSuccess_horizonAt {h β r : ℝ} (hh : 0 < h) (hβ : 0 < β) (hr0 : 0 < r) (hr1 : r < 1) :
    pSuccess h β (horizonAt h β r) = r := by
  unfold pSuccess
  rw [logit_horizonAt hh hβ hr0 hr1, logistic_log_odds hr0 hr1]

/-- 80-versus-50 ratio law. -/
theorem horizonAt_eighty {h β : ℝ} (hh : 0 < h) (hβ : 0 < β) :
    horizonAt h β (4 / 5) = h * (4 : ℝ) ^ (-(1 / β)) := by
  unfold horizonAt odds
  norm_num

-- STATEMENT UNREVIEWED (written by Fable, session 2, block A4).
-- Source: project sheet, row METR, "80-versus-50 ratio law: h_0.8 = h · 4^(−1/β)"; not a
-- displayed statement of Kwa et al. (the paper reports the ratio empirically, p. 7).
/-- Proposed replacement for `horizonAt_eighty` without its two unused hypotheses
(`0 < h`, `0 < β`): the identity is definitional, because `odds (4/5) = 4`. -/
theorem horizonAt_eighty_proposed (h β : ℝ) :
    horizonAt h β (4 / 5) = h * (4 : ℝ) ^ (-(1 / β)) := by
  unfold horizonAt odds
  norm_num

/-- Shorter tasks than the r-horizon succeed with probability above r. -/
theorem lt_pSuccess_of_lt_horizonAt {h β r t : ℝ} (hh : 0 < h) (hβ : 0 < β)
    (hr0 : 0 < r) (hr1 : r < 1) (ht : 0 < t) (htr : t < horizonAt h β r) :
    r < pSuccess h β t := by
  have hlog : log t < log (horizonAt h β r) := log_lt_log ht htr
  have key : (log h - log (horizonAt h β r)) * β < (log h - log t) * β :=
    mul_lt_mul_of_pos_right (by linarith) hβ
  calc r = pSuccess h β (horizonAt h β r) := (pSuccess_horizonAt hh hβ hr0 hr1).symm
    _ < pSuccess h β t := logistic_strictMono key

/-- Longer tasks than the r-horizon succeed with probability below r. -/
theorem pSuccess_lt_of_horizonAt_lt {h β r t : ℝ} (hh : 0 < h) (hβ : 0 < β)
    (hr0 : 0 < r) (hr1 : r < 1) (htr : horizonAt h β r < t) :
    pSuccess h β t < r := by
  have hlog : log (horizonAt h β r) < log t := log_lt_log (horizonAt_pos hh hr0 hr1) htr
  have key : (log h - log t) * β < (log h - log (horizonAt h β r)) * β :=
    mul_lt_mul_of_pos_right (by linarith) hβ
  calc pSuccess h β t < pSuccess h β (horizonAt h β r) := logistic_strictMono key
    _ = r := pSuccess_horizonAt hh hβ hr0 hr1

/-- Compounding, product form: with independent per-step failure rate ε, reliability r
holds for n steps exactly up to log r / log(1 − ε) steps. -/
theorem compound_product {ε r : ℝ} (n : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    r ≤ (1 - ε) ^ n ↔ (n : ℝ) ≤ log r / log (1 - ε) := by
  have h1 : 0 < 1 - ε := by linarith
  have hneg : log (1 - ε) < 0 := log_neg h1 (by linarith)
  rw [le_div_iff_of_neg hneg, ← log_pow, log_le_log_iff hr0 (pow_pos h1 n)]

-- STATEMENT UNREVIEWED (written by Fable, session 2, block A4).
-- Source: project sheet, row METR, "compounding, product form:
-- r ≤ (1−ε)^n ↔ n ≤ log r / log(1−ε)"; not in Kwa et al.
/-- Proposed replacement for `compound_product` without its unused hypothesis `r ≤ 1`. -/
theorem compound_product_proposed {ε r : ℝ} (n : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hr0 : 0 < r) :
    r ≤ (1 - ε) ^ n ↔ (n : ℝ) ≤ log r / log (1 - ε) := by
  have h1 : 0 < 1 - ε := by linarith
  have hneg : log (1 - ε) < 0 := log_neg h1 (by linarith)
  rw [le_div_iff_of_neg hneg, ← log_pow, log_le_log_iff hr0 (pow_pos h1 n)]

-- STATEMENT UNREVIEWED (written by Fable, session 2, block A4).
-- Source: as for `compound_product_proposed`; the floor is the form a monitor that counts
-- steps would use (NOTES.md, session 1, "Observations on the drafted statements").
/-- Monitor form of `compound_product`: reliability `r` holds for `n` steps iff `n` is at
most the natural number `⌊log r / log (1 − ε)⌋`. Here `r ≤ 1` IS needed: for `r > 1` the
ratio is negative, its natural floor is `0`, and the right-hand side would hold at `n = 0`
while the left-hand side `r ≤ 1` fails. -/
theorem compound_product_floor_proposed {ε r : ℝ} (n : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    r ≤ (1 - ε) ^ n ↔ n ≤ ⌊log r / log (1 - ε)⌋₊ := by
  have hneg : log (1 - ε) < 0 := log_neg (by linarith) (by linarith)
  have hnonneg : 0 ≤ log r / log (1 - ε) :=
    div_nonneg_of_nonpos (log_nonpos hr0.le hr1) hneg.le
  rw [compound_product n hε0 hε1 hr0 hr1, Nat.le_floor_iff hnonneg]

/-- Compounding, union-bound form (no independence needed): if each of n steps fails with
probability at most ε, some step fails with probability at most n·ε. -/
theorem compound_union {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : ℕ → Set Ω) (ε : ENNReal) (n : ℕ) (hF : ∀ i, μ (F i) ≤ ε) :
    μ (⋃ i ∈ Finset.range n, F i) ≤ n * ε := by
  calc μ (⋃ i ∈ Finset.range n, F i) ≤ ∑ i ∈ Finset.range n, μ (F i) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range n, ε := Finset.sum_le_sum fun i _ => hF i
    _ = n * ε := by simp

-- STATEMENT UNREVIEWED (written by Fable, session 2, block A4).
-- Source: Kwa et al., arXiv 2503.14499, eq. (1), p. 25 (the logistic model); the two facts
-- below are properties of that model for positive task lengths, not statements of the paper.
/-- Proposed guarded fact: for a positive horizon and a positive task length the model's
success probability is strictly between 0 and 1. (True for all real arguments; the
hypotheses record the domain on which `pSuccess` is the paper's model.) -/
theorem pSuccess_mem_Ioo_proposed {h β t : ℝ} (_hh : 0 < h) (_ht : 0 < t) :
    pSuccess h β t ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold pSuccess logistic
  have he : 0 < exp (-((log h - log t) * β)) := exp_pos _
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

-- STATEMENT UNREVIEWED (written by Fable, session 2, block A4). Source: as above.
/-- Proposed guarded fact: for a positive horizon and positive slope, success probability is
strictly decreasing in the task length on `(0, ∞)`. -/
theorem pSuccess_strictAntiOn_proposed {h β : ℝ} (_hh : 0 < h) (hβ : 0 < β) :
    StrictAntiOn (pSuccess h β) (Set.Ioi 0) := by
  intro s hs t _ hst
  have hlog : log s < log t := log_lt_log hs hst
  exact logistic_strictMono (mul_lt_mul_of_pos_right (by linarith) hβ)

end UncontainabilityLean.MetrHorizon
