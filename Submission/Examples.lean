/-
# The worked number behind DHAR-2: 738 tasks at ε = δ = 0.05

Copied unchanged from `UncontainabilityLean/Review/PaperExamples.lean` in the project's working
repository (section `Dhar`). `sample_size_certificate` (`Targets/DharEstimator.lean`) asks for
`n ≥ log (2/δ) / (2 ε²)`; these lemmas show that at ε = δ = 0.05 this means exactly `n ≥ 738`.
-/
import Mathlib

open Real

namespace UncontainabilityLean.Review.PaperExamples


/-- `0.2226 < log (5/4) < 0.2235` (true value 0.22314…), from four terms of the series of
`log (1 − x)` at `x = 1/5`. -/
theorem log_five_fourths_bounds : 0.2226 < log (5 / 4 : ℝ) ∧ log (5 / 4 : ℝ) < 0.2235 := by
  have h := abs_log_sub_add_sum_range_le (x := (1 / 5 : ℝ)) (by norm_num [abs_of_pos]) 4
  have e : log (1 - 1 / 5 : ℝ) = -log (5 / 4) := by
    rw [show (1 - 1 / 5 : ℝ) = (5 / 4)⁻¹ by norm_num, log_inv]
  rw [e] at h
  norm_num [Finset.sum_range_succ, abs_of_pos] at h
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- `3.6883 < log 40 < 3.6893` (true value 3.68888…). -/
theorem log_forty_bounds : 3.6883 < log (40 : ℝ) ∧ log (40 : ℝ) < 3.6893 := by
  have e : log (40 : ℝ) = 5 * log 2 + log (5 / 4) := by
    rw [show (40 : ℝ) = 2 ^ 5 * (5 / 4) by norm_num, log_mul (by norm_num) (by norm_num),
      log_pow]
    norm_num
  have h2l := log_two_gt_d9
  have h2u := log_two_lt_d9
  obtain ⟨hl, hu⟩ := log_five_fourths_bounds
  rw [e]
  constructor <;> linarith

/-- The threshold `ln(2/δ)/(2ε²)` of `sample_size_certificate` at ε = δ = 0.05 lies strictly
between 737 and 738. -/
theorem sample_size_threshold_bounds :
    737 < log (2 / (0.05 : ℝ)) / (2 * (0.05 : ℝ) ^ 2) ∧
      log (2 / (0.05 : ℝ)) / (2 * (0.05 : ℝ) ^ 2) < 738 := by
  obtain ⟨hl, hu⟩ := log_forty_bounds
  rw [show (2 / 0.05 : ℝ) = 40 by norm_num, show (2 * (0.05 : ℝ) ^ 2) = 1 / 200 by norm_num]
  constructor <;> linarith

/-- **At ε = δ = 0.05 the certificate requires exactly n ≥ 738**: a natural number `n`
meets the size condition iff `738 ≤ n`. -/
theorem sample_size_738 (n : ℕ) :
    log (2 / (0.05 : ℝ)) / (2 * (0.05 : ℝ) ^ 2) ≤ n ↔ 738 ≤ n := by
  obtain ⟨hl, hu⟩ := sample_size_threshold_bounds
  constructor
  · intro h
    have : (737 : ℝ) < n := lt_of_lt_of_le hl h
    exact_mod_cast this
  · intro h
    have : (738 : ℝ) ≤ n := by exact_mod_cast h
    linarith

end UncontainabilityLean.Review.PaperExamples
