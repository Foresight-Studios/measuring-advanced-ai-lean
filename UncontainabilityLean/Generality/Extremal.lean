/-
# The generality metric: the extremal theorem  (index ID 125; Tier 2, package B)

Source: Hernández-Orallo et al. 2021, Supplementary Information §E.2 (properties 3 and 5),
§F.1 (Corollary 8, Proposition 11) and §F.5:
`papers/index/files/125_supplementary_information.pdf`. Page numbers are PDF pages.

For a curve `ψ` with values in `[0, 1]`, vanishing beyond difficulty `q`, with capability
`Ψ` and moment `M`:

    0 ≤ 2M − Ψ² ≤ 2Ψ(q − Ψ),

with equality on the left exactly when `ψ` is the step curve at `Ψ`, and on the right
exactly when `ψ` is the reversed step on `[q − Ψ, q]` (both almost everywhere).

WHAT IS THE PAPER'S AND WHAT IS THE PROJECT'S.

  * The two inequalities are the paper's claims: Corollary 8 (PDF p. 36) says the step
    curve gives "the maximum generality" at fixed capability, and Proposition 11 (PDF
    p. 37) says the reversed step gives "the minimum generality" on a bounded interval.
    The supplement's argument for Corollary 8 is an exchange sketch resting on Proposition
    7, and its proof of Proposition 11 only computes the reversed step's value. The proof
    here is a different, direct one: with `σ` the step curve at `Ψ`,
    `2M − Ψ² = 2·∫ (h − Ψ)(ψ − σ) dh` and the integrand is non-negative pointwise; the
    right-hand inequality is the mirror image with the reversed step.
  * The equality cases (uniqueness of the extremal curves, almost everywhere) are NOT
    stated in the paper as results. They are this project's own results. The supplement
    does use one of them without proof: the proof of Proposition 14 (PDF p. 38) says
    "both agents will have step functions" when generality is infinite.

MODELLING CHOICES, in addition to those of `Basic.lean`.

  D9.  "ψ(h) = 0 beyond difficulty q" is `VanishesBeyond q ψ`: `ψ h = 0` for all `h > q`.
  D10. Equality of curves is almost everywhere for Lebesgue measure on `(0, ∞)`; a curve
       can be changed on a null set of difficulties without changing any quantity here.
  D11. The normalised spread of §F.5 is `(S² − S²_cnst)/(S²_max − S²_cnst)` with
       `S²_cnst = Ψ(q − Ψ)` and `S²_max = 2Ψ(q − Ψ)`. The supplement's display names this
       ratio `s²` and then writes `γ = −s` (PDF p. 42). The ratio can be negative and the
       text gives both it and `γ` the range −1 to 1, so `γ` is read as minus the ratio,
       not minus its square root. When `Ψ = 0` or `Ψ = q` the denominator is 0 and Lean's
       value is 0.

Every statement stays `-- STATEMENT UNREVIEWED` until a human reviewer signs off.
-/
import UncontainabilityLean.Generality.Basic

open MeasureTheory Set
open scoped ENNReal

namespace UncontainabilityLean.Generality

/-! ## Auxiliary facts -/

theorem step_of_le {l h : ℝ} (h0 : 0 ≤ h) (hl : h ≤ l) : step l h = 1 := by
  simp [step, box, h0, hl]

theorem step_of_gt {l h : ℝ} (hl : l < h) : step l h = 0 := by
  simp [step, box, not_le.2 hl]

theorem reversedStep_of_mem {q Ψ h : ℝ} (h1 : q - Ψ ≤ h) (h2 : h ≤ q) :
    reversedStep q Ψ h = 1 := by
  simp [reversedStep, box, h1, h2]

theorem reversedStep_of_lt {q Ψ h : ℝ} (h1 : h < q - Ψ) : reversedStep q Ψ h = 0 := by
  simp [reversedStep, box, not_le.2 h1]

theorem reversedStep_of_gt {q Ψ h : ℝ} (h2 : q < h) : reversedStep q Ψ h = 0 := by
  simp [reversedStep, box, not_le.2 h2]

/-- Capability and moment depend on the curve only up to a null set of difficulties. -/
theorem capability_congr_ae {ψ φ : ℝ → ℝ} (h : ψ =ᵐ[volume.restrict (Ioi 0)] φ) :
    capability ψ = capability φ :=
  integral_congr_ae h

theorem effort_congr_ae {ψ φ : ℝ → ℝ} (h : ψ =ᵐ[volume.restrict (Ioi 0)] φ) :
    effort ψ = effort φ :=
  integral_congr_ae (by filter_upwards [h] with x hx; rw [hx])

/-- The integral behind both inequalities. -/
theorem integral_sub_mul_sub {ψ φ : ℝ → ℝ} (hψ : IsCurve ψ) (hφ : IsCurve φ) (c : ℝ) :
    IntegrableOn (fun h => (h - c) * (ψ h - φ h)) (Ioi 0) ∧
      ∫ h in Ioi (0 : ℝ), (h - c) * (ψ h - φ h)
        = effort ψ - effort φ - c * (capability ψ - capability φ) := by
  have h1 := hψ.integrable_mul.sub hφ.integrable_mul
  have h2 := (hψ.integrable.sub hφ.integrable).const_mul c
  have e : (fun h => (h - c) * (ψ h - φ h))
      = ((fun h => h * ψ h) - fun h => h * φ h) - fun h => c * (ψ - φ) h := by
    ext h; simp only [Pi.sub_apply]; ring
  refine ⟨by rw [e]; exact h1.sub h2, ?_⟩
  rw [e, integral_sub' h1 h2, integral_sub' hψ.integrable_mul hφ.integrable_mul,
    integral_const_mul, integral_sub' hψ.integrable hφ.integrable]
  rfl

theorem ae_restrict_ne (c : ℝ) : ∀ᵐ h ∂(volume.restrict (Ioi (0 : ℝ))), h ≠ c :=
  ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton c))

/-! ## Capability lies between 0 and q -/

-- STATEMENT UNREVIEWED
/-- The capability of a curve is non-negative. Source: implicit in SI §E.1, PDF p. 33. -/
theorem capability_nonneg {ψ : ℝ → ℝ} (hψ : IsCurve ψ) : 0 ≤ capability ψ :=
  setIntegral_nonneg measurableSet_Ioi fun h hh => hψ.nonneg h (le_of_lt hh)

-- STATEMENT UNREVIEWED
/-- The curve is zero beyond difficulty `q`. Source: SI Proposition 11, PDF p. 37
("assuming ψ(h) = 0 beyond difficulty q"). -/
def VanishesBeyond (q : ℝ) (ψ : ℝ → ℝ) : Prop := ∀ h, q < h → ψ h = 0

theorem VanishesBeyond.mono {q q' : ℝ} {ψ : ℝ → ℝ} (hv : VanishesBeyond q ψ) (h : q ≤ q') :
    VanishesBeyond q' ψ := fun x hx => hv x (lt_of_le_of_lt h hx)

theorem vanishesBeyond_box (c a q : ℝ) : VanishesBeyond q (box c a q) := fun h hh => by
  simp [box, not_le.2 hh]

theorem vanishesBeyond_step (l : ℝ) : VanishesBeyond l (step l) := vanishesBeyond_box 1 0 l

theorem vanishesBeyond_constCurve (c q : ℝ) : VanishesBeyond q (constCurve c q) :=
  vanishesBeyond_box c 0 q

theorem vanishesBeyond_reversedStep (q Ψ : ℝ) : VanishesBeyond q (reversedStep q Ψ) :=
  vanishesBeyond_box 1 (q - Ψ) q

-- STATEMENT UNREVIEWED
/-- A curve that vanishes beyond `q` has capability at most `q`. Source: implicit in SI
Proposition 11, PDF p. 37 (the reversed step starts at `q − Ψ ≥ 0`). -/
theorem capability_le {ψ : ℝ → ℝ} {q : ℝ} (hψ : IsCurve ψ) (hq : 0 ≤ q)
    (hv : VanishesBeyond q ψ) : capability ψ ≤ q := by
  have h := setIntegral_mono_on hψ.integrable (isCurve_step q).integrable measurableSet_Ioi
    (fun h hh => by
      rcases le_or_gt h q with hle | hgt
      · rw [step_of_le (le_of_lt hh) hle]; exact hψ.le_one h (le_of_lt hh)
      · rw [step_of_gt hgt, hv h hgt])
  have e : ∫ h in Ioi (0 : ℝ), step q h = q := capability_step hq
  rw [e] at h
  exact h

/-! ## The left inequality: spread is defined, and is zero only for a step curve -/

-- STATEMENT UNREVIEWED
/-- **The quantity under the square root is never negative**: `0 ≤ 2M − Ψ²` for every
curve. Source: this is the inequality behind SI Corollary 8, PDF p. 36 ("given a fixed
capability Ψ, the minimum expected difficulty H and the maximum generality Γ are obtained
with a step agent characteristic function on h = Ψ"): the step curve has `2M − Ψ² = 0`
(`spreadSq_step`), and no curve has less. The supplement's exchange argument is replaced
by a direct proof. -/
theorem spreadSq_nonneg {ψ : ℝ → ℝ} (hψ : IsCurve ψ) : 0 ≤ spreadSq ψ := by
  have hΨ := capability_nonneg hψ
  have key := (integral_sub_mul_sub hψ (isCurve_step (capability ψ)) (capability ψ)).2
  rw [capability_step hΨ, effort_step hΨ] at key
  have hpos : 0 ≤ ∫ h in Ioi (0 : ℝ), (h - capability ψ) * (ψ h - step (capability ψ) h) :=
    setIntegral_nonneg measurableSet_Ioi fun h hh => by
      rcases le_or_gt h (capability ψ) with hle | hgt
      · rw [step_of_le (le_of_lt hh) hle]
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hle)
          (sub_nonpos.2 (hψ.le_one h (le_of_lt hh)))
      · rw [step_of_gt hgt, sub_zero]
        exact mul_nonneg (sub_nonneg.2 hgt.le) (hψ.nonneg h (le_of_lt hh))
  unfold spreadSq
  nlinarith [key, hpos]

-- STATEMENT UNREVIEWED
/-- **Project's own result (not stated in the paper):** `2M − Ψ² = 0` exactly when the
curve is the step curve at its own capability, up to a null set of difficulties. The
supplement uses the forward direction without proof in Proposition 14, PDF p. 38 ("both
agents will have step functions"). -/
theorem spreadSq_eq_zero_iff {ψ : ℝ → ℝ} (hψ : IsCurve ψ) :
    spreadSq ψ = 0 ↔ ψ =ᵐ[volume.restrict (Ioi 0)] step (capability ψ) := by
  have hΨ := capability_nonneg hψ
  obtain ⟨hint, key⟩ := integral_sub_mul_sub hψ (isCurve_step (capability ψ)) (capability ψ)
  rw [capability_step hΨ, effort_step hΨ] at key
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun h => (h - capability ψ) * (ψ h - step (capability ψ) h) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    rcases le_or_gt h (capability ψ) with hle | hgt
    · rw [step_of_le (le_of_lt hh) hle]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hle)
        (sub_nonpos.2 (hψ.le_one h (le_of_lt hh)))
    · rw [step_of_gt hgt, sub_zero]
      exact mul_nonneg (sub_nonneg.2 hgt.le) (hψ.nonneg h (le_of_lt hh))
  constructor
  · intro h0
    have hz : ∫ h in Ioi (0 : ℝ), (h - capability ψ) * (ψ h - step (capability ψ) h) = 0 := by
      unfold spreadSq at h0; rw [key]; linarith
    have := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hint).1 hz
    filter_upwards [this, ae_restrict_ne (capability ψ)] with h hh hne
    have := (mul_eq_zero.1 hh).resolve_left (sub_ne_zero.2 hne)
    linarith
  · intro hae
    unfold spreadSq
    rw [effort_congr_ae hae, effort_step hΨ]
    ring

/-! ## The right inequality: the reversed step has the largest spread on `[0, q]` -/

-- STATEMENT UNREVIEWED
/-- **`2M − Ψ² ≤ 2Ψ(q − Ψ)`** for every curve that vanishes beyond `q`. Source: this is
the inequality behind SI Proposition 11, PDF p. 37 ("the maximum expected difficulty H and
the minimum generality Γ … are obtained with an increasing step agent characteristic
function on h = q − Ψ (until q), leading to S = √(2Ψ(q − Ψ))"). The supplement's proof
computes the value for the reversed step and does not argue that it is the maximum; this
proof supplies that. -/
theorem spreadSq_le {ψ : ℝ → ℝ} {q : ℝ} (hψ : IsCurve ψ) (hq : 0 ≤ q)
    (hv : VanishesBeyond q ψ) :
    spreadSq ψ ≤ 2 * capability ψ * (q - capability ψ) := by
  have hΨ := capability_nonneg hψ
  have hΨq := capability_le hψ hq hv
  have key := (integral_sub_mul_sub hψ (isCurve_reversedStep q (capability ψ))
    (q - capability ψ)).2
  rw [capability_reversedStep hΨ hΨq, effort_reversedStep hΨ hΨq] at key
  have hneg : ∫ h in Ioi (0 : ℝ),
      (h - (q - capability ψ)) * (ψ h - reversedStep q (capability ψ) h) ≤ 0 :=
    setIntegral_nonpos measurableSet_Ioi fun h hh => by
      rcases lt_or_ge h (q - capability ψ) with hlt | hge
      · rw [reversedStep_of_lt hlt, sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hlt.le) (hψ.nonneg h (le_of_lt hh))
      · rcases le_or_gt h q with hle | hgt
        · rw [reversedStep_of_mem hge hle]
          exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hge)
            (sub_nonpos.2 (hψ.le_one h (le_of_lt hh)))
        · rw [reversedStep_of_gt hgt, hv h hgt]; simp
  unfold spreadSq
  nlinarith [key, hneg]

-- STATEMENT UNREVIEWED
/-- **Project's own result (not stated in the paper):** a curve vanishing beyond `q`
attains `2M − Ψ² = 2Ψ(q − Ψ)` exactly when it is the reversed step on `[q − Ψ, q]`, up to
a null set of difficulties. -/
theorem spreadSq_eq_max_iff {ψ : ℝ → ℝ} {q : ℝ} (hψ : IsCurve ψ) (hq : 0 ≤ q)
    (hv : VanishesBeyond q ψ) :
    spreadSq ψ = 2 * capability ψ * (q - capability ψ)
      ↔ ψ =ᵐ[volume.restrict (Ioi 0)] reversedStep q (capability ψ) := by
  have hΨ := capability_nonneg hψ
  have hΨq := capability_le hψ hq hv
  obtain ⟨hint, key⟩ := integral_sub_mul_sub hψ (isCurve_reversedStep q (capability ψ))
    (q - capability ψ)
  rw [capability_reversedStep hΨ hΨq, effort_reversedStep hΨ hΨq] at key
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun h => -((h - (q - capability ψ)) * (ψ h - reversedStep q (capability ψ) h)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    rw [Pi.zero_apply, neg_nonneg]
    rcases lt_or_ge h (q - capability ψ) with hlt | hge
    · rw [reversedStep_of_lt hlt, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hlt.le) (hψ.nonneg h (le_of_lt hh))
    · rcases le_or_gt h q with hle | hgt
      · rw [reversedStep_of_mem hge hle]
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hge)
          (sub_nonpos.2 (hψ.le_one h (le_of_lt hh)))
      · rw [reversedStep_of_gt hgt, hv h hgt]; simp
  constructor
  · intro h0
    have hz : ∫ h in Ioi (0 : ℝ),
        -((h - (q - capability ψ)) * (ψ h - reversedStep q (capability ψ) h)) = 0 := by
      unfold spreadSq at h0; rw [integral_neg, key]; nlinarith
    have := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hint.neg).1 hz
    filter_upwards [this, ae_restrict_ne (q - capability ψ)] with h hh hne
    have := (mul_eq_zero.1 (neg_eq_zero.1 hh)).resolve_left (sub_ne_zero.2 hne)
    linarith
  · intro hae
    unfold spreadSq
    rw [effort_congr_ae hae, effort_reversedStep hΨ hΨq]
    ring

-- STATEMENT UNREVIEWED
/-- **The extremal theorem** (the band of SI §F.5, PDF pp. 41–42: "squared spreads in a
band that goes from 0 to twice the value Ψ(q − Ψ)"): for every curve vanishing beyond `q`,
`0 ≤ 2M − Ψ² ≤ 2Ψ(q − Ψ)`. Completes SI Corollary 8 (PDF p. 36) and the extremal half of
SI Proposition 11 (PDF p. 37). -/
theorem extremal {ψ : ℝ → ℝ} {q : ℝ} (hψ : IsCurve ψ) (hq : 0 ≤ q) (hv : VanishesBeyond q ψ) :
    0 ≤ spreadSq ψ ∧ spreadSq ψ ≤ 2 * capability ψ * (q - capability ψ) :=
  ⟨spreadSq_nonneg hψ, spreadSq_le hψ hq hv⟩

/-! ## Consequences for spread, generality and expected difficulty -/

-- STATEMENT UNREVIEWED
/-- **Spread is always defined**: for every curve, `S² = 2M − Ψ²` (the square root is of a
non-negative number). Source: SI Eq. 9, PDF p. 33, which takes the square root without
comment. -/
theorem spread_sq {ψ : ℝ → ℝ} (hψ : IsCurve ψ) : spread ψ ^ 2 = spreadSq ψ :=
  Real.sq_sqrt (spreadSq_nonneg hψ)

-- STATEMENT UNREVIEWED
/-- **Project's own result (not stated in the paper):** spread is 0 only for a step curve
(almost everywhere). -/
theorem spread_eq_zero_iff {ψ : ℝ → ℝ} (hψ : IsCurve ψ) :
    spread ψ = 0 ↔ ψ =ᵐ[volume.restrict (Ioi 0)] step (capability ψ) := by
  unfold spread
  rw [Real.sqrt_eq_zero (spreadSq_nonneg hψ), spreadSq_eq_zero_iff hψ]

-- STATEMENT UNREVIEWED
/-- **Project's own result (not stated in the paper; used in the proof of SI Proposition
14, PDF p. 38):** generality is infinite exactly for a step curve (almost everywhere). -/
theorem generality_eq_top_iff_step {ψ : ℝ → ℝ} (hψ : IsCurve ψ) :
    generality ψ = ⊤ ↔ ψ =ᵐ[volume.restrict (Ioi 0)] step (capability ψ) := by
  rw [generality_eq_top_iff, spread_eq_zero_iff hψ]

-- STATEMENT UNREVIEWED
/-- **SI Corollary 8** (PDF p. 36), generality: at fixed capability the step curve has the
largest generality. (Its generality is `⊤`, so in this form the statement is immediate;
the content is in `spreadSq_nonneg` and `generality_eq_top_iff_step`.) -/
theorem generality_le_step {ψ : ℝ → ℝ} (hψ : IsCurve ψ) :
    generality ψ ≤ generality (step (capability ψ)) := by
  rw [generality_step (capability_nonneg hψ)]; exact le_top

-- STATEMENT UNREVIEWED
/-- **SI Corollary 8** (PDF p. 36), expected difficulty: at fixed capability `Ψ > 0` the
expected difficulty is at least `Ψ/2`, the step curve's value ("the minimum expected
difficulty H"). -/
theorem half_capability_le_expectedDifficulty {ψ : ℝ → ℝ} (hψ : IsCurve ψ)
    (hpos : 0 < capability ψ) :
    expectedDifficulty (step (capability ψ)) = capability ψ / 2 ∧
      capability ψ / 2 ≤ expectedDifficulty ψ := by
  constructor
  · have := capability_step_eq_two_mul_expectedDifficulty hpos.le
    rw [capability_step hpos.le] at this
    linarith
  · have h := spreadSq_nonneg hψ
    unfold spreadSq at h
    unfold expectedDifficulty
    rw [le_div_iff₀ hpos]
    nlinarith

-- STATEMENT UNREVIEWED
/-- **SI Proposition 11**, extremal half (PDF p. 37), spread: a curve vanishing beyond `q`
has spread at most `√(2Ψ(q − Ψ))`, the reversed step's value. -/
theorem spread_le {ψ : ℝ → ℝ} {q : ℝ} (hψ : IsCurve ψ) (hq : 0 ≤ q)
    (hv : VanishesBeyond q ψ) :
    spread ψ ≤ spread (reversedStep q (capability ψ)) := by
  rw [spread_reversedStep (capability_nonneg hψ) (capability_le hψ hq hv)]
  exact Real.sqrt_le_sqrt (spreadSq_le hψ hq hv)

-- STATEMENT UNREVIEWED
/-- **SI Proposition 11**, extremal half (PDF p. 37), generality: among curves of the same
capability vanishing beyond `q`, the reversed step has "the minimum generality". -/
theorem generality_reversedStep_le {ψ : ℝ → ℝ} {q : ℝ} (hψ : IsCurve ψ) (hq : 0 ≤ q)
    (hv : VanishesBeyond q ψ) :
    generality (reversedStep q (capability ψ)) ≤ generality ψ := by
  unfold generality
  exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal (spread_le hψ hq hv))

-- STATEMENT UNREVIEWED
/-- **SI Proposition 11**, extremal half (PDF p. 37), expected difficulty: for a curve of
capability `Ψ > 0` vanishing beyond `q`, the expected difficulty is at most `q − Ψ/2`, the
reversed step's value ("the maximum expected difficulty H"). -/
theorem expectedDifficulty_le {ψ : ℝ → ℝ} {q : ℝ} (hψ : IsCurve ψ) (hq : 0 ≤ q)
    (hv : VanishesBeyond q ψ) (hpos : 0 < capability ψ) :
    expectedDifficulty (reversedStep q (capability ψ)) = q - capability ψ / 2 ∧
      expectedDifficulty ψ ≤ q - capability ψ / 2 := by
  have hΨq := capability_le hψ hq hv
  constructor
  · unfold expectedDifficulty
    rw [capability_reversedStep hpos.le hΨq, effort_reversedStep hpos.le hΨq]
    field_simp
    ring
  · have h := spreadSq_le hψ hq hv
    unfold spreadSq at h
    unfold expectedDifficulty
    rw [div_le_iff₀ hpos]
    nlinarith

/-! ## Normalised generality (SI §F.5, PDF pp. 41–42) -/

-- STATEMENT UNREVIEWED
/-- The Interval Relative Squared Spread ("normalised spread") on `[0, q]`:
`(S² − S²_cnst)/(S²_max − S²_cnst)` with `S²_cnst = Ψ(q − Ψ)` and `S²_max = 2Ψ(q − Ψ)`.
Source: SI §F.5, PDF p. 42 (the display "s² = (S² − S²_cnst)/(S²_max − S²_cnst)"). -/
noncomputable def normalisedSpread (q : ℝ) (ψ : ℝ → ℝ) : ℝ :=
  (spreadSq ψ - capability ψ * (q - capability ψ))
    / (2 * capability ψ * (q - capability ψ) - capability ψ * (q - capability ψ))

-- STATEMENT UNREVIEWED
/-- Normalised generality: the negative of the normalised spread. Source: SI §F.5, PDF
p. 42 ("we use the term normalised generality as the negative value of normalised spread,
i.e., γ = −s"; the display defines the ratio under the name `s²`, see modelling choice D11). -/
noncomputable def normalisedGenerality (q : ℝ) (ψ : ℝ → ℝ) : ℝ := -normalisedSpread q ψ

-- STATEMENT UNREVIEWED
/-- **SI §F.5** (PDF p. 42): the normalised spread "goes from −1 (minimum spread, maximum
generality) to 1 (maximum spread, minimum generality)". -/
theorem normalisedSpread_mem_Icc {ψ : ℝ → ℝ} {q : ℝ} (hψ : IsCurve ψ) (hq : 0 ≤ q)
    (hv : VanishesBeyond q ψ) : normalisedSpread q ψ ∈ Icc (-1 : ℝ) 1 := by
  have h0 := spreadSq_nonneg hψ
  have h1 := spreadSq_le hψ hq hv
  have hd : 0 ≤ capability ψ * (q - capability ψ) :=
    mul_nonneg (capability_nonneg hψ) (sub_nonneg.2 (capability_le hψ hq hv))
  unfold normalisedSpread
  rcases eq_or_lt_of_le hd with hz | hpos
  · rw [show 2 * capability ψ * (q - capability ψ) - capability ψ * (q - capability ψ) = 0 by
      linarith, div_zero]
    constructor <;> norm_num
  · have hden : 0 < 2 * capability ψ * (q - capability ψ) - capability ψ * (q - capability ψ) := by
      linarith
    constructor
    · rw [le_div_iff₀ hden]; linarith
    · rw [div_le_one hden]; linarith

-- STATEMENT UNREVIEWED
/-- **SI §F.5** (PDF p. 42): normalised generality lies between −1 "(minimum generality)"
and +1 "(maximum generality)". -/
theorem normalisedGenerality_mem_Icc {ψ : ℝ → ℝ} {q : ℝ} (hψ : IsCurve ψ) (hq : 0 ≤ q)
    (hv : VanishesBeyond q ψ) : normalisedGenerality q ψ ∈ Icc (-1 : ℝ) 1 := by
  have := normalisedSpread_mem_Icc hψ hq hv
  unfold normalisedGenerality
  exact ⟨by linarith [this.2], by linarith [this.1]⟩

-- STATEMENT UNREVIEWED
/-- **SI §F.5** (PDF p. 42): the step curve has normalised generality `+1`, the constant
curve `0`, and the reversed step `−1`, for `0 < Ψ < q`. -/
theorem normalisedGenerality_values {q Ψ : ℝ} (h0 : 0 < Ψ) (hq : Ψ < q) :
    normalisedGenerality q (step Ψ) = 1 ∧
      normalisedGenerality q (constCurve (Ψ / q) q) = 0 ∧
      normalisedGenerality q (reversedStep q Ψ) = -1 := by
  have hqpos : 0 < q := h0.trans hq
  have hd : Ψ * (q - Ψ) ≠ 0 := (mul_pos h0 (sub_pos.2 hq)).ne'
  have hc : capability (constCurve (Ψ / q) q) = Ψ := by
    rw [capability_constCurve _ hqpos.le]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · unfold normalisedGenerality normalisedSpread
    rw [spreadSq_step h0.le, capability_step h0.le]
    field_simp; ring
  · unfold normalisedGenerality normalisedSpread
    rw [spreadSq_constCurve_of_capability hqpos, hc]
    simp
  · unfold normalisedGenerality normalisedSpread
    rw [spreadSq_reversedStep h0.le hq.le, capability_reversedStep h0.le hq.le]
    field_simp

-- STATEMENT UNREVIEWED
/-- Normalised generality in closed form: `γ = 1 − S²/(Ψ(q − Ψ))` when `Ψ(q − Ψ) ≠ 0`.
Source: SI §F.5, PDF p. 42, by substituting `S²_cnst = Ψ(q − Ψ)`, `S²_max = 2Ψ(q − Ψ)`. -/
theorem normalisedGenerality_eq {ψ : ℝ → ℝ} {q : ℝ}
    (hd : capability ψ * (q - capability ψ) ≠ 0) :
    normalisedGenerality q ψ = 1 - spreadSq ψ / (capability ψ * (q - capability ψ)) := by
  unfold normalisedGenerality normalisedSpread
  rw [show 2 * capability ψ * (q - capability ψ) - capability ψ * (q - capability ψ)
    = capability ψ * (q - capability ψ) by ring, sub_div, div_self hd]
  ring

-- STATEMENT UNREVIEWED
/-- **SI §F.5** (PDF p. 42): "normalised generality depends on the width of the interval
(q). For the same agent, with a wider range of difficulties, the normalised generality
would be more positive". -/
theorem normalisedGenerality_mono {ψ : ℝ → ℝ} {q q' : ℝ} (hψ : IsCurve ψ)
    (hpos : 0 < capability ψ) (hq : capability ψ < q) (hqq : q ≤ q') :
    normalisedGenerality q ψ ≤ normalisedGenerality q' ψ := by
  have d1 : 0 < capability ψ * (q - capability ψ) := mul_pos hpos (sub_pos.2 hq)
  have d2 : capability ψ * (q - capability ψ) ≤ capability ψ * (q' - capability ψ) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  rw [normalisedGenerality_eq d1.ne', normalisedGenerality_eq (d1.trans_le d2).ne']
  have := div_le_div_of_nonneg_left (spreadSq_nonneg hψ) d1 d2
  linarith

end UncontainabilityLean.Generality
