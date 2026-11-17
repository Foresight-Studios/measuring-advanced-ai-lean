/-
# The generality metric: definitions and identities  (index ID 125; Tier 1, package A)

Source: J. Hernández-Orallo, B. S. Loe, L. Cheke, F. Martínez-Plumed, S. Ó hÉigeartaigh,
*General intelligence disentangled via a generality metric for natural and artificial
intelligence*, Scientific Reports 11, 22822 (2021), Supplementary Information §E and §F:
`papers/index/files/125_supplementary_information.pdf`. Page numbers below are pages of
that PDF file (the document's own page number is the PDF page plus 17).

What a Lean proof shows here: for the generality metric as defined by Hernández-Orallo et
al., the identities of SI Propositions 4, 5, 6, 9, 10, 11 (value only), 12, 15 and Lemma 19
hold. Nothing in this file shows that the metric orders real AI systems, or that a position
on it relates to harm.

MODELLING CHOICES (each is a review item; see also the blueprint chapter, "Deviations from
the source").

  D1. A curve is a function `ψ : ℝ → ℝ`. Only its values at difficulties `h ≥ 0` matter:
      every integral is over `(0, ∞)` (Lebesgue measure; the point 0 has measure zero).
  D2. The source leaves measurability and integrability informal ("we want agent
      characteristic curves to ensure that the area under these curves is finite", PDF
      p. 33). `IsCurve ψ` collects: `0 ≤ ψ h ≤ 1` for `h ≥ 0`, and `ψ` and `h ↦ h·ψ h` are
      integrable on `(0, ∞)`. The integrals are Bochner integrals, which are 0 for a
      non-integrable function, so results about an arbitrary curve assume `IsCurve`.
  D3. Spread is defined as `√(2M − Ψ²)`, the form the supplement's proofs use. The
      supplement's Eq. 9 writes `√((2H − Ψ)·Ψ)` with `H = M/Ψ`; the two agree when
      `Ψ ≠ 0` (`spread_eq_sqrt_expectedDifficulty`). In Lean `M/0 = 0`.
  D4. Generality is `1/S` with "Γ = ∞" when `S = 0`. It is modelled in `ℝ≥0∞` as
      `(ENNReal.ofReal S)⁻¹`, so that `generality ψ = ⊤ ↔ spread ψ = 0`.
  D5. "s-saturated" is `ψ h = 1` for all `0 ≤ h ≤ s` (the source writes `∀ h ≤ s`, with
      difficulty ranging over `h ≥ 0`).
  D6. The named curves are indicator functions of closed intervals times a constant
      (`box c a b`). The source does not say what a step curve is at its jump; the choice
      changes no integral.
  D7. Translation by `k ≥ 0` is `h ↦ if h < k then 1 else ψ (h − k)`; the negative
      translation by `k` is `h ↦ ψ (h + k)`, applied to a `k`-saturated curve.
  D8. Proposition 15 ("same units") is a dimensional argument. It is stated as homogeneity
      under rescaling difficulty by `lam > 0`: `rescale lam ψ = fun h ↦ ψ (h / lam)`.

Every statement stays `-- STATEMENT UNREVIEWED` until a human reviewer signs off.
-/
import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace UncontainabilityLean.Generality

/-! ## Definitions (SI §E.1, PDF p. 33) -/

-- STATEMENT UNREVIEWED
/-- Capability `Ψ = ∫₀^∞ ψ(h) dh`. Source: SI Eq. 7, PDF p. 33. -/
noncomputable def capability (ψ : ℝ → ℝ) : ℝ := ∫ h in Ioi (0 : ℝ), ψ h

-- STATEMENT UNREVIEWED
/-- The moment `M = ∫₀^∞ h·ψ(h) dh`, which the supplement calls "effort". Source: SI §E.1,
PDF p. 33 (Eq. 8), and the proof of Proposition 6, PDF p. 36. -/
noncomputable def effort (ψ : ℝ → ℝ) : ℝ := ∫ h in Ioi (0 : ℝ), h * ψ h

-- STATEMENT UNREVIEWED
/-- Expected difficulty `H = M/Ψ`. Source: SI Eq. 8, PDF p. 33. (In Lean `M/0 = 0`.) -/
noncomputable def expectedDifficulty (ψ : ℝ → ℝ) : ℝ := effort ψ / capability ψ

-- STATEMENT UNREVIEWED
/-- Squared spread `S² = 2M − Ψ²`. Source: the form of SI Eq. 9 used in the proof of
Proposition 6, PDF p. 36. -/
noncomputable def spreadSq (ψ : ℝ → ℝ) : ℝ := 2 * effort ψ - capability ψ ^ 2

-- STATEMENT UNREVIEWED
/-- Spread `S = √(2M − Ψ²)`. Source: SI Eq. 9, PDF p. 33, in the form used in the proof of
Proposition 6, PDF p. 36. See modelling choice D3. -/
noncomputable def spread (ψ : ℝ → ℝ) : ℝ := Real.sqrt (spreadSq ψ)

-- STATEMENT UNREVIEWED
/-- Generality `Γ = 1/S`, with value `⊤` ("Γ = ∞") when `S = 0`. Source: SI §E.2, property
3, PDF p. 35, and the main article. See modelling choice D4. -/
noncomputable def generality (ψ : ℝ → ℝ) : ℝ≥0∞ := (ENNReal.ofReal (spread ψ))⁻¹

-- STATEMENT UNREVIEWED
/-- A curve is `s`-saturated if `ψ h = 1` for every difficulty `0 ≤ h ≤ s`. Source: SI
§E.1, PDF p. 33 ("∀h ≤ s : ψ(h) = 1"). -/
def Saturated (s : ℝ) (ψ : ℝ → ℝ) : Prop := ∀ h, 0 ≤ h → h ≤ s → ψ h = 1

-- STATEMENT UNREVIEWED
/-- An agent characteristic curve: values in `[0, 1]` at every difficulty `h ≥ 0`, with
finite area and finite moment. Source: SI §E.1, PDF p. 33; the integrability conditions are
this project's reading of "the area under these curves is finite" (modelling choice D2). -/
structure IsCurve (ψ : ℝ → ℝ) : Prop where
  nonneg : ∀ h, 0 ≤ h → 0 ≤ ψ h
  le_one : ∀ h, 0 ≤ h → ψ h ≤ 1
  integrable : IntegrableOn ψ (Ioi 0)
  integrable_mul : IntegrableOn (fun h => h * ψ h) (Ioi 0)

/-! ## Basic facts -/

theorem capability_congr {ψ φ : ℝ → ℝ} (h : ∀ x, 0 < x → ψ x = φ x) :
    capability ψ = capability φ :=
  setIntegral_congr_fun measurableSet_Ioi fun x hx => h x hx

theorem effort_congr {ψ φ : ℝ → ℝ} (h : ∀ x, 0 < x → ψ x = φ x) : effort ψ = effort φ :=
  setIntegral_congr_fun measurableSet_Ioi fun x hx => by simp only [h x hx]

theorem spreadSq_congr {ψ φ : ℝ → ℝ} (h : ∀ x, 0 < x → ψ x = φ x) :
    spreadSq ψ = spreadSq φ := by
  unfold spreadSq; rw [capability_congr h, effort_congr h]

theorem spread_nonneg (ψ : ℝ → ℝ) : 0 ≤ spread ψ := Real.sqrt_nonneg _

-- STATEMENT UNREVIEWED
/-- Generality is infinite exactly when spread is zero. Source: SI §E.2, property 3, PDF
p. 35 ("spread S = 0 and generality Γ = ∞"); modelling choice D4. -/
theorem generality_eq_top_iff (ψ : ℝ → ℝ) : generality ψ = ⊤ ↔ spread ψ = 0 := by
  unfold generality
  rw [ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero]
  exact ⟨fun h => le_antisymm h (spread_nonneg ψ), fun h => h.le⟩

-- STATEMENT UNREVIEWED
/-- The supplement's own form of the spread, `S = √((2H − Ψ)·Ψ)`, agrees with
`√(2M − Ψ²)` whenever capability is non-zero. Source: SI Eq. 9, PDF p. 33. -/
theorem spread_eq_sqrt_expectedDifficulty (ψ : ℝ → ℝ) (hΨ : capability ψ ≠ 0) :
    spread ψ = Real.sqrt ((2 * expectedDifficulty ψ - capability ψ) * capability ψ) := by
  unfold spread spreadSq expectedDifficulty
  congr 1
  field_simp

/-! ## Integrals of shifted and piecewise functions (auxiliary) -/

theorem setIntegral_Ioi_shift (g : ℝ → ℝ) (k : ℝ) :
    ∫ h in Ioi k, g (h - k) = ∫ h in Ioi (0 : ℝ), g h := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_sub_right_eq_self (fun h => (Ioi (0 : ℝ)).indicator g h) k]
  congr 1
  ext h
  simp only [indicator, mem_Ioi, sub_pos]

theorem integrableOn_Ioi_shift' {g : ℝ → ℝ} (a k : ℝ) (hg : IntegrableOn g (Ioi a)) :
    IntegrableOn (fun h => g (h - k)) (Ioi (a + k)) := by
  rw [← integrable_indicator_iff measurableSet_Ioi] at hg ⊢
  refine (hg.comp_sub_right k).congr (Filter.Eventually.of_forall fun h => ?_)
  simp only [indicator, mem_Ioi, lt_sub_iff_add_lt]

theorem integrableOn_Ioi_shift {g : ℝ → ℝ} (k : ℝ) (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun h => g (h - k)) (Ioi k) := by
  simpa using integrableOn_Ioi_shift' 0 k hg

/-- A function equal to `F` below `k` and to a shifted copy of `G` from `k` on. -/
theorem piecewise_Ioi {F G : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k)
    (hF : IntervalIntegrable F volume 0 k) (hG : IntegrableOn G (Ioi 0)) :
    IntegrableOn (fun h => if h < k then F h else G (h - k)) (Ioi 0) ∧
      ∫ h in Ioi (0 : ℝ), (if h < k then F h else G (h - k))
        = (∫ h in (0 : ℝ)..k, F h) + ∫ h in Ioi (0 : ℝ), G h := by
  set f : ℝ → ℝ := fun h => if h < k then F h else G (h - k) with hf
  have e1 : EqOn f F (Ioo 0 k) := fun h hh => by simp [hf, hh.2]
  have e2 : EqOn f (fun h => G (h - k)) (Ioi k) := fun h hh => by
    simp [hf, not_lt.2 (le_of_lt (mem_Ioi.1 hh))]
  have hFo : IntegrableOn F (Ioo 0 k) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hk).1 hF).mono_set Ioo_subset_Ioc_self
  have h1 : IntegrableOn f (Ioc 0 k) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hFo.congr_fun e1.symm measurableSet_Ioo
  have h2 : IntegrableOn f (Ioi k) :=
    (integrableOn_Ioi_shift k hG).congr_fun e2.symm measurableSet_Ioi
  refine ⟨by rw [← Ioc_union_Ioi_eq_Ioi hk]; exact h1.union h2, ?_⟩
  conv_lhs => rw [← Ioc_union_Ioi_eq_Ioi hk]
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2,
    integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo e1,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hk,
    setIntegral_congr_fun measurableSet_Ioi e2, setIntegral_Ioi_shift]

/-! ## Translation (SI Propositions 4, 5, 6; PDF pp. 35–36) -/

-- STATEMENT UNREVIEWED
/-- Positive translation by `k`: the curve is shifted right by `k` and the new part is
saturated. Source: SI §E.2, PDF p. 33 ("If k is positive we have a translation to the
right, and we assume that ψ(h) = 1 for all h < k"). -/
noncomputable def translate (k : ℝ) (ψ : ℝ → ℝ) : ℝ → ℝ := fun h => if h < k then 1 else ψ (h - k)

-- STATEMENT UNREVIEWED
/-- Negative translation by `k`: the curve is shifted left by `k`, and what falls below
difficulty 0 is cut. Source: SI §E.2, PDF p. 33 ("If k is negative we have a translation
to the left, where every result with h < 0 is cut out"). -/
def translateLeft (k : ℝ) (ψ : ℝ → ℝ) : ℝ → ℝ := fun h => ψ (h + k)

theorem isCurve_translate {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ) :
    IsCurve (translate k ψ) := by
  refine ⟨fun h _ => ?_, fun h _ => ?_, ?_, ?_⟩
  · unfold translate; split_ifs with hh
    · exact zero_le_one
    · exact hψ.nonneg _ (sub_nonneg.2 (not_lt.1 hh))
  · unfold translate; split_ifs with hh
    · exact le_rfl
    · exact hψ.le_one _ (sub_nonneg.2 (not_lt.1 hh))
  · exact (piecewise_Ioi (F := fun _ => 1) hk intervalIntegrable_const hψ.integrable).1
  · have hG : IntegrableOn (fun u => (u + k) * ψ u) (Ioi 0) := by
      have := hψ.integrable_mul.add (hψ.integrable.const_mul k)
      refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
      simp only [Pi.add_apply]; ring
    have := (piecewise_Ioi (F := fun h => h) hk intervalIntegral.intervalIntegrable_id hG).1
    refine this.congr_fun (fun h _ => ?_) measurableSet_Ioi
    by_cases hlt : h < k <;> simp [translate, hlt]

-- STATEMENT UNREVIEWED
/-- **SI Proposition 4** (PDF p. 35): "Given an agent with capability Ψ, any positive
translation by k implies that capability becomes Ψ + k." -/
theorem capability_translate {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ) :
    capability (translate k ψ) = capability ψ + k := by
  unfold capability translate
  rw [(piecewise_Ioi (F := fun _ => 1) hk intervalIntegrable_const hψ.integrable).2]
  simp [add_comm]

-- STATEMENT UNREVIEWED
/-- The moment after a positive translation: `M′ = k²/2 + M + k·Ψ`. Source: the proof of
SI Proposition 6, PDF p. 36. -/
theorem effort_translate {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ) :
    effort (translate k ψ) = k ^ 2 / 2 + effort ψ + k * capability ψ := by
  have hG : IntegrableOn (fun u => (u + k) * ψ u) (Ioi 0) := by
    have := hψ.integrable_mul.add (hψ.integrable.const_mul k)
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  have key := (piecewise_Ioi (F := fun h => h) hk intervalIntegral.intervalIntegrable_id hG).2
  have e : effort (translate k ψ)
      = ∫ h in Ioi (0 : ℝ), (if h < k then h else (h - k + k) * ψ (h - k)) := by
    unfold effort translate
    refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
    by_cases hlt : h < k <;> simp [hlt]
  have s : ∫ u in Ioi (0 : ℝ), (u + k) * ψ u = effort ψ + k * capability ψ := by
    unfold effort capability
    rw [← integral_const_mul, ← integral_add hψ.integrable_mul (hψ.integrable.const_mul k)]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    ring
  rw [e, key, s, integral_id]
  ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 6**, positive case (PDF p. 36): the squared spread is unchanged by a
positive translation. -/
theorem spreadSq_translate {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ) :
    spreadSq (translate k ψ) = spreadSq ψ := by
  unfold spreadSq
  rw [capability_translate hk hψ, effort_translate hk hψ]
  ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 6**, positive case (PDF p. 36): spread is unchanged by a positive
translation. -/
theorem spread_translate {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ) :
    spread (translate k ψ) = spread ψ := by
  unfold spread; rw [spreadSq_translate hk hψ]

-- STATEMENT UNREVIEWED
/-- **SI Proposition 6**, positive case (PDF p. 36): "generality is invariant to
translation." -/
theorem generality_translate {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ) :
    generality (translate k ψ) = generality ψ := by
  unfold generality; rw [spread_translate hk hψ]

/-- A `k`-saturated curve is the positive translation of its negative translation, at
every difficulty `h > 0`. -/
theorem translate_translateLeft {ψ : ℝ → ℝ} {k : ℝ} (hsat : Saturated k ψ) (h : ℝ)
    (hh : 0 < h) : translate k (translateLeft k ψ) h = ψ h := by
  unfold translate translateLeft
  split_ifs with hlt
  · exact (hsat h hh.le hlt.le).symm
  · simp

theorem isCurve_translateLeft {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ) :
    IsCurve (translateLeft k ψ) := by
  have hi : IntegrableOn (fun h => ψ (h + k)) (Ioi 0) := by
    simpa using integrableOn_Ioi_shift' k (-k) (hψ.integrable.mono_set (Ioi_subset_Ioi hk))
  have him : IntegrableOn (fun h => (h + k) * ψ (h + k)) (Ioi 0) := by
    simpa using integrableOn_Ioi_shift' (g := fun u => u * ψ u) k (-k)
      (hψ.integrable_mul.mono_set (Ioi_subset_Ioi hk))
  refine ⟨fun h hh => hψ.nonneg _ (add_nonneg hh hk), fun h hh => hψ.le_one _ (add_nonneg hh hk),
    hi, ?_⟩
  have := him.sub (hi.const_mul k)
  refine this.congr_fun (fun h _ => ?_) measurableSet_Ioi
  simp only [translateLeft, Pi.sub_apply]; ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 5** (PDF pp. 35–36): "Given an agent with capability Ψ where the
|l|-leftmost part of the original curve was saturated, any negative translation by k ≤ l
implies that capability becomes Ψ − k." Here the curve is assumed `k`-saturated, which is
what "saturated up to some l ≥ k" gives. -/
theorem capability_translateLeft {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ)
    (hsat : Saturated k ψ) : capability (translateLeft k ψ) = capability ψ - k := by
  rw [← capability_congr (translate_translateLeft hsat),
    capability_translate hk (isCurve_translateLeft hk hψ)]
  ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 6**, negative case (PDF p. 36, "The proof for the negative translation
is similar"): the squared spread of a `k`-saturated curve is unchanged by the negative
translation by `k`. -/
theorem spreadSq_translateLeft {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ)
    (hsat : Saturated k ψ) : spreadSq (translateLeft k ψ) = spreadSq ψ := by
  rw [← spreadSq_congr (translate_translateLeft hsat),
    spreadSq_translate hk (isCurve_translateLeft hk hψ)]

-- STATEMENT UNREVIEWED
/-- **SI Proposition 6**, negative case (PDF p. 36): spread is unchanged. -/
theorem spread_translateLeft {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ)
    (hsat : Saturated k ψ) : spread (translateLeft k ψ) = spread ψ := by
  unfold spread; rw [spreadSq_translateLeft hk hψ hsat]

-- STATEMENT UNREVIEWED
/-- **SI Proposition 6**, negative case (PDF p. 36): generality is unchanged. -/
theorem generality_translateLeft {ψ : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) (hψ : IsCurve ψ)
    (hsat : Saturated k ψ) : generality (translateLeft k ψ) = generality ψ := by
  unfold generality; rw [spread_translateLeft hk hψ hsat]

/-! ## Piecewise-constant curves -/

/-- The curve equal to `c` on `[a, b]` and to 0 elsewhere (modelling choice D6). -/
noncomputable def box (c a b : ℝ) : ℝ → ℝ := (Icc a b).indicator fun _ => c

theorem setIntegral_Ioi_indicator_Icc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (f : ℝ → ℝ) :
    ∫ h in Ioi (0 : ℝ), (Icc a b).indicator f h = ∫ h in a..b, f h := by
  have hI : Ici 0 ∩ Icc a b = Icc a b := inter_eq_right.2 fun x hx => ha.trans hx.1
  rw [← integral_Ici_eq_integral_Ioi, setIntegral_indicator measurableSet_Icc, hI,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

theorem mul_box (c a b h : ℝ) : h * box c a b h = (Icc a b).indicator (fun h => h * c) h := by
  unfold box; by_cases hh : h ∈ Icc a b <;> simp [hh]

theorem capability_box {a b : ℝ} (c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    capability (box c a b) = c * (b - a) := by
  unfold capability box
  rw [setIntegral_Ioi_indicator_Icc ha hab]
  simp [mul_comm]

theorem effort_box {a b : ℝ} (c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    effort (box c a b) = c * (b ^ 2 - a ^ 2) / 2 := by
  unfold effort
  simp_rw [mul_box]
  rw [setIntegral_Ioi_indicator_Icc ha hab, intervalIntegral.integral_mul_const, integral_id]
  ring

theorem integrableOn_box (c a b : ℝ) : IntegrableOn (box c a b) (Ioi 0) :=
  ((integrable_indicator_iff measurableSet_Icc).2
    (continuous_const.integrableOn_Icc)).integrableOn

theorem integrableOn_mul_box (c a b : ℝ) : IntegrableOn (fun h => h * box c a b h) (Ioi 0) := by
  simp_rw [mul_box]
  exact ((integrable_indicator_iff measurableSet_Icc).2
    ((continuous_id.mul continuous_const).integrableOn_Icc)).integrableOn

theorem isCurve_box {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a b : ℝ) : IsCurve (box c a b) := by
  refine ⟨fun h _ => ?_, fun h _ => ?_, integrableOn_box c a b, integrableOn_mul_box c a b⟩
  · unfold box; by_cases hh : h ∈ Icc a b <;> simp [hh, hc0]
  · unfold box; by_cases hh : h ∈ Icc a b <;> simp [hh, hc1]

/-! ## The step curve (SI Proposition 9, PDF pp. 36–37) -/

-- STATEMENT UNREVIEWED
/-- The decreasing step curve with location `l`: 1 up to difficulty `l`, 0 after. Source:
SI §E.2, property 3, PDF p. 35 ("a decreasing step agent characteristic function abruptly
falling from 1 to 0 on h = Ψ"). -/
noncomputable def step (l : ℝ) : ℝ → ℝ := box 1 0 l

theorem isCurve_step (l : ℝ) : IsCurve (step l) := isCurve_box zero_le_one le_rfl 0 l

-- STATEMENT UNREVIEWED
/-- The step curve with location `l` is `l`-saturated. Source: SI §E.2, property 6, PDF
p. 35 ("Agents with maximum generality Γ = ∞ are s-saturated with s = Ψ"), for the step
curve. -/
theorem saturated_step (l : ℝ) : Saturated l (step l) := fun h h0 hl => by
  simp [step, box, h0, hl]

-- STATEMENT UNREVIEWED
/-- **SI Proposition 9** (PDF p. 36): "The area of a step function with location l is
Ψ = ∫₀^l 1 dh = l." -/
theorem capability_step {l : ℝ} (hl : 0 ≤ l) : capability (step l) = l := by
  unfold step; rw [capability_box 1 le_rfl hl]; ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 9** (PDF p. 36): `M = ∫₀^l h·1 dh = l²/2`. -/
theorem effort_step {l : ℝ} (hl : 0 ≤ l) : effort (step l) = l ^ 2 / 2 := by
  unfold step; rw [effort_box 1 le_rfl hl]; ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 9** (PDF pp. 36–37): for a step curve, "capability is double the
expected difficulty (i.e., Ψ = 2H)". -/
theorem capability_step_eq_two_mul_expectedDifficulty {l : ℝ} (hl : 0 ≤ l) :
    capability (step l) = 2 * expectedDifficulty (step l) := by
  unfold expectedDifficulty
  rw [capability_step hl, effort_step hl]
  rcases eq_or_lt_of_le hl with rfl | hpos
  · simp
  · field_simp

-- STATEMENT UNREVIEWED
/-- **SI Proposition 9** (PDF p. 37): the squared spread of a step curve is 0. -/
theorem spreadSq_step {l : ℝ} (hl : 0 ≤ l) : spreadSq (step l) = 0 := by
  unfold spreadSq; rw [capability_step hl, effort_step hl]; ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 9** (PDF p. 37): the spread of a step curve is 0. -/
theorem spread_step {l : ℝ} (hl : 0 ≤ l) : spread (step l) = 0 := by
  unfold spread; rw [spreadSq_step hl, Real.sqrt_zero]

-- STATEMENT UNREVIEWED
/-- **SI Proposition 9** (PDF pp. 36–37): for a step curve, "generality Γ = ∞". -/
theorem generality_step {l : ℝ} (hl : 0 ≤ l) : generality (step l) = ⊤ :=
  (generality_eq_top_iff _).2 (spread_step hl)

/-! ## The constant curve (SI Proposition 10, PDF p. 37) -/

-- STATEMENT UNREVIEWED
/-- The constant curve: `c` from difficulty 0 to `q`, 0 after. Source: SI Proposition 10,
PDF p. 37 ("a constant function ψ(h) = c from 0 to q"). -/
noncomputable def constCurve (c q : ℝ) : ℝ → ℝ := box c 0 q

theorem isCurve_constCurve {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (q : ℝ) :
    IsCurve (constCurve c q) := isCurve_box hc0 hc1 0 q

-- STATEMENT UNREVIEWED
/-- **SI Proposition 10** (PDF p. 37): `Ψ = cq`. -/
theorem capability_constCurve (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    capability (constCurve c q) = c * q := by
  unfold constCurve; rw [capability_box c le_rfl hq]; ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 10** (PDF p. 37): `M = c·q²/2`. -/
theorem effort_constCurve (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    effort (constCurve c q) = c * q ^ 2 / 2 := by
  unfold constCurve; rw [effort_box c le_rfl hq]; ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 10** (PDF p. 37): `S² = c(1 − c)q²`. -/
theorem spreadSq_constCurve (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    spreadSq (constCurve c q) = c * (1 - c) * q ^ 2 := by
  unfold spreadSq; rw [capability_constCurve c hq, effort_constCurve c hq]; ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 10** (PDF p. 37): `S = q·√(c(1 − c))`. (The identity holds in Lean for
every real `c`; the source has `0 ≤ c ≤ 1`.) -/
theorem spread_constCurve (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    spread (constCurve c q) = q * Real.sqrt (c * (1 - c)) := by
  unfold spread
  rw [spreadSq_constCurve c hq, Real.sqrt_mul' _ (sq_nonneg q), Real.sqrt_sq hq, mul_comm]

-- STATEMENT UNREVIEWED
/-- **SI Proposition 10** (PDF p. 37): `Γ = 1/(q·√(c(1 − c)))`. -/
theorem generality_constCurve (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    generality (constCurve c q) = (ENNReal.ofReal (q * Real.sqrt (c * (1 - c))))⁻¹ := by
  unfold generality; rw [spread_constCurve c hq]

-- STATEMENT UNREVIEWED
/-- **SI §E.2, property 4** (PDF p. 35): "In the particular case of c = 0.5 we have
S = q/2". -/
theorem spread_constCurve_half {q : ℝ} (hq : 0 ≤ q) : spread (constCurve (1 / 2) q) = q / 2 := by
  rw [spread_constCurve _ hq]
  have : Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2)) = 1 / 2 := by
    rw [show ((1 / 2 : ℝ) * (1 - 1 / 2)) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [this]; ring

/-! ## The reversed step (SI Propositions 11 and 12, PDF p. 37) -/

-- STATEMENT UNREVIEWED
/-- The increasing ("reversed") step curve on `[0, q]` with capability `Ψ`: 0 up to
`q − Ψ`, then 1 up to `q`, 0 after. Source: SI Proposition 11, PDF p. 37 ("an increasing
step agent characteristic function on h = q − Ψ (until q)"). -/
noncomputable def reversedStep (q Ψ : ℝ) : ℝ → ℝ := box 1 (q - Ψ) q

theorem isCurve_reversedStep (q Ψ : ℝ) : IsCurve (reversedStep q Ψ) :=
  isCurve_box zero_le_one le_rfl _ _

-- STATEMENT UNREVIEWED
/-- The reversed step with parameter `Ψ` has capability `Ψ`. Source: SI Proposition 11,
PDF p. 37 (implicit). -/
theorem capability_reversedStep {q Ψ : ℝ} (h0 : 0 ≤ Ψ) (hq : Ψ ≤ q) :
    capability (reversedStep q Ψ) = Ψ := by
  unfold reversedStep
  rw [capability_box 1 (sub_nonneg.2 hq) (sub_le_self q h0)]; ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 11**, value (PDF p. 37): `M = (q² − (q − Ψ)²)/2`. -/
theorem effort_reversedStep {q Ψ : ℝ} (h0 : 0 ≤ Ψ) (hq : Ψ ≤ q) :
    effort (reversedStep q Ψ) = (q ^ 2 - (q - Ψ) ^ 2) / 2 := by
  unfold reversedStep
  rw [effort_box 1 (sub_nonneg.2 hq) (sub_le_self q h0)]; ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 11**, value (PDF p. 37): `S² = 2Ψ(q − Ψ)` for the reversed step. The
claim that this is the largest spread at capability `Ψ` on `[0, q]` is not proved in the
supplement and not here (Tier 2). -/
theorem spreadSq_reversedStep {q Ψ : ℝ} (h0 : 0 ≤ Ψ) (hq : Ψ ≤ q) :
    spreadSq (reversedStep q Ψ) = 2 * Ψ * (q - Ψ) := by
  unfold spreadSq
  rw [capability_reversedStep h0 hq, effort_reversedStep h0 hq]; ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 11**, value (PDF p. 37): `S = √(2Ψ(q − Ψ))` for the reversed step. -/
theorem spread_reversedStep {q Ψ : ℝ} (h0 : 0 ≤ Ψ) (hq : Ψ ≤ q) :
    spread (reversedStep q Ψ) = Real.sqrt (2 * Ψ * (q - Ψ)) := by
  unfold spread; rw [spreadSq_reversedStep h0 hq]

-- STATEMENT UNREVIEWED
/-- **SI Proposition 11**, value (PDF p. 37): `Γ = 1/√(2Ψ(q − Ψ))` for the reversed
step. -/
theorem generality_reversedStep {q Ψ : ℝ} (h0 : 0 ≤ Ψ) (hq : Ψ ≤ q) :
    generality (reversedStep q Ψ) = (ENNReal.ofReal (Real.sqrt (2 * Ψ * (q - Ψ))))⁻¹ := by
  unfold generality; rw [spread_reversedStep h0 hq]

-- STATEMENT UNREVIEWED
/-- **SI Proposition 12** (PDF p. 37): "With the same capability, the square spread for
the minimum case (most abstruse case in an interval) is exactly twice the square spread
for the constant case (in the same interval)." The constant curve on `[0, q]` with
capability `Ψ` has height `Ψ/q`. -/
theorem spreadSq_reversedStep_eq_two_mul_constCurve {q Ψ : ℝ} (h0 : 0 ≤ Ψ) (hq : Ψ ≤ q)
    (hqpos : 0 < q) :
    capability (constCurve (Ψ / q) q) = capability (reversedStep q Ψ) ∧
      spreadSq (reversedStep q Ψ) = 2 * spreadSq (constCurve (Ψ / q) q) := by
  rw [capability_constCurve _ hqpos.le, capability_reversedStep h0 hq,
    spreadSq_reversedStep h0 hq, spreadSq_constCurve _ hqpos.le]
  constructor <;> field_simp

-- STATEMENT UNREVIEWED
/-- The squared spread of the constant curve on `[0, q]` with capability `Ψ` is
`Ψ(q − Ψ)`. Source: the proof of SI Proposition 12, PDF p. 37, and §F.5, PDF p. 41
("S²_cnst = Ψ(q − Ψ)"). -/
theorem spreadSq_constCurve_of_capability {q Ψ : ℝ} (hqpos : 0 < q) :
    spreadSq (constCurve (Ψ / q) q) = Ψ * (q - Ψ) := by
  rw [spreadSq_constCurve _ hqpos.le]; field_simp

/-! ## Averages of curves, and the mixture of step curves (SI Lemma 19, PDF pp. 39–40) -/

section Mixture

variable {ι : Type*} [Fintype ι]

-- STATEMENT UNREVIEWED
/-- The pointwise average of finitely many curves. Source: SI Lemma 19, PDF p. 39 ("if we
average them into a single ACC"). -/
noncomputable def average (ψ : ι → ℝ → ℝ) : ℝ → ℝ :=
  fun h => (∑ i, ψ i h) / Fintype.card ι

-- STATEMENT UNREVIEWED
/-- The capability of an average of curves is the average of their capabilities. Source:
the proof of SI Lemma 19, PDF p. 39 ("as areas are additive"). -/
theorem capability_average (ψ : ι → ℝ → ℝ) (hψ : ∀ i, IntegrableOn (ψ i) (Ioi 0)) :
    capability (average ψ) = (∑ i, capability (ψ i)) / Fintype.card ι := by
  unfold capability average
  rw [integral_div, integral_finsetSum _ fun i _ => hψ i]

-- STATEMENT UNREVIEWED
/-- The moment of an average of curves is the average of their moments. Source: used in
the proof of SI Lemma 19, PDF p. 40. -/
theorem effort_average (ψ : ι → ℝ → ℝ)
    (hψ : ∀ i, IntegrableOn (fun h => h * ψ i h) (Ioi 0)) :
    effort (average ψ) = (∑ i, effort (ψ i)) / Fintype.card ι := by
  unfold effort average
  rw [← integral_finsetSum _ fun i _ => hψ i, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  rw [← mul_div_assoc, Finset.mul_sum]

-- STATEMENT UNREVIEWED
/-- The average of the step curves with locations `a i`: a descending staircase. Source:
SI Lemma 19, PDF p. 39. -/
noncomputable def stepMixture (a : ι → ℝ) : ℝ → ℝ := average fun i => step (a i)

-- STATEMENT UNREVIEWED
/-- **SI Lemma 19**, capability (PDF p. 39): the average of `N` step curves with
capabilities `a₁, …, a_N` has capability `(1/N)·Σ aᵢ`. -/
theorem capability_stepMixture (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    capability (stepMixture a) = (∑ i, a i) / Fintype.card ι := by
  unfold stepMixture
  rw [capability_average _ fun i => (isCurve_step (a i)).integrable]
  simp_rw [capability_step (ha _)]

-- STATEMENT UNREVIEWED
/-- **SI Lemma 19**, moment (PDF p. 40): `M = (1/(2N))·Σ aᵢ²`. -/
theorem effort_stepMixture (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    effort (stepMixture a) = (∑ i, a i ^ 2) / (2 * Fintype.card ι) := by
  unfold stepMixture
  rw [effort_average _ fun i => (isCurve_step (a i)).integrable_mul]
  simp_rw [effort_step (ha _)]
  rw [← Finset.sum_div]; ring

-- STATEMENT UNREVIEWED
/-- **SI Lemma 19**, squared spread (PDF p. 40): `S² = (1/N)·Σ aᵢ² − ((1/N)·Σ aᵢ)²`. -/
theorem spreadSq_stepMixture (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    spreadSq (stepMixture a)
      = (∑ i, a i ^ 2) / Fintype.card ι - ((∑ i, a i) / Fintype.card ι) ^ 2 := by
  unfold spreadSq
  rw [capability_stepMixture a ha, effort_stepMixture a ha]; ring

-- STATEMENT UNREVIEWED
/-- **SI Lemma 19** (PDF pp. 39–40): the squared spread of the average of `N ≥ 1` step
curves is the population variance of their capabilities, `(1/N)·Σ (aᵢ − ā)²` with
`ā = (1/N)·Σ aᵢ`. -/
theorem spreadSq_stepMixture_eq_variance [Nonempty ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    spreadSq (stepMixture a)
      = (∑ i, (a i - (∑ j, a j) / Fintype.card ι) ^ 2) / Fintype.card ι := by
  rw [spreadSq_stepMixture a ha]
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

-- STATEMENT UNREVIEWED
/-- **SI Lemma 19** (PDF pp. 39–40): "we have a descending staircase ACC with average
capability Ψ = (1/N)·Σ aᵢ and spread S being the standard deviation of the original
capabilities" (the population standard deviation, SI footnote 10, PDF p. 32). -/
theorem spread_stepMixture [Nonempty ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    capability (stepMixture a) = (∑ i, a i) / Fintype.card ι ∧
      spread (stepMixture a)
        = Real.sqrt ((∑ i, (a i - (∑ j, a j) / Fintype.card ι) ^ 2) / Fintype.card ι) := by
  refine ⟨capability_stepMixture a ha, ?_⟩
  unfold spread; rw [spreadSq_stepMixture_eq_variance a ha]

theorem isCurve_stepMixture [Nonempty ι] (a : ι → ℝ) : IsCurve (stepMixture a) := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨fun h hh => ?_, fun h hh => ?_, ?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg fun i _ => (isCurve_step (a i)).nonneg h hh) hN.le
  · unfold stepMixture average
    rw [div_le_one hN]
    calc ∑ i, step (a i) h ≤ ∑ _i : ι, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (isCurve_step (a i)).le_one h hh
      _ = Fintype.card ι := by simp
  · exact (integrable_finsetSum _ fun i _ => (isCurve_step (a i)).integrable).div_const _
  · have := (integrable_finsetSum (Finset.univ : Finset ι)
      fun i _ => (isCurve_step (a i)).integrable_mul).div_const (Fintype.card ι : ℝ)
    refine IntegrableOn.congr_fun this (fun h _ => ?_) measurableSet_Ioi
    simp only [stepMixture, average]
    rw [← mul_div_assoc, Finset.mul_sum]

end Mixture

/-! ## Homogeneity under rescaling difficulty (SI Proposition 15, PDF p. 38) -/

-- STATEMENT UNREVIEWED
/-- The curve after difficulty is measured in a unit `lam` times smaller: a task of old
difficulty `h` has new difficulty `lam·h`. Source: SI Proposition 15, PDF p. 38, read as
homogeneity (modelling choice D8). -/
noncomputable def rescale (lam : ℝ) (ψ : ℝ → ℝ) : ℝ → ℝ := fun h => ψ (h / lam)

-- STATEMENT UNREVIEWED
/-- **SI Proposition 15** (PDF p. 38): "capability is also measured in witts": rescaling
difficulty by `lam > 0` multiplies capability by `lam`. -/
theorem capability_rescale (ψ : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    capability (rescale lam ψ) = lam * capability ψ := by
  unfold capability rescale
  have := integral_comp_mul_left_Ioi ψ 0 (inv_pos.2 hlam)
  simp only [mul_zero, inv_inv, smul_eq_mul] at this
  rw [← this]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  simp only [div_eq_inv_mul]

-- STATEMENT UNREVIEWED
/-- **SI Proposition 15** (PDF p. 38): the moment `M` "is in witts²": rescaling difficulty
by `lam > 0` multiplies it by `lam²`. -/
theorem effort_rescale (ψ : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    effort (rescale lam ψ) = lam ^ 2 * effort ψ := by
  unfold effort rescale
  have := integral_comp_mul_left_Ioi (fun u => u * ψ u) 0 (inv_pos.2 hlam)
  simp only [mul_zero, inv_inv, smul_eq_mul] at this
  rw [sq, mul_assoc, ← this, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  simp only [div_eq_inv_mul]
  field_simp

-- STATEMENT UNREVIEWED
/-- **SI Proposition 15** (PDF p. 38): the squared spread scales by `lam²`. -/
theorem spreadSq_rescale (ψ : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    spreadSq (rescale lam ψ) = lam ^ 2 * spreadSq ψ := by
  unfold spreadSq; rw [capability_rescale ψ hlam, effort_rescale ψ hlam]; ring

-- STATEMENT UNREVIEWED
/-- **SI Proposition 15** (PDF p. 38): "spread is also measured in witts": rescaling
difficulty by `lam > 0` multiplies spread by `lam`. -/
theorem spread_rescale (ψ : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    spread (rescale lam ψ) = lam * spread ψ := by
  unfold spread
  rw [spreadSq_rescale ψ hlam, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hlam.le]

-- STATEMENT UNREVIEWED
/-- **SI Proposition 15** (PDF p. 38): "generality is measured in 1/witts": rescaling
difficulty by `lam > 0` divides generality by `lam`. -/
theorem generality_rescale (ψ : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    generality (rescale lam ψ) = generality ψ / ENNReal.ofReal lam := by
  unfold generality
  rw [spread_rescale ψ hlam, ENNReal.ofReal_mul hlam.le,
    ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 hlam).ne') (Or.inl ENNReal.ofReal_ne_top),
    div_eq_mul_inv, mul_comm]

-- STATEMENT UNREVIEWED
/-- Expected difficulty carries the unit of difficulty: rescaling by `lam > 0` multiplies
it by `lam`. Source: SI Proposition 15, PDF p. 38 (implicit). -/
theorem expectedDifficulty_rescale (ψ : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    expectedDifficulty (rescale lam ψ) = lam * expectedDifficulty ψ := by
  unfold expectedDifficulty
  rw [capability_rescale ψ hlam, effort_rescale ψ hlam]
  field_simp

end UncontainabilityLean.Generality
