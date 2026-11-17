/-
# The generality metric: compactness, corrected  (index ID 125; Tier 3, package C)

Source: Hernández-Orallo et al. 2021, Supplementary Information §E.2 (property 2, PDF
p. 34) and §F.1 (Proposition 7, PDF p. 36):
`papers/index/files/125_supplementary_information.pdf`. Page numbers are PDF pages.

Proposition 7 reads: "Compactness: any mass moved to the left of the plot such that
Ψ^[h₁:h₂] ← Ψ^[h₁:h₂] + q while Ψ^[h₃:h₄] ← Ψ^[h₃:h₄] − q, with h₂ < h₃ will increase Γ."
Here Ψ^[a:b] = ∫_a^b ψ(h) dh is a partial area (SI §E.2, PDF p. 33).

FINDING. Read literally, the statement constrains only the two partial areas (and, from
the proof's display, leaves the curve unchanged outside the two intervals). In that form
it is FALSE: `compactness_literal_false`. The counterexample is the one found by the
earlier reading (`policy/bridge/08-generality-metric-proofs.md`): ψ = ½ on [0, 1] and on
[2, 3]; ψ′ = 1 on [0.4, 1] and on [2.6, 3]. The area over [0, 1] rises by 0.1, the area
over [2, 3] falls by 0.1, the curves agree elsewhere and have the same capability, yet the
squared spread rises from 2 to 2.08, so generality falls.

The supplement's proof asserts `M′ < M` "since h₂ < h₃". That step needs mass to be ADDED
pointwise on [h₁, h₂] and REMOVED pointwise on [h₃, h₄]. With those two hypotheses the
result holds: `compactness_corrected`.

MODELLING CHOICES, in addition to those of `Basic.lean` and `Extremal.lean`.

  D12. The partial area Ψ^[a:b] is the integral over the closed interval `[a, b]`.
  D13. The moved mass is called `m` (the source calls it `q`, which elsewhere is the
       maximum difficulty).
  D14. "Unchanged elsewhere" is: `ψ′ h = ψ h` at every `h > 0` outside both intervals.

Every statement stays `-- STATEMENT UNREVIEWED` until a human reviewer signs off.
-/
import UncontainabilityLean.Generality.Extremal

open MeasureTheory Set
open scoped ENNReal

namespace UncontainabilityLean.Generality

/-! ## Auxiliary facts -/

theorem capability_add {ψ φ : ℝ → ℝ} (hψ : IntegrableOn ψ (Ioi 0))
    (hφ : IntegrableOn φ (Ioi 0)) :
    capability (fun h => ψ h + φ h) = capability ψ + capability φ :=
  integral_add hψ hφ

theorem effort_add {ψ φ : ℝ → ℝ} (hψ : IntegrableOn (fun h => h * ψ h) (Ioi 0))
    (hφ : IntegrableOn (fun h => h * φ h) (Ioi 0)) :
    effort (fun h => ψ h + φ h) = effort ψ + effort φ := by
  unfold effort
  rw [← integral_add hψ hφ]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  ring

theorem integrable_box (c a b : ℝ) : Integrable (box c a b) :=
  (integrable_indicator_iff measurableSet_Icc).2 continuous_const.integrableOn_Icc

theorem box_of_notMem {c a b x : ℝ} (hx : x ∉ Icc a b) : box c a b x = 0 := by
  simp [box, hx]

theorem box_of_mem {c a b x : ℝ} (hx : x ∈ Icc a b) : box c a b x = c := by
  simp [box, hx]

/-- Spread and generality are in reverse order. -/
theorem generality_lt_generality {ψ φ : ℝ → ℝ} (h : spread ψ < spread φ) :
    generality φ < generality ψ := by
  unfold generality
  exact ENNReal.inv_lt_inv.2
    ((ENNReal.ofReal_lt_ofReal_iff ((spread_nonneg ψ).trans_lt h)).2 h)

theorem setIntegral_Ioi_indicator_Icc' {a b : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) :
    ∫ h in Ioi (0 : ℝ), (Icc a b).indicator f h = ∫ h in Icc a b, f h := by
  have hI : Ici 0 ∩ Icc a b = Icc a b := inter_eq_right.2 fun x hx => ha.trans hx.1
  rw [← integral_Ici_eq_integral_Ioi, setIntegral_indicator measurableSet_Icc, hI]

/-- A function on `(0, ∞)` that vanishes outside two separated closed intervals. -/
theorem setIntegral_Ioi_eq_add {f : ℝ → ℝ} {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbc : b < c) (hf : IntegrableOn f (Ioi 0))
    (hout : ∀ h, 0 < h → h ∉ Icc a b → h ∉ Icc c d → f h = 0) :
    ∫ h in Ioi (0 : ℝ), f h = (∫ h in Icc a b, f h) + ∫ h in Icc c d, f h := by
  have e : ∀ h ∈ Ioi (0 : ℝ), f h = (Icc a b).indicator f h + (Icc c d).indicator f h := by
    intro h hh
    by_cases h1 : h ∈ Icc a b
    · have h2 : h ∉ Icc c d := fun h2 => by linarith [h1.2, h2.1]
      simp [h1, h2]
    · by_cases h2 : h ∈ Icc c d
      · simp [h1, h2]
      · simp [h1, h2, hout h hh h1 h2]
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    integral_add (hf.indicator measurableSet_Icc) (hf.indicator measurableSet_Icc),
    setIntegral_Ioi_indicator_Icc' ha, setIntegral_Ioi_indicator_Icc' (by linarith)]

theorem IsCurve.integrableOn_Icc {ψ : ℝ → ℝ} (hψ : IsCurve ψ) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    IntegrableOn ψ (Icc a b) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact hψ.integrable.mono_set fun x hx => lt_of_le_of_lt ha hx.1

theorem IsCurve.integrableOn_mul_Icc {ψ : ℝ → ℝ} (hψ : IsCurve ψ) {a : ℝ} (ha : 0 ≤ a)
    (b : ℝ) : IntegrableOn (fun h => h * ψ h) (Icc a b) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact hψ.integrable_mul.mono_set fun x hx => lt_of_le_of_lt ha hx.1

/-! ## Partial areas -/

-- STATEMENT UNREVIEWED
/-- The partial area `Ψ^[a:b] = ∫_a^b ψ(h) dh`. Source: SI §E.2, PDF p. 33 ("we introduce
the notation for partial areas, i.e., Ψ^[h₁:h₂] = ∫_{h₁}^{h₂} ψ(h) dh"). -/
noncomputable def partialArea (ψ : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ h in Icc a b, ψ h

theorem partialArea_box (c a b x y : ℝ) :
    partialArea (box c a b) x y = c * max (min y b - max x a) 0 := by
  unfold partialArea box
  rw [setIntegral_indicator measurableSet_Icc, Icc_inter_Icc, setIntegral_const,
    Real.volume_real_Icc, smul_eq_mul, mul_comm]

theorem partialArea_add {ψ φ : ℝ → ℝ} (a b : ℝ) (hψ : IntegrableOn ψ (Icc a b))
    (hφ : IntegrableOn φ (Icc a b)) :
    partialArea (fun h => ψ h + φ h) a b = partialArea ψ a b + partialArea φ a b :=
  integral_add hψ hφ

/-! ## The corrected statement -/

-- STATEMENT UNREVIEWED
/-- **SI Proposition 7, corrected** (PDF p. 36; property 2, PDF p. 34): at equal
capability, if the curve is raised pointwise on `[h₁, h₂]` and lowered pointwise on
`[h₃, h₄]`, by the same mass `m > 0`, with `h₂ < h₃`, and is unchanged elsewhere, then
capability is unchanged, the moment `M` falls by at least `(h₃ − h₂)·m`, spread falls and
generality rises. The pointwise hypotheses `hadd` and `hrem` are the correction: the
source constrains only the two partial areas (see `compactness_literal_false`). The
supplement's own proof establishes this form. -/
theorem compactness_corrected {ψ ψ' : ℝ → ℝ} {h₁ h₂ h₃ h₄ m : ℝ}
    (hψ : IsCurve ψ) (hψ' : IsCurve ψ')
    (h1 : 0 ≤ h₁) (h12 : h₁ ≤ h₂) (h23 : h₂ < h₃)
    (hadd : ∀ h ∈ Icc h₁ h₂, ψ h ≤ ψ' h) (hrem : ∀ h ∈ Icc h₃ h₄, ψ' h ≤ ψ h)
    (hout : ∀ h, 0 < h → h ∉ Icc h₁ h₂ → h ∉ Icc h₃ h₄ → ψ' h = ψ h)
    (hm : 0 < m)
    (hA : partialArea ψ' h₁ h₂ = partialArea ψ h₁ h₂ + m)
    (hB : partialArea ψ' h₃ h₄ = partialArea ψ h₃ h₄ - m) :
    capability ψ' = capability ψ ∧ effort ψ' ≤ effort ψ - (h₃ - h₂) * m ∧
      spread ψ' < spread ψ ∧ generality ψ < generality ψ' := by
  have h3 : 0 ≤ h₃ := by linarith
  -- the mass of the difference on each interval
  have dA : ∫ h in Icc h₁ h₂, (ψ' h - ψ h) = m := by
    rw [integral_sub (hψ'.integrableOn_Icc h1 _) (hψ.integrableOn_Icc h1 _)]
    unfold partialArea at hA; linarith
  have dB : ∫ h in Icc h₃ h₄, (ψ' h - ψ h) = -m := by
    rw [integral_sub (hψ'.integrableOn_Icc h3 _) (hψ.integrableOn_Icc h3 _)]
    unfold partialArea at hB; linarith
  -- capability
  have hcap : capability ψ' - capability ψ = 0 := by
    unfold capability
    rw [← integral_sub hψ'.integrable hψ.integrable,
      setIntegral_Ioi_eq_add (f := fun h => ψ' h - ψ h) h1 h12 h23
        (hψ'.integrable.sub hψ.integrable)
        (fun h hh ha hb => by show ψ' h - ψ h = 0; rw [hout h hh ha hb, sub_self]), dA, dB]
    ring
  -- moment
  have iA := (hψ'.integrableOn_mul_Icc h1 h₂).sub (hψ.integrableOn_mul_Icc h1 h₂)
  have iB := (hψ'.integrableOn_mul_Icc h3 h₄).sub (hψ.integrableOn_mul_Icc h3 h₄)
  have mA : ∫ h in Icc h₁ h₂, (h * ψ' h - h * ψ h) ≤ h₂ * m := by
    rw [← dA, ← integral_const_mul]
    refine setIntegral_mono_on iA
      (((hψ'.integrableOn_Icc h1 _).sub (hψ.integrableOn_Icc h1 _)).const_mul h₂)
      measurableSet_Icc fun h hh => ?_
    have := hadd h hh
    nlinarith [hh.2]
  have mB : ∫ h in Icc h₃ h₄, (h * ψ' h - h * ψ h) ≤ h₃ * (-m) := by
    rw [← dB, ← integral_const_mul]
    refine setIntegral_mono_on iB
      (((hψ'.integrableOn_Icc h3 _).sub (hψ.integrableOn_Icc h3 _)).const_mul h₃)
      measurableSet_Icc fun h hh => ?_
    have := hrem h hh
    nlinarith [hh.1]
  have heff : effort ψ' - effort ψ ≤ h₂ * m + h₃ * (-m) := by
    unfold effort
    rw [← integral_sub hψ'.integrable_mul hψ.integrable_mul,
      setIntegral_Ioi_eq_add (f := fun h => h * ψ' h - h * ψ h) h1 h12 h23
        (hψ'.integrable_mul.sub hψ.integrable_mul)
        (fun h hh ha hb => by show h * ψ' h - h * ψ h = 0; rw [hout h hh ha hb, sub_self])]
    exact add_le_add mA mB
  have hcap' : capability ψ' = capability ψ := by linarith
  have hsq : spreadSq ψ' < spreadSq ψ := by
    unfold spreadSq
    rw [hcap']
    nlinarith [mul_pos (sub_pos.2 h23) hm]
  have hsp : spread ψ' < spread ψ := Real.sqrt_lt_sqrt (spreadSq_nonneg hψ') hsq
  exact ⟨hcap', by linarith, hsp, generality_lt_generality hsp⟩

/-! ## The literal statement, and its counterexample -/

-- STATEMENT UNREVIEWED
/-- **SI Proposition 7 as literally stated** (PDF p. 36): for curves of equal capability
that agree outside `[h₁, h₂]` and `[h₃, h₄]`, if the partial area over `[h₁, h₂]` rises by
`m > 0` and the partial area over `[h₃, h₄]` falls by `m`, with `h₂ < h₃`, then generality
rises. (Agreement outside the two intervals is taken from the proof's display of `M′`; the
statement itself does not say it. Including it makes the refutation stronger.) -/
def CompactnessLiteral : Prop :=
  ∀ (ψ ψ' : ℝ → ℝ) (h₁ h₂ h₃ h₄ m : ℝ), IsCurve ψ → IsCurve ψ' →
    0 ≤ h₁ → h₁ ≤ h₂ → h₂ < h₃ → h₃ ≤ h₄ → 0 < m →
    capability ψ' = capability ψ →
    (∀ h, h ∉ Icc h₁ h₂ → h ∉ Icc h₃ h₄ → ψ' h = ψ h) →
    partialArea ψ' h₁ h₂ = partialArea ψ h₁ h₂ + m →
    partialArea ψ' h₃ h₄ = partialArea ψ h₃ h₄ - m →
    generality ψ < generality ψ'

/-- The counterexample's original curve: ½ on `[0, 1]` and on `[2, 3]`. -/
noncomputable def cexBefore : ℝ → ℝ := fun h => box (1 / 2) 0 1 h + box (1 / 2) 2 3 h

/-- The counterexample's modified curve: 1 on `[0.4, 1]` and on `[2.6, 3]`. -/
noncomputable def cexAfter : ℝ → ℝ := fun h => box 1 (2 / 5) 1 h + box 1 (13 / 5) 3 h

theorem isCurve_cexBefore : IsCurve cexBefore := by
  refine ⟨fun h _ => ?_, fun h _ => ?_,
    (integrableOn_box _ _ _).add (integrableOn_box _ _ _), ?_⟩
  · unfold cexBefore box; simp only [indicator, mem_Icc]; split_ifs <;> norm_num
  · unfold cexBefore box; simp only [indicator, mem_Icc]; split_ifs <;> norm_num
  · refine ((integrableOn_mul_box (1 / 2) 0 1).add (integrableOn_mul_box (1 / 2) 2 3)).congr_fun
      (fun h _ => ?_) measurableSet_Ioi
    simp only [cexBefore, Pi.add_apply]; ring

theorem isCurve_cexAfter : IsCurve cexAfter := by
  refine ⟨fun h _ => ?_, fun h _ => ?_,
    (integrableOn_box _ _ _).add (integrableOn_box _ _ _), ?_⟩
  · unfold cexAfter box; simp only [indicator, mem_Icc]; split_ifs <;> norm_num
  · unfold cexAfter box; simp only [indicator, mem_Icc]
    split_ifs with h1 h2 <;> first | (exfalso; linarith [h1.2, h2.1]) | norm_num
  · refine ((integrableOn_mul_box 1 (2 / 5) 1).add (integrableOn_mul_box 1 (13 / 5) 3)).congr_fun
      (fun h _ => ?_) measurableSet_Ioi
    simp only [cexAfter, Pi.add_apply]; ring

theorem capability_cexBefore : capability cexBefore = 1 := by
  unfold cexBefore
  rw [capability_add (integrableOn_box _ _ _) (integrableOn_box _ _ _),
    capability_box _ (by norm_num) (by norm_num), capability_box _ (by norm_num) (by norm_num)]
  norm_num

theorem capability_cexAfter : capability cexAfter = 1 := by
  unfold cexAfter
  rw [capability_add (integrableOn_box _ _ _) (integrableOn_box _ _ _),
    capability_box _ (by norm_num) (by norm_num), capability_box _ (by norm_num) (by norm_num)]
  norm_num

theorem spreadSq_cexBefore : spreadSq cexBefore = 2 := by
  unfold spreadSq
  rw [capability_cexBefore]
  unfold cexBefore
  rw [effort_add (integrableOn_mul_box _ _ _) (integrableOn_mul_box _ _ _),
    effort_box _ (by norm_num) (by norm_num), effort_box _ (by norm_num) (by norm_num)]
  norm_num

theorem spreadSq_cexAfter : spreadSq cexAfter = 52 / 25 := by
  unfold spreadSq
  rw [capability_cexAfter]
  unfold cexAfter
  rw [effort_add (integrableOn_mul_box _ _ _) (integrableOn_mul_box _ _ _),
    effort_box _ (by norm_num) (by norm_num), effort_box _ (by norm_num) (by norm_num)]
  norm_num

theorem partialArea_cex :
    partialArea cexAfter 0 1 = partialArea cexBefore 0 1 + 1 / 10 ∧
      partialArea cexAfter 2 3 = partialArea cexBefore 2 3 - 1 / 10 := by
  unfold cexAfter cexBefore
  constructor
  all_goals
    rw [partialArea_add _ _ (integrable_box _ _ _).integrableOn (integrable_box _ _ _).integrableOn,
      partialArea_add _ _ (integrable_box _ _ _).integrableOn (integrable_box _ _ _).integrableOn]
    simp only [partialArea_box]
    norm_num

theorem cexAfter_eq_cexBefore_outside (h : ℝ) (hA : h ∉ Icc (0 : ℝ) 1) (hB : h ∉ Icc (2 : ℝ) 3) :
    cexAfter h = cexBefore h := by
  have a1 : h ∉ Icc (2 / 5 : ℝ) 1 := fun hx => hA ⟨by linarith [hx.1], hx.2⟩
  have a2 : h ∉ Icc (13 / 5 : ℝ) 3 := fun hx => hB ⟨by linarith [hx.1], hx.2⟩
  unfold cexAfter cexBefore
  rw [box_of_notMem a1, box_of_notMem a2, box_of_notMem hA, box_of_notMem hB]

-- STATEMENT UNREVIEWED
/-- **The counterexample to SI Proposition 7 as literally stated** (PDF p. 36). The curve
`cexBefore` (½ on `[0, 1]` and `[2, 3]`) and the curve `cexAfter` (1 on `[0.4, 1]` and
`[2.6, 3]`) are both agent characteristic curves of capability 1 that agree outside
`[0, 1] ∪ [2, 3]`; the partial area over `[0, 1]` is larger by 1/10 in `cexAfter` and the
partial area over `[2, 3]` smaller by 1/10; and yet the squared spread is 2 before and
2.08 after, so generality is strictly SMALLER after the move. -/
theorem compactness_counterexample :
    IsCurve cexBefore ∧ IsCurve cexAfter ∧ capability cexAfter = capability cexBefore ∧
      (∀ h, h ∉ Icc (0 : ℝ) 1 → h ∉ Icc (2 : ℝ) 3 → cexAfter h = cexBefore h) ∧
      partialArea cexAfter 0 1 = partialArea cexBefore 0 1 + 1 / 10 ∧
      partialArea cexAfter 2 3 = partialArea cexBefore 2 3 - 1 / 10 ∧
      spreadSq cexBefore = 2 ∧ spreadSq cexAfter = 52 / 25 ∧
      generality cexAfter < generality cexBefore := by
  refine ⟨isCurve_cexBefore, isCurve_cexAfter, by rw [capability_cexAfter, capability_cexBefore],
    cexAfter_eq_cexBefore_outside, partialArea_cex.1, partialArea_cex.2, spreadSq_cexBefore,
    spreadSq_cexAfter, generality_lt_generality ?_⟩
  unfold spread
  rw [spreadSq_cexBefore, spreadSq_cexAfter]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

-- STATEMENT UNREVIEWED
/-- **SI Proposition 7 is false as literally stated** (PDF p. 36). -/
theorem compactness_literal_false : ¬ CompactnessLiteral := by
  intro H
  obtain ⟨hb, ha, hcap, hout, hA, hB, -, -, hlt⟩ := compactness_counterexample
  exact lt_asymm hlt
    (H cexBefore cexAfter 0 1 2 3 (1 / 10) hb ha le_rfl (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hcap hout hA hB)

end UncontainabilityLean.Generality
