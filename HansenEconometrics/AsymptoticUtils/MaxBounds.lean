import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.IdentDistrib

/-!
# Uniform-integrability tail controls for Chapter 6 maximum bounds

This module records the Mathlib-facing uniform-integrability layer needed for
Hansen Theorem 6.16.  The main public theorem is stated on the nonnegative
power scale: if the sequence `Z_i = |Y_i|^r` is uniformly integrable in `L¹`,
then `n⁻¹ max_{i<n} Z_i` converges to zero in measure.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology MeasureTheory ProbabilityTheory Function

namespace HansenEconometrics

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Finite-sample maximum of the norms of a real-valued sequence. -/
noncomputable def maxNNNorm (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  (Finset.range n).sup fun i => ‖Z i ω‖₊

/-- Power-scale version of Hansen's maximum statistic.

When `Z i = |Y i| ^ r`, this is `n⁻¹ max_i |Y_i|^r`, the natural
nonnegative-power form of Theorem 6.16 before applying the `r`th-root CMT. -/
noncomputable def scaledMaxNNNorm (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * (maxNNNorm Z n ω : ℝ)

/-- Uniform integrability gives uniform control of large-tail `L¹` seminorms.

This is the Mathlib-backed UI layer used by Hansen Theorem 6.16.  The result is
for a real-valued sequence `Z`; in the textbook application `Z i` is the
nonnegative power variable `|Y_i|^r`. -/
theorem uniformIntegrable_tail_eLpNorm_one
    {Z : ℕ → Ω → ℝ} (hZ : UniformIntegrable Z 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0,
      ∀ i : ℕ,
        eLpNorm ({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) 1 μ ≤ ENNReal.ofReal ε := by
  simpa using
    (UniformIntegrable.spec (μ := μ) (f := Z)
      (p := (1 : ℝ≥0∞)) (by simp) (by simp) hZ hε)

/-- Tail `L¹` control gives Mathlib's probability-theory uniform integrability.

This is the converse of `uniformIntegrable_tail_eLpNorm_one`, stated as a
chapter-facing Definition 6.4 bridge. -/
theorem uniformIntegrable_one_of_tail_eLpNorm
    [IsFiniteMeasure μ] {Z : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
      ∀ i : ℕ,
        eLpNorm ({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) 1 μ ≤ ENNReal.ofReal ε) :
    UniformIntegrable Z 1 μ := by
  exact uniformIntegrable_of (μ := μ) (f := Z) (p := (1 : ℝ≥0∞))
    (by simp) (by simp) hZ hTail

/-- Two-sided tail characterization of `L¹` uniform integrability for real
sequences, with measurability supplied explicitly for the converse direction. -/
theorem uniformIntegrable_one_iff_tail_eLpNorm
    [IsFiniteMeasure μ] {Z : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ) :
    UniformIntegrable Z 1 μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
        ∀ i : ℕ,
          eLpNorm ({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) 1 μ ≤ ENNReal.ofReal ε :=
  ⟨fun hUI ε hε => uniformIntegrable_tail_eLpNorm_one (ε := ε) hUI hε,
    fun hTail => uniformIntegrable_one_of_tail_eLpNorm hZ hTail⟩

omit [MeasurableSpace Ω] in
private theorem max_norm_scaled_event_subset_tailUnion
    {Z : ℕ → Ω → ℝ} {ε : ℝ} (hε : 0 < ε) {C : ℝ≥0} {n : ℕ}
    (hn : 0 < n) (hC : (C : ℝ) ≤ (n : ℝ) * ε) :
    {ω | ε ≤ dist (scaledMaxNNNorm Z n ω) 0} ⊆
      ⋃ i ∈ Finset.range n,
        {ω | ENNReal.ofReal ((n : ℝ) * ε) ≤
          ‖({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) ω‖ₑ} := by
  intro ω hω
  let a : ℝ≥0 := ⟨(n : ℝ) * ε, (mul_pos (Nat.cast_pos.mpr hn) hε).le⟩
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have ha_pos : (⊥ : ℝ≥0) < a := by
    rw [← NNReal.coe_lt_coe]
    simpa [a] using mul_pos hnpos hε
  have hscaled_nonneg : 0 ≤ scaledMaxNNNorm Z n ω := by
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (NNReal.coe_nonneg _)
  have hscaled : ε ≤ scaledMaxNNNorm Z n ω := by
    simpa [Real.dist_eq, abs_of_nonneg hscaled_nonneg] using hω
  have hmax_ge_real : (n : ℝ) * ε ≤ (maxNNNorm Z n ω : ℝ) := by
    calc
      (n : ℝ) * ε ≤ (n : ℝ) * scaledMaxNNNorm Z n ω :=
        mul_le_mul_of_nonneg_left hscaled hnpos.le
      _ = (maxNNNorm Z n ω : ℝ) := by
        rw [scaledMaxNNNorm, ← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul]
  have hmax_ge : a ≤ maxNNNorm Z n ω := by
    rw [← NNReal.coe_le_coe]
    simpa [a] using hmax_ge_real
  change a ≤ (Finset.range n).sup (fun i => ‖Z i ω‖₊) at hmax_ge
  obtain ⟨i, hi, hi_le⟩ :=
    (Finset.le_sup_iff (s := Finset.range n) (f := fun i => ‖Z i ω‖₊) ha_pos).1
      hmax_ge
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, ?_⟩⟩
  have hC_a : C ≤ a := by
    rw [← NNReal.coe_le_coe]
    simpa [a] using hC
  have htail_mem : C ≤ ‖Z i ω‖₊ := hC_a.trans hi_le
  have htail_mem_set : ω ∈ {ω' | C ≤ ‖Z i ω'‖₊} := htail_mem
  have hindicator :
      ({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) ω = Z i ω :=
    Set.indicator_of_mem htail_mem_set _
  have hthreshold :
      ENNReal.ofReal ((n : ℝ) * ε) = (a : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (mul_pos hnpos hε).le]
  have hnorm : (a : ℝ≥0∞) ≤ ‖Z i ω‖ₑ := by
    simpa [enorm_eq_nnnorm] using (show (a : ℝ≥0∞) ≤ (‖Z i ω‖₊ : ℝ≥0∞) by
      exact_mod_cast hi_le)
  simpa [hthreshold, hindicator] using hnorm

private theorem measure_tail_indicator_le
    {Z : ℕ → Ω → ℝ} (hZ : UniformIntegrable Z 1 μ)
    {η ε : ℝ}
    {C : ℝ≥0} (hCtail :
      ∀ i : ℕ,
        eLpNorm ({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) 1 μ ≤ ENNReal.ofReal η)
    (hε : 0 < ε) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    μ {ω | ENNReal.ofReal ((n : ℝ) * ε) ≤
          ‖({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) ω‖ₑ}
      ≤ ENNReal.ofReal η / ENNReal.ofReal ((n : ℝ) * ε) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdenpos : 0 < (n : ℝ) * ε := mul_pos hnpos hε
  have htail_null :
      NullMeasurableSet {ω | C ≤ ‖Z i ω‖₊} μ := by
    exact (aestronglyMeasurable_const.nullMeasurableSet_le
      ((UniformIntegrable.aestronglyMeasurable hZ i).nnnorm))
  have htail_meas :
      AEStronglyMeasurable ({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) μ :=
    (UniformIntegrable.aestronglyMeasurable hZ i).indicator₀ htail_null
  have hmarkov :=
    meas_ge_le_lintegral_div
      (μ := μ)
      (f := fun ω => ‖({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) ω‖ₑ)
      htail_meas.enorm
      (ENNReal.ofReal_pos.mpr hdenpos).ne'
      ENNReal.ofReal_ne_top
  refine hmarkov.trans ?_
  simpa [eLpNorm_one_eq_lintegral_enorm] using
    ENNReal.div_le_div_right (hCtail i) (ENNReal.ofReal ((n : ℝ) * ε))

private theorem max_norm_scaled_measure_event_le
    {Z : ℕ → Ω → ℝ} (hZ : UniformIntegrable Z 1 μ)
    {C : ℝ≥0} {η ε : ℝ} (hε : 0 < ε)
    (hCtail :
      ∀ i : ℕ,
        eLpNorm ({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) 1 μ ≤ ENNReal.ofReal η)
    {δ : ℝ≥0∞} (hδtop : δ ≠ ∞) {n : ℕ}
    (hn : 0 < n) (hC : (C : ℝ) ≤ (n : ℝ) * ε)
    (hη : η = ε * δ.toReal / 2) :
    μ {ω | ε ≤ dist (scaledMaxNNNorm Z n ω) 0} ≤ δ := by
  have hsubset :=
    max_norm_scaled_event_subset_tailUnion
      (Z := Z) hε (C := C) (n := n) hn hC
  have hunion :
      μ (⋃ i ∈ Finset.range n,
        {ω | ENNReal.ofReal ((n : ℝ) * ε) ≤
          ‖({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) ω‖ₑ})
      ≤ ∑ i ∈ Finset.range n,
        μ {ω | ENNReal.ofReal ((n : ℝ) * ε) ≤
          ‖({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) ω‖ₑ} :=
    measure_biUnion_finset_le (Finset.range n) _
  have hsingle :
      ∀ i ∈ Finset.range n,
        μ {ω | ENNReal.ofReal ((n : ℝ) * ε) ≤
          ‖({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) ω‖ₑ}
        ≤ ENNReal.ofReal η / ENNReal.ofReal ((n : ℝ) * ε) := by
    intro i _
    exact measure_tail_indicator_le hZ hCtail hε hn i
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdenpos : 0 < (n : ℝ) * ε := mul_pos hnpos hε
  have hsum :
      (∑ i ∈ Finset.range n,
        ENNReal.ofReal η / ENNReal.ofReal ((n : ℝ) * ε))
        = ENNReal.ofReal (δ.toReal / 2) := by
    calc
      (∑ i ∈ Finset.range n,
        ENNReal.ofReal η / ENNReal.ofReal ((n : ℝ) * ε))
          = n • (ENNReal.ofReal η / ENNReal.ofReal ((n : ℝ) * ε)) := by simp
      _ = n • ENNReal.ofReal (η / ((n : ℝ) * ε)) := by
        rw [ENNReal.ofReal_div_of_pos hdenpos]
      _ = ENNReal.ofReal (n • (η / ((n : ℝ) * ε))) := by
        rw [ENNReal.ofReal_nsmul]
      _ = ENNReal.ofReal (δ.toReal / 2) := by
        congr 1
        simp [hη, nsmul_eq_mul]
        field_simp [hnpos.ne', hε.ne']
  calc
    μ {ω | ε ≤ dist (scaledMaxNNNorm Z n ω) 0}
        ≤ μ (⋃ i ∈ Finset.range n,
          {ω | ENNReal.ofReal ((n : ℝ) * ε) ≤
            ‖({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) ω‖ₑ}) :=
      measure_mono hsubset
    _ ≤ ∑ i ∈ Finset.range n,
        μ {ω | ENNReal.ofReal ((n : ℝ) * ε) ≤
          ‖({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) ω‖ₑ} :=
      hunion
    _ ≤ ∑ i ∈ Finset.range n,
        ENNReal.ofReal η / ENNReal.ofReal ((n : ℝ) * ε) :=
      Finset.sum_le_sum hsingle
    _ = ENNReal.ofReal (δ.toReal / 2) := hsum
    _ ≤ ENNReal.ofReal δ.toReal :=
      ENNReal.ofReal_le_ofReal (by
        have hδnonneg : 0 ≤ δ.toReal := ENNReal.toReal_nonneg
        nlinarith)
    _ = δ := ENNReal.ofReal_toReal hδtop

/-- Hansen Theorem 6.16 on the nonnegative power scale.

If `Z_i = |Y_i|^r` is uniformly integrable in `L¹`, then
`n⁻¹ max_{i<n} |Y_i|^r` converges to zero in measure.  The textbook
`n^{-1/r} max_i |Y_i|` form follows by applying the `r`th-root continuous
mapping theorem to this nonnegative statistic. -/
theorem max_norm_scaled_tendstoInMeasure_zero_of_uniformIntegrable_norm_r
    {Z : ℕ → Ω → ℝ}
    (hZ : UniformIntegrable Z 1 μ) :
    TendstoInMeasure μ (scaledMaxNNNorm Z) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  by_cases hδtop : δ = ∞
  · exact ⟨0, fun n _ => by simp [hδtop]⟩
  have hδreal : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
  let η : ℝ := ε * δ.toReal / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨C, hCtail⟩ := uniformIntegrable_tail_eLpNorm_one hZ hη_pos
  obtain ⟨N, hN⟩ := exists_nat_ge ((C : ℝ) / ε)
  refine ⟨max 1 N, fun n hn => ?_⟩
  have hnpos : 0 < n := by
    exact lt_of_lt_of_le (Nat.zero_lt_one) ((le_max_left 1 N).trans hn)
  have hNn : N ≤ n := (le_max_right 1 N).trans hn
  have hC : (C : ℝ) ≤ (n : ℝ) * ε := by
    have hdiv : (C : ℝ) / ε ≤ (n : ℝ) := hN.trans (by exact_mod_cast hNn)
    exact (div_le_iff₀ hε).1 hdiv
  exact max_norm_scaled_measure_event_le hZ hε hCtail hδtop hnpos hC rfl

/-- **Hansen Theorem 6.14, identically distributed `L¹` UI wrapper.**

An identically distributed real sequence with a finite first moment is uniformly
integrable in `L¹`.  This is the primitive moment-to-UI bridge used to feed
Hansen's maximum theorem when the power variables are iid. -/
theorem uniformIntegrable_one_of_identDistrib_memLp
    [IsFiniteMeasure μ] {Z : ℕ → Ω → ℝ}
    (hZ0 : MemLp (Z 0) 1 μ)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ) :
    UniformIntegrable Z 1 μ := by
  exact MemLp.uniformIntegrable_of_identDistrib
    (μ := μ) (f := Z) (j := 0) (p := 1)
    (by simp) (by simp) hZ0 hident

/-- **Hansen Theorem 6.16, iid finite-power-moment maximum wrapper.**

If the power variables `Z_i` are identically distributed and `Z_0` is in `L¹`,
then `n⁻¹ max_{i<n} |Z_i|` on the nonnegative-power scale is `oₚ(1)`.
For Hansen's textbook statement, use `Z_i = |Y_i|^r`. -/
theorem max_norm_scaled_tendstoInMeasure_zero_of_identDistrib_memLp
    [IsFiniteMeasure μ] {Z : ℕ → Ω → ℝ}
    (hZ0 : MemLp (Z 0) 1 μ)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ) :
    TendstoInMeasure μ (scaledMaxNNNorm Z) atTop (fun _ => 0) := by
  exact max_norm_scaled_tendstoInMeasure_zero_of_uniformIntegrable_norm_r
    (μ := μ) (Z := Z)
    (uniformIntegrable_one_of_identDistrib_memLp
      (μ := μ) (Z := Z) hZ0 hident)

end HansenEconometrics
