import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Tight

/-!
# Stochastic-order helpers for Chapter 6

This module adds a small norm-valued companion to the real-valued
`BoundedInProbability` API in `HansenEconometrics.AsymptoticUtils`.  The public
surface is intentionally minimal: tightness from convergence in distribution,
scaling by deterministic constants converging to zero, and a law-relabeling
bridge for named limit laws.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Function

namespace HansenEconometrics

variable {Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {ν : Measure Ω'}

section NormBounded

variable [NormedAddCommGroup E]

/-- Norm-valued boundedness in probability (`Oₚ(1)`).

For every probability tolerance `δ`, the norm tails are eventually bounded by a
deterministic radius.  This is the vector/normed-space analogue of the
real-valued `BoundedInProbability` already used in Chapter 7. -/
def BoundedInProbabilityNorm (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ δ : ℝ≥0∞, 0 < δ → ∃ M : ℝ, 0 < M ∧
    ∀ᶠ n in atTop, μ {ω | M ≤ ‖X n ω‖} ≤ δ

/-- Convergence in distribution implies norm-boundedness in probability.

This is the tightness bridge needed by Delta-method arguments.  It is the
normed-space analogue of `BoundedInProbability.of_tendstoInDistribution`. -/
theorem BoundedInProbabilityNorm.of_tendstoInDistribution
    [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] [CompleteSpace E] [BorelSpace E]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z (fun _ => μ) ν) :
    BoundedInProbabilityNorm μ X := by
  let law : ℕ → ProbabilityMeasure E := fun n =>
    ⟨μ.map (X n), Measure.isProbabilityMeasure_map (h.forall_aemeasurable n)⟩
  let lawZ : ProbabilityMeasure E :=
    ⟨ν.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩
  have hlaw : Tendsto law atTop (𝓝 lawZ) := by
    simpa [law, lawZ] using h.tendsto
  have hcompact_insert : IsCompact (insert lawZ (Set.range law)) :=
    hlaw.isCompact_insert_range
  have hclosure_subset : closure (Set.range law) ⊆ insert lawZ (Set.range law) :=
    closure_minimal (by intro x hx; exact Or.inr hx) hcompact_insert.isClosed
  have hcompact_closure : IsCompact (closure (Set.range law)) :=
    hcompact_insert.of_isClosed_subset isClosed_closure hclosure_subset
  have htight : IsTightMeasureSet
      {((ρ : ProbabilityMeasure E) : Measure E) | ρ ∈ Set.range law} :=
    isTightMeasureSet_of_isCompact_closure (S := Set.range law) hcompact_closure
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  intro δ hδ
  obtain ⟨K, hKcompact, hKtail⟩ := htight δ hδ
  obtain ⟨M, hMpos, hKball⟩ := hKcompact.isBounded.subset_ball_lt 0 (0 : E)
  refine ⟨M, hMpos, Eventually.of_forall ?_⟩
  intro n
  have htail_meas : MeasurableSet {x : E | M ≤ ‖x‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have htail_subset : {x : E | M ≤ ‖x‖} ⊆ Kᶜ := by
    intro x hx hxK
    have hxball := hKball hxK
    have hxlt : ‖x‖ < M := by
      simpa [Metric.mem_ball, dist_eq_norm] using hxball
    exact (not_le_of_gt hxlt) hx
  have hlawK : ((law n : ProbabilityMeasure E) : Measure E) Kᶜ ≤ δ := by
    exact hKtail ((law n : ProbabilityMeasure E) : Measure E)
      ⟨law n, ⟨n, rfl⟩, rfl⟩
  have hmap_tail :
      (μ.map (X n)) {x : E | M ≤ ‖x‖} =
        μ {ω | M ≤ ‖X n ω‖} := by
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) htail_meas]
    rfl
  calc
    μ {ω | M ≤ ‖X n ω‖}
        = (μ.map (X n)) {x : E | M ≤ ‖x‖} := hmap_tail.symm
    _ = ((law n : ProbabilityMeasure E) : Measure E) {x : E | M ≤ ‖x‖} := rfl
    _ ≤ ((law n : ProbabilityMeasure E) : Measure E) Kᶜ := measure_mono htail_subset
    _ ≤ δ := hlawK

/-- A deterministic scalar sequence converging to zero times an `Oₚ(1)`
normed sequence is `oₚ(1)`. -/
theorem BoundedInProbabilityNorm.tendstoInMeasure_const_smul_zero
    [NormedSpace ℝ E]
    {X : ℕ → Ω → E} {c : ℕ → ℝ}
    (hX : BoundedInProbabilityNorm μ X)
    (hc : Tendsto c atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n ω => c n • X n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  obtain ⟨M, hMpos, hMev⟩ := hX δ hδ
  have hεM : 0 < ε / M := div_pos hε hMpos
  have hcsmall : ∀ᶠ n in atTop, ‖c n‖ < ε / M := by
    have hnorm : Tendsto (fun n => ‖c n‖) atTop (𝓝 ‖(0 : ℝ)‖) := hc.norm
    have hεM' : ‖(0 : ℝ)‖ < ε / M := by simpa using hεM
    exact hnorm.eventually_lt_const hεM'
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hMev.and hcsmall)
  refine ⟨N, fun n hnN => ?_⟩
  have hn_tail : μ {ω | M ≤ ‖X n ω‖} ≤ δ := (hN n hnN).1
  have hn_c : ‖c n‖ < ε / M := (hN n hnN).2
  have hcover :
      {ω | ε ≤ dist (c n • X n ω) 0} ⊆ {ω | M ≤ ‖X n ω‖} := by
    intro ω hω
    by_contra hlt
    have hXlt : ‖X n ω‖ < M := not_le.mp hlt
    have hmul_lt : ‖c n‖ * ‖X n ω‖ < (ε / M) * M := by
      calc
        ‖c n‖ * ‖X n ω‖ ≤ (ε / M) * ‖X n ω‖ :=
          mul_le_mul_of_nonneg_right hn_c.le (norm_nonneg _)
        _ < (ε / M) * M :=
          mul_lt_mul_of_pos_left hXlt hεM
    have hdist_lt : dist (c n • X n ω) 0 < ε := by
      calc
        dist (c n • X n ω) 0 = ‖c n • X n ω‖ := by simp [dist_eq_norm]
        _ = ‖c n‖ * ‖X n ω‖ := norm_smul _ _
        _ < (ε / M) * M := hmul_lt
        _ = ε := div_mul_cancel₀ ε hMpos.ne'
    exact (not_le_of_gt hdist_lt) hω
  exact le_trans (measure_mono hcover) hn_tail

end NormBounded

section LawRelabel

/-- Relabel a distributional limit by its law.

If `Tₙ ⇒ Z` under an auxiliary probability space and `Z` has law `η`, then
`Tₙ ⇒ id` under `η`.  This generalizes the real-valued bridge used in Chapter 7. -/
theorem tendstoInDistribution_id_of_hasLaw_limit
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    [IsProbabilityMeasure ν] {η : Measure E} [IsProbabilityMeasure η]
    {T : ℕ → Ω → E} {Z : Ω' → E}
    (hT : TendstoInDistribution T atTop Z P ν)
    (hZ : HasLaw Z η ν) :
    TendstoInDistribution T atTop (fun x : E => x) P η := by
  refine ⟨hT.forall_aemeasurable, ?_, ?_⟩
  · fun_prop
  · have htarget :
      (⟨ν.map Z, Measure.isProbabilityMeasure_map hT.aemeasurable_limit⟩ :
          ProbabilityMeasure E) =
        ⟨η.map (fun x : E => x), Measure.isProbabilityMeasure_map (by fun_prop)⟩ := by
      apply Subtype.ext
      simp [hZ.map_eq]
    simpa [htarget] using hT.tendsto

end LawRelabel

end HansenEconometrics
