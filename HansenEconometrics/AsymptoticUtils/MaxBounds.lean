import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Algebra.Order.Ring.Star

/-!
# Uniform-integrability tail controls for Chapter 6 maximum bounds

This module records the Mathlib-facing uniform-integrability layer needed for
Hansen Theorem 6.16.  The main public theorem is stated for the nonnegative
power variable `|Y_i|^r`: if that sequence is uniformly integrable in `L¹`, its
tails have the uniform `eLpNorm` control used by the standard maximum argument.
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

/-- Proof-engine form of Hansen Theorem 6.16.

Mathlib's `UniformIntegrable.spec` supplies the tail seminorm bound; the finite
maximum/union-bound argument is represented by `hmax`.  This keeps the theorem
usable by downstream asymptotic proofs while isolating the only remaining
chapter-specific combinatorial inequality. -/
theorem max_norm_scaled_tendstoInMeasure_zero_of_uniformIntegrable_norm_r
    {Z : ℕ → Ω → ℝ}
    (hZ : UniformIntegrable Z 1 μ)
    (hmax :
      ∀ ⦃ε : ℝ⦄, 0 < ε →
      ∀ ⦃δ : ℝ≥0∞⦄, 0 < δ →
        (∃ C : ℝ≥0,
          ∀ i : ℕ,
            eLpNorm ({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) 1 μ ≤
              ENNReal.ofReal (ε * δ.toReal / 2)) →
        ∀ᶠ n in atTop,
          μ {ω | ε ≤ dist (scaledMaxNNNorm Z n ω) 0} ≤ δ) :
    TendstoInMeasure μ (scaledMaxNNNorm Z) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  by_cases hδtop : δ = ∞
  · exact ⟨0, fun n _ => by simp [hδtop]⟩
  have hδreal : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
  have htol : 0 < ε * δ.toReal / 2 := by positivity
  exact eventually_atTop.1 ((hmax hε hδ) (uniformIntegrable_tail_eLpNorm_one hZ htol))

end HansenEconometrics
