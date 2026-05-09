import Mathlib.Probability.Independence.Conditional
import HansenEconometrics.Chapter2CondExp

/-!
# Chapter 2 Potential Outcomes

This file starts the variable-facing potential-outcomes API for Hansen Section 2.30.
The first public surface is stated as random-variable and almost-everywhere identities, matching the
Chapter 2 probability layer. Pointwise regular-conditional-distribution versions of Theorem 2.12 can
be built on top of this layer later.
-/

open scoped ENNReal Topology MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Ω β : Type*}

/-- Hansen Section 2.30 observed outcome for a binary treatment:
`Y = Y(1)` on treated units and `Y = Y(0)` on untreated units. -/
def observedOutcome (D : Ω → Bool) (Y0 Y1 : Ω → ℝ) : Ω → ℝ :=
  fun ω => if D ω then Y1 ω else Y0 ω

/-- Hansen Definition 2.6: individual treatment effect `Y(1) - Y(0)`. -/
def treatmentEffect (Y0 Y1 : Ω → ℝ) : Ω → ℝ :=
  fun ω => Y1 ω - Y0 ω

@[simp] theorem observedOutcome_true (Y0 Y1 : Ω → ℝ) :
    observedOutcome (fun _ => true) Y0 Y1 = Y1 := by
  funext ω
  simp [observedOutcome]

@[simp] theorem observedOutcome_false (Y0 Y1 : Ω → ℝ) :
    observedOutcome (fun _ => false) Y0 Y1 = Y0 := by
  funext ω
  simp [observedOutcome]

@[simp] theorem observedOutcome_of_treated
    {D : Ω → Bool} {Y0 Y1 : Ω → ℝ} {ω : Ω} (hD : D ω = true) :
    observedOutcome D Y0 Y1 ω = Y1 ω := by
  simp [observedOutcome, hD]

@[simp] theorem observedOutcome_of_untreated
    {D : Ω → Bool} {Y0 Y1 : Ω → ℝ} {ω : Ω} (hD : D ω = false) :
    observedOutcome D Y0 Y1 ω = Y0 ω := by
  simp [observedOutcome, hD]

@[simp] theorem treatmentEffect_eq_sub (Y0 Y1 : Ω → ℝ) :
    treatmentEffect Y0 Y1 = fun ω => Y1 ω - Y0 ω := rfl

section Probability

variable [MeasurableSpace Ω] [MeasurableSpace β]
variable {μ : Measure Ω}

/-- Average treatment effect: the population mean of the individual treatment effect.
Hansen Definition 2.7 calls this the average causal effect, `ACE`. -/
noncomputable def averageTreatmentEffect (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) : ℝ :=
  ∫ ω, treatmentEffect Y0 Y1 ω ∂μ

/-- Conditional mean of a potential outcome after conditioning on observed covariates. -/
noncomputable def potentialOutcomeMeanOn
    (μ : Measure Ω) (Yd : Ω → ℝ) (X : Ω → β) : Ω → ℝ :=
  condExpOn μ Yd X

/-- Conditional average treatment effect after conditioning on observed covariates.
Hansen Definition 2.8 writes this as the conditional average causal effect, `ACE(x)`. -/
noncomputable def conditionalAverageTreatmentEffectOn
    (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) (X : Ω → β) : Ω → ℝ :=
  condExpOn μ (treatmentEffect Y0 Y1) X

/-- Difference between the conditional means of the treated and untreated potential outcomes. -/
noncomputable def conditionalPotentialOutcomeContrastOn
    (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) (X : Ω → β) : Ω → ℝ :=
  fun ω => potentialOutcomeMeanOn μ Y1 X ω - potentialOutcomeMeanOn μ Y0 X ω

/-- A mean-independence bridge toward Hansen's conditional-independence assumption:
conditioning on treatment and covariates gives the same potential-outcome conditional means as
conditioning on covariates alone. CIA implies this condition under standard integrability and
regular-conditional-probability hypotheses. -/
def TreatmentMeanIndependentOn
    (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) (D : Ω → Bool) (X : Ω → β) : Prop :=
  condExpOn μ Y0 (fun ω => (D ω, X ω)) =ᵐ[μ] condExpOn μ Y0 X ∧
    condExpOn μ Y1 (fun ω => (D ω, X ω)) =ᵐ[μ] condExpOn μ Y1 X

/-- Hansen Definition 2.9, variable-facing conditional independence assumption.

This package records the conditional independence of treatment and each potential outcome after
conditioning on covariates, together with the measurability and integrability hypotheses needed to
turn that conditional-independence statement into the mean-independence bridge used by the CATE
theorems below. -/
structure PotentialOutcomeCIAOn
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y0 Y1 : Ω → ℝ) (D : Ω → Bool) (X : Ω → β) : Prop where
  /-- Covariates are measurable. -/
  x_measurable : Measurable X
  /-- Treatment is measurable. -/
  d_measurable : Measurable D
  /-- Untreated potential outcome is measurable. -/
  y0_measurable : Measurable Y0
  /-- Treated potential outcome is measurable. -/
  y1_measurable : Measurable Y1
  /-- Untreated potential outcome is integrable. -/
  y0_integrable : Integrable Y0 μ
  /-- Treated potential outcome is integrable. -/
  y1_integrable : Integrable Y1 μ
  /-- Treatment and the untreated potential outcome are conditionally independent given `X`. -/
  condIndep_y0 : D ⟂ᵢ[X, x_measurable; μ] Y0
  /-- Treatment and the treated potential outcome are conditionally independent given `X`. -/
  condIndep_y1 : D ⟂ᵢ[X, x_measurable; μ] Y1

omit [MeasurableSpace Ω] in
theorem conditioningSpace_pair_comm
    {D : Ω → Bool} {X : Ω → β} :
    conditioningSpace (fun ω => (D ω, X ω)) =
      conditioningSpace (fun ω => (X ω, D ω)) := by
  unfold conditioningSpace
  change MeasurableSpace.comap (fun ω => (D ω, X ω))
      ((inferInstance : MeasurableSpace Bool).prod (inferInstance : MeasurableSpace β)) =
    MeasurableSpace.comap (fun ω => (X ω, D ω))
      ((inferInstance : MeasurableSpace β).prod (inferInstance : MeasurableSpace Bool))
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_prodMk, sup_comm]

private theorem condExpOn_covariate_treatment_eq_of_condIndep
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hX : Measurable X) (hD : Measurable D) (hYmeas : Measurable Y)
    (hYint : Integrable Y μ)
    (hcond : D ⟂ᵢ[X, hX; μ] Y) :
    condExpOn μ Y (fun ω => (X ω, D ω)) =ᵐ[μ] condExpOn μ Y X := by
  have hpair : Measurable (fun ω => (X ω, D ω)) := hX.prod hD
  have hkernel_map :
      condDistrib Y (fun ω => (X ω, D ω)) μ =ᵐ[μ.map (fun ω => (X ω, D ω))]
        (condDistrib Y X μ).prodMkRight Bool := by
    exact (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
      (f := Y) (g := D) (k := X) hYmeas hD hX).mp hcond
  have hkernel :
      ∀ᵐ ω ∂μ, condDistrib Y (fun ω => (X ω, D ω)) μ (X ω, D ω) =
        (condDistrib Y X μ).prodMkRight Bool (X ω, D ω) :=
    ae_of_ae_map hpair.aemeasurable hkernel_map
  have hpair_ce :
      condExpOn μ Y (fun ω => (X ω, D ω)) =ᵐ[μ]
        fun ω => ∫ y, y ∂condDistrib Y (fun ω => (X ω, D ω)) μ (X ω, D ω) := by
    simpa [condExpOn, conditioningSpace] using
      (condExp_ae_eq_integral_condDistrib'
        (X := fun ω => (X ω, D ω)) (Y := Y) (μ := μ) hpair hYint)
  have hX_ce :
      condExpOn μ Y X =ᵐ[μ]
        fun ω => ∫ y, y ∂condDistrib Y X μ (X ω) := by
    simpa [condExpOn, conditioningSpace] using
      (condExp_ae_eq_integral_condDistrib'
        (X := X) (Y := Y) (μ := μ) hX hYint)
  have hintegral :
      (fun ω => ∫ y, y ∂condDistrib Y (fun ω => (X ω, D ω)) μ (X ω, D ω)) =ᵐ[μ]
        fun ω => ∫ y, y ∂condDistrib Y X μ (X ω) := by
    filter_upwards [hkernel] with ω hω
    rw [hω]
    rfl
  exact hpair_ce.trans (hintegral.trans hX_ce.symm)

/-- Conditional independence of treatment and each potential outcome given `X` implies the
mean-independence bridge used by the variable-facing CATE theorems. -/
theorem PotentialOutcomeCIAOn.toTreatmentMeanIndependentOn
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hcia : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    TreatmentMeanIndependentOn μ Y0 Y1 D X := by
  constructor
  · have hXD := condExpOn_covariate_treatment_eq_of_condIndep
      (μ := μ) (Y := Y0) (D := D) (X := X)
      hcia.x_measurable hcia.d_measurable hcia.y0_measurable hcia.y0_integrable
      hcia.condIndep_y0
    simpa [condExpOn, conditioningSpace_pair_comm] using hXD
  · have hXD := condExpOn_covariate_treatment_eq_of_condIndep
      (μ := μ) (Y := Y1) (D := D) (X := X)
      hcia.x_measurable hcia.d_measurable hcia.y1_measurable hcia.y1_integrable
      hcia.condIndep_y1
    simpa [condExpOn, conditioningSpace_pair_comm] using hXD

/-- The average treatment effect is the difference in the means of the two potential outcomes.
Hansen writes this quantity as `ACE`. -/
theorem averageTreatmentEffect_eq_integral_sub
    {Y0 Y1 : Ω → ℝ}
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    averageTreatmentEffect μ Y0 Y1 = ∫ ω, Y1 ω ∂μ - ∫ ω, Y0 ω ∂μ := by
  simp [averageTreatmentEffect, treatmentEffect, integral_sub hY1 hY0]

/-- Conditional average treatment effects are the difference in conditional means of the two
potential outcomes. Hansen writes this quantity as `ACE(x)`. -/
theorem conditionalAverageTreatmentEffectOn_eq_sub
    {Y0 Y1 : Ω → ℝ} {X : Ω → β}
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 X =ᵐ[μ]
      fun ω => potentialOutcomeMeanOn μ Y1 X ω - potentialOutcomeMeanOn μ Y0 X ω := by
  simpa [conditionalAverageTreatmentEffectOn, potentialOutcomeMeanOn,
      treatmentEffect, condExpOn] using
    (MeasureTheory.condExp_sub
      (μ := μ) (f := Y1) (g := Y0) hY1 hY0 (conditioningSpace X))

/-- CATE equals the reusable contrast between conditional potential-outcome means. -/
theorem conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
    {Y0 Y1 : Ω → ℝ} {X : Ω → β}
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 X =ᵐ[μ]
      conditionalPotentialOutcomeContrastOn μ Y0 Y1 X := by
  simpa [conditionalPotentialOutcomeContrastOn] using
    conditionalAverageTreatmentEffectOn_eq_sub (μ := μ) (X := X) hY1 hY0

/-- The average treatment effect is the mean of the CATE. Hansen writes this as the identity
`ACE = ∫ ACE(x) f(x) dx`; this is the potential-outcomes version of the tower property. -/
theorem averageTreatmentEffect_eq_integral_conditionalAverageTreatmentEffectOn
    {Y0 Y1 : Ω → ℝ} {X : Ω → β}
    (hX : Measurable X)
    [SigmaFinite (μ.trim (conditioningSpace_le hX))] :
    averageTreatmentEffect μ Y0 Y1 =
      ∫ ω, conditionalAverageTreatmentEffectOn μ Y0 Y1 X ω ∂μ := by
  exact
    (simple_law_iterated_expectation_rv
      (μ := μ) (Y := treatmentEffect Y0 Y1) (X := X) hX).symm

/-- The average treatment effect is also the mean of the conditional potential-outcome contrast.
This is the a.e. Lean version of Hansen's identity `ACE = ∫ ACE(x) f(x) dx` after rewriting
the CATE as a difference of conditional potential-outcome means. -/
theorem averageTreatmentEffect_eq_integral_conditionalPotentialOutcomeContrastOn
    {Y0 Y1 : Ω → ℝ} {X : Ω → β}
    (hX : Measurable X)
    [SigmaFinite (μ.trim (conditioningSpace_le hX))]
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    averageTreatmentEffect μ Y0 Y1 =
      ∫ ω, conditionalPotentialOutcomeContrastOn μ Y0 Y1 X ω ∂μ := by
  rw [averageTreatmentEffect_eq_integral_conditionalAverageTreatmentEffectOn (μ := μ) hX]
  exact integral_congr_ae
    (conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
      (μ := μ) (X := X) hY1 hY0)

/-- If treatment is mean-independent of potential outcomes after conditioning on `X`, then adding
the treatment indicator to the conditioning variables does not change the conditional
potential-outcome contrast. -/
theorem conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_of_meanIndependent
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hmean : TreatmentMeanIndependentOn μ Y0 Y1 D X) :
    conditionalPotentialOutcomeContrastOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalPotentialOutcomeContrastOn μ Y0 Y1 X := by
  filter_upwards [hmean.2, hmean.1] with ω hY1 hY0
  simp [conditionalPotentialOutcomeContrastOn, potentialOutcomeMeanOn, hY1, hY0]

/-- Mean-independence bridge for the variable-facing version of Hansen Theorem 2.12. Under the
mean-independence consequence of CIA, the potential-outcome contrast after conditioning on
`(D, X)` equals the conditional average treatment effect after conditioning on `X`. -/
theorem conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_cate_of_meanIndependent
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hmean : TreatmentMeanIndependentOn μ Y0 Y1 D X)
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    conditionalPotentialOutcomeContrastOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalAverageTreatmentEffectOn μ Y0 Y1 X :=
  (conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_of_meanIndependent
    (μ := μ) hmean).trans <|
      (conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
        (μ := μ) (X := X) hY1 hY0).symm

/-- Direct CATE bridge for the variable-facing version of Hansen Theorem 2.12. Under the
mean-independence consequence of CIA, conditioning the treatment effect on `(D, X)` gives the same
conditional average treatment effect as conditioning on `X` alone. -/
theorem conditionalAverageTreatmentEffectOn_treatment_covariates_eq_of_meanIndependent
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hmean : TreatmentMeanIndependentOn μ Y0 Y1 D X)
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalAverageTreatmentEffectOn μ Y0 Y1 X :=
  (conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
    (μ := μ) (X := fun ω => (D ω, X ω)) hY1 hY0).trans <|
      (conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_of_meanIndependent
        (μ := μ) hmean).trans <|
        (conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
          (μ := μ) (X := X) hY1 hY0).symm

/-- CIA-facing version of the variable-conditioned potential-outcome contrast theorem.
Conditional independence of treatment and potential outcomes given covariates implies that adding
treatment to the conditioning variables does not change the potential-outcome contrast. -/
theorem conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_of_CIA
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hcia : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    conditionalPotentialOutcomeContrastOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalPotentialOutcomeContrastOn μ Y0 Y1 X :=
  conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_of_meanIndependent
    (μ := μ) hcia.toTreatmentMeanIndependentOn

/-- CIA-facing version of Hansen Theorem 2.12 at the variable/a.e. layer. Under conditional
independence of treatment and potential outcomes given covariates, the treatment-and-covariate
potential-outcome contrast equals the conditional average treatment effect. -/
theorem conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_cate_of_CIA
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hcia : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    conditionalPotentialOutcomeContrastOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalAverageTreatmentEffectOn μ Y0 Y1 X :=
  conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_cate_of_meanIndependent
    (μ := μ) hcia.toTreatmentMeanIndependentOn hcia.y1_integrable hcia.y0_integrable

/-- Direct CIA-facing CATE bridge for Hansen Theorem 2.12: under conditional independence,
conditioning the treatment effect on `(D, X)` gives the same CATE as conditioning on `X` alone. -/
theorem conditionalAverageTreatmentEffectOn_treatment_covariates_eq_of_CIA
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hcia : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalAverageTreatmentEffectOn μ Y0 Y1 X :=
  conditionalAverageTreatmentEffectOn_treatment_covariates_eq_of_meanIndependent
    (μ := μ) hcia.toTreatmentMeanIndependentOn hcia.y1_integrable hcia.y0_integrable

end Probability

end HansenEconometrics
