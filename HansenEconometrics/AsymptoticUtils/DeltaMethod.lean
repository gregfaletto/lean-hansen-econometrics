import Mathlib.Analysis.Calculus.FDeriv.Basic
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.AsymptoticUtils.StochasticOrder
import HansenEconometrics.ProbabilityUtils

/-!
# Delta-method and smooth-function asymptotic wrappers

This module provides the Chapter 6-facing Delta-method surface.  The main
distributional theorem is stated in proof-engine form: differentiability supplies
the deterministic little-o remainder, while the stochastic theorem composes the
linearized limit with an explicit `oₚ(1)` remainder.  This keeps the public API
usable without introducing a parallel stochastic-order framework.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Function
open scoped Matrix MatrixOrder RealInnerProductSpace

namespace HansenEconometrics

variable {Ω Ω' E F : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {ν : Measure Ω'}

section DeterministicRemainder

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

/-- Deterministic Delta-method remainder from Mathlib's Fréchet derivative API.

This is the analytic core of Hansen Theorem 6.8: after subtracting the linear
approximation, the remainder is little-o of the input displacement. -/
theorem deltaMethod_remainder_isLittleO
    {g : E → F} {G : E →L[ℝ] F} {θ : E}
    (hg : HasFDerivAt g G θ) :
    (fun x => g x - g θ - G (x - θ)) =o[𝓝 θ] (fun x => x - θ) :=
  hg.isLittleO

end DeterministicRemainder

section DeltaDistribution

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F]

/-- Delta-method Slutsky wrapper.

If the linearized statistic `Tₙ` converges in distribution and the nonlinear
statistic differs from `G Tₙ` by an `oₚ(1)` remainder, then the nonlinear
statistic has the linear image of the limit.  The deterministic source of the
remainder is `deltaMethod_remainder_isLittleO`. -/
theorem deltaMethod_tendstoInDistribution
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : ℕ → Ω → E} {Z : Ω' → E} {R : ℕ → Ω → F} {G : E →L[ℝ] F}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hR : TendstoInMeasure μ R atTop (fun _ => 0))
    (hR_meas : ∀ n, AEMeasurable (R n) μ) :
    TendstoInDistribution
      (fun n ω => G (T n ω) + R n ω)
      atTop (fun ω => G (Z ω)) (fun _ => μ) ν := by
  have hG :
      TendstoInDistribution
        (fun n => G ∘ T n) atTop (G ∘ Z) (fun _ => μ) ν :=
    hT.continuous_comp G.continuous
  simpa [Function.comp_def] using
    hG.add_of_tendstoInMeasure_const (c := 0) hR hR_meas

end DeltaDistribution

section SmoothConsistency

variable [IsFiniteMeasure μ]
  [PseudoEMetricSpace E] [PseudoEMetricSpace F] [TopologicalSpace.PseudoMetrizableSpace F]

/-- Hansen Theorem 6.9, proof-engine form: smooth-function consistency from
consistency of the input and continuity at the target. -/
theorem smoothFunction_consistency
    {θhat : ℕ → Ω → E} {θ : E} {g : E → F}
    (hθ_meas : ∀ n, AEStronglyMeasurable (θhat n) μ)
    (hgθ_meas : ∀ n, AEStronglyMeasurable (fun ω => g (θhat n ω)) μ)
    (hθ : TendstoInMeasure μ θhat atTop (fun _ => θ))
    (hg : ContinuousAt g θ) :
    TendstoInMeasure μ (fun n ω => g (θhat n ω)) atTop (fun _ => g θ) :=
  tendstoInMeasure_continuousAt_const_comp hθ_meas hgθ_meas hθ hg

end SmoothConsistency

section GaussianSmoothFunction

variable {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
  {S : Matrix k k ℝ} {R : Matrix q k ℝ}

/-- Hansen Theorem 6.10, Gaussian proof-engine form.

The input statistic converges to a centered multivariate Gaussian.  The nonlinear
statistic is represented as its matrix-linear Delta-method image plus an
`oₚ(1)` remainder.  The conclusion is stated directly with the named Gaussian
law of the image, using `hasLaw_multivariateGaussian_zero_linearMap`. -/
theorem smoothFunction_asymptoticNormality_gaussian
    {T : ℕ → Ω → EuclideanSpace ℝ k}
    {Y : ℕ → Ω → EuclideanSpace ℝ q}
    [IsProbabilityMeasure μ]
    (hS : S.PosSemidef)
    (hT :
      TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ) (multivariateGaussian 0 S))
    (hrem :
      TendstoInMeasure μ
        (Y - fun n ω => matrixContinuousLinearMap R (T n ω))
        atTop (fun _ => 0))
    (hY_meas : ∀ n, AEMeasurable (Y n) μ) :
    TendstoInDistribution Y atTop (fun z : EuclideanSpace ℝ q => z)
      (fun _ => μ) (multivariateGaussian 0 (R * S * Rᵀ)) := by
  have hlin :
      TendstoInDistribution
        (fun n => matrixContinuousLinearMap R ∘ T n)
        atTop (matrixContinuousLinearMap R ∘ fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ) (multivariateGaussian 0 S) :=
    hT.continuous_comp (matrixContinuousLinearMap R).continuous
  have hLaw :
      HasLaw (fun z : EuclideanSpace ℝ k => matrixContinuousLinearMap R z)
        (multivariateGaussian 0 (R * S * Rᵀ)) (multivariateGaussian 0 S) := by
    simpa [matrixContinuousLinearMap, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := q) hS R
  have htarget :
      TendstoInDistribution
        (fun n ω => matrixContinuousLinearMap R (T n ω))
        atTop (fun z : EuclideanSpace ℝ q => z)
        (fun _ => μ) (multivariateGaussian 0 (R * S * Rᵀ)) := by
    simpa [Function.comp_def] using
      tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ q) hlin hLaw
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => matrixContinuousLinearMap R (T n ω))
    (Y := Y)
    (Z := fun z : EuclideanSpace ℝ q => z)
    htarget hrem hY_meas

end GaussianSmoothFunction

end HansenEconometrics
