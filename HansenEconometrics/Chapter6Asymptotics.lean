import Mathlib.Probability.CentralLimitTheorem
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.ProbabilityUtils

/-!
# Chapter 6 Asymptotics

This file collects chapter-facing large-sample theorem wrappers.  The current
public surface covers the iid scalar CLT and the finite-dimensional iid vector
CLT, using Mathlib's one-dimensional CLT plus the reusable Cramer-Wold bridge in
`AsymptoticUtils`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Real Topology ProbabilityTheory

namespace HansenEconometrics

open Matrix

section IidCLT

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
/-- Measurability of a fixed dot-product projection on finite-dimensional vectors. -/
private theorem measurable_dotProduct_right (a : k → ℝ) :
    Measurable (fun v : k → ℝ => v ⬝ᵥ a) := by
  classical
  simpa [dotProduct] using
    (continuous_finset_sum Finset.univ
      (fun i _ => (continuous_apply i).mul continuous_const)).measurable

omit [DecidableEq k] in
/-- A fixed dot-product projection of a square-integrable finite-dimensional vector is
square-integrable. -/
private theorem dotProduct_memLp_two
    {μ : Measure Ω} {Y : Ω → k → ℝ}
    (hY : MemLp Y 2 μ) (a : k → ℝ) :
    MemLp (fun ω => Y ω ⬝ᵥ a) 2 μ := by
  classical
  convert (memLp_finset_sum' (s := Finset.univ)
    (f := fun i ω => Y ω i * a i)
    (fun i _ => (hY.eval i).mul_const (a i))) using 1
  ext ω
  simp [dotProduct]

omit [DecidableEq k] in
/-- The covariance matrix of a square-integrable finite-dimensional vector is positive
semidefinite. -/
theorem covMat_posSemidef
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → k → ℝ}
    (hY : MemLp Y 2 μ) :
    (covMat μ Y).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian]
    ext i j
    simp [covMat, ProbabilityTheory.covariance_comm]
  · intro a
    have hvar := variance_dotProduct_eq_dotProduct_covMat_mulVec
      (μ := μ) (X := Y) a (fun i => hY.eval i)
    have hnonneg := ProbabilityTheory.variance_nonneg (fun ω => Y ω ⬝ᵥ a) μ
    rw [hvar] at hnonneg
    simpa using hnonneg

/-- **Hansen Theorem 6.3, scalar iid CLT wrapper.**

For iid real random variables with finite second moment, the centered sample
sum scaled by `1 / sqrt n` converges in distribution to the Gaussian with the
matching variance. This is a chapter-facing name for Mathlib's scalar CLT. -/
theorem iidScalarCLT_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 Var[Y 0; μ].toNNReal) ν)
    (hY : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ))⁻¹ * (∑ i ∈ Finset.range n, Y i ω - n * μ[Y 0]))
      atTop Z (fun _ => μ) ν :=
  ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub hZ hY hindep hident

omit [DecidableEq k] in
/-- **Hansen Theorem 6.3, scalar projection of the iid vector CLT.**

For iid finite-dimensional vectors with finite second moment, every fixed
linear projection of the centered sample sum satisfies the scalar CLT with
variance `a'Va`, where `V` is the covariance matrix of one draw. -/
theorem iidVectorProjectionCLT_tendstoInDistribution_gaussian_cov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {Y : ℕ → Ω → k → ℝ} (hY : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (a : k → ℝ) {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (a ⬝ᵥ (covMat μ (Y 0) *ᵥ a)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ))⁻¹ *
          (∑ i ∈ Finset.range n, Y i ω ⬝ᵥ a - n * (meanVec μ (Y 0) ⬝ᵥ a)))
      atTop Z (fun _ => μ) ν := by
  have hdot_meas := measurable_dotProduct_right (k := k) a
  have hident_scalar : ∀ i,
      IdentDistrib (fun ω => Y i ω ⬝ᵥ a) (fun ω => Y 0 ω ⬝ᵥ a) μ μ := by
    intro i
    simpa [Function.comp_def] using (hident i).comp hdot_meas
  have hindep_scalar :
      iIndepFun (fun i ω => Y i ω ⬝ᵥ a) μ := by
    simpa [Function.comp_def] using
      hindep.comp (fun _ v => v ⬝ᵥ a) (fun _ => hdot_meas)
  have hmean :
      μ[fun ω => Y 0 ω ⬝ᵥ a] = meanVec μ (Y 0) ⬝ᵥ a := by
    exact integral_dotProduct_eq_meanVec_dotProduct
      (μ := μ) (X := Y 0) a (fun i => (hY.eval i).integrable (by norm_num))
  have hZ' : HasLaw Z
      (gaussianReal 0 Var[fun ω => Y 0 ω ⬝ᵥ a; μ].toNNReal) ν := by
    rw [variance_dotProduct_eq_dotProduct_covMat_mulVec
      (μ := μ) (X := Y 0) a (fun i => hY.eval i)]
    exact hZ
  have hclt := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
    (P := μ) (P' := ν) (X := fun i ω => Y i ω ⬝ᵥ a)
    (Y := Z) hZ' (dotProduct_memLp_two (μ := μ) hY a) hindep_scalar hident_scalar
  convert hclt using 2 with n ω
  rw [hmean]

/-- **Hansen Theorem 6.3, finite-dimensional iid vector CLT.**

For iid `k`-vectors with finite second moment, the centered sample sum scaled
by `1 / sqrt n` converges in distribution to the centered multivariate Gaussian
with covariance matrix `covMat μ (Y 0)`. The theorem is stated in
`EuclideanSpace` form so it can be consumed directly by Cramer-Wold and Gaussian
law infrastructure. -/
theorem iidVectorCLT_tendstoInDistribution_multivariateGaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → k → ℝ} (hY : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        WithLp.toLp 2
          ((Real.sqrt (n : ℝ))⁻¹ •
            (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0))))
      atTop
      (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ)
      (multivariateGaussian 0 (covMat μ (Y 0))) := by
  refine cramerWold_tendstoInDistribution ?_ (by fun_prop) ?_
  · intro n
    have hsum : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ :=
      Finset.aemeasurable_fun_sum (Finset.range n)
        (fun i _ => (hident i).aemeasurable_fst)
    have hcenter : AEMeasurable
        (fun ω => ∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0)) μ :=
      hsum.sub aemeasurable_const
    have hscaled : AEMeasurable
        (fun ω => (Real.sqrt (n : ℝ))⁻¹ •
          (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0))) μ :=
      hcenter.const_smul ((Real.sqrt (n : ℝ))⁻¹)
    exact (PiLp.continuous_toLp 2 (fun _ : k => ℝ)).measurable.comp_aemeasurable
      hscaled
  · intro t
    let a : k → ℝ := t.ofLp
    have hLawDot := hasLaw_multivariateGaussian_zero_dotProduct
      (S := covMat μ (Y 0)) (covMat_posSemidef (μ := μ) hY) a
    have hLawDual : HasLaw
        (fun z : EuclideanSpace ℝ k =>
          (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ k) t) z)
        (gaussianReal 0 (a ⬝ᵥ (covMat μ (Y 0) *ᵥ a)).toNNReal)
        (multivariateGaussian 0 (covMat μ (Y 0))) := by
      refine hLawDot.congr (ae_of_all _ fun z => ?_)
      change inner ℝ t z = z.ofLp ⬝ᵥ a
      simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k) t.ofLp z.ofLp)
    have hscalar := iidVectorProjectionCLT_tendstoInDistribution_gaussian_cov
      (μ := μ) (ν := multivariateGaussian 0 (covMat μ (Y 0)))
      (Y := Y) hY hindep hident a hLawDual
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hscalar
    intro n
    exact ae_of_all μ (fun ω => by
      change (Real.sqrt (n : ℝ))⁻¹ *
          (∑ i ∈ Finset.range n, Y i ω ⬝ᵥ a - n * (meanVec μ (Y 0) ⬝ᵥ a)) =
        inner ℝ t
          (WithLp.toLp 2
            ((Real.sqrt (n : ℝ))⁻¹ •
              (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0))))
      calc
        (Real.sqrt (n : ℝ))⁻¹ *
              (∑ i ∈ Finset.range n, Y i ω ⬝ᵥ a -
                n * (meanVec μ (Y 0) ⬝ᵥ a)) =
            ((Real.sqrt (n : ℝ))⁻¹ •
              (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0))) ⬝ᵥ a := by
              rw [smul_dotProduct, sub_dotProduct, sum_dotProduct, smul_dotProduct,
                smul_eq_mul]
              simp
        _ = inner ℝ t
            (WithLp.toLp 2
              ((Real.sqrt (n : ℝ))⁻¹ •
                (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0)))) := by
              simpa [a] using
                (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k) t.ofLp
                  ((Real.sqrt (n : ℝ))⁻¹ •
                    (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0)))).symm)

end IidCLT

end HansenEconometrics
