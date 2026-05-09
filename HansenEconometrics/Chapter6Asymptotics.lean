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

section Consistency

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
variable [PseudoEMetricSpace E]

/-- **Hansen Definition 6.3, consistency.**

An estimator sequence is consistent for `θ` when it converges to the constant
limit `θ` in measure. This is a chapter-facing name for the Mathlib
`TendstoInMeasure` idiom used throughout the asymptotic files. -/
def Consistent (μ : Measure Ω) (θhat : ℕ → Ω → E) (θ : E) : Prop :=
  TendstoInMeasure μ θhat atTop (fun _ => θ)

/-- Unfolding lemma for the chapter-facing consistency definition. -/
theorem consistent_iff_tendstoInMeasure
    {μ : Measure Ω} {θhat : ℕ → Ω → E} {θ : E} :
    Consistent μ θhat θ ↔ TendstoInMeasure μ θhat atTop (fun _ => θ) :=
  Iff.rfl

/-- Projection from the chapter-facing consistency definition to the underlying
Mathlib convergence-in-measure statement. -/
theorem Consistent.tendstoInMeasure
    {μ : Measure Ω} {θhat : ℕ → Ω → E} {θ : E}
    (h : Consistent μ θhat θ) :
    TendstoInMeasure μ θhat atTop (fun _ => θ) :=
  h

end Consistency

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

/-- **Chapter 6 vector CLT reduction by Cramér-Wold.**

If every fixed scalar projection of a finite-dimensional statistic converges to
the matching scalar projection of a centered multivariate Gaussian, then the
whole statistic converges to that multivariate Gaussian. This is the
chapter-facing endpoint used by iid and future triangular-array CLT wrappers. -/
theorem vectorCLT_tendstoInDistribution_multivariateGaussian_of_projections
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hT : ∀ n, AEMeasurable (T n) μ)
    (hproj : ∀ a : k → ℝ,
      TendstoInDistribution
        (fun n ω => T n ω ⬝ᵥ a)
        atTop
        (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a)
        (fun _ => μ)
        (multivariateGaussian 0 S)) :
    TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (T n ω))
      atTop
      (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ)
      (multivariateGaussian 0 S) := by
  refine cramerWold_tendstoInDistribution ?_ (by fun_prop) ?_
  · intro n
    exact (PiLp.continuous_toLp 2 (fun _ : k => ℝ)).measurable.comp_aemeasurable (hT n)
  · intro t
    let a : k → ℝ := t.ofLp
    have hscalar := hproj a
    refine TendstoInDistribution.congr ?_ ?_ hscalar
    · intro n
      exact ae_of_all μ (fun ω => by
        change T n ω ⬝ᵥ a =
          inner ℝ t (WithLp.toLp 2 (T n ω))
        simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k)
          t.ofLp (T n ω)).symm)
    · exact ae_of_all (multivariateGaussian 0 S) (fun z => by
        change z.ofLp ⬝ᵥ a = inner ℝ t z
        simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k)
          t.ofLp z.ofLp).symm)

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

section BestUnbiased

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Hansen Theorem 6.11, sample-mean sharpness face.**

For pairwise independent identically distributed square-integrable scalar
observations, the variance of the finite-sample average is `1 / n` times the
variance of one draw. This formalizes the sharp sample-mean variance identity
around Hansen's best-unbiased-estimation theorem; the full lower bound for
arbitrary unbiased estimators is a separate efficiency statement. -/
theorem iidSampleMean_variance_eq_inv_card_mul
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty ι]
    {Z : ι → Ω → ℝ} (j : ι)
    (hZ : ∀ i, MemLp (Z i) 2 μ)
    (hindep : Pairwise (fun i j => Z i ⟂ᵢ[μ] Z j))
    (hident : ∀ i, IdentDistrib (Z i) (Z j) μ μ) :
    Var[fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω; μ] =
      (Fintype.card ι : ℝ)⁻¹ * Var[Z j; μ] := by
  classical
  let c : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hpair : Set.Pairwise (↑(Finset.univ : Finset ι) : Set ι)
      (fun i j => Z i ⟂ᵢ[μ] Z j) := by
    intro i _ j _ hij
    exact hindep hij
  have hvarsum := ProbabilityTheory.IndepFun.variance_sum
    (μ := μ) (X := Z) (s := Finset.univ)
    (fun i _ => hZ i) hpair
  have hsumvar :
      (∑ i, Var[Z i; μ]) = (Fintype.card ι : ℝ) * Var[Z j; μ] := by
    calc
      (∑ i, Var[Z i; μ]) = ∑ _i : ι, Var[Z j; μ] := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact (hident i).variance_eq
      _ = (Fintype.card ι : ℝ) * Var[Z j; μ] := by
        simp
  have hsample_eq :
      (fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω) =
        fun ω => c * (∑ i, Z i) ω := by
    ext ω
    simp [c]
  rw [hsample_eq]
  calc
    Var[fun ω => c * (∑ i, Z i) ω; μ]
        = c ^ 2 * Var[(∑ i, Z i); μ] := by
          rw [ProbabilityTheory.variance_const_mul]
    _ = c ^ 2 * (∑ i, Var[Z i; μ]) := by
          rw [hvarsum]
    _ = c ^ 2 * ((Fintype.card ι : ℝ) * Var[Z j; μ]) := by
          rw [hsumvar]
    _ = (Fintype.card ι : ℝ)⁻¹ * Var[Z j; μ] := by
          have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          dsimp [c]
          field_simp [hcard]

/-- **Hansen Theorem 6.11, covariance-matrix sample-mean sharpness face.**

For finite-dimensional square-integrable observations whose coordinates are
pairwise independent across distinct observations and whose one-draw covariance
matrix is common across observations, the covariance matrix of the sample mean
is exactly `1 / n` times that one-draw covariance matrix. This is the
matrix-valued version of the sample-mean sharpness identity around Hansen's
best-unbiased-estimation theorem. -/
theorem iidSampleMean_covMat_eq_inv_card_smul
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty ι]
    {Z : ι → Ω → k → ℝ} (j : ι)
    (hZ : ∀ i a, MemLp (fun ω => Z i ω a) 2 μ)
    (hindep : ∀ a b, Pairwise (fun i l =>
      (fun ω => Z i ω a) ⟂ᵢ[μ] (fun ω => Z l ω b)))
    (hcov : ∀ i a b,
      cov[fun ω => Z i ω a, fun ω => Z i ω b; μ] =
        cov[fun ω => Z j ω a, fun ω => Z j ω b; μ]) :
    covMat μ (fun ω a => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω a) =
      (Fintype.card ι : ℝ)⁻¹ • covMat μ (Z j) := by
  classical
  ext a b
  let c : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hsumcov :
      (∑ i : ι, ∑ l : ι, cov[fun ω => Z i ω a, fun ω => Z l ω b; μ]) =
        (Fintype.card ι : ℝ) *
          cov[fun ω => Z j ω a, fun ω => Z j ω b; μ] := by
    calc
      (∑ i : ι, ∑ l : ι, cov[fun ω => Z i ω a, fun ω => Z l ω b; μ])
          = ∑ i : ι, cov[fun ω => Z i ω a, fun ω => Z i ω b; μ] := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.sum_eq_single i]
            · intro l _ hli
              exact (hindep a b (Ne.symm hli)).covariance_eq_zero (hZ i a) (hZ l b)
            · intro hi
              simp at hi
      _ = ∑ _i : ι, cov[fun ω => Z j ω a, fun ω => Z j ω b; μ] := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact hcov i a b
      _ = (Fintype.card ι : ℝ) *
            cov[fun ω => Z j ω a, fun ω => Z j ω b; μ] := by
            simp
  have hsum :
      cov[fun ω => ∑ i : ι, Z i ω a, fun ω => ∑ i : ι, Z i ω b; μ] =
        (Fintype.card ι : ℝ) *
          cov[fun ω => Z j ω a, fun ω => Z j ω b; μ] := by
    rw [ProbabilityTheory.covariance_fun_sum_fun_sum]
    · exact hsumcov
    · intro i
      exact hZ i a
    · intro i
      exact hZ i b
  calc
    covMat μ (fun ω a => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω a) a b
        = c ^ 2 *
            cov[fun ω => ∑ i : ι, Z i ω a, fun ω => ∑ i : ι, Z i ω b; μ] := by
          dsimp [covMat, c]
          rw [ProbabilityTheory.covariance_const_mul_left,
            ProbabilityTheory.covariance_const_mul_right]
          ring
    _ = c ^ 2 *
          ((Fintype.card ι : ℝ) *
            cov[fun ω => Z j ω a, fun ω => Z j ω b; μ]) := by
          rw [hsum]
    _ = ((Fintype.card ι : ℝ)⁻¹ • covMat μ (Z j)) a b := by
          have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          dsimp [c, covMat]
          field_simp [hcard]

/-- IID-facing wrapper for `iidSampleMean_covMat_eq_inv_card_smul`.

Vector identical distribution supplies the common one-draw covariance matrix,
while the independence assumption is kept at the coordinate level needed by the
covariance calculation. -/
theorem iidSampleMean_covMat_eq_inv_card_smul_of_identDistrib
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty ι]
    {Z : ι → Ω → k → ℝ} (j : ι)
    (hZ : ∀ i a, MemLp (fun ω => Z i ω a) 2 μ)
    (hindep : ∀ a b, Pairwise (fun i l =>
      (fun ω => Z i ω a) ⟂ᵢ[μ] (fun ω => Z l ω b)))
    (hident : ∀ i, IdentDistrib (Z i) (Z j) μ μ) :
    covMat μ (fun ω a => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω a) =
      (Fintype.card ι : ℝ)⁻¹ • covMat μ (Z j) :=
  iidSampleMean_covMat_eq_inv_card_smul (μ := μ) (j := j) hZ hindep
    (fun i a b => identDistrib_covariance_apply_eq (hident i) a b)

end BestUnbiased

section ArrayCLT

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {k : Type*} [Fintype k] [DecidableEq k]

/-- Projection-level sufficient condition package for Hansen's multivariate
Lindeberg CLT.

The scalar Lindeberg proof obligations are represented by the projection CLT
field. This package keeps the chapter-facing multivariate endpoint usable while
leaving the scalar triangular-array Lindeberg theorem as the remaining
probability-engine task. -/
structure MultivariateLindebergCLTConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ → Ω → (k → ℝ)) (S : Matrix k k ℝ) where
  /-- A.e. measurability of the normalized array statistic at each sample size. -/
  aemeasurable : ∀ n, AEMeasurable (T n) μ
  /-- Scalar projection CLTs against the matching multivariate Gaussian law. -/
  projection_clt : ∀ a : k → ℝ,
    TendstoInDistribution
      (fun n ω => T n ω ⬝ᵥ a)
      atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a)
      (fun _ => μ)
      (multivariateGaussian 0 S)

/-- **Hansen Theorem 6.4, multivariate Lindeberg CLT endpoint.**

Once scalar projection Lindeberg CLTs are available for a normalized triangular
array statistic, Cramér-Wold gives the corresponding multivariate Gaussian
limit. The textbook normalization `V_n^{-1/2} ∑ᵢ Y_{ni}` is represented by the
user-supplied statistic `T`. -/
theorem multivariateLindebergCLT_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → (k → ℝ)} {S : Matrix k k ℝ}
    (h : MultivariateLindebergCLTConditions μ T S) :
    TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (T n ω))
      atTop
      (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ)
      (multivariateGaussian 0 S) :=
  vectorCLT_tendstoInDistribution_multivariateGaussian_of_projections
    h.aemeasurable h.projection_clt

/-- Projection-level sufficient condition package for Hansen's heterogeneous
array CLT. The statistic `T n` is typically `√n * \bar Y_n`; the limit
covariance is the supplied matrix `V`. -/
abbrev HeterogeneousArrayCLTConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ → Ω → (k → ℝ)) (V : Matrix k k ℝ) :=
  MultivariateLindebergCLTConditions μ T V

/-- **Hansen Theorem 6.5, heterogeneous-array CLT endpoint.**

This is the multivariate Cramér-Wold assembly for the heterogeneous-array CLT:
scalar projection CLTs for the normalized sample average imply convergence to
the centered Gaussian with covariance `V`. -/
theorem heterogeneousArrayCLT_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → (k → ℝ)} {V : Matrix k k ℝ}
    (h : HeterogeneousArrayCLTConditions μ T V) :
    TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (T n ω))
      atTop
      (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ)
      (multivariateGaussian 0 V) :=
  multivariateLindebergCLT_tendstoInDistribution h

end ArrayCLT

end HansenEconometrics
