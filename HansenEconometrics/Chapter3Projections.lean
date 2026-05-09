import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.Chapter3LeastSquaresAlgebra

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k l : Type*}
variable [Fintype n]

variable [Fintype k] [DecidableEq k]

/-- Hansen Section 3.11: the OLS projection / hat matrix `P = X (Xᵀ X)⁻¹ Xᵀ`. -/
noncomputable def hatMatrix (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] : Matrix n n ℝ :=
  X * ⅟ (Xᵀ * X) * Xᵀ

/-- Hansen Section 3.12: the annihilator matrix `M = I - P`. -/
noncomputable def annihilatorMatrix (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    Matrix n n ℝ :=
  (1 : Matrix n n ℝ) - hatMatrix X

/-- Hansen Theorem 3.3.1: the hat matrix is symmetric. -/
theorem hatMatrix_transpose
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    (hatMatrix X)ᵀ = hatMatrix X := by
  unfold hatMatrix
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, inv_gram_transpose]
  simp [Matrix.mul_assoc]

/-- Hansen Section 3.12 / Exercise 3.8: the annihilator matrix is symmetric. -/
theorem annihilatorMatrix_transpose
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    (annihilatorMatrix X)ᵀ = annihilatorMatrix X := by
  simp [annihilatorMatrix, Matrix.transpose_sub, hatMatrix_transpose (X := X)]

/-- Hansen Section 3.11: the closed-form OLS fitted vector equals `P Y`. -/
theorem hat_mul_y_eq_closed_form_fit
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    hatMatrix X *ᵥ y = X *ᵥ ((⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)) := by
  unfold hatMatrix
  calc
    (X * ⅟ (Xᵀ * X) * Xᵀ) *ᵥ y = (X * (⅟ (Xᵀ * X) * Xᵀ)) *ᵥ y := by rw [Matrix.mul_assoc]
    _ = X *ᵥ ((⅟ (Xᵀ * X) * Xᵀ) *ᵥ y) := by
          simp
    _ = X *ᵥ ((⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)) := by
          simp

/-- Hansen equation (3.23): the closed-form OLS residual vector equals `M Y`. -/
theorem annihilator_mul_y_eq_closed_form_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    annihilatorMatrix X *ᵥ y = y - X *ᵥ ((⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)) := by
  unfold annihilatorMatrix
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hat_mul_y_eq_closed_form_fit]

/-- Hansen Section 3.11: the hat matrix fixes the regressor matrix, `P X = X`. -/
theorem hat_mul_X
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    hatMatrix X * X = X := by
  unfold hatMatrix
  calc
    X * ⅟ (Xᵀ * X) * Xᵀ * X = X * (⅟ (Xᵀ * X) * (Xᵀ * X)) := by
      simp [Matrix.mul_assoc]
    _ = X * (1 : Matrix k k ℝ) := by rw [invOf_mul_self]
    _ = X := by simp

/-- Hansen Section 3.11: the hat matrix fixes every matrix in the range of `X`. -/
theorem hat_mul_range
    (X : Matrix n k ℝ) (Γ : Matrix k l ℝ) [Invertible (Xᵀ * X)] :
    hatMatrix X * (X * Γ) = X * Γ := by
  rw [← Matrix.mul_assoc, hat_mul_X]

/-- Hansen equation (3.21): the annihilator matrix kills the regressor matrix, `M X = 0`. -/
theorem annihilator_mul_X
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    annihilatorMatrix X * X = 0 := by
  unfold annihilatorMatrix
  rw [Matrix.sub_mul, Matrix.one_mul, hat_mul_X]
  simp

/-- Hansen Section 3.12: the annihilator kills every matrix in the range of `X`. -/
theorem annihilator_mul_range
    (X : Matrix n k ℝ) (Γ : Matrix k l ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    annihilatorMatrix X * (X * Γ) = 0 := by
  rw [← Matrix.mul_assoc, annihilator_mul_X, Matrix.zero_mul]

/-- Hansen Theorem 3.3.2: the hat matrix is idempotent. -/
theorem hatMatrix_idempotent
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    hatMatrix X * hatMatrix X = hatMatrix X := by
  change hatMatrix X * (X * ⅟ (Xᵀ * X) * Xᵀ) = X * ⅟ (Xᵀ * X) * Xᵀ
  rw [Matrix.mul_assoc X (⅟ (Xᵀ * X)) Xᵀ]
  rw [← Matrix.mul_assoc (hatMatrix X) X (⅟ (Xᵀ * X) * Xᵀ)]
  rw [hat_mul_X]

/-- Hansen Theorem 3.3.3: the trace of the hat matrix is the number of regressors. -/
theorem hatMatrix_trace
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    Matrix.trace (hatMatrix X) = Fintype.card k := by
  unfold hatMatrix
  calc
    Matrix.trace (X * ⅟ (Xᵀ * X) * Xᵀ)
        = Matrix.trace (Xᵀ * X * ⅟ (Xᵀ * X)) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (1 : Matrix k k ℝ) := by
          rw [mul_invOf_self]
    _ = Fintype.card k := by
          rw [Matrix.trace_one]

/-- Hansen Section 3.12 / Exercise 3.8: the annihilator matrix is idempotent. -/
theorem annihilatorMatrix_idempotent
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    annihilatorMatrix X * annihilatorMatrix X = annihilatorMatrix X := by
  simp [annihilatorMatrix, Matrix.sub_mul, Matrix.mul_sub, hatMatrix_idempotent]

/-- Hansen Exercise 3.7: the annihilator kills the hat matrix on the left. -/
theorem annihilator_mul_hatMatrix
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    annihilatorMatrix X * hatMatrix X = 0 := by
  simp [annihilatorMatrix, Matrix.sub_mul, hatMatrix_idempotent]

/-- Hansen Exercise 3.7: the annihilator kills the hat matrix on the right. -/
theorem hatMatrix_mul_annihilator
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    hatMatrix X * annihilatorMatrix X = 0 := by
  simp [annihilatorMatrix, Matrix.mul_sub, hatMatrix_idempotent]

/-- Hansen equation (3.22): the trace of the annihilator matrix is `n - k`. -/
theorem annihilatorMatrix_trace
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    Matrix.trace (annihilatorMatrix X) = (Fintype.card n : ℝ) - Fintype.card k := by
  simp [annihilatorMatrix, Matrix.trace_sub, Matrix.trace_one, hatMatrix_trace]

/-- The annihilator matrix is Hermitian (equivalently, symmetric for real matrices). -/
theorem annihilatorMatrix_isHermitian
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    (annihilatorMatrix X).IsHermitian :=
  (Matrix.conjTranspose_eq_transpose_of_trivial _).trans (annihilatorMatrix_transpose X)

/-- The hat matrix is Hermitian (equivalently, symmetric for real matrices). -/
theorem hatMatrix_isHermitian
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    (hatMatrix X).IsHermitian :=
  (Matrix.conjTranspose_eq_transpose_of_trivial _).trans (hatMatrix_transpose X)

/-- The rank of the annihilator matrix plus the number of regressors equals
the number of observations. Equivalent to rank(M) = n − k. -/
theorem rank_annihilatorMatrix_add
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    (annihilatorMatrix X).rank + Fintype.card k = Fintype.card n := by
  have h := rank_eq_natCast_trace_of_isHermitian_idempotent
    (annihilatorMatrix_isHermitian X) (annihilatorMatrix_idempotent X)
  rw [annihilatorMatrix_trace] at h
  exact_mod_cast show ((annihilatorMatrix X).rank : ℝ) + (Fintype.card k : ℝ)
    = (Fintype.card n : ℝ) by linarith

/-- Hansen Section 3.12: the rank of the annihilator matrix is `n - k`. -/
theorem rank_annihilatorMatrix
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    (annihilatorMatrix X).rank = Fintype.card n - Fintype.card k :=
  Nat.eq_sub_of_add_eq (rank_annihilatorMatrix_add X)

/-- The rank of the hat matrix equals the number of regressors. -/
theorem rank_hatMatrix
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    (hatMatrix X).rank = Fintype.card k := by
  have h := rank_eq_natCast_trace_of_isHermitian_idempotent
    (hatMatrix_isHermitian X) (hatMatrix_idempotent X)
  rw [hatMatrix_trace] at h
  exact_mod_cast h

/-- Hansen Theorem 3.3.4: every eigenvalue of the hat matrix is `0` or `1`. -/
theorem hatMatrix_eigenvalues_zero_or_one
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    ∀ i : n,
      (hatMatrix_isHermitian X).eigenvalues i = 0 ∨
        (hatMatrix_isHermitian X).eigenvalues i = 1 :=
  eigenvalues_zero_or_one_of_isHermitian_idempotent
    (hatMatrix_isHermitian X) (hatMatrix_idempotent X)

/-- Hansen Theorem 3.3.4: exactly `k` hat-matrix eigenvalues are equal to `1`. -/
theorem hatMatrix_card_eigenvalues_eq_one
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    Fintype.card {i : n // (hatMatrix_isHermitian X).eigenvalues i = 1} =
      Fintype.card k := by
  have h := rank_eq_card_eigenvalues_eq_one_of_isHermitian_idempotent
    (hatMatrix_isHermitian X) (hatMatrix_idempotent X)
  rw [rank_hatMatrix X] at h
  exact h.symm

/-- Hansen Section 3.12: every eigenvalue of the annihilator matrix is `0` or `1`. -/
theorem annihilatorMatrix_eigenvalues_zero_or_one
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    ∀ i : n,
      (annihilatorMatrix_isHermitian X).eigenvalues i = 0 ∨
        (annihilatorMatrix_isHermitian X).eigenvalues i = 1 :=
  eigenvalues_zero_or_one_of_isHermitian_idempotent
    (annihilatorMatrix_isHermitian X) (annihilatorMatrix_idempotent X)

/-- Hansen Section 3.12: exactly `n - k` annihilator-matrix eigenvalues are equal to `1`. -/
theorem annihilatorMatrix_card_eigenvalues_eq_one
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    Fintype.card {i : n // (annihilatorMatrix_isHermitian X).eigenvalues i = 1} =
      Fintype.card n - Fintype.card k := by
  have h := rank_eq_card_eigenvalues_eq_one_of_isHermitian_idempotent
    (annihilatorMatrix_isHermitian X) (annihilatorMatrix_idempotent X)
  rw [rank_annihilatorMatrix X] at h
  exact h.symm

/-- Hansen Section 3.11: fitted values are the hat matrix applied to the data vector. -/
theorem fitted_eq_hat_mul_y
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    fitted X y = hatMatrix X *ᵥ y := by
  unfold fitted olsBeta
  rw [← hat_mul_y_eq_closed_form_fit]

/-- A vector orthogonal to the columns of `X` is killed by the hat matrix. -/
theorem hat_mulVec_eq_zero_of_regressors_orthogonal
    (X : Matrix n k ℝ) (v : n → ℝ) [Invertible (Xᵀ * X)]
    (hv : Xᵀ *ᵥ v = 0) :
    hatMatrix X *ᵥ v = 0 := by
  unfold hatMatrix
  rw [Matrix.mul_assoc]
  rw [← Matrix.mulVec_mulVec v X (⅟ (Xᵀ * X) * Xᵀ)]
  rw [← Matrix.mulVec_mulVec v (⅟ (Xᵀ * X)) Xᵀ, hv]
  simp

/-- Hansen Section 3.12: `M` fixes vectors orthogonal to the columns of `X`. -/
theorem annihilator_mulVec_eq_self_of_regressors_orthogonal
    (X : Matrix n k ℝ) (v : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)]
    (hv : Xᵀ *ᵥ v = 0) :
    annihilatorMatrix X *ᵥ v = v := by
  unfold annihilatorMatrix
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hat_mulVec_eq_zero_of_regressors_orthogonal X v hv]
  simp

/-- Hansen equation (3.23): residuals are the annihilator matrix applied to the data vector. -/
theorem residual_eq_annihilator_mul_y
    (X : Matrix n k ℝ) (y : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    residual X y = annihilatorMatrix X *ᵥ y := by
  unfold residual fitted olsBeta
  rw [← annihilator_mul_y_eq_closed_form_residual]

/-- Hansen Section 3.14: fitted values and residuals are orthogonal. -/
theorem fitted_dot_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    fitted X y ⬝ᵥ residual X y = 0 := by
  rw [dotProduct_comm]
  unfold fitted
  rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose]
  rw [normal_equations]
  simp

/-- Hansen Section 3.14: finite-sample Pythagorean decomposition for fitted values and residuals. -/
theorem fitted_residual_pythagorean
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    y ⬝ᵥ y = fitted X y ⬝ᵥ fitted X y + residual X y ⬝ᵥ residual X y := by
  calc
    y ⬝ᵥ y = (fitted X y + residual X y) ⬝ᵥ (fitted X y + residual X y) := by
      rw [fitted_add_residual]
    _ = fitted X y ⬝ᵥ fitted X y + residual X y ⬝ᵥ residual X y := by
      rw [add_dotProduct, dotProduct_add, dotProduct_add]
      rw [fitted_dot_residual]
      rw [dotProduct_comm (residual X y) (fitted X y), fitted_dot_residual]
      simp

/-- Sample mean of a finite real vector. -/
noncomputable def sampleMean (y : n → ℝ) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * ∑ i, y i

/-- Center a vector around the sample mean of a reference vector. -/
noncomputable def centeredAtSampleMean (y z : n → ℝ) : n → ℝ :=
  z - sampleMean y • (1 : n → ℝ)

/-- Hansen Section 3.14: total sum of squares around the sample mean. -/
noncomputable def totalSumSquares (y : n → ℝ) : ℝ :=
  centeredAtSampleMean y y ⬝ᵥ centeredAtSampleMean y y

/-- Hansen Section 3.14: explained sum of squares around the sample mean of `y`. -/
noncomputable def explainedSumSquares
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : ℝ :=
  centeredAtSampleMean y (fitted X y) ⬝ᵥ centeredAtSampleMean y (fitted X y)

/-- Hansen Section 3.14: residual sum of squares. -/
noncomputable def residualSumSquares
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : ℝ :=
  residual X y ⬝ᵥ residual X y

/-- Hansen Section 3.14: coefficient of determination. -/
noncomputable def rSquared
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : ℝ :=
  explainedSumSquares X y / totalSumSquares y

/-- Pythagorean identity for any orthogonal vector decomposition. -/
theorem dotProduct_add_self_eq_of_orthogonal
    (u v : n → ℝ) (huv : u ⬝ᵥ v = 0) :
    (u + v) ⬝ᵥ (u + v) = u ⬝ᵥ u + v ⬝ᵥ v := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add]
  rw [huv, dotProduct_comm v u, huv]
  simp

/-- Hansen Section 3.14: with an intercept, centered fitted values are orthogonal to residuals. -/
theorem centered_fitted_dot_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)]
    {c : k → ℝ} (hc : X *ᵥ c = 1) :
    centeredAtSampleMean y (fitted X y) ⬝ᵥ residual X y = 0 := by
  have hsum := residual_sum_zero_of_one_mem_colspan X y hc
  have hone : (1 : n → ℝ) ⬝ᵥ residual X y = 0 := by
    rw [dotProduct_comm, dotProduct_one, hsum]
  have hconst : (sampleMean y • (1 : n → ℝ)) ⬝ᵥ residual X y = 0 := by
    rw [smul_dotProduct, hone, smul_zero]
  unfold centeredAtSampleMean
  rw [sub_dotProduct, fitted_dot_residual, hconst]
  simp

/-- Centering the fitted-plus-residual decomposition around the sample mean of `y`. -/
theorem centeredAtSampleMean_eq_centered_fitted_add_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    centeredAtSampleMean y y = centeredAtSampleMean y (fitted X y) + residual X y := by
  ext i
  have hi := congrFun (fitted_add_residual X y) i
  unfold centeredAtSampleMean
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
  rw [← hi]
  simp only [Pi.add_apply]
  ring_nf

/-- Hansen Section 3.14: centered analysis-of-variance decomposition for OLS with an intercept. -/
theorem centered_anova_decomposition
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)]
    {c : k → ℝ} (hc : X *ᵥ c = 1) :
    totalSumSquares y = explainedSumSquares X y + residualSumSquares X y := by
  unfold totalSumSquares explainedSumSquares residualSumSquares
  rw [centeredAtSampleMean_eq_centered_fitted_add_residual X y]
  exact dotProduct_add_self_eq_of_orthogonal
    (centeredAtSampleMean y (fitted X y)) (residual X y)
    (centered_fitted_dot_residual X y hc)

/-- Hansen Section 3.14: `R²` can be written as one minus the residual share of TSS. -/
theorem rSquared_eq_one_sub_residualSumSquares_div_totalSumSquares
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)]
    {c : k → ℝ} (hc : X *ᵥ c = 1)
    (hTSS : totalSumSquares y ≠ 0) :
    rSquared X y = 1 - residualSumSquares X y / totalSumSquares y := by
  unfold rSquared
  have hdecomp := centered_anova_decomposition X y hc
  have hdiv :
      explainedSumSquares X y / totalSumSquares y =
        (totalSumSquares y - residualSumSquares X y) / totalSumSquares y := by
    rw [hdecomp]
    ring
  rw [hdiv]
  field_simp [hTSS]

end HansenEconometrics
