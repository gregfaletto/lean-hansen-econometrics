import Mathlib.Data.Matrix.ColumnRowPartitioned
import HansenEconometrics.Chapter3Projections

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k k₁ k₂ : Type*}
variable [Fintype n]

/-- Hansen model (3.31): normal equations for a column-partitioned regression, first block. -/
theorem normal_equations_fromCols_left
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    X₁ᵀ *ᵥ residual (Matrix.fromCols X₁ X₂) y = 0 := by
  have h := normal_equations (Matrix.fromCols X₁ X₂) y
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mulVec] at h
  ext j
  simpa using congrFun h (Sum.inl j)

/-- Hansen model (3.31): normal equations for a column-partitioned regression, second block. -/
theorem normal_equations_fromCols_right
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    X₂ᵀ *ᵥ residual (Matrix.fromCols X₁ X₂) y = 0 := by
  have h := normal_equations (Matrix.fromCols X₁ X₂) y
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mulVec] at h
  ext j
  simpa using congrFun h (Sum.inr j)

/-- Hansen equation (3.21), transposed: left multiplication by `M` is orthogonal to `X`. -/
theorem regressors_transpose_mul_annihilator
    (X : Matrix n k ℝ) [DecidableEq n] [Fintype k] [DecidableEq k]
    [Invertible (Xᵀ * X)] :
    Xᵀ * annihilatorMatrix X = 0 := by
  calc
    Xᵀ * annihilatorMatrix X = Xᵀ * (annihilatorMatrix X)ᵀ := by
      rw [annihilatorMatrix_transpose]
    _ = (annihilatorMatrix X * X)ᵀ := by
      rw [Matrix.transpose_mul]
    _ = 0 := by
      rw [annihilator_mul_X]
      simp

/-- Hansen Section 3.18: residualized regressors `X̃₂ = M₁ X₂` for FWL. -/
noncomputable def residualizedRegressors
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁]
    [Invertible (X₁ᵀ * X₁)] : Matrix n k₂ ℝ :=
  annihilatorMatrix X₁ * X₂

/-- Hansen Theorem 3.5: the FWL coefficient from regressing `M₁ y` on `M₁ X₂`. -/
noncomputable def fwlBeta
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂)] :
    k₂ → ℝ :=
  olsBeta (residualizedRegressors X₁ X₂) (annihilatorMatrix X₁ *ᵥ y)

/-- Hansen Theorem 3.4: the left-block coefficient from regressing `M₂ y` on `M₂ X₁`. -/
noncomputable def fwlLeftBeta
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₂ᵀ * X₂)]
    [Invertible ((residualizedRegressors X₂ X₁)ᵀ * residualizedRegressors X₂ X₁)] :
    k₁ → ℝ :=
  olsBeta (residualizedRegressors X₂ X₁) (annihilatorMatrix X₂ *ᵥ y)

/-- Hansen equation (3.38): the right-block partitioned-regression formula. -/
noncomputable def partitionedRightBetaFormula
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)] :
    k₂ → ℝ :=
  (X₂ᵀ * annihilatorMatrix X₁ * X₂)⁻¹ *ᵥ (X₂ᵀ *ᵥ (annihilatorMatrix X₁ *ᵥ y))

/-- Hansen equation (3.37): the left-block partitioned-regression formula. -/
noncomputable def partitionedLeftBetaFormula
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₂ᵀ * X₂)] :
    k₁ → ℝ :=
  (X₁ᵀ * annihilatorMatrix X₂ * X₁)⁻¹ *ᵥ (X₁ᵀ *ᵥ (annihilatorMatrix X₂ *ᵥ y))

/-- The first block of the full-regression coefficient on `[X₁ X₂]`. -/
noncomputable def fromColsLeftBeta
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    k₁ → ℝ :=
  fun j => olsBeta (Matrix.fromCols X₁ X₂) y (Sum.inl j)

/-- The second block of the full-regression coefficient on `[X₁ X₂]`. -/
noncomputable def fromColsRightBeta
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    k₂ → ℝ :=
  fun j => olsBeta (Matrix.fromCols X₁ X₂) y (Sum.inr j)

/-- The fitted vector from the full regression splits into its two regressor blocks. -/
theorem fromCols_full_fitted_eq
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    Matrix.fromCols X₁ X₂ *ᵥ olsBeta (Matrix.fromCols X₁ X₂) y =
      X₁ *ᵥ fromColsLeftBeta X₁ X₂ y + X₂ *ᵥ fromColsRightBeta X₁ X₂ y := by
  rw [Matrix.fromCols_mulVec]
  rfl

/-- Hansen Section 3.18: the residualized regressors are orthogonal to the regressors
they partial out. -/
theorem residualizedRegressors_orthogonal_left
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁]
    [Invertible (X₁ᵀ * X₁)] :
    X₁ᵀ * residualizedRegressors X₁ X₂ = 0 := by
  unfold residualizedRegressors
  rw [← Matrix.mul_assoc, regressors_transpose_mul_annihilator, Matrix.zero_mul]

/-- Gram matrix of residualized regressors in Hansen's partitioned-regression notation. -/
theorem residualizedRegressors_gram_eq
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁]
    [Invertible (X₁ᵀ * X₁)] :
    (residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂ =
      X₂ᵀ * annihilatorMatrix X₁ * X₂ := by
  unfold residualizedRegressors
  rw [Matrix.transpose_mul, annihilatorMatrix_transpose]
  calc
    (X₂ᵀ * annihilatorMatrix X₁) * (annihilatorMatrix X₁ * X₂)
        = X₂ᵀ * ((annihilatorMatrix X₁ * annihilatorMatrix X₁) * X₂) := by
          simp [Matrix.mul_assoc]
    _ = X₂ᵀ * (annihilatorMatrix X₁ * X₂) := by
          rw [annihilatorMatrix_idempotent]
    _ = X₂ᵀ * annihilatorMatrix X₁ * X₂ := by
          rw [Matrix.mul_assoc]

/-- Cross moment of residualized regressors and residualized outcomes. -/
theorem residualizedRegressors_cross_y_eq
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁]
    [Invertible (X₁ᵀ * X₁)] :
    (residualizedRegressors X₁ X₂)ᵀ *ᵥ (annihilatorMatrix X₁ *ᵥ y) =
      X₂ᵀ *ᵥ (annihilatorMatrix X₁ *ᵥ y) := by
  unfold residualizedRegressors
  rw [Matrix.transpose_mul, annihilatorMatrix_transpose]
  calc
    (X₂ᵀ * annihilatorMatrix X₁) *ᵥ (annihilatorMatrix X₁ *ᵥ y)
        = ((X₂ᵀ * annihilatorMatrix X₁) * annihilatorMatrix X₁) *ᵥ y := by
          rw [Matrix.mulVec_mulVec]
    _ = (X₂ᵀ * (annihilatorMatrix X₁ * annihilatorMatrix X₁)) *ᵥ y := by
          rw [Matrix.mul_assoc]
    _ = (X₂ᵀ * annihilatorMatrix X₁) *ᵥ y := by
          rw [annihilatorMatrix_idempotent]
    _ = X₂ᵀ *ᵥ (annihilatorMatrix X₁ *ᵥ y) := by
          rw [← Matrix.mulVec_mulVec]

/--
The residual in the auxiliary FWL regression, evaluated at the second block of the full-regression
coefficient, is the full-regression residual after applying `M₁`.
-/
theorem fwl_auxiliary_residual_eq_annihilator_full_residual
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    annihilatorMatrix X₁ *ᵥ y -
        residualizedRegressors X₁ X₂ *ᵥ fromColsRightBeta X₁ X₂ y =
      annihilatorMatrix X₁ *ᵥ residual (Matrix.fromCols X₁ X₂) y := by
  unfold residual fitted residualizedRegressors
  rw [fromCols_full_fitted_eq]
  rw [Matrix.mulVec_sub, Matrix.mulVec_add]
  rw [Matrix.mulVec_mulVec]
  rw [annihilator_mul_X]
  ext i
  simp [sub_eq_add_neg, add_comm]

/-- The full-regression right block satisfies the FWL auxiliary normal equations. -/
theorem fwl_fromColsRightBeta_normal_equations
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    (residualizedRegressors X₁ X₂)ᵀ *ᵥ
        (annihilatorMatrix X₁ *ᵥ y -
          residualizedRegressors X₁ X₂ *ᵥ fromColsRightBeta X₁ X₂ y) = 0 := by
  rw [fwl_auxiliary_residual_eq_annihilator_full_residual]
  have hM :
      annihilatorMatrix X₁ *ᵥ residual (Matrix.fromCols X₁ X₂) y =
        residual (Matrix.fromCols X₁ X₂) y :=
    annihilator_mulVec_eq_self_of_regressors_orthogonal X₁
      (residual (Matrix.fromCols X₁ X₂) y)
      (normal_equations_fromCols_left X₁ X₂ y)
  rw [hM]
  unfold residualizedRegressors
  rw [Matrix.transpose_mul, annihilatorMatrix_transpose]
  rw [← Matrix.mulVec_mulVec (residual (Matrix.fromCols X₁ X₂) y) X₂ᵀ
    (annihilatorMatrix X₁)]
  rw [hM]
  exact normal_equations_fromCols_right X₁ X₂ y

/-- Hansen Theorem 3.5, coefficient part: the second full-regression block equals FWL. -/
theorem fromColsRightBeta_eq_fwlBeta
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    [Invertible ((residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂)] :
    fromColsRightBeta X₁ X₂ y = fwlBeta X₁ X₂ y := by
  symm
  unfold fwlBeta
  exact olsBeta_eq_of_normal_equations
    (residualizedRegressors X₁ X₂)
    (annihilatorMatrix X₁ *ᵥ y)
    (fromColsRightBeta X₁ X₂ y)
    (fwl_fromColsRightBeta_normal_equations X₁ X₂ y)

/--
The residual in the left-block auxiliary regression, evaluated at the first block of the
full-regression coefficient, is the full-regression residual after applying `M₂`.
-/
theorem fwl_left_auxiliary_residual_eq_annihilator_full_residual
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₂ᵀ * X₂)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    annihilatorMatrix X₂ *ᵥ y -
        residualizedRegressors X₂ X₁ *ᵥ fromColsLeftBeta X₁ X₂ y =
      annihilatorMatrix X₂ *ᵥ residual (Matrix.fromCols X₁ X₂) y := by
  unfold residual fitted residualizedRegressors
  rw [fromCols_full_fitted_eq]
  rw [Matrix.mulVec_sub, Matrix.mulVec_add]
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec (fromColsRightBeta X₁ X₂ y) (annihilatorMatrix X₂) X₂]
  rw [annihilator_mul_X]
  ext i
  simp [sub_eq_add_neg]

/-- The full-regression left block satisfies the left auxiliary normal equations. -/
theorem fwl_fromColsLeftBeta_normal_equations
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₂ᵀ * X₂)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    (residualizedRegressors X₂ X₁)ᵀ *ᵥ
        (annihilatorMatrix X₂ *ᵥ y -
          residualizedRegressors X₂ X₁ *ᵥ fromColsLeftBeta X₁ X₂ y) = 0 := by
  rw [fwl_left_auxiliary_residual_eq_annihilator_full_residual]
  have hM :
      annihilatorMatrix X₂ *ᵥ residual (Matrix.fromCols X₁ X₂) y =
        residual (Matrix.fromCols X₁ X₂) y :=
    annihilator_mulVec_eq_self_of_regressors_orthogonal X₂
      (residual (Matrix.fromCols X₁ X₂) y)
      (normal_equations_fromCols_right X₁ X₂ y)
  rw [hM]
  unfold residualizedRegressors
  rw [Matrix.transpose_mul, annihilatorMatrix_transpose]
  rw [← Matrix.mulVec_mulVec (residual (Matrix.fromCols X₁ X₂) y) X₁ᵀ
    (annihilatorMatrix X₂)]
  rw [hM]
  exact normal_equations_fromCols_left X₁ X₂ y

/-- Hansen Theorem 3.4, left coefficient part: the first full-regression block equals FWL. -/
theorem fromColsLeftBeta_eq_fwlLeftBeta
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₂ᵀ * X₂)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    [Invertible ((residualizedRegressors X₂ X₁)ᵀ * residualizedRegressors X₂ X₁)] :
    fromColsLeftBeta X₁ X₂ y = fwlLeftBeta X₁ X₂ y := by
  symm
  unfold fwlLeftBeta
  exact olsBeta_eq_of_normal_equations
    (residualizedRegressors X₂ X₁)
    (annihilatorMatrix X₂ *ᵥ y)
    (fromColsLeftBeta X₁ X₂ y)
    (fwl_fromColsLeftBeta_normal_equations X₁ X₂ y)

/-- Hansen equation (3.38): `fwlBeta` is the explicit `X₂ᵀ M₁ X₂` formula. -/
theorem fwlBeta_eq_partitionedRightBetaFormula
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂)] :
    fwlBeta X₁ X₂ y = partitionedRightBetaFormula X₁ X₂ y := by
  unfold fwlBeta partitionedRightBetaFormula olsBeta
  rw [Matrix.invOf_eq_nonsing_inv]
  rw [residualizedRegressors_gram_eq, residualizedRegressors_cross_y_eq]

/-- Hansen equation (3.37): `fwlLeftBeta` is the explicit `X₁ᵀ M₂ X₁` formula. -/
theorem fwlLeftBeta_eq_partitionedLeftBetaFormula
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₂ᵀ * X₂)]
    [Invertible ((residualizedRegressors X₂ X₁)ᵀ * residualizedRegressors X₂ X₁)] :
    fwlLeftBeta X₁ X₂ y = partitionedLeftBetaFormula X₁ X₂ y := by
  unfold fwlLeftBeta partitionedLeftBetaFormula olsBeta
  rw [Matrix.invOf_eq_nonsing_inv]
  rw [residualizedRegressors_gram_eq, residualizedRegressors_cross_y_eq]

/-- Hansen Theorem 3.4, equation (3.38): the second block equals the explicit formula. -/
theorem fromColsRightBeta_eq_partitionedRightBetaFormula
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    [Invertible ((residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂)] :
    fromColsRightBeta X₁ X₂ y = partitionedRightBetaFormula X₁ X₂ y := by
  rw [fromColsRightBeta_eq_fwlBeta, fwlBeta_eq_partitionedRightBetaFormula]

/-- Hansen Theorem 3.4, equation (3.37): the first block equals the explicit formula. -/
theorem fromColsLeftBeta_eq_partitionedLeftBetaFormula
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₂ᵀ * X₂)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    [Invertible ((residualizedRegressors X₂ X₁)ᵀ * residualizedRegressors X₂ X₁)] :
    fromColsLeftBeta X₁ X₂ y = partitionedLeftBetaFormula X₁ X₂ y := by
  rw [fromColsLeftBeta_eq_fwlLeftBeta, fwlLeftBeta_eq_partitionedLeftBetaFormula]

/-- Hansen Theorem 3.4: both partitioned-regression coefficients in formula form. -/
theorem fromColsBeta_eq_partitionedBetaFormulas
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)] [Invertible (X₂ᵀ * X₂)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    [Invertible ((residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂)]
    [Invertible ((residualizedRegressors X₂ X₁)ᵀ * residualizedRegressors X₂ X₁)] :
    fromColsLeftBeta X₁ X₂ y = partitionedLeftBetaFormula X₁ X₂ y ∧
      fromColsRightBeta X₁ X₂ y = partitionedRightBetaFormula X₁ X₂ y :=
  ⟨fromColsLeftBeta_eq_partitionedLeftBetaFormula X₁ X₂ y,
    fromColsRightBeta_eq_partitionedRightBetaFormula X₁ X₂ y⟩

/-- Hansen Theorem 3.5, residual part: FWL and full OLS produce the same residual. -/
theorem fwl_residual_eq_full_residual
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    [Invertible ((residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂)] :
    residual (residualizedRegressors X₁ X₂) (annihilatorMatrix X₁ *ᵥ y) =
      residual (Matrix.fromCols X₁ X₂) y := by
  have hcoef := fromColsRightBeta_eq_fwlBeta X₁ X₂ y
  unfold residual fitted fwlBeta at *
  rw [← hcoef]
  rw [fwl_auxiliary_residual_eq_annihilator_full_residual]
  exact annihilator_mulVec_eq_self_of_regressors_orthogonal X₁
    (residual (Matrix.fromCols X₁ X₂) y)
    (normal_equations_fromCols_left X₁ X₂ y)

/-- Hansen Theorem 3.5: normal equations for the residualized regression defining the
FWL coefficient. -/
theorem fwl_normal_equations
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂)] :
    (residualizedRegressors X₁ X₂)ᵀ *ᵥ
        residual (residualizedRegressors X₁ X₂) (annihilatorMatrix X₁ *ᵥ y) = 0 :=
  normal_equations (residualizedRegressors X₁ X₂) (annihilatorMatrix X₁ *ᵥ y)

/--
Hansen Theorem 3.5 setup: the sequential FWL residual maker `M_{M₁X₂} M₁`
annihilates both blocks of `[X₁ X₂]`. This is the projection-geometry core needed before
proving the full FWL coefficient identity.
-/
theorem fwl_residual_maker_mul_fromCols
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂)] :
    annihilatorMatrix (residualizedRegressors X₁ X₂) * annihilatorMatrix X₁ *
        Matrix.fromCols X₁ X₂ = 0 := by
  have hleft :
      (annihilatorMatrix (residualizedRegressors X₁ X₂) * annihilatorMatrix X₁) * X₁ = 0 := by
    calc
      (annihilatorMatrix (residualizedRegressors X₁ X₂) * annihilatorMatrix X₁) * X₁
          = annihilatorMatrix (residualizedRegressors X₁ X₂) * (annihilatorMatrix X₁ * X₁) := by
            rw [Matrix.mul_assoc]
      _ = 0 := by
            rw [annihilator_mul_X]
            simp
  have hright :
      (annihilatorMatrix (residualizedRegressors X₁ X₂) * annihilatorMatrix X₁) * X₂ = 0 := by
    calc
      (annihilatorMatrix (residualizedRegressors X₁ X₂) * annihilatorMatrix X₁) * X₂
          = annihilatorMatrix (residualizedRegressors X₁ X₂) *
              (annihilatorMatrix X₁ * X₂) := by
            rw [Matrix.mul_assoc]
      _ = annihilatorMatrix (residualizedRegressors X₁ X₂) *
            residualizedRegressors X₁ X₂ := by
            rfl
      _ = 0 := by
            rw [annihilator_mul_X]
  rw [Matrix.mul_fromCols, hleft, hright]
  simp

end HansenEconometrics
