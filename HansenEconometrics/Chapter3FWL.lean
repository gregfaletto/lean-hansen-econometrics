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

/-- Mirror of `fwl_auxiliary_residual_eq_annihilator_full_residual` for the left
block: the auxiliary residual `M₂Y - (M₂X₁) ⋅ β̂₁` equals `M₂` applied to the
full-regression residual. Companion to the existing right-block version, used in the
proof of the symmetric Theorem 3.5 coefficient identity for β̂₁. -/
theorem fwl_auxiliary_residual_eq_annihilator_full_residual_left
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
  rw [Matrix.mulVec_mulVec (fromColsRightBeta X₁ X₂ y) (annihilatorMatrix X₂) X₂]
  rw [annihilator_mul_X]
  ext i
  simp [sub_eq_add_neg]

/-- Mirror of `fwl_fromColsRightBeta_normal_equations`: the full-regression left block
satisfies the symmetric FWL auxiliary normal equations (with M₂ as the residual maker). -/
theorem fwl_fromColsLeftBeta_normal_equations
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₂ᵀ * X₂)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    (residualizedRegressors X₂ X₁)ᵀ *ᵥ
        (annihilatorMatrix X₂ *ᵥ y -
          residualizedRegressors X₂ X₁ *ᵥ fromColsLeftBeta X₁ X₂ y) = 0 := by
  rw [fwl_auxiliary_residual_eq_annihilator_full_residual_left]
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

/-- Symmetric companion to `fromColsRightBeta_eq_fwlBeta`: the left block of the full
regression equals the FWL coefficient computed by partialling out X₂. The two together
say:

  fromColsRightBeta X₁ X₂ y = fwlBeta X₁ X₂ y    -- X₁ residualizes X₂ (right block)
  fromColsLeftBeta  X₁ X₂ y = fwlBeta X₂ X₁ y    -- X₂ residualizes X₁ (left block)
-/
theorem fromColsLeftBeta_eq_fwlBeta
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₂ᵀ * X₂)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    [Invertible ((residualizedRegressors X₂ X₁)ᵀ * residualizedRegressors X₂ X₁)] :
    fromColsLeftBeta X₁ X₂ y = fwlBeta X₂ X₁ y := by
  symm
  unfold fwlBeta
  exact olsBeta_eq_of_normal_equations
    (residualizedRegressors X₂ X₁)
    (annihilatorMatrix X₂ *ᵥ y)
    (fromColsLeftBeta X₁ X₂ y)
    (fwl_fromColsLeftBeta_normal_equations X₁ X₂ y)

/-- Hansen Theorem 3.4, equation (3.38): the right block of the partitioned-regression
OLS coefficient has the explicit form `(X₂' M₁ X₂)⁻¹ (X₂' M₁ Y)`. Combined with
`fromColsLeftBeta_eq_partitioned_form` (Eq. 3.37), this gives both halves of Hansen
Theorem 3.4. -/
theorem fromColsRightBeta_eq_partitioned_form
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    [Invertible (X₂ᵀ * annihilatorMatrix X₁ * X₂)] :
    fromColsRightBeta X₁ X₂ y =
      (⅟ (X₂ᵀ * annihilatorMatrix X₁ * X₂)) *ᵥ
        (X₂ᵀ *ᵥ (annihilatorMatrix X₁ *ᵥ y)) := by
  have hquad :
      (residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂ =
        X₂ᵀ * annihilatorMatrix X₁ * X₂ := by
    unfold residualizedRegressors
    rw [Matrix.transpose_mul, annihilatorMatrix_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (annihilatorMatrix X₁) (annihilatorMatrix X₁) X₂]
    rw [show annihilatorMatrix X₁ * annihilatorMatrix X₁ = annihilatorMatrix X₁
      from annihilatorMatrix_idempotent X₁]
    rw [← Matrix.mul_assoc]
  have hcross :
      (residualizedRegressors X₁ X₂)ᵀ *ᵥ (annihilatorMatrix X₁ *ᵥ y) =
        X₂ᵀ *ᵥ (annihilatorMatrix X₁ *ᵥ y) := by
    unfold residualizedRegressors
    rw [Matrix.transpose_mul, annihilatorMatrix_transpose]
    rw [← Matrix.mulVec_mulVec]
    have hidem :
        annihilatorMatrix X₁ *ᵥ (annihilatorMatrix X₁ *ᵥ y) =
          annihilatorMatrix X₁ *ᵥ y := by
      rw [Matrix.mulVec_mulVec]
      rw [show annihilatorMatrix X₁ * annihilatorMatrix X₁ = annihilatorMatrix X₁
        from annihilatorMatrix_idempotent X₁]
    rw [hidem]
  have : Invertible ((residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂) :=
    (inferInstance : Invertible (X₂ᵀ * annihilatorMatrix X₁ * X₂)).copy _ hquad
  have hInvOfEq :
      ⅟ ((residualizedRegressors X₁ X₂)ᵀ * residualizedRegressors X₁ X₂) =
        ⅟ (X₂ᵀ * annihilatorMatrix X₁ * X₂) := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.invOf_eq_nonsing_inv, hquad]
  rw [fromColsRightBeta_eq_fwlBeta]
  unfold fwlBeta olsBeta
  rw [hcross, hInvOfEq]

/-- Hansen Theorem 3.4, equation (3.37): the left block of the partitioned-regression
OLS coefficient has the explicit form `(X₁' M₂ X₁)⁻¹ (X₁' M₂ Y)`. Symmetric companion
to `fromColsRightBeta_eq_partitioned_form` (Eq. 3.38); the two together give Hansen
Theorem 3.4. -/
theorem fromColsLeftBeta_eq_partitioned_form
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [DecidableEq n] [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]
    [Invertible (X₂ᵀ * X₂)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    [Invertible (X₁ᵀ * annihilatorMatrix X₂ * X₁)] :
    fromColsLeftBeta X₁ X₂ y =
      (⅟ (X₁ᵀ * annihilatorMatrix X₂ * X₁)) *ᵥ
        (X₁ᵀ *ᵥ (annihilatorMatrix X₂ *ᵥ y)) := by
  have hquad :
      (residualizedRegressors X₂ X₁)ᵀ * residualizedRegressors X₂ X₁ =
        X₁ᵀ * annihilatorMatrix X₂ * X₁ := by
    unfold residualizedRegressors
    rw [Matrix.transpose_mul, annihilatorMatrix_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (annihilatorMatrix X₂) (annihilatorMatrix X₂) X₁]
    rw [show annihilatorMatrix X₂ * annihilatorMatrix X₂ = annihilatorMatrix X₂
      from annihilatorMatrix_idempotent X₂]
    rw [← Matrix.mul_assoc]
  have hcross :
      (residualizedRegressors X₂ X₁)ᵀ *ᵥ (annihilatorMatrix X₂ *ᵥ y) =
        X₁ᵀ *ᵥ (annihilatorMatrix X₂ *ᵥ y) := by
    unfold residualizedRegressors
    rw [Matrix.transpose_mul, annihilatorMatrix_transpose]
    rw [← Matrix.mulVec_mulVec]
    have hidem :
        annihilatorMatrix X₂ *ᵥ (annihilatorMatrix X₂ *ᵥ y) =
          annihilatorMatrix X₂ *ᵥ y := by
      rw [Matrix.mulVec_mulVec]
      rw [show annihilatorMatrix X₂ * annihilatorMatrix X₂ = annihilatorMatrix X₂
        from annihilatorMatrix_idempotent X₂]
    rw [hidem]
  have : Invertible ((residualizedRegressors X₂ X₁)ᵀ * residualizedRegressors X₂ X₁) :=
    (inferInstance : Invertible (X₁ᵀ * annihilatorMatrix X₂ * X₁)).copy _ hquad
  have hInvOfEq :
      ⅟ ((residualizedRegressors X₂ X₁)ᵀ * residualizedRegressors X₂ X₁) =
        ⅟ (X₁ᵀ * annihilatorMatrix X₂ * X₁) := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.invOf_eq_nonsing_inv, hquad]
  rw [fromColsLeftBeta_eq_fwlBeta]
  unfold fwlBeta olsBeta
  rw [hcross, hInvOfEq]

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
