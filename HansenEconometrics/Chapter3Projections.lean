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

/-- Hansen equation (3.40): the `i`th leverage value is the `i`th diagonal
entry of the hat matrix. -/
noncomputable def leverageValue
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (i : n) : ℝ :=
  hatMatrix X i i

/-- Hansen equation (3.40): leverage as the row quadratic form
`xᵢ'(X'X)⁻¹xᵢ`. -/
theorem leverageValue_eq_row_invGram_row
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (i : n) :
    leverageValue X i = X i ⬝ᵥ (⅟ (Xᵀ * X) *ᵥ X i) := by
  unfold leverageValue hatMatrix
  rw [Matrix.dotProduct_mulVec]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply]

/-- Hansen Theorem 3.6.1: leverage values are nonnegative. -/
theorem leverageValue_nonneg
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (i : n) :
    0 ≤ leverageValue X i := by
  unfold leverageValue
  exact diag_nonneg_of_symm_idempotent
    (hatMatrix X) (hatMatrix_transpose X) (hatMatrix_idempotent X) i

/-- Hansen Theorem 3.6.3: the leverage values sum to the number of regressors. -/
theorem sum_leverageValue_eq_card
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    ∑ i : n, leverageValue X i = (Fintype.card k : ℝ) := by
  calc
    ∑ i : n, leverageValue X i = Matrix.trace (hatMatrix X) := by
      simp [leverageValue, Matrix.trace]
    _ = (Fintype.card k : ℝ) := by
      simpa using hatMatrix_trace (X := X)

private lemma sum_sq_le_card_mul_dotProduct_self (r : n → ℝ) :
    (∑ j, r j) ^ 2 ≤ (r ⬝ᵥ r) * (Fintype.card n : ℝ) := by
  have h := real_inner_mul_inner_self_le (WithLp.toLp 2 r : EuclideanSpace ℝ n)
    (WithLp.toLp 2 (1 : n → ℝ))
  change ((1 : n → ℝ) ⬝ᵥ r) * ((1 : n → ℝ) ⬝ᵥ r) ≤
      (r ⬝ᵥ r) * ((1 : n → ℝ) ⬝ᵥ (1 : n → ℝ)) at h
  rw [one_dotProduct, one_dotProduct_one] at h
  simpa [pow_two] using h

private lemma hatMatrix_row_dot_self_eq_diag
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (i : n) :
    (hatMatrix X i) ⬝ᵥ (hatMatrix X i) = hatMatrix X i i := by
  have hid := congrArg (fun M : Matrix n n ℝ => M i i) (hatMatrix_idempotent X)
  have hsymm : ∀ j : n, hatMatrix X j i = hatMatrix X i j := by
    intro j
    have h := congrArg (fun M : Matrix n n ℝ => M j i) (hatMatrix_transpose X)
    simpa [Matrix.transpose_apply] using h.symm
  simpa [Matrix.mul_apply, dotProduct, hsymm] using hid

/-- If the regressor matrix contains an intercept, the hat matrix fixes the
constant vector. -/
theorem hatMatrix_mulVec_one_of_intercept
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] {c : k → ℝ} (hc : X *ᵥ c = 1) :
    hatMatrix X *ᵥ (1 : n → ℝ) = 1 := by
  calc
    hatMatrix X *ᵥ (1 : n → ℝ) = hatMatrix X *ᵥ (X *ᵥ c) := by rw [← hc]
    _ = (hatMatrix X * X) *ᵥ c := by rw [Matrix.mulVec_mulVec]
    _ = X *ᵥ c := by rw [hat_mul_X]
    _ = 1 := hc

/-- Hansen Theorem 3.6.2: if `X` contains an intercept, every leverage value is at least
`1 / n`. -/
theorem inv_card_le_leverageValue_of_intercept
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] {c : k → ℝ} (hc : X *ᵥ c = 1) (i : n) :
    (Fintype.card n : ℝ)⁻¹ ≤ leverageValue X i := by
  have hrow_sum : ∑ j : n, hatMatrix X i j = 1 := by
    have h := congrFun (hatMatrix_mulVec_one_of_intercept (X := X) hc) i
    rw [← dotProduct_one (hatMatrix X i)]
    simpa [Matrix.mulVec] using h
  have hcauchy := sum_sq_le_card_mul_dotProduct_self (hatMatrix X i)
  rw [hrow_sum, hatMatrix_row_dot_self_eq_diag] at hcauchy
  have hmul : 1 ≤ leverageValue X i * (Fintype.card n : ℝ) := by
    simpa [leverageValue, pow_two, mul_comm] using hcauchy
  have hcard_pos : 0 < (Fintype.card n : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩ : 0 < Fintype.card n)
  have hdiv : (1 : ℝ) / (Fintype.card n : ℝ) ≤ leverageValue X i := by
    rw [div_le_iff₀ hcard_pos]
    simpa [mul_comm] using hmul
  simpa [one_div] using hdiv

/-- Hansen Section 3.12 / Exercise 3.8: the annihilator matrix is idempotent. -/
theorem annihilatorMatrix_idempotent
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    annihilatorMatrix X * annihilatorMatrix X = annihilatorMatrix X := by
  simp [annihilatorMatrix, Matrix.sub_mul, Matrix.mul_sub, hatMatrix_idempotent]

/-- Hansen Theorem 3.6.1: leverage values are bounded above by one. -/
theorem leverageValue_le_one
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (i : n) :
    leverageValue X i ≤ 1 := by
  classical
  have hdiag_nonneg : 0 ≤ annihilatorMatrix X i i :=
    diag_nonneg_of_symm_idempotent
      (annihilatorMatrix X) (annihilatorMatrix_transpose X)
      (annihilatorMatrix_idempotent X) i
  have hdiag_eq : annihilatorMatrix X i i = 1 - hatMatrix X i i := by
    simp [annihilatorMatrix, Matrix.sub_apply]
  unfold leverageValue
  linarith

/-- Hansen equation (3.42): the leave-one-out Gram matrix
`X'X - Xᵢ Xᵢ'`. -/
noncomputable def leaveOneOutGram (X : Matrix n k ℝ) (i : n) : Matrix k k ℝ :=
  Xᵀ * X - Matrix.vecMulVec (X i) (X i)

/-- Hansen equation (3.42): the leave-one-out cross-product vector
`X'Y - Xᵢ Yᵢ`. -/
noncomputable def leaveOneOutCross (X : Matrix n k ℝ) (y : n → ℝ) (i : n) : k → ℝ :=
  Xᵀ *ᵥ y - y i • X i

/-- Hansen equation (3.42): leave-one-out coefficient written with the reduced
Gram matrix. -/
noncomputable def leaveOneOutBeta
    (X : Matrix n k ℝ) (y : n → ℝ) (i : n) [Invertible (leaveOneOutGram X i)] :
    k → ℝ :=
  ⅟ (leaveOneOutGram X i) *ᵥ leaveOneOutCross X y i

/-- Leave-one-out fitted value for observation `i`. -/
noncomputable def leaveOneOutPrediction
    (X : Matrix n k ℝ) (y : n → ℝ) (i : n) [Invertible (leaveOneOutGram X i)] : ℝ :=
  X i ⬝ᵥ leaveOneOutBeta X y i

/-- Hansen equation (3.44): leave-one-out prediction error. -/
noncomputable def leaveOneOutResidual
    (X : Matrix n k ℝ) (y : n → ℝ) (i : n) [Invertible (leaveOneOutGram X i)] : ℝ :=
  y i - leaveOneOutPrediction X y i

/-- The leave-one-out coefficient satisfies the reduced normal equations. -/
theorem leaveOneOutGram_mulVec_leaveOneOutBeta
    (X : Matrix n k ℝ) (y : n → ℝ) (i : n) [Invertible (leaveOneOutGram X i)] :
    leaveOneOutGram X i *ᵥ leaveOneOutBeta X y i = leaveOneOutCross X y i := by
  unfold leaveOneOutBeta
  rw [Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]

/-- Hansen Theorem 3.7 / equation (3.43): leave-one-out coefficients can be
computed from the full-sample coefficient and prediction error. -/
theorem leaveOneOutBeta_eq_olsBeta_sub_invGram_mulVec
    (X : Matrix n k ℝ) (y : n → ℝ) (i : n)
    [Invertible (Xᵀ * X)] [Invertible (leaveOneOutGram X i)] :
    leaveOneOutBeta X y i =
      olsBeta X y - leaveOneOutResidual X y i • (⅟ (Xᵀ * X) *ᵥ X i) := by
  let A : Matrix k k ℝ := Xᵀ * X
  let x : k → ℝ := X i
  let b : k → ℝ := leaveOneOutBeta X y i
  let t : ℝ := leaveOneOutResidual X y i
  have hnormal := leaveOneOutGram_mulVec_leaveOneOutBeta X y i
  have hAeq : A *ᵥ b = Xᵀ *ᵥ y - t • x := by
    subst A; subst x; subst b; subst t
    unfold leaveOneOutResidual leaveOneOutPrediction at *
    unfold leaveOneOutGram leaveOneOutCross at hnormal
    rw [Matrix.sub_mulVec, Matrix.vecMulVec_mulVec] at hnormal
    ext j
    have hj := congrFun hnormal j
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    linarith
  subst A; subst x; subst b; subst t
  calc
    leaveOneOutBeta X y i =
        ⅟ (Xᵀ * X) *ᵥ ((Xᵀ * X) *ᵥ leaveOneOutBeta X y i) := by
      rw [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec]
    _ = ⅟ (Xᵀ * X) *ᵥ (Xᵀ *ᵥ y - leaveOneOutResidual X y i • X i) := by
      rw [hAeq]
    _ = olsBeta X y - leaveOneOutResidual X y i • (⅟ (Xᵀ * X) *ᵥ X i) := by
      unfold olsBeta
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul]

/-- Hansen Theorem 3.7 / equation (3.44), multiplication form:
`(1 - hᵢᵢ) ẽᵢ = êᵢ`. -/
theorem one_sub_leverage_mul_leaveOneOutResidual_eq_residual
    (X : Matrix n k ℝ) (y : n → ℝ) (i : n)
    [Invertible (Xᵀ * X)] [Invertible (leaveOneOutGram X i)] :
    (1 - leverageValue X i) * leaveOneOutResidual X y i = residual X y i := by
  have hcoef := congrArg (fun b : k → ℝ => X i ⬝ᵥ b)
    (leaveOneOutBeta_eq_olsBeta_sub_invGram_mulVec X y i)
  have hpred :
      leaveOneOutPrediction X y i =
        fitted X y i - leaveOneOutResidual X y i * leverageValue X i := by
    calc
      leaveOneOutPrediction X y i = X i ⬝ᵥ leaveOneOutBeta X y i := rfl
      _ = X i ⬝ᵥ
          (olsBeta X y - leaveOneOutResidual X y i • (⅟ (Xᵀ * X) *ᵥ X i)) := by
            simpa using hcoef
      _ = fitted X y i - leaveOneOutResidual X y i * leverageValue X i := by
        unfold fitted
        rw [dotProduct_sub, dotProduct_smul, ← leverageValue_eq_row_invGram_row]
        simp [smul_eq_mul, Matrix.mulVec, dotProduct]
  unfold leaveOneOutResidual residual at *
  simp [Pi.sub_apply] at hpred ⊢
  nlinarith

/-- Hansen Theorem 3.7 / equation (3.44): leave-one-out prediction errors are
full-sample residuals scaled by `(1 - hᵢᵢ)⁻¹`. -/
theorem leaveOneOutResidual_eq_inv_one_sub_leverage_mul_residual
    (X : Matrix n k ℝ) (y : n → ℝ) (i : n)
    [Invertible (Xᵀ * X)] [Invertible (leaveOneOutGram X i)]
    (hdenom : 1 - leverageValue X i ≠ 0) :
    leaveOneOutResidual X y i = (1 - leverageValue X i)⁻¹ * residual X y i := by
  have h := one_sub_leverage_mul_leaveOneOutResidual_eq_residual X y i
  rw [← h]
  rw [← mul_assoc, inv_mul_cancel₀ hdenom, one_mul]

/-- Hansen equation (3.48): the change in coefficient estimates after dropping
observation `i`. -/
theorem olsBeta_sub_leaveOneOutBeta_eq_invGram_mulVec
    (X : Matrix n k ℝ) (y : n → ℝ) (i : n)
    [Invertible (Xᵀ * X)] [Invertible (leaveOneOutGram X i)] :
    olsBeta X y - leaveOneOutBeta X y i =
      leaveOneOutResidual X y i • (⅟ (Xᵀ * X) *ᵥ X i) := by
  have h := leaveOneOutBeta_eq_olsBeta_sub_invGram_mulVec X y i
  ext j
  have hj := congrFun h j
  simp [Pi.sub_apply, Pi.smul_apply] at hj ⊢
  linarith

/-- Hansen Section 3.21: the full-sample fitted value minus the leave-one-out
predicted value is `hᵢᵢ ẽᵢ`. -/
theorem fitted_sub_leaveOneOutPrediction_eq_leverage_mul_residual
    (X : Matrix n k ℝ) (y : n → ℝ) (i : n)
    [Invertible (Xᵀ * X)] [Invertible (leaveOneOutGram X i)] :
    fitted X y i - leaveOneOutPrediction X y i =
      leverageValue X i * leaveOneOutResidual X y i := by
  have hcoef := congrArg (fun b : k → ℝ => X i ⬝ᵥ b)
    (olsBeta_sub_leaveOneOutBeta_eq_invGram_mulVec X y i)
  change X i ⬝ᵥ (olsBeta X y - leaveOneOutBeta X y i) =
      X i ⬝ᵥ (leaveOneOutResidual X y i • (⅟ (Xᵀ * X) *ᵥ X i)) at hcoef
  have hleft : X i ⬝ᵥ (olsBeta X y - leaveOneOutBeta X y i) =
      fitted X y i - leaveOneOutPrediction X y i := by
    unfold fitted leaveOneOutPrediction
    rw [dotProduct_sub]
    simp [Matrix.mulVec, dotProduct]
  have hright : X i ⬝ᵥ (leaveOneOutResidual X y i • (⅟ (Xᵀ * X) *ᵥ X i)) =
      leverageValue X i * leaveOneOutResidual X y i := by
    rw [dotProduct_smul, ← leverageValue_eq_row_invGram_row]
    simp [smul_eq_mul, mul_comm]
  rw [hleft, hright] at hcoef
  exact hcoef

/-- Section 3.21 prediction-change diagnostic for a single observation. -/
noncomputable def predictionInfluence
    (X : Matrix n k ℝ) (y : n → ℝ) (i : n)
    [Invertible (Xᵀ * X)] [Invertible (leaveOneOutGram X i)] : ℝ :=
  |fitted X y i - leaveOneOutPrediction X y i|

/-- Hansen Section 3.21: the prediction-change diagnostic is
`|hᵢᵢ ẽᵢ|`. -/
theorem predictionInfluence_eq_abs_leverage_mul_leaveOneOutResidual
    (X : Matrix n k ℝ) (y : n → ℝ) (i : n)
    [Invertible (Xᵀ * X)] [Invertible (leaveOneOutGram X i)] :
    predictionInfluence X y i = |leverageValue X i * leaveOneOutResidual X y i| := by
  unfold predictionInfluence
  rw [fitted_sub_leaveOneOutPrediction_eq_leverage_mul_residual]

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
