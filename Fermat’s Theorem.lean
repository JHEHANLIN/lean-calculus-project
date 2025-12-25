import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace Local

theorem IsLocalMin.deriv_eq_zero
  {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMin f a) :
  deriv f a = 0 := by
  classical
  by_cases hf : DifferentiableAt ℝ f a
  · -- 可微：用 HasDerivAt 版本的 Fermat，再轉成 deriv
    -- h.hasDerivAt_eq_zero : HasDerivAt f f' a → f' = 0
    -- hf.hasDerivAt : HasDerivAt f (deriv f a) a
    exact (h.hasDerivAt_eq_zero hf.hasDerivAt)
  · -- 不可微：deriv 在不可微點被定義為 0
    exact deriv_zero_of_not_differentiableAt hf

theorem IsLocalMax.deriv_eq_zero
  {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMax f a) :
  deriv f a = 0 := by
  classical
  by_cases hf : DifferentiableAt ℝ f a
  · exact (h.hasDerivAt_eq_zero hf.hasDerivAt)
  · exact deriv_zero_of_not_differentiableAt hf

end Local
