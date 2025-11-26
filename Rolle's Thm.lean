import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

open scoped Topology

theorem rolle
  {f : ℝ → ℝ} {a b : ℝ}
  (hcont : ContinuousOn f (Set.Icc a b))
  (hdiff : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
  (hends : f a = f b)
  (hab : a < b) :
  ∃ c ∈ Set.Ioo a b, deriv f c = 0 := by
  classical
  have h := exists_deriv_eq_zero' hcont hdiff hends hab
  exact h
