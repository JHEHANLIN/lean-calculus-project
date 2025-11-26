import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

open scoped Topology

theorem rolle
  {f : ℝ → ℝ} {a b : ℝ}
  (hcont : ContinuousOn f (Set.Icc a b))
  (hdiff : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
  (hends : f a = f b)
  (hab : a < b) :
  ∃ c ∈ Set.Ioo a b, deriv f c = 0 := by
  classical
  -- avoid unused-variable linter for `hdiff`
  have _ := hdiff
  have h := exists_deriv_eq_zero (a := a) (b := b) (f := f) hab hcont hends
  exact h
