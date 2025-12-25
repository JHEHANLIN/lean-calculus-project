import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

open Set

namespace Local

theorem Rolle's_Theorem
  {f : ℝ → ℝ} {a b : ℝ}
  (hcont : ContinuousOn f (Set.Icc a b))
  (hends : f a = f b)
  (hab : a < b) :
  ∃ c ∈ Set.Ioo a b, deriv f c = 0 := by
  simpa using exists_deriv_eq_zero (a := a) (b := b) (f := f) hab hcont hends

theorem exists_deriv_eq_zero
  {f : ℝ → ℝ} {a b : ℝ}
  (hab : a < b)
  (hfc : ContinuousOn f (Icc a b))
  (hfI : f a = f b) :
  ∃ c ∈ Ioo a b, deriv f c = 0 := by
  rcases exists_isLocalExtr_Ioo hab hfc hfI with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, hc.deriv_eq_zero⟩

end Local
