import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set

namespace Local
/-- 由 Cauchy MVT 推出 Lagrange MVT（`HasDerivAt` 版本）。 -/
theorem exists_deriv_eq_slope
  {f : ℝ → ℝ} {a b : ℝ}
  (hab : a < b)
  (hfc : ContinuousOn f (Icc a b))
  (hfd : DifferentiableOn ℝ f (Ioo a b)) :
  ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
by
  -- 直接用 Lagrange MVT 的 HasDerivAt 版本（f' := deriv f）
  simpa using
    (exists_hasDerivAt_eq_slope
      (f := f) (f' := deriv f) (a := a) (b := b)
      hab hfc
      (fun x hx =>
        ((hfd x hx).differentiableAt (IsOpen.mem_nhds isOpen_Ioo hx)).hasDerivAt))

theorem exists_hasDerivAt_eq_slope
  {f f' : ℝ → ℝ} {a b : ℝ}
  (hab : a < b)
  (hfc : ContinuousOn f (Icc a b))
  (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
  ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  obtain ⟨c, cmem, hc⟩ :
      ∃ c ∈ Ioo a b, (b - a) * f' c = (f b - f a) * (1 : ℝ) :=
    exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hff'
      id (1 : ℝ → ℝ) continuousOn_id
      (fun x _ => hasDerivAt_id x)
  use c, cmem
  rwa [mul_one, mul_comm, ← eq_div_iff (sub_ne_zero.2 hab.ne')] at hc

theorem exists_ratio_hasDerivAt_eq_ratio_slope
  {f f' g g' : ℝ → ℝ} {a b : ℝ}
  (hab : a < b)
  (hfc : ContinuousOn f (Icc a b))
  (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
  (hgc : ContinuousOn g (Icc a b))
  (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) :
  ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c := by
  let h x := (g b - g a) * f x - (f b - f a) * g x
  have hI : h a = h b := by
    simp [h]
    ring
  let h' x := (g b - g a) * f' x - (f b - f a) * g' x
  have hhh' : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := by
    intro x hx
    simpa [h, h'] using
      ((hff' x hx).const_mul (g b - g a)).sub
        ((hgg' x hx).const_mul (f b - f a))
  have hhc : ContinuousOn h (Icc a b) := by
    simpa [h] using
      (continuousOn_const.mul hfc).sub (continuousOn_const.mul hgc)
  rcases exists_hasDerivAt_eq_zero hab hhc hI hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩



end Local
