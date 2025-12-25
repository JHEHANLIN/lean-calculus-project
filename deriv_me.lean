import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic

open Filter Topology

/-!
Project-local derivative predicate (kept separate from Mathlib's
`HasDerivAt`). This is intended for teaching/experiments; keep it in a
`Local` namespace to avoid name clashes with real mathlib exports.
-/

namespace Local

def deriv (f : ℝ → ℝ) (f' c : ℝ) : Prop :=
  ∀ ε > 0,
    ∃ δ > 0, ∀ h,
      0 < |h| ∧ |h| < δ
      → |(f (c + h) - f c) / h - f'| < ε

theorem deriv_sq (c : ℝ) : deriv (fun x : ℝ => x^2) (2*c) c := by
  intro ε hεpos
  refine ⟨ε, hεpos, ?_⟩
  intro h hh
  have hne : h ≠ 0 := by
    exact abs_ne_zero.mp (ne_of_gt hh.1)
  -- 把差商化簡成 h（核心）
  have hcalc :
      ((fun x : ℝ => x^2) (c + h) - (fun x : ℝ => x^2) c) / h - (2*c) = h := by
    field_simp [hne]
    ring
  -- |差商 - 2c| = |h| < ε
  simpa [hcalc] using hh.2

end Local
