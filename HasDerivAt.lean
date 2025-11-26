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

def HasDerivAt (f : ℝ → ℝ) (f' c : ℝ) : Prop :=
  Tendsto
    (fun h : ℝ => (f (c + h) - f c - f' * h) / |h|)
    ((𝓝 (0 : ℝ) : Filter ℝ))
    ((𝓝 (0 : ℝ) : Filter ℝ))

end Local
