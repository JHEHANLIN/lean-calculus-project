import Mathlib.Analysis.Calculus.Deriv.Basic

open Filter Topology

/-!
Keep a local project-level alias for `HasDerivAt` inside the `Local`
namespace to avoid shadowing Mathlib's implementation while keeping the
function available for experimentation and teaching.
-/

namespace Local

abbrev HasDerivAt (f : ℝ → ℝ) (f' c : ℝ) : Prop :=
  Mathlib.Analysis.Calculus.Deriv.Basic.HasDerivAt f f' c

end Local
