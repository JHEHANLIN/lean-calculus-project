import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Interval.Set.Basic

open Set

-- Extreme Value Theorem：在 [a, b] 連續 ⇒ 一定有最大值與最小值
theorem extremeValueTheorem
    (f : ℝ → ℝ) {a b : ℝ} (h_le : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) :
    (∃ x ∈ Icc a b, ∀ y ∈ Icc a b, f y ≤ f x) ∧
    (∃ z ∈ Icc a b, ∀ y ∈ Icc a b, f z ≤ f y) := by
  -- 1. [a, b] 是緊緻的
  have hcompact : IsCompact (Icc a b) := isCompact_Icc

  -- 2. [a, b] 非空（至少有 a 自己）
  have hne : (Icc a b).Nonempty := ⟨a, by exact ⟨le_rfl, h_le⟩⟩

  -- 3. 用 IsCompact.exists_isMaxOn 拿到最大值點
  obtain ⟨x, hx_mem, hx_max⟩ :=
    hcompact.exists_isMaxOn hne hcont

  -- 4. 用 IsCompact.exists_isMinOn 拿到最小值點
  obtain ⟨z, hz_mem, hz_min⟩ :=
    hcompact.exists_isMinOn hne hcont

  -- 5. 把性質整理成想要的敘述
  refine ⟨?maxPart, ?minPart⟩
  · -- 最大值那一半
    refine ⟨x, hx_mem, ?_⟩
    intro y hy
    -- hx_max : IsMaxOn f (Icc a b) x
    -- 展開定義就是：∀ {y}, y ∈ Icc a b → f y ≤ f x
    exact hx_max hy
  · -- 最小值那一半
    refine ⟨z, hz_mem, ?_⟩
    intro y hy
    -- 同理 hx_min : IsMinOn f (Icc a b) z
    exact hz_min hy
