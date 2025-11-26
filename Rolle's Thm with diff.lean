import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

open scoped Topology

/--
`HasLocalMax f c`：在點 `c` 有「局部極大值」，
實作上直接用 mathlib 內建的 `IsLocalMax f c`。
這樣之後可以直接吃到所有跟局部極值有關的現成 lemma。
-/
def HasLocalMax (f : ℝ → ℝ) (c : ℝ) : Prop :=
  IsLocalMax f c

/--
`HasLocalMin f c`：在點 `c` 有「局部極小值」，
同樣只是 `IsLocalMin f c` 的別名。
-/
def HasLocalMin (f : ℝ → ℝ) (c : ℝ) : Prop :=
  IsLocalMin f c

/--
Fermat 定理（局部極大版）：

若 `f` 在 `c` 可微，且 `c` 為局部極大點，
則在 `c` 的導數為 0。

數學上是用導數左右極限定義做出來；
在 mathlib 裡已經有對應 lemma：
`IsLocalMax.deriv_eq_zero`。
-/
lemma fermat_local_max
  {f : ℝ → ℝ} {c : ℝ}
  (hdiffc : DifferentiableAt ℝ f c)
  (hmax : HasLocalMax f c) :
  deriv f c = 0 := by
  -- `hdiffc` 在這個 proof 裡其實沒用到，這一行只是避免 linter 抱怨
  have _ := hdiffc
  -- 直接套用 `IsLocalMax.deriv_eq_zero`
  simpa [HasLocalMax] using
    (IsLocalMax.deriv_eq_zero (f := f) (a := c) hmax)

/--
Fermat 定理（局部極小版）：

若 `f` 在 `c` 可微，且 `c` 為局部極小點，
則在 `c` 的導數也為 0。
-/
lemma fermat_local_min
  {f : ℝ → ℝ} {c : ℝ}
  (hdiffc : DifferentiableAt ℝ f c)
  (hmin : HasLocalMin f c) :
  deriv f c = 0 := by
  have _ := hdiffc
  simpa [HasLocalMin] using
    (IsLocalMin.deriv_eq_zero (f := f) (a := c) hmin)

/--
**Lemma：常數函數在開區間上的導數為 0。**

假設：
* `f` 在 `(a, b)` 上處處可微；
* 在整個封閉區間 `[a, b]` 上，`f x = f a`（也就是常數）。

則結論：
* 對所有 `x ∈ (a, b)`，`deriv f x = 0`。
-/
lemma deriv_zero_on_Ioo_of_constant
  {f : ℝ → ℝ} {a b : ℝ}
  (hdiff : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
  (hconst : ∀ x ∈ Set.Icc a b, f x = f a) :
  ∀ x ∈ Set.Ioo a b, deriv f x = 0 := by
  intro x hxIoo
  -- 把 `x ∈ (a,b)` 升級成 `x ∈ [a,b]`
  have hxIcc : x ∈ Set.Icc a b := ⟨le_of_lt hxIoo.1, le_of_lt hxIoo.2⟩

  /- 選一個「完全在 [a,b] 裡面的小區間」：
     δ = min(x-a, b-x) > 0
     就可以確保 (x-δ, x+δ) ⊆ [a,b]。 -/
  have hx_left  : 0 < x - a := sub_pos.mpr hxIoo.1
  have hx_right : 0 < b - x := sub_pos.mpr hxIoo.2
  let δ : ℝ := min (x - a) (b - x)
  have hδ_pos : 0 < δ := by
    have : 0 < min (x - a) (b - x) := by
      exact lt_min_iff.mpr ⟨hx_left, hx_right⟩
    simpa [δ] using this

  -- `δ ≤ x - a` 與 `δ ≤ b - x`
  have hδ_le_left  : δ ≤ x - a := min_le_left (x - a) (b - x)
  have hδ_le_right : δ ≤ b - x := min_le_right (x - a) (b - x)

  /- 接下來證明：
     若 `|y - x| < δ`，則 `y ∈ [a,b]`。 -/
  have hball_sub_Icc : {y : ℝ | |y - x| < δ} ⊆ Set.Icc a b := by
    intro y hy
    have hyineq : |y - x| < δ := hy
    rcases abs_lt.mp hyineq with ⟨hy_left, hy_right⟩

    -- 左邊不等式：a ≤ y
    have hy1 : a ≤ y := by
      have h1 : a ≤ x - δ := by linarith [hδ_le_left]
      have h2 : x - δ < y := by linarith
      exact le_trans h1 (le_of_lt h2)

    -- 右邊不等式：y ≤ b
    have hy2 : y ≤ b := by
      have h3 : x + δ ≤ b := by linarith [hδ_le_right]
      have h4 : y < x + δ := by linarith
      exact le_trans (le_of_lt h4) h3

    exact ⟨hy1, hy2⟩

  /- 利用上面的 inclusion，把「小球」變成一個 nhds x 的集合，
     再用 `hconst` 說明在這個鄰域內 `f` 跟常數函數 `fun _ => f a` 相等。 -/
  have hloc :
      (fun y : ℝ => f y) =ᶠ[𝓝 x] fun _ : ℝ => f a := by
    -- `|y-x| < δ` 這個集合形成一個 `nhds x` 的基本鄰域
    have hball : {y : ℝ | |y - x| < δ} ∈ 𝓝 x := by
      have := Metric.ball_mem_nhds (x := x) hδ_pos
      simpa [Metric.ball, Real.dist_eq, abs_sub_comm] using this
    -- 在這個集合裡 f y = f a
    refine Filter.mem_of_superset hball ?_
    intro y hy
    have hyIcc : y ∈ Set.Icc a b := hball_sub_Icc hy
    exact hconst y hyIcc

  -- 避免 `hdiff` 沒被用到的 linter 警告
  have _ := hdiff

  /- 常數函數 `fun _ => f a` 的導數是 0，
     `hasDerivAt_const` 給出 `HasDerivAt (fun _ => f a) 0 x`。 -/
  have hconstDeriv : HasDerivAt (fun _ : ℝ => f a) 0 x :=
    hasDerivAt_const x (f a)

  /- 因為在 x 的鄰域裡兩個函數點值相同，
     用 `congr_of_eventuallyEq` 把 HasDerivAt 換到 `f` 上。 -/
  have hDerivf : HasDerivAt f 0 x :=
    hconstDeriv.congr_of_eventuallyEq hloc

  -- 取出導數，得到 `deriv f x = 0`
  exact hDerivf.deriv

/--
**Lemma：在 `[a,b]` 上連續，端點相等且非常數 ⇒
在 `(a,b)` 中有局部極大或局部極小。**

這裡就是把「極值定理 + 三個 case」形式化成一個 lemma：
* `IsCompact (Icc a b)` ⇒ 存在全域最大點 `xmax` 與全域最小點 `xmin`；
* 因為 `f a = f b` 且 `f` 不是常數，
  得到「某點 `x0` 的函數值 ≠ f a」，
  再細分成 `f x0 < f a` 或 `f x0 > f a`；
* 對應地得到內點全域最小 ⇒ 局部極小，
  或內點全域最大 ⇒ 局部極大。
-/
lemma exists_local_extrema_in_Ioo
  {f : ℝ → ℝ} {a b : ℝ}
  (hcont : ContinuousOn f (Set.Icc a b))
  (hab : a < b)
  (hends : f a = f b)
  (hnotconst : ¬ ∀ x ∈ Set.Icc a b, f x = f a) :
  ∃ c ∈ Set.Ioo a b, HasLocalMax f c ∨ HasLocalMin f c := by
  classical

  -- [a,b] 是緊集且非空
  have hcmp : IsCompact (Set.Icc a b) := isCompact_Icc
  have hne  : (Set.Icc a b).Nonempty := ⟨a, ⟨le_rfl, le_of_lt hab⟩⟩

  -- 取全域最大值點與最小值點
  obtain ⟨xmax, hxmax_mem, hxmax⟩ :=
    hcmp.exists_isMaxOn hne hcont
  obtain ⟨xmin, hxmin_mem, hxmin⟩ :=
    hcmp.exists_isMinOn hne hcont

  -- 先證明有某個點值 ≠ f a（「非常數」的形式化）
  have exists_x0 : ∃ x ∈ Set.Icc a b, f x ≠ f a := by
    by_contra H
    -- 若不存在，表示所有 x∈[a,b] 都有 f x = f a，與 hnotconst 矛盾
    have all_eq : ∀ x ∈ Set.Icc a b, f x = f a := by
      intro x hx; by_contra hx'; apply H; exact ⟨x, hx, hx'⟩
    exact hnotconst all_eq

  obtain ⟨x0, hx0Icc, hx0_ne⟩ := exists_x0

  -- `f x0` 不是 `f a` ⇒ 要嘛比它大，要嘛比它小
  have hx0_lt_or_gt : f x0 < f a ∨ f x0 > f a :=
    lt_or_gt_of_ne hx0_ne

  -- 分成「內部局部極小」或「內部局部極大」兩種情況
  rcases hx0_lt_or_gt with hx0_lt | hx0_gt

  /- 情況一：存在比 f(a) 更小的值 ⇒ 全域最小值也比 f(a) 小，
     又端點值 = f(a)，所以全域最小值不可能在端點上，
     只好在內部點 ⇒ 局部極小。 -/
  · -- 先證明 f xmin < f a
    have hmin_lt : f xmin < f a := by
      have hxmin_le : f xmin ≤ f x0 := hxmin hx0Icc
      exact lt_of_le_of_lt hxmin_le hx0_lt

    -- 接著證明 xmin 是內點：xmin ∈ (a,b)
    have hxminIoo : xmin ∈ Set.Ioo a b := by
      rcases hxmin_mem with ⟨ha, hb⟩
      -- xmin ≠ a：否則 f xmin < f a 會變 f a < f a
      have hxmin_ne_a : a ≠ xmin := by
        intro heq; subst heq
        exact lt_irrefl _ hmin_lt
      -- xmin ≠ b：利用端點 f b = f a
      have hxmin_ne_b : xmin ≠ b := by
        intro heq; subst heq
        have h' : f xmin < f xmin := by
          rw [hends] at hmin_lt
          exact hmin_lt
        exact lt_irrefl _ h'
      -- a < xmin 與 xmin < b
      have ha_lt_xmin : a < xmin := lt_of_le_of_ne ha (by intro heq; exact hxmin_ne_a heq)
      have xmin_lt_b : xmin < b := lt_of_le_of_ne hb hxmin_ne_b
      exact ⟨ha_lt_xmin, xmin_lt_b⟩

    -- 把 [a,b] 當成一個 nhds，利用 `IsMinOn.isLocalMin` 得到局部極小
    have hIcc_nhds : Set.Icc a b ∈ 𝓝 xmin :=
      Icc_mem_nhds hxminIoo.1 hxminIoo.2

    have hlocmin : IsLocalMin f xmin :=
      IsMinOn.isLocalMin hxmin hIcc_nhds

    refine ⟨xmin, hxminIoo, ?_⟩
    right; exact hlocmin

  /- 情況二：存在比 f(a) 更大的值 ⇒ 同理全域最大值必在內部，
     於是取得局部極大。 -/
  · have hmax_gt : f xmax > f a := by
      have hxmax_ge : f xmax ≥ f x0 := hxmax hx0Icc
      exact lt_of_lt_of_le hx0_gt hxmax_ge

    have hxmaxIoo : xmax ∈ Set.Ioo a b := by
      rcases hxmax_mem with ⟨ha, hb⟩
      -- 排除 xmax = a
      have hxmax_ne_a : a ≠ xmax := by
        intro heq; subst heq
        exact lt_irrefl _ hmax_gt
      -- 排除 xmax = b（用 f b = f a）
      have hxmax_ne_b : xmax ≠ b := by
        intro heq; subst heq
        have h' : f xmax < f xmax := by
          rw [hends] at hmax_gt
          exact hmax_gt
        exact lt_irrefl _ h'
      -- a < xmax 與 xmax < b
      have a_lt_xmax : a < xmax := lt_of_le_of_ne ha (by intro heq; exact hxmax_ne_a heq)
      have xmax_lt_b : xmax < b := lt_of_le_of_ne hb hxmax_ne_b
      exact ⟨a_lt_xmax, xmax_lt_b⟩

    have hIcc_nhds : Set.Icc a b ∈ 𝓝 xmax :=
      Icc_mem_nhds hxmaxIoo.1 hxmaxIoo.2

    have hlocmax : IsLocalMax f xmax :=
      IsMaxOn.isLocalMax hxmax hIcc_nhds

    refine ⟨xmax, hxmaxIoo, ?_⟩
    left; exact hlocmax

/--
**Rolle 定理（手做版本）：**

假設：
* `f` 在 `[a,b]` 上連續 (`ContinuousOn`)；
* 在開區間 `(a,b)` 上處處可微；
* 端點相等 `f a = f b`；
* 並且 `a < b`。

結論：
* 存在 `c ∈ (a,b)`，使得 `f` 在 `c` 可微，且 `deriv f c = 0`。

整個結構分成兩個 case：

1. `f` 在 `[a,b]` 上是常數 ⇒ 導數處處為 0，任取中點即可；
2. `f` 不是常數 ⇒ 用前面的 `exists_local_extrema_in_Ioo`
   找到局部極大或局部極小，再套 Fermat 定理。
-/
theorem rolle_manual
  {f : ℝ → ℝ} {a b : ℝ}
  (hcont : ContinuousOn f (Set.Icc a b))
  (hdiff : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
  (hends : f a = f b)
  (hab : a < b) :
  ∃ c ∈ Set.Ioo a b, DifferentiableAt ℝ f c ∧ deriv f c = 0 := by
  classical

  -- 先把「f 是否為常數」分成兩種情況
  by_cases hconst : ∀ x ∈ Set.Icc a b, f x = f a

  /- Case I：f 在 [a,b] 上是常數。 -/
  · have hderiv_zero : ∀ x ∈ Set.Ioo a b, deriv f x = 0 :=
      deriv_zero_on_Ioo_of_constant hdiff hconst

    /- 任取中點 c = (a+b)/2，先證明 c ∈ (a,b)。 -/
    have hsub : 0 < b - a := sub_pos.mpr hab
    have h1 : a < a + (b - a) / 2 := by linarith
    have h2 : a + (b - a) / 2 < b := by linarith

    have h_eq1 : (a + b) / 2 = a + (b - a) / 2 := by ring
    have h_eq2 : (a + b) / 2 = b - (b - a) / 2 := by ring

    have hmid : a < (a + b) / 2 ∧ (a + b) / 2 < b := by
      constructor <;> linarith [hsub]

    rcases hmid with ⟨h_left, h_right⟩
    let c : ℝ := (a + b) / 2
    have hcI : c ∈ Set.Ioo a b := ⟨h_left, h_right⟩
    have hdiffc : DifferentiableAt ℝ f c := hdiff c hcI
    have hderivc : deriv f c = 0 := hderiv_zero c hcI
    exact ⟨c, hcI, hdiffc, hderivc⟩

  /- Case II / III：f 不是常數 ⇒ 在 (a,b) 內有局部極大或局部極小。 -/
  · have hnotconst : ¬ ∀ x ∈ Set.Icc a b, f x = f a := hconst
    obtain ⟨c, hcI, hloc⟩ :=
      exists_local_extrema_in_Ioo hcont hab hends hnotconst

    have hdiffc : DifferentiableAt ℝ f c := hdiff c hcI
    -- 對「局部極大 / 局部極小」分情況，用 Fermat 定理得到導數為 0
    have hderivc : deriv f c = 0 := by
      cases hloc with
      | inl hmax => exact fermat_local_max hdiffc hmax
      | inr hmin => exact fermat_local_min hdiffc hmin

    exact ⟨c, hcI, hdiffc, hderivc⟩
