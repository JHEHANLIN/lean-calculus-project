import Mathlib

namespace Local

/-- 課本式 ε-δ 差商極限定義：`deriv f f' c` 表示 f' 是 f 在 c 的導數（Prop） -/
def deriv (f : ℝ → ℝ) (f' c : ℝ) : Prop :=
  ∀ ε > 0,
    ∃ δ > 0, ∀ h,
      0 < |h| ∧ |h| < δ
      → |(f (c + h) - f c) / h - f'| < ε

/-- 課本式局部極大：存在 δ0>0，使得 |h|<δ0 → f(c+h) ≤ f(c) -/
def IsLocalMax (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ δ0 > 0, ∀ h, |h| < δ0 → f (c + h) ≤ f c
/-- 課本式局部極小：存在 δ0>0，使得 |h|<δ0 → f c ≤ f (c + h) -/
def IsLocalMin (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ δ0 > 0, ∀ h, |h| < δ0 → f c ≤ f (c + h)
/-- Fermat 定理（局部極大 + 可微 ⇒ 導數為 0）：
若 c 是局部極大點，且 `deriv f f' c`，則 `f' = 0`。 -/
theorem fermat_localMax
    {f : ℝ → ℝ} {c f' : ℝ}
    (hmax : IsLocalMax f c)
    (hf : deriv f f' c) : f' = 0 := by
  -- 先證：∀ ε>0, |f'| < ε
  have hforall : ∀ ε > 0, |f'| < ε := by
    intro ε hε
    rcases hmax with ⟨δ0, hδ0pos, hδ0⟩
    rcases hf ε hε with ⟨δ1, hδ1pos, hδ1⟩
    -- 共同 δ
    let δ : ℝ := min δ0 δ1
    have hδpos : 0 < δ := lt_min hδ0pos hδ1pos
    have hδle0 : δ ≤ δ0 := min_le_left _ _
    have hδle1 : δ ≤ δ1 := min_le_right _ _
    -- 取 h = δ/2 > 0
    let h : ℝ := δ / 2
    have hpos : 0 < h := by positivity
    have habs_h_pos : 0 < |h| := by simpa [h, abs_of_pos hpos] using hpos
    have habs_h_lt_δ : |h| < δ := by
      simpa [h, abs_of_pos hpos] using (by linarith [hδpos] : δ/2 < δ)
    have habs_h_lt_δ0 : |h| < δ0 := lt_of_lt_of_le habs_h_lt_δ hδle0
    have habs_h_lt_δ1 : |h| < δ1 := lt_of_lt_of_le habs_h_lt_δ hδle1
    -- (A) h>0 時：由局部極大得 f(c+h) ≤ f(c) ⇒ 差商 q ≤ 0
    have fch_le : f (c + h) ≤ f c := hδ0 h habs_h_lt_δ0
    have num_le_zero : f (c + h) - f c ≤ 0 := sub_nonpos.mpr fch_le
    set q : ℝ := (f (c + h) - f c) / h
    have q_le_zero : q ≤ 0 := by
      -- numerator ≤ 0, denominator > 0
      dsimp [q]
      -- q * h = f(c+h) - f c, and h > 0, so q ≤ 0
      have hneq : h ≠ 0 := by linarith [hpos]
      have hmul : q * h = f (c + h) - f c := by dsimp [q]; field_simp [hneq]
      have q_mul_h_le : q * h ≤ 0 := by linarith [hmul, num_le_zero]
      have q_mul_h_le' : q * h ≤ 0 * h := by simpa [mul_zero] using q_mul_h_le
      exact le_of_mul_le_mul_right q_mul_h_le' hpos
    -- 由導數定義：|q - f'| < ε
    have hineq_pos : |q - f'| < ε := by
      -- 注意：定義裡是 |... - f'|，我們剛好令 q 為差商
      have := hδ1 h ⟨habs_h_pos, habs_h_lt_δ1⟩
      simpa [q, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    -- 由 |q - f'| < ε 得 f' < q + ε ≤ ε
    have f'_lt_eps : f' < ε := by
      have hlt : -ε < q - f' ∧ q - f' < ε := abs_lt.mp hineq_pos
      have f'_lt_q_add : f' < q + ε := by linarith [hlt.1]
      have q_add_le : q + ε ≤ ε := by linarith [q_le_zero]
      exact lt_of_lt_of_le f'_lt_q_add q_add_le
    -- (B) 用 -h（仍滿足 |-| < δ0, δ1）
    have habs_neg : |(-h)| = |h| := by simp [abs_neg]
    have habs_neg_pos : 0 < |(-h)| := by simpa [habs_neg] using habs_h_pos
    have habs_neg_lt_δ0 : |(-h)| < δ0 := by simpa [habs_neg] using habs_h_lt_δ0
    have habs_neg_lt_δ1 : |(-h)| < δ1 := by simpa [habs_neg] using habs_h_lt_δ1
    have hneg : (-h) < 0 := by linarith [hpos]
    -- 由局部極大：f(c-h) ≤ f(c) ⇒ numerator' ≤ 0
    have fchm_le : f (c + (-h)) ≤ f c := hδ0 (-h) habs_neg_lt_δ0
    have num'_le_zero : f (c + (-h)) - f c ≤ 0 := sub_nonpos.mpr fchm_le
    -- 分母 (-h) < 0，故 q' = numerator'/(-h) ≥ 0
    set q' : ℝ := (f (c + (-h)) - f c) / (-h)
    have q'_ge_zero : 0 ≤ q' := by
      dsimp [q']
      -- q' * (-h) = f(c-h) - f c ≤ 0, so q' * h ≥ 0 and thus q' ≥ 0 since h > 0
      have hneq' : (-h) ≠ 0 := by linarith [hneg]
      have hmul' : q' * (-h) = f (c + (-h)) - f c := by dsimp [q']; field_simp [hneq']
      have q'_mul_neg_h_le : q' * (-h) ≤ 0 := by simpa [hmul'] using num'_le_zero
      have q'_mul_h_ge : 0 ≤ q' * h := by
        have : q' * h = - (q' * (-h)) := by ring
        linarith [q'_mul_neg_h_le, this]
      have q_mul_h_ge' : 0 * h ≤ q' * h := by simpa [mul_zero] using q'_mul_h_ge
      exact le_of_mul_le_mul_right q_mul_h_ge' hpos
    -- 導數不等式：|q' - f'| < ε
    have hineq_neg : |q' - f'| < ε := by
      have := hδ1 (-h) ⟨habs_neg_pos, habs_neg_lt_δ1⟩
      simpa [q', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    -- 由 |q' - f'| < ε 與 q' ≥ 0 推得 -ε < f'
    have neg_eps_lt_f' : -ε < f' := by
      have hlt : -ε < q' - f' ∧ q' - f' < ε := abs_lt.mp hineq_neg
      have f'_gt_q'_sub : q' - ε < f' := by linarith [hlt.2]
      have q'_sub_ge : -ε ≤ q' - ε := by linarith [q'_ge_zero]
      exact lt_of_le_of_lt q'_sub_ge f'_gt_q'_sub
    -- 合併得 |f'| < ε
    exact abs_lt.mpr ⟨neg_eps_lt_f', f'_lt_eps⟩
  -- 由 ∀ε>0, |f'|<ε 推出 f'=0（取 ε=|f'|/2 反證）
  by_contra hne
  have habs_pos : 0 < |f'| := abs_pos.mpr hne
  have : |f'| < |f'| / 2 := hforall (|f'| / 2) (by linarith [habs_pos])
  linarith

theorem fermat_localMin
    {f : ℝ → ℝ} {c f' : ℝ}
    (hmin : IsLocalMin f c)
    (hf : deriv f f' c) : f' = 0 := by
  -- 先證：∀ ε>0, |f'| < ε
  have hforall : ∀ ε > 0, |f'| < ε := by
    intro ε hε
    rcases hmin with ⟨δ0, hδ0pos, hδ0⟩
    rcases hf ε hε with ⟨δ1, hδ1pos, hδ1⟩
    -- 共同 δ
    let δ : ℝ := min δ0 δ1
    have hδpos : 0 < δ := lt_min hδ0pos hδ1pos
    have hδle0 : δ ≤ δ0 := min_le_left _ _
    have hδle1 : δ ≤ δ1 := min_le_right _ _
    -- 取 h = δ/2 > 0
    let h : ℝ := δ / 2
    have hpos : 0 < h := by positivity
    have habs_h_pos : 0 < |h| := by simpa [h, abs_of_pos hpos] using hpos
    have habs_h_lt_δ : |h| < δ := by
      simpa [h, abs_of_pos hpos] using (by linarith [hδpos] : δ / 2 < δ)
    have habs_h_lt_δ0 : |h| < δ0 := lt_of_lt_of_le habs_h_lt_δ hδle0
    have habs_h_lt_δ1 : |h| < δ1 := lt_of_lt_of_le habs_h_lt_δ hδle1
    ----------------------------------------------------------------
    -- (A) h>0：局部極小 ⇒ f(c) ≤ f(c+h) ⇒ numerator ≥ 0 ⇒ q ≥ 0
    ----------------------------------------------------------------
    have fc_le_fch : f c ≤ f (c + h) := hδ0 h habs_h_lt_δ0
    have num_ge_zero : 0 ≤ f (c + h) - f c := sub_nonneg.mpr fc_le_fch
    set q : ℝ := (f (c + h) - f c) / h
    have q_ge_zero : 0 ≤ q := by
      have : 0 ≤ (f (c + h) - f c) / h :=
        div_nonneg num_ge_zero (le_of_lt hpos)
      simpa [q] using this
    -- 導數不等式：|q - f'| < ε
    have hineq_pos : |q - f'| < ε := by
      have := hδ1 h ⟨habs_h_pos, habs_h_lt_δ1⟩
      simpa [q] using this
    -- 由 |q - f'| < ε 且 q ≥ 0 推得 -ε < f'
    have neg_eps_lt_f' : -ε < f' := by
      have hlt : -ε < q - f' ∧ q - f' < ε := abs_lt.mp hineq_pos
      have f'_gt_q_sub : q - ε < f' := by linarith [hlt.2]
      have q_sub_ge : -ε ≤ q - ε := by linarith [q_ge_zero]
      exact lt_of_le_of_lt q_sub_ge f'_gt_q_sub
    ----------------------------------------------------------------
    -- (B) 用 -h：
    --     局部極小 ⇒ f(c) ≤ f(c-h) ⇒ numerator' ≥ 0
    --     分母 (-h) < 0，所以 q' ≤ 0
    ----------------------------------------------------------------
    have habs_neg : |(-h)| = |h| := by simp [abs_neg]
    have habs_neg_pos : 0 < |(-h)| := by simpa [habs_neg] using habs_h_pos
    have habs_neg_lt_δ0 : |(-h)| < δ0 := by simpa [habs_neg] using habs_h_lt_δ0
    have habs_neg_lt_δ1 : |(-h)| < δ1 := by simpa [habs_neg] using habs_h_lt_δ1
    have hneg : (-h) < 0 := by linarith [hpos]
    have fc_le_fchm : f c ≤ f (c + (-h)) := hδ0 (-h) habs_neg_lt_δ0
    have num'_ge_zero : 0 ≤ f (c + (-h)) - f c := sub_nonneg.mpr fc_le_fchm
    set q' : ℝ := (f (c + (-h)) - f c) / (-h)
    have q'_le_zero : q' ≤ 0 := by
      have : (f (c + (-h)) - f c) / (-h) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos num'_ge_zero (le_of_lt hneg)
      simpa [q'] using this
    -- 導數不等式：|q' - f'| < ε
    have hineq_neg : |q' - f'| < ε := by
      have := hδ1 (-h) ⟨habs_neg_pos, habs_neg_lt_δ1⟩
      simpa [q'] using this
    -- 由 |q' - f'| < ε 且 q' ≤ 0 推得 f' < ε
    have f'_lt_eps : f' < ε := by
      have hlt : -ε < q' - f' ∧ q' - f' < ε := abs_lt.mp hineq_neg
      have f'_lt_q'_add : f' < q' + ε := by linarith [hlt.1]
      have q'_add_le : q' + ε ≤ ε := by linarith [q'_le_zero]
      exact lt_of_lt_of_le f'_lt_q'_add q'_add_le
    -- 合併得 |f'| < ε
    exact abs_lt.mpr ⟨neg_eps_lt_f', f'_lt_eps⟩
  -- 由 ∀ε>0, |f'|<ε 推出 f'=0（取 ε=|f'|/2 反證）
  by_contra hne
  have habs_pos : 0 < |f'| := abs_pos.mpr hne
  have : |f'| < |f'| / 2 :=
    hforall (|f'| / 2) (by nlinarith [habs_pos])
  linarith

end Local
