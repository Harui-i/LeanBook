import LeanBook.NatOrder.OrderDef
-- 6.3.1 狭義順序の定義

/-- m < nを表す -/
def MyNat.lt (m n : MyNat) : Prop := (m+1) ≤ n

/-- a < b という書き方をできるようにする -/
instance : LT MyNat where
  lt := MyNat.lt

example (m n : MyNat) : m < n ↔ (m+1) ≤ n := by
  -- これ↓をあまり理解していない
  dsimp [(· < ·), MyNat.lt]
  rfl

/-- 1≠ 0 -/
@[simp] theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

@[simp] theorem MyNat.zero_neq_one : 0 ≠ 1 := by
  intro h
  injection h

/-- ゼロに関する順序の性質-/
@[simp] theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
  rw [MyNat.le_iff_add]
  exists n
  ac_rfl

/-- 0以下の自然数は0しかない-/
theorem MyNat.zero_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by
  -- ここ、ゼロから始める...はnで帰納法まわしてるけどテキトーにsimpスレば通る
  simp [MyNat.le_iff_add] at h
  exact h

/-- 0以下の自然数は0しかない -/
@[simp] theorem MyNat.le_zero {n : MyNat} : n≤0 ↔ n = 0 := by
  constructor
  ·
    intro h
    exact MyNat.zero_of_le_zero h
  ·
    intro h
    simp [MyNat.le_iff_add]
    exact h


/-- 任意の自然数はゼロか正 -/
theorem MyNat.eq_zero_or_pos {n : MyNat} : n =0 ∨ 0 < n := by
  induction n with
  | zero => 
    left
    rfl
  | succ n ih => 
    dsimp [(· < ·), MyNat.lt] at *
    right
    simp [MyNat.le_iff_add]
    exists n
    ac_rfl

-- 補題3: n≤m ↔ n = m ∨ n < m
theorem MyNat.eq_or_lt_of_le {m n : MyNat} : n≤m → n = m ∨ n < m := by
  intro h
  dsimp [(· < ·), MyNat.lt] at *
  simp [MyNat.le_iff_add] at *
  obtain ⟨l, hl⟩ := h
  -- テキストみるとlの帰納法回すのがはやいっぽい。自分も結局lの機能法回してはいるのか
  have hl2 : l=0 ∨ 0 < l := MyNat.eq_zero_or_pos
  cases hl2 with
  | inl hl2 =>
    simp [hl2] at hl
    exact Or.inl hl
  | inr hl2 =>
    right
    rw [← hl]
    dsimp [(· < ·), MyNat.lt] at hl2
    simp at hl2
    -- hl2: 1 ≤ l

    -- ⊢: ∃ k, n+1+k = n+l
    -- 1+k = l
    -- k = l - 1だけど、引き算定義してないねんな
    have h_lprev : ∃ lp : MyNat, lp+1 = l := by
      induction l with
      |zero =>
        exfalso
        simp [MyNat.le_iff_add] at hl2
      | succ l2 ih =>
        exists l2
    
    obtain ⟨lprev, h_lprevl⟩ := h_lprev 
    exists lprev
    rw [show n+1+lprev = n+(lprev+1) from by ac_rfl]
    simp [h_lprevl]


/-- 狭義順序は広義順序より強い-/
theorem MyNat.le_of_lt {a b : MyNat} (h : a < b) : a ≤ b := by
  dsimp [(· < ·), MyNat.lt] at h
  simp [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h 
  exists k+1
  rw [show a+(k+1) = a+1+k from by ac_rfl]
  exact hk

theorem MyNat.le_of_eq_or_lt {m n : MyNat} : n = m ∨ n < m → n ≤ m := by
  intro h
  cases h with
  | inl h =>
    simp [MyNat.le_iff_add]
    exists 0
  | inr h =>
    dsimp [(· < ·), MyNat.lt] at h
    exact MyNat.le_of_lt h

/-- 広義順序≤は等号と狭義順序<で書き換えられる-/
theorem MyNat.le_iff_eq_or_lt {m n : MyNat} : n≤m ↔ n=m ∨ n < m := by
  constructor
  · apply MyNat.eq_or_lt_of_le
  · apply MyNat.le_of_eq_or_lt 

-- なんか、le_iff_addを振り回したらテキストよりも簡単?に示せた
theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
  dsimp [(· < ·), MyNat.lt]
  induction b with
  | zero => 
    right
    simp [MyNat.le_iff_add]
  | succ n ih =>
    -- ih: a+1 ≤ n ∨ n ≤ a
    -- a+1 ≤ n+1 ∨ n+1 ≤ a
    cases ih with
    | inl ih =>
      left
      simp [MyNat.le_iff_add] at *
      obtain ⟨l, il⟩ := ih
      exists l+1
      rw [← il]
      rw [show a+1+(l+1)=a+1+l+1 from by ac_rfl]
    | inr ih => 
      simp [MyNat.le_iff_add] at *
      obtain ⟨l, il⟩ := ih
      simp [← il] 
      --⊢ (∃ k, n+l+1+k=n+1) ∨ ∃ k, n+1+k=n+l
      induction l with
      | zero => 
        left
        exists 0
      | succ m ih =>
        right
        exists m
        ac_rfl


theorem MyNat.lt_of_not_le {a b : MyNat} (h: ¬ a ≤ b) : b < a := by
  have h1 := MyNat.lt_or_ge b a
  cases h1 with
  | inl h1 =>
    exact h1
  | inr h1 =>
    exfalso
    exact h h1

theorem MyNat.not_le_of_lt {a b : MyNat} (h : a < b) : ¬ b ≤ a := by
  intro h2
  let h1 := MyNat.lt_or_ge b a
  cases h1 with
  | inl h1 =>
    dsimp [(· < ·), MyNat.lt] at *
    simp [MyNat.le_iff_add] at *
    obtain ⟨k, h⟩ := h 
    obtain ⟨k2, h2⟩ := h2
    rw [← h] at h2

    -- h2: a + 1 + k + k2 = a
    -- この右辺のaをa+0に変えたいが、普通のrwは両方変えてしまう
    -- rwにどれを変えるか指定したいときはnth_rw
    -- を使おうとおもったがMathlibのimportは大変なのでこれで凌ぐ
    rw (config := {occs := .pos [2]}) [show a = a+0 from by ac_rfl] at h2

    -- 左側を a + (1 + k + k2) の形にそろえてから左加法キャンセル
    have h2' : a + (1 + k + k2) = a + 0 := by
      --simpa [MyNat.add_assoc] using h2
      simp [MyNat.add_assoc] at h2
    have h3 : 1 + k + k2 = 0 :=
      (MyNat.add_left_cancel_iff).1 h2'

    -- h3: 1+k+k2 = 0が怪しすぎる
    have h4: 1+k+k2 ≤ 0 := by
      apply MyNat.le_of_eq_or_lt 
      exact Or.inl h3
    
    simp [MyNat.le_iff_add] at h4
  | inr h1 =>
    -- h : a < b
    -- h2: b ≤ a
    dsimp [(· < ·), MyNat.lt] at h
    simp [MyNat.le_iff_add] at *
    obtain ⟨k, hk⟩ := h
    obtain ⟨k2, hk2⟩ := h2 
    rw [← hk] at hk2
    rw (config := {occs := .pos [2]}) [show a = a+0 from by ac_rfl] at hk2
    rw [show a+1+k+k2 = a+(1+k+k2) from by ac_rfl] at hk2

    simp [MyNat.add_left_cancel_iff] at hk2

theorem MyNat.lt_iff_le_not_le (a b : MyNat) : a < b ↔ a≤b ∧ ¬ b ≤ a := by
  constructor <;> intro h
  ·
    constructor
    ·
      exact MyNat.le_of_lt h
    ·
      -- h: a<b
      -- ⊢ ¬ b≤a
      exact MyNat.not_le_of_lt h
  ·
    exact MyNat.lt_of_not_le h.right

theorem MyNat.le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  cases (MyNat.lt_or_ge a b) <;> simp_all [MyNat.le_of_lt]

example (a : MyNat) : a ≠ a+1 := by
  intro h
  simp at h

example (n : MyNat) : ¬ n+1 ≤ n := by
  -- theorem MyNat.eq_or_lt_of_le {m n : MyNat} : n≤m → n = m ∨ n < m := by
  intro h
  have h2 : n+1=n ∨ n+1 < n := by
    exact MyNat.eq_or_lt_of_le h 
  cases h2 with
  |inl h2 =>
    simp at h2

  |inr h2 =>
    simp [MyNat.le_iff_add] at h
    obtain ⟨k, hk⟩ := h
    rw [show n = n+0 from by ac_rfl] at hk
    rw [show n+0+1+k = n+(1+k) from by ac_rfl] at hk
    simp at hk

