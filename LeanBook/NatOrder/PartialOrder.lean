import LeanBook.NatOrder.OrdMonoid

-- 6.6章 a≤b → b≤a → a = bを示す
-- 6.6.1 準備: 順序関係の推移律を示す
-- 広義順序そのものと、狭義順序そのものの推移律はもう示しているが混ざった場合は示していない(?)
--
variable {n m k : MyNat}

theorem MyNat.lt_trans (h₁ : n < m) (h₂ : m < k) : n < k := by
  notation_simp at *
  -- h₁ : n + 1 ≤ m
  -- h₂ : m + 1 ≤ k 
  -- ⊢ n + 1 ≤ k
  calc 
  _ = n+1 := by rfl
  _ ≤ m := h₁ 
  _ ≤ m+1 := by simp
  _ ≤ k := h₂ 

theorem MyNat.lt_of_le_of_lt (h₁ : n ≤ m) (h₂ : m < k) : n < k := by
  notation_simp at *
  -- h₁: n ≤ m
  -- h₂: m + 1 ≤ k
  -- ⊢ n + 1 ≤ k
  calc
    _ ≤ m + 1 := by compatible
    _ ≤ k := h₂

theorem MyNat.lt_of_lt_of_le (h₁ : n < m) (h₂ : m ≤ k) : n < k := by
  notation_simp at *
  -- h₁ : n + 1 ≤ m
  -- h₂ : m ≤ k
  -- ⊢ n + 1 ≤  k
  calc
    _ ≤ m := h₁
    _ ≤ k := h₂ 

instance : Trans (· < · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_trans

instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_of_le_of_lt

instance : Trans (· < · : MyNat → MyNat → Prop) (· ≤ ·) (· < ·) where
  trans := MyNat.lt_of_lt_of_le

-- 6.6.2 狭義順序の非反射律
-- ¬( n < n)
@[simp]
theorem MyNat.lt_irrefl (n : MyNat) : ¬ n < n := by
  intro h
  notation_simp at *
  simp [MyNat.le_iff_add] at h
  obtain ⟨k, hk⟩ := h 
  -- hk: n + 1 + k = n
  rw [show n+1+k = n+(1+k) from by ac_rfl] at hk
  rw (config := {occs := .pos [2]}) [show n = n+0 from by ac_rfl] at hk

  have hk2 : 1+k = 0 := MyNat.add_left_cancel hk
  rw [show 1+k=k+1 from by ac_rfl] at hk2
  -- hk2: k+1 = 0
  -- k+1はk.succだけど、これは帰納型が単射であることに矛盾する
  injections

-- 6.6.3 反対称律
--
theorem MyNat.le_antisymm (h₁ : n ≤ m) (h₂ : m ≤ n) : n = m := by
  simp [MyNat.le_iff_add]  at h₁ 
  obtain ⟨k₁, hk₁⟩ := h₁ 
  rw [← hk₁]
  cases k₁ with
  | zero => 
    simp
  | succ k => 
    -- hk₁ : n + k.succ = m
    -- h₂ : m ≤ n
    exfalso
    rw [← hk₁] at h₂ 
    -- h₂ : n + k.succ ≤ n
    simp [MyNat.le_iff_add] at h₂
    obtain ⟨k₂, hk₂⟩ := h₂
    rw [show (n+k+k₂).succ = n + (k+k₂).succ from by ac_rfl] at hk₂ 
    -- hk₂ : n + (k + k₂).succ = n
    rw (config := {occs := .pos [2]}) [show n = n+0 from by ac_rfl] at hk₂
    simp at hk₂
    -- hk₂ : (k+k₂).succ = 0
    injections

-- 練習問題   6.6.4
example (a b : MyNat) : a < b ∨ a = b → a ≤ b := by
  intro h
  rcases h with h1|h2
  ·
    notation_simp at h1
    -- h1 : a + 1 ≤ b
    -- ⊢ a ≤ b
    calc 
      _ = a := by rfl
      _ ≤ a + 1 := by simp
      _ ≤ b := h1

  ·
    -- h2 : a = b
    -- ⊢ a ≤ b
    rw [h2]
