-- 6.2 順序を定義する
import LeanBook.NatOder.AddCancel

-- 6.2.1 順序関係を帰納的に定義する

/-- 自然数上の広義の順序関係 -/
inductive MyNat.le (n : MyNat) : MyNat → Prop
  /-- ∀ n, n ≤ n -/
  | refl : MyNat.le n n 
  /-- n ≤ m ならば n ≤ m+1-/
  | step {m : MyNat} : MyNat.le n m → MyNat.le n (m+1)

/-- MyNat.leを ≤で表せるようにする-/
instance : LE MyNat where
  le := MyNat.le

/-
Leanではすべての帰納型で帰納法が使える。 
Leanでは、「順序関係やデータ構造など幅広い対象を帰納的に定義し、証明の際は帰納法を用いる」
のが一般的らしい。
-/

-- これどういうこと？
/-
example (m n : MyNat) (P : MyNat → MyNat → Prop) (h : m ≤ n) : P m n := by
  induction h with
  | refl =>
      guard_target =ₛ P m m
      sorry
  -- このアットマークなに？
  -- これは暗黙的引数を明示的引数に変えるための構文。
  -- Leanでは明示的に名前をつけていない変数や、名前が被ってしまった変数には†がついて
  -- 明示的アクセスができなくなる.
  -- MyNat.leの定義にでてくるmにnを与えている?
  | @step n h ih  =>
      -- P m n → P m (n+1)を示す
      guard_hyp ih : P m n
      guard_target =ₛ P m (n+1)
      sorry
-/

-- MyNat上の帰納法の場合と同様で、そのまま帰納法を使うと定義した記法が崩れる
-- 4.5.3でやったアレ
@[induction_eliminator]
def MyNat.le.recAux {n b : MyNat}
  {motive : (a : MyNat) → n ≤ a → Prop}
  (refl : motive n MyNat.le.refl)
  (step : ∀ {m : MyNat} (a : n ≤ m),
    motive m a → motive (m+1) (MyNat.le.step a))
  (t : n ≤ b) : 
  motive b t := by
    induction t with
    | refl => exact refl
    | @step c h ih =>
      exact step (a := h) ih


/-- 反射律 -/
theorem MyNat.le_refl (n : MyNat) : n ≤ n := by
  exact MyNat.le.refl

variable {m n k : MyNat}
theorem MyNat.le_step(h : n≤m) : n ≤ m+1 := by
  apply MyNat.le.step
  exact h

/-- 推移律 -/
theorem MyNat.le_trans (hnm : n≤m) (hmk : m ≤ k) : n≤k := by
  induction hmk with 
  | refl =>
    exact hnm
  | @step k hmk hnk =>
    --  hmk : m ≤ k
    --  hnk : n ≤ k
    --  ⊢ n≤k+1
    exact le_step hnk

-- 反射率をrflタクティクから使えるように
attribute [refl] MyNat.le_refl

theorem MyNat.le_add_one_right (n : MyNat) : n ≤ n+1 := by
  apply MyNat.le_step
  -- ⊢ n ≤ n
  -- rflで閉じられる。すげー
  rfl

-- 推移率は推移的な二項関係なのでcalcで使えるようにしたい
/-- MyNat.le を推移的な二項関係として登録する -/
instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· ≤ ·) (· ≤ ·) where
  trans := MyNat.le_trans

theorem MyNat.le_add_one_left (n : MyNat) : n ≤ 1 + n := calc
  _ ≤ n+1 := by apply le_add_one_right
  _ = 1+n := by ac_rfl

-- n≤nや n≤n+1は等式でも同値性でもないが、[simp]属性を付与して再利用可能にできる
attribute [simp] MyNat.le_refl MyNat.le_add_one_right MyNat.le_add_one_left
-- simpは等式や同値性の形をしたルールしか扱わないので、このようなルールを登録すると自動的に等式の書き換えルールに変換される
-- (n ≤ n) ↔ True とか

-- 6.2.4 順序関係を和の等式に書き換える
-- n≤ m は ∃ k, n+k = mに書き換えられる

/-- a ≤ bから和の等式を導く -/
theorem MyNat.le.dest (h : n≤m) : ∃ k, n+k = m := by
  induction h with
  | refl =>
    exists 0
  | @step a hna hk =>
    -- ここテキストだともっときれいに証明してる
    -- hna : n ≤ a
    -- hk : ∃ k, n + k = a
    -- ⊢  ∃ k, n+k = a + 1
    obtain ⟨k, hk⟩ := hk 
    exists k+1
    calc
      _ = n + (k+1) := by rfl
      _ = (n+k) + 1 := by ac_rfl
      _ = a + 1 := by rw [hk]

theorem MyNat.le_add_right (n m : MyNat) : n ≤ n + m := by
  induction m with
  | zero => rfl
  | succ m im =>
    -- im : n ≤ n + m
    -- ⊢ n ≤ n + (m + 1)
    rw [show n + (m+1) = n+m+1 from by ac_rfl]
    -- ⊢ n ≤ n+m+1
    exact le_step im

/-- 和の等式から a ≤ b を導く -/
theorem MyNat.le.intro (h : n + k = m) : n ≤ m := by
  induction k with
  | zero => 
    simp at h
    simp [h]
  | succ k ih =>
    -- ih: n + k = m → n ≤ m
    -- h : n + (k+1) = m
    -- ⊢ n ≤ m
    rw [← h]
    apply MyNat.le_add_right


/-- 順序関係 n≤mを足し算で書き換える-/
theorem MyNat.le_iff_add : n ≤ m ↔ ∃ k, n + k = m := by
  constructor
  ·
    intro h
    -- h : n≤m
    -- ⊢ ∃ k, n + k = m
    apply MyNat.le.dest
    exact h
  ·
    intro h
    obtain ⟨k, ih⟩ := h
    -- ih : n + k = m
    -- ⊢ : n ≤ m
    exact le.intro ih
   

-- 6.2.5 練習問題
example : 1 ≤ 4 := by
  simp [MyNat.le_iff_add]
  exists 3

