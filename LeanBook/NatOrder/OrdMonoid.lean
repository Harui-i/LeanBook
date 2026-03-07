-- 6.5 足し算が順序を保つことを示す
import LeanBook.NatOrder.NotationSimp
import LeanBook.NatOrder.CompatibleTag

-- 6.5.1 足し算は順序を保つ

-- 数学では、「二項関係∼が関数fの適用で保たれる」というタイプの定理がよく出てくる
-- その一つに「(l+·)という関数を適用しても順序関係が保たれる」というのがある。
-- 式で書くと n ≤ m → l+n ≤ l+m

variable {a b m n : MyNat}

/-- 足し算(l+·)は順序を保つ-/
theorem MyNat.add_le_add_left (h: n≤m) (l: MyNat) : l + n ≤ l+m := by
  simp [MyNat.le_iff_add] at *
  obtain ⟨kh, hk⟩ := h
  -- hk: n+kh = m
  -- ⊢ ∃ k, l + n + k = l + m
  /-
  最初はこうやって書いた。けど、等式を逆に使うのは
  -- simp [← h]みたいにやればよかった。
  have hk2 : m = n + kh := by
    simp [hk]
  simp [hk2]
  -/
  simp [← hk]
  -- ⊢ ∃ k, l + n + k = l + (n+kh)
  rw [show l+(n+kh) = l+n+kh from by ac_rfl]
  -- ⊢ ∃ k, l + n + k = l + n+kh
  exists kh

/-- 足し算(· + l) は順序を保つ-/
theorem MyNat.add_le_add_right (h: m ≤ n) (l : MyNat) : m+l ≤ n+l := calc
  _ = l+m := by ac_rfl
  _ ≤ l+n := by apply MyNat.add_le_add_left h l
  _ = n+l := by ac_rfl
  -- ↑この証明すげー　かっこいい

theorem MyNat.add_le_add (h1 : m ≤ n) (h2 : a ≤ b) : m+a ≤ n+b := calc
  _ ≤ n+a := by apply add_le_add_right h1 a
  _ ≤ n+b := by apply add_le_add_left h2 n
-- この証明もかっこいい↑

-- これらの定理を再利用可能にしたい
-- 6.5.2 足し算が順序を保つことを再利用可能にする
--
-- Mathlibのgcongrというタクティクは「関数fは関係~を保つ」というタイプのルールを@[gcongr]というタグで登録すると再利用可能になる
-- ただここでは分配法則の時と同じように自前でやる

open Lean Elab Tactic in

/-- 関係 ∼ が成り立つなら f a ∼ f bが成り立つ、というタイプの推論を行う-/
elab "compatible" : tactic => do
  -- [compatible]属性が付与された定理をリストアップする
  let taggedDecls ← labelled `compatible
  if taggedDecls.isEmpty then
    throwError "`[compatible]`が付与された定理はありません。"
  for decl in taggedDecls do
    let declStx := mkIdent decl
    try
      -- [compatible]属性が付与された定理thmに対してapply thm <;> assumptionを試す
      evalTactic <| ← `(tactic| apply $declStx <;> assumption)
      -- 成功したら終了
      return ()
    catch _ =>
      -- 失敗したら次の候補に進む
      pure ()
  throwError "ゴールを閉じることができませんでした。"

-- elab: 構文に意味を与えるコマンド。コマンドやタクティク、各種の記法を定義できる。
-- macroなどと違い, 手続き的なメタプログラミングに向いている
-- 指定されたタグが付与された宣言をリストアップするにはLean.labbelledを使う
-- evalTacticは、与えられたタクティクを 実行する関数
-- <| は後方パイプライン演算子。 f <| xはf xとおなじ。関数適用のカッコを省略したいときによく使われる。

attribute [compatible] MyNat.add_le_add_left MyNat.add_le_add_right MyNat.add_le_add

example (h : n ≤ m) (l : MyNat) : l+n≤l+m := by compatible
example (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by compatible
example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by compatible


-- 6.5.3 足し算が狭義順序を保つことを示す
@[compatible]
theorem MyNat.add_lt_add_left {m n : MyNat} (h: m < n) (k : MyNat) 
  : k + m < k + n := by
    notation_simp at *
    -- h: m+1≤ n
    -- ⊢ k+m+1 ≤ k+n
    calc _ = k + (m+1) := by ac_rfl
    _ ≤ k + n := by compatible
    

@[compatible]
theorem MyNat.add_lt_add_right {m n : MyNat} (h : m < n) (k : MyNat)
  : m + k < n + k := by
    calc 
      _ = k + m := by ac_rfl
      _ < k + n := MyNat.add_lt_add_left h k
      _ = n + k := by ac_rfl

-- 6.5.4 順序についても足し算はキャンセル可能

section

variable (m n k : MyNat)

theorem MyNat.le_of_add_le_add_left : k + m ≤ k + n → m ≤ n := by
  intro h
  simp [MyNat.le_iff_add] at *
  obtain ⟨k1, hk1⟩ := h
  -- hk1: k+m+k1 = k+n
  rw [show k+m+k1 = k+(m+k1) by ac_rfl] at hk1
  have h1 : m+k1 = n := MyNat.add_left_cancel hk1 
  exists k1

theorem MyNat.le_of_add_le_add_right : m+k ≤ n+k → m≤n := by
  intro h
  -- h: m+k ≤ n+k
  apply MyNat.le_of_add_le_add_left
  rw [show k+m = m+k from by ac_rfl]
  rw [show k+n = n+k from by ac_rfl]
  exact h

@[simp] theorem MyNat.add_le_add_iff_left : k + m ≤ k + n ↔ m ≤ n := by
  constructor
  ·
    --⊢ k+m ≤ k+n → m≤ n
    exact MyNat.le_of_add_le_add_left m n k
  ·
    --⊢ m≤ n → k+m ≤ k+n
    intro h
    exact MyNat.add_le_add_left h k

@[simp] theorem MyNat.add_le_add_iff_right : m + k ≤ n + k ↔ m ≤ n := by
  constructor
  ·
    exact MyNat.le_of_add_le_add_right m n k
  ·
    intro h
    compatible

-- 6.5.5 練習問題
variable (m₁ m₂ n₁ n₂ l₁ l₂ : MyNat) 

example (h1 : m₁ ≤ m₂) (h2: n₁ ≤ n₂) (h3 : l₁ ≤ l₂) 
  : l₁ + m₁ + n₁ ≤ l₂ + n₂ + m₂ := calc
  _ = l₁ + n₁ + m₁:= by ac_rfl
  _ ≤ l₁ + n₁ + m₂ := by compatible
  _ = l₁ + m₂ + n₁ := by ac_rfl
  _ ≤ l₁ + m₂ + n₂ := by compatible
  _ = m₂ + n₂ + l₁ := by ac_rfl
  _ ≤ m₂ + n₂ + l₂ := by compatible
  _ = l₂ + n₂ + m₂ := by ac_rfl
-- この証明面白い 
-- Leanの処理系の気持ちになって、足し算が左結合で(a+b)+cという順序で評価される
-- ことを考えて右側にあるのを書き換えていく感じ


end


