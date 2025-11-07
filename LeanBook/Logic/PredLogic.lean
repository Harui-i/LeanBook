-- 3.3 述語論理

/-- 人間たちの集合　-/
opaque Human : Type

/-- 愛の関係 -/
opaque Love : Human → Human → Prop

-- `opaque` を使って `def` と同様に新しい定数を定義できる。`def` とは違い、実装を与えずに存在だけ定義することができる


-- 専用の中置記法を用意する
-- 元のLoveのドキュメントを引き継げるようにするために `@[inherit_doc]`を指定する
@[inherit_doc] infix:50 " -♥→ " => Love

-- 任意の人間が愛するような人間が存在する
def IdolExists : Prop := ∃ idol : Human, ∀ h : Human, h -♥→ idol

-- だれでも好きなひとの一人くらいいる

def EveryoneLovesSomeone: Prop := ∀ h : Human, ∃ loved : Human, h -♥→ loved


-- 練習問題3.3.4
example : IdolExists → EveryoneLovesSomeone := by
  rw [IdolExists, EveryoneLovesSomeone]
  intro hIE
  intro h
  obtain ⟨idol, h_idol⟩ := hIE -- hIEが存在命題なので、それを使って idolをとってくる
  exists idol
  -- h_idol : ∀ (h : Human), h -♥→ idol
  -- ⊢ h -♥→ idol
  exact h_idol h
