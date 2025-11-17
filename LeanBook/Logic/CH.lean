/-- 1+1 = 2 という命題の証明 -/

theorem one_add_one_eq_two : 1 + 1 = 2 := by
  rfl

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp


-- 証明を実行するためのツールとして紹介してきたタクティクは、実は
-- 「与えられた型の項を構成するツール」だった。
def idOnNat : Nat → Nat := by
  intro n
  exact n

/-- 3.6.4 練習問題 -/
example (P Q : Prop) (hp : P) : Q → P :=
  fun _a => hp


example (P Q : Prop) (hp : P) : Q → P := by? -- Try this : fun hq => hp
  intro hq
  exact hp
