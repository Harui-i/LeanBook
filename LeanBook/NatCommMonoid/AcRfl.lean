-- 4.4 足し算の交換法則と結合法則を解放する
import LeanBook.NatCommMonoid.Simp

-- 足し算の交換法則
theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    simp [MyNat.ctor_eq_zero]
  | succ n ih =>
    simp [ih]

-- 足し算の結合法則
theorem MyNat.add_assoc (l m n : MyNat) : l + m + n = l + (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [ih]

example (l m n : MyNat) : l + m + n + 3 = m + (l + n) + 3 := calc
  _ = m + l + n + 3 := by rw [MyNat.add_comm l m]
  _ = m + (l + n) + 3 := by rw [MyNat.add_assoc m l n]

  -- 交換法則や結合法則は式の単純化じゃないからsimpは使えない
  -- Leanの標準ライブラリに用意されているac_rflを使えば、交換法則・結合法則を満たすことを型クラス経由で登録しておけば一発で通せる

-- MyNatの足し算が結合法則を満たすことを、型クラスのインスタンスをつくることで登録
-- (· + · )は fun x y => x + yを簡単に表す記法
instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc

-- 交換法則
instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm


example (l m n : MyNat) : l + m + n + 3 = m + (l + n) + 3 := by
  -- gg wp, gg ez
  -- tactic gap gg
  ac_rfl


-- 練習問題 4.4.3
example (l m n : MyNat) : l + (1 + m) + n = m + (l + n) + 1 := by
  ac_rfl
