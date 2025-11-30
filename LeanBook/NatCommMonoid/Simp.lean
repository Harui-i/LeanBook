import LeanBook.NatCommMonoid.Induction
-- P70 4.3 等式変形による単純化を自動化する

-- simpタクティクによる自動化は、証明済みの命題に[simp]属性を付与することで実現される。
-- 属性の付与には `attribute` コマンドを使う。


example (n : MyNat) : 0 + (n + 0) = n := by
  fail_if_success simp -- simpがうまくいかない
  rw [MyNat.add_zero]
  rw [MyNat.zero_add]


attribute [simp] MyNat.add_zero MyNat.zero_add

example (n : MyNat) : 0 + (n + 0) = n := by
  simp -- simpがうまくいく

theorem MyNat.ctor_eq_zero : MyNat.zero = 0 := by
  rfl

example : MyNat.zero = 0 := by
  fail_if_success simp -- simpはうまくいかない(MyNat.ctor_eq_zeroがsimp属性がないので)
  simp [MyNat.ctor_eq_zero] -- 指定すればうまくいく

attribute [simp] MyNat.ctor_eq_zero
attribute [simp] MyNat.add_succ

-- 4.3.2 at構文
--
example (m n : MyNat) (h: m + n + 0 = n + m) : m + n = n + m := by
  -- ローカルコンテキストにあるhを単純化させる
  simp at h
  guard_hyp h : m+n = n + m
  rw [h]

example (m n : MyNat) (h: m + 0 = n) : (m + 0) + 0 = n := by
  simp at * -- ローカルコンテキストすべての仮定とゴールを単純化する
  guard_hyp h : m = n
  guard_target =ₛ m = n
  rw [h]

example (m n : MyNat) (h: m + 0 = n) : (m + 0) + 0 = n := by
  simp_all

-- 4.3.4 @[simp] タグ
/--
  simpで証明した時点でtheoremにsimpにより適用されるようにタグをつけることもできる。

-/


-- なんか証明通ったけど正直何をしてるか理解できないな
@[simp] theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m+n) := by
  induction n with
  | zero =>
    rfl
  | succ n2 ih =>
    simp [ih]

-- 4.3.6 calcコマンド
-- 等号など、推移的な二項関係を続けてかけるたくてぃく
example (m n : MyNat) : .succ m + n = .succ (m+n) := by
  induction n with
  | zero => rfl
  | succ n2 ih =>
    -- m.succ + n2.succ = (m + n2.succ).succ
    calc
    _ = (m.succ + n2).succ := by rw [MyNat.add_succ] -- 左辺を`_`で省略するとゴールの左辺と認識される
    -- (m.succ + n2).succ = (m+n2.succ).succ
    _ = (m + n2).succ.succ := by rw [MyNat.succ_add]
    _ = (m + n2.succ).succ := by rw [MyNat.add_succ]


example (n : MyNat) : 1 + n = n + 1 := calc
  _ = .succ 0 + n := by rfl
  _ = .succ (0 + n) := by rw [MyNat.succ_add]
  _ = .succ n := by rw [MyNat.zero_add]
  _ = n + 1 := by rfl

example (n : MyNat) : 2 + n = n + 2 := calc
  _ = MyNat.zero.succ.succ + n := by rfl
  _ = (MyNat.zero.succ + n).succ := by rw [MyNat.succ_add]
  _ = (MyNat.zero + n).succ.succ := by rw [MyNat.succ_add]
  -- MyNat.zeroと0は定義的にイコールじゃない(!?)
  _ = (0 + n).succ.succ := by rfl
  _ = n.succ.succ := by rw [MyNat.zero_add]
  _ = n + 2 := by rfl
