import LeanBook.NatSemiring.Distrib
-- 第6章 自然数の順序と、計算を利用する証明
-- 6.1 a+b=a+c → b=c

/-
ペアノの公理

1. 0は自然数である
2. 後者関数と呼ばれる、自然数から自然数への関数succが存在する
3. succは単射
4. 0 と succの像は交わらない。つまり 0 ≠ succ(n)
5. 帰納法の原理が成り立つ。つまり自然数上の任意の術後Pに対して「P(0) ∧ ∀n, P(n) → P(succ(n))」
ならば、 「∀n, P(n)」


帰納法の原理が成り立つことは、MyNat.recという関数が自動生成されていることに相当するので、確認済み
残るは、3. succは単射と 4. 0とsuccの像は交わらないこと。

Leanでinductiveにより定義した型は自動的にこの性質を満たす。
すなわち、各コンストラクタ(MyNatならzero,succ)の像が重なることはなく、コンストラクタは全て単射。
この規則はinjectionタクティクで使える
-/

/-- MyNatの各コンストラクタの像は重ならない -/
example (n : MyNat) : MyNat.succ n ≠ MyNat.zero := by
  intro h
  -- h: n.succ = MyNat.zero
  injection h


/-- MyNatのコンストラクタは単射 -/
example (m n : MyNat) (h: MyNat.succ m = MyNat.succ n) : m = n := by
  injection h

example (m n : MyNat) (h : m + 1 = n + 1) : m = n := by
  injection h

-- 6.1.2 足し算のキャンセル可能性の証明

--  以降l,m,nはすべてMyNat型の項とする
variable {l m n : MyNat}

/-- 右から足す演算 (· + m) は単射 -/
theorem MyNat.add_right_cancel (h : l + m = n + m) : l = n := by
  induction m with
  | zero =>
    simp_all
  | succ m ih =>
    -- h: l + (m+1) = n + (m+1)
    -- ih : l+m = n+m → l=n
    -- ⊢ l=n
    apply ih
    -- ⊢ l+m =n+m
    injection h


/-- 左から足す演算 (l + ·) は単射-/
theorem MyNat.add_left_cancel (h : l + m = l + n) : m = n := by
  -- rw [MyNat.add_comm l m, MyNat.add_comm l n] at hでも示せる
  have h2 : m+l = n + l := by
    calc
    _ = m + l := by rfl
    _ = l + m := by ac_rfl
    _ = l + n := by rw [h]
    _ = n + l := by ac_rfl
  exact MyNat.add_right_cancel h2

-- 6.1.3 simpタクティクで再利用できるようにする

/-- 右からの足し算のキャンセル-/
@[simp ↓] theorem Mynat.add_right_cancel_iff : l + m = n +m ↔ l = n := by
  constructor
  · apply MyNat.add_right_cancel
  · intro h
    rw [h]

@[simp ↓] theorem MyNat.add_left_cancel_iff : l + m = l+n ↔ m = n := by
  constructor
  · apply MyNat.add_left_cancel
  · intro h
    rw [h]


@[simp] theorem MyNat.add_right_eq_self : m +n = m ↔ n = 0 := by
  constructor
  ·
    intro h
    -- h:  m + n = m
    -- ⊢  n = 0
    have h2 : m + n = m + 0 := by exact h

    simp_all
  ·
    intro h
    rw [h]
    ac_rfl

@[simp] theorem MyNat.add_left_eq_self : n + m = m ↔ n = 0 := by
  rw [MyNat.add_comm n m, MyNat.add_right_eq_self]

@[simp] theorem MyNat.self_eq_add_right : m = m + n ↔ n = 0 := by
  rw [show (m = m+n) ↔ (m + n = m) from by exact eq_comm]
  exact MyNat.add_right_eq_self

@[simp] theorem MyNat.self_eq_add_left : m = n + m ↔ n = 0 := by
  rw [MyNat.add_comm n m, MyNat.self_eq_add_right]


-- 6.1.4 応用 : a * b = 0 ↔ a = 0 ∨ b = 0
-- のまえに、まずは a+b = 0 ↔ a=0 ∧ b= 0

@[simp]
theorem MyNat.eq_zero_iff_add_eq_zero : m + n = 0 ↔ m = 0 ∧ n = 0 := by
  constructor
  ·
    intro h
    induction n with
    | zero =>
      -- h : m + 0 = 0
      have h1 : m = 0 := by
        simp at h
        exact h
      have h2 : 0 = 0 := by rfl

      exact And.intro h1 h2

    | succ n ih =>
      -- ih : m + n = 0 → m = 0 ∧ n =0
      -- h : m + (n+1) = 0
      -- ⊢ : m = 0 ∧ n+1 = 0
      exfalso
      have h2 : (m+n) + 1 = 0 := by
        exact h

      injection h
  ·
    intro h
    simp [h.left, h.right]


@[simp]
theorem MyNat.mul_eq_zero (m n : MyNat) : m * n = 0 ↔ m = 0 ∨ n = 0 := by
  constructor <;> intro h
  case mpr =>
    cases h <;> simp_all
  case mp =>
    induction n with
    | zero =>
      right
      rfl
    | succ n _ =>
      -- m * (n+1) = 0
      -- ⊢ m = 0 ∨ n+1 = 0
      have h1 : m*n + m = 0 := calc
        _ = m * (n + 1) := by distrib
        _ = 0 := by rw [h]

      simp_all


-- 6.1.5 練習問題
example (n m : MyNat) : n + (1+m) = n + 2 → m = 1 := by
  intro h
  simp at h
  -- h : 1 + m = 2
  -- m = 1

  -- ↓こう書いても同じだけど、rw [show]のほうがかっこいいので
  --have h1 : 2 = 1+1 := by distrib
  --rw [h1] at h
  rw [show 2=1+1 from by distrib] at h
  -- h: 1+m =1+1
  -- 左から1を足しているのをキャンセルしたり
  simp_all
