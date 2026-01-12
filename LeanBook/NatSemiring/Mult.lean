-- 第5章　分配法則を証明し、マクロで再利用可能にする
-- 5.1 掛け算を定義して交換法則、結合法則、分配法則を示す
import LeanBook.NatCommMonoid.BetterInduction

/-- MyNatについての掛け算 -/
def MyNat.mul (m n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => MyNat.mul m n + m

-- MyNatの掛け算を * で表せるように型クラスMulのインスタンスにする
instance : Mul MyNat where
  mul := MyNat.mul

-- これが6になるのすげ
#eval 2 * 3


-- 5.1.2 succに対する分配法則
-- m * (n+1) = m*n + m
-- (m+1) * n = m*n + m

-- 右のオペランドにある(· + 1)の除去
theorem MyNat.mul_add_one (m n : MyNat) : m * (n+1) = m * n + m := by
  rfl

/-- 左のオペランドにある(· + 1)の除去 -/
theorem MyNat.add_one_mul (m n : MyNat) : (m + 1) * n = m*n + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    /-
    ↓これでも証明できた
    rw [MyNat.mul_add_one m n]
    rw [MyNat.mul_add_one (m+1) n]
    rw [ih]
    ac_rfl
    -/

    calc
    (m+1) * (n +1) = (m+1) * n + (m+1) := by rw [MyNat.mul_add_one]
    _ = m * n + n + (m+1) := by rw [ih]
    _ = m * n + m + (n+1) := by ac_rfl -- 足し算の交換・結合法則だけなのでac_rflが効く
    _ = m * (n +1) + (n + 1) := by rw [MyNat.mul_add_one]

    -- 左辺をm * (n + 1) + (n+1)に変形したい


/-- 右から0をかけても0 -/
@[simp] theorem MyNat.mul_zero (m : MyNat) : m * 0 = 0 := by
  rfl

/-- 左から0をかけても0-/
@[simp] theorem MyNat.zero_mul (n : MyNat) : 0 * n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- simp[MyNat.mul_add_one, ih]で一発でやることもできる
    rw [MyNat.mul_add_one 0 n]
    rw [ih]
    rfl


/-- 右から1を掛けてもかわらない -/
@[simp] theorem MyNat.mul_one (n : MyNat) : n * 1 = n := calc
  _ = n * (0 + 1) := by simp
  _ = n * 0 + n := by rw [MyNat.mul_add_one]
  _ = n := by simp

/-- 左から1を掛けてもかわらない-/
@[simp] theorem MyNat.one_mul (n : MyNat) : 1 * n = n := calc
  _ = (0 + 1) * n := by simp
  _ = 0 * n + n := by rw [MyNat.add_one_mul] -- これで 1*nが消える
  _ = n := by simp


/-- 掛け算の交換法則 -/
theorem MyNat.mul_comm (m n : MyNat) : m * n = n * m := by
  induction n with
  | zero => simp
  | succ n ih => calc
    -- ih : m * n = n *m
    -- goal: m * (n+1) = (n+1) * m
    -- m*n + m
    _ = m*n + m := by rw [MyNat.mul_add_one]
    _ = n*m + m := by rw [ih]
    _ = (n + 1) * m := by rw [add_one_mul]

/-- 右から掛けたときの分配法則-/
theorem MyNat.add_mul (l m n : MyNat) : (l + m) * n = l * n + m * n := by
  induction n with
  | zero => rfl
  | succ n ih => calc
    -- ih : (l+m)*n = l*n + m*n
    -- goal: (l+m)*(n+1) = l*(n+1) + m * (n+1)
    -- ↑と思っていたけど、コンパイルエラーをよく見ると
    -- Unsolved goals: l*n+m*n +m = l*n+l+(m*n+m)になっていた
    _ = (l + m) * (n + 1) := by rfl -- 最初の左辺
    _ = (l+m)*n + (l+m) := by rw [MyNat.mul_add_one]
    _ = l*n + m*n + (l+m) := by rw [ih]
    _ = l * n + l + (m*n + m) := by ac_rfl

/-- 左から掛けたときの分配法則 -/
theorem MyNat.mul_add (l m n : MyNat) : l * (m+n) = l * m + l * n := calc
  _ = l * (m + n) := by rfl
  -- 掛け算の可換性を使って右からの分配法則に帰着
  _ = (m+n) * l := by simp [MyNat.mul_comm]
  _ = m * l + n * l := by simp [MyNat.add_mul]
  _ = l * m + l * n := by simp [MyNat.mul_comm]

theorem MyNat.mul_assoc (l m n : MyNat) : l * m * n = l * (m * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- ih: l*m*n = l * (m*n)
    -- l * m * (n+1) = l * (m * (n + 1))
    -- simpすげー
    simp [MyNat.mul_add, ih]


instance : Std.Associative (α := MyNat) (· * ·) where
  assoc := MyNat.mul_assoc

instance : Std.Commutative (α := MyNat) (· * ·) where
  comm := MyNat.mul_comm


-- 5.1.5 練習問題

theorem mul2_eq_plus_plus (n : MyNat) : n * 2 = n + n := by calc
  _ = n * 2 := by rfl
  _ = n*1 + n:= by rfl
  _ = n + n := by simp

example (m n : MyNat) : m * n * n * m = m * m * n* n := by ac_rfl
example (m n : MyNat) : (m+n) * (m+n) = m*m + 2*m*n + n*n := by calc
  _ = (m+n)*(m+n) := by rfl -- left hand side
  _ = (m+n)*m + (m+n) * n := by simp [MyNat.mul_add, MyNat.add_mul]
  _ = (m*m + n*m)+ (m*n + n *n) := by simp [MyNat.add_mul]
  _ = m*m + (m*n + m*n) + n*n := by ac_rfl
  _ = m*m + (m*n) * 2 + n*n := by rw [mul2_eq_plus_plus]
  _ = m*m + 2 * m*n + n *n := by ac_rfl
