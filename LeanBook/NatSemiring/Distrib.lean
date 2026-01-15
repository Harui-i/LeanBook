import LeanBook.NatSemiring.Mult
-- 5.2 分配法則を再利用可能にする
-- mathlibで定義されているringタクティクを使えば分配法則を再利用可能になる
-- が、今回は類似タクティクの自作を試みる


-- step1: 掛け算のオペランドに足し算がこないよう変形することを考える
-- a * (b+c) -> a*b + a*cてきな



/-
example (m n: MyNat) : m * (n+1) + 2 * (m + n) = m * n + 3 *m + 2 * n := by
  rw [MyNat.mul_add]
  -- rwは一回だけ置き換えてやめてしまう
  guard_target =ₛ m * n + m * 1 + 2 * (m+n) = m * n + 3 * m + 2 * n
  sorry

example (m n: MyNat) : m * (n+1) + 2 * (m + n) = m * n + 3 *m + 2 * n := by
  -- onlyを使うと、[]で囲まれた補題だけを使って単純化する
  simp only [MyNat.mul_add]
  guard_target =ₛ m * n + m * 1 + (2 * m + 2 * n) = m * n + 3 * m + 2 * n
  sorry
-/


/-- 分配法則を適用して足し算を式の外側に持ってくるタクティク -/
macro "distrib" : tactic => `(tactic| simp only [MyNat.mul_add, MyNat.add_mul])
/-
example (m n: MyNat) : m * (n+1) + 2 * (m + n) = m * n + 3 *m + 2 * n := by
  distrib
  guard_target =ₛ m * n + m * 1 + (2 * m + 2 * n) = m * n + 3 * m + 2 * n
  sorry
-/

/-- 分配法則を適用して足し算を式の外側に持ってくるタクティク-/

macro "distrib" : tactic => `(tactic| focus
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl
)


example (m n : MyNat) : m * (n+1) + (2+n) * n = m*n + m + 2 * n + n * n := by
  distrib

example (m n : MyNat) : m * (n+1) + (2+m) * m = m * n + 3 * m + m * m := by
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_one]
  fail_if_success ac_rfl

  -- 2*m と mをac_rflではまとめられていない　
  guard_target =ₛ m * n + m + (2 * m + m * m) = m*n + 3*m + m*m

  rw [show 3 = 1 + 1 + 1 from rfl]
  rw [show 2 = 1 + 1 from rfl]
  distrib


/-- 数値リテラルを1+1+ ... + 1に分解するための補題 -/
theorem unfoldNatLit (x : Nat)
  : (OfNat.ofNat (x+2) : MyNat) = (OfNat.ofNat (x +1) : MyNat) + 1 := rfl

macro "expand_num" : tactic => `(tactic| focus
  simp only [unfoldNatLit]

  -- 標準のNatの和を簡単な形にする
  simp only [Nat.reduceAdd]
  -- OfNat.ofNatを消す
  dsimp only [OfNat.ofNat]
  simp only [
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl
  ]
)

example (n : MyNat) : 3 * n = 2 * n + 1 * n := by
  expand_num
  simp only [MyNat.add_mul]

macro "distrib": tactic => `(tactic| focus
  expand_num
  simp only [
    MyNat.mul_add,
    MyNat.add_mul,
    MyNat.mul_zero,
    MyNat.zero_mul,
    MyNat.mul_one,
    MyNat.one_mul,
  ]
  ac_rfl
)


example (m n : MyNat) : (m + 4) * n + n = m * n + 5 * n := by
  distrib

/-- 数値リテラルを1+1+ ... + 1に分解するための補題 -/
macro "expand_num" : tactic => `(tactic| focus
  try simp only [unfoldNatLit]

  -- 標準のNatの和を簡単な形にする
  try simp only [Nat.reduceAdd]
  -- OfNat.ofNatを消す
  try dsimp only [OfNat.ofNat]
  try simp only [
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl
  ]
)

macro "distrib": tactic => `(tactic| focus
  expand_num
  try simp only [
    MyNat.mul_add,
    MyNat.add_mul,
    MyNat.mul_zero,
    MyNat.zero_mul,
    MyNat.mul_one,
    MyNat.one_mul,
  ]
  try ac_rfl
)

example (n : MyNat) : ∃ s t : MyNat, s*t = n*n + 8*n + 16 := by
  -- (n+4)**2
  -- ∃命題を証明するときに、実際に構築して示すタクティク、忘れちゃったからわざわざ過去のファイルを検索して調べた
  exists n+4
  exists n+4
  distrib
