import LeanBook.FirstProof.NaturalNumber

-- 第4章  帰納法で足し算の性質を証明する
-- P62
/-
0を表すために MyNat.zeroと書かなければいけないなどの不便な点があったし、+のような演算子を使えなかった。
Leanでは、「標準ライブラリに定義されている特定の型インスタンスを定義する」ことで実元するらしい。

Rustで impl Cloneしたり C++で operator<を実装したり、Pythonで def __eq__()を実装したりするみたいな？


-/


/--
Nat(自然数のlean組み込みの型)の項から対応するMyNatの項を得る
-/
def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => MyNat.zero
  | n + 1 => MyNat.succ (MyNat.ofNat n)


-- 数値リテラルは、 `OfNat`という　型クラスのインスタンス　を実装することで実現できる。
-- OfNatクラスは、数値リテラルの解釈を定めるもの。
/-- OfNatのインスタンスを実装する -/
@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

#check 0 -- 0 : MyNat


-- 足し算を表すのに `+` 演算子を利用できるようにするためには、 `Add` という型クラスのインスタンスを実装する。
/-- MyNat.addを足し算として登録する -/
instance : Add MyNat where
  add := MyNat.add

#check 1+1
#check MyNat.zero + MyNat.one

#eval 1 + 2 -- MyNat.succ (MyNat.succ (MyNat.succ (MyNat.zero)))

-- #evalの結果はリテラルで表現されていない。
-- Reprという型クラスのインスタンスを作ることで、型クラスの値を文字列のような形式に変換する方法を指定できる

def MyNat.toNat (n: MyNat) : Nat :=
  match n with
  | 0 => 0 -- 右側はNat
  | n+1 => MyNat.toNat n + 1 -- Nat + Nat

instance : Repr MyNat where
  reprPrec n _ := repr n.toNat

#eval 0 + 0

#eval 3 + 5

-- 4.1.4　型クラスとは？

example (n: MyNat) : n + 0 = n := by
  rfl
