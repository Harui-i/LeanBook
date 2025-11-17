-- 3.7 依存型
-- カリーハワード同型対応は、命題が全称量化や存在量化されている場合でも成り立っている。
-- 値に依存してよい型は、依存型(dependent type)とよぶ。


-- 3.7.1 全称量化
#check Nat.add_zero

-- Nat.add_zero は「すべての自然数nについて n+0=nが成り立つ」」
-- add_zeroに具体的なn : Natを適用すればそれについてn + 0 = nの証明が得られる

-- Nat.add_zeroの型は？ nに依存している。
-- Leanでは、この関数の型を (n: Nat) → n + 0 = nお表記する

#check (Nat.add_zero : ((n: Nat) → n + 0 = n))

-- 返り値の型が入力の値に依存して変わる関数を「依存関数」と呼ぶ。

example : (∀ n : Nat, n + 0 = n) = ((n : Nat) → n + 0 = n) := by
  rfl
-- Note: exampleは証明に限らず「型の(が？)具体的な値かどうかを確認する」コマンドとして使える

set_option pp.foralls false in
#check (∀ n : Nat, n + 0 = n)


-- 3.7.2 ベクトル
-- List α は帰納的に定義されている。
-- 1. 空リスト [] は List αの値である。
-- 2. α型の値aと、 List α の値 l　が与えられたとき、
--    lの直前にaを追加して新しいList α 型の値が得られる

/-
inductive List (α : Type) : Type where
  | nil
  | cons (a : α) (l : List α)
-/

example : List Nat := [0, 1, 2, 3]

-- 依存型を使うと、要素数についての情報を含んだ連結リストを構成できる
-- そんなものをベクトルと呼ぶことにする。

inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons {n : Nat} (a : α) (v : Vect α n) : Vect α (n+1)

example : Vect Nat 1 := Vect.cons 42 Vect.nil

-- [(Nat, 1), (Bool, true), (Prop, True)]みたいなリストを考える
-- (x,y)は 型, その型の値　みたいな関係になっている。こようなペアにも型をつけられる

-- × は \timesで出した
example : (α : Type) × α := ⟨Nat, 1⟩

example : (α : Type) × α := ⟨Bool, True⟩

example : (α : Type) × α := ⟨Prop, True⟩

example : List ((α : Type) × α) := [⟨Nat, 1⟩, ⟨Bool, True⟩, ⟨Prop, True⟩]

-- (α : Type) × α のような型は「依存ペア型」と呼ばれる


-- 3.7.4 練習問題
example : List ((α : Type) × α) := [⟨Nat, 42⟩, ⟨Bool, false⟩]

example : {α: Type} → {n : Nat} → (a : α) → (v : Vect α n) → Vect α (n+1) :=
  -- Vect.cons a v --  unknown identifier a
  fun {α : Type} {n : Nat} (a : α) (v : Vect α n) => Vect.cons a v
