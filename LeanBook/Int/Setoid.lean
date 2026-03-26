-- 第7章 同値関係で割って整数を作る

-- 7.1 同値関係
-- Leanでは二項関係rが同値関係であることを示すために　Equivalenceという構造体を使う。
-- 7.1.1 Leanの構造体

structure Point where
  x : Int
  y : Int

-- 構造体は一つの型として扱えるので、その項を定義できる。
-- 項を定義する方法はいくつかある。
-- 一つは、フィールドの値に続いて:区切りで構造体の名前を指定し全体を｛｝で囲む記法。
#check { x:= 1, y:= 2 : Point}

-- ２つ目は、コンストラクタを使う方法。構造体をstructureコマンドで定義すると、.mkという名前でコンストラクタが定義される.
#check Point.mk -- Point.mk (x y : Int) : Point
#check Point.mk 1 2

-- 構造体を定義すると、コンストラクタと同時に、構造体の項からフィールドの値を取り出すアクセサ関数も生成される。

#check Point.x -- Point.x (self : Point) : Int
#check Point.x (Point.mk 1 2) -- : Int
#eval Point.y (Point.mk 1 2) -- : 2

-- アクセサ関数はフィールドへの直接のアクセスのようにかける
#eval
  let p : Point := {x := 1, y:= 2}
  p.x

/-
同値関係Equivalenceは標準ライブラリで以下のように定義されている。
structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
  refl : ∀ x, r x x
  symm : ∀ {x, y}, r x y → r y x
  trans : ∀ {x, y, z}, r x y → r y z → r x z
-/

example {α : Type} (r : α → α → Prop) (h : Equivalence r) : ∀ x, r x x := h.refl

-- どんな型αに対しても r x y := x = yと定義すると必ず同値関係になる　を示す
example {α : Type} : Equivalence (fun x y : α => x = y) := by
  constructor
  ·
    intro x
    rfl
  ·
    intro x
    intro y
    intro hx
    rw [hx]
  ·
    intro x
    intro y
    intro z
    intro hxy
    intro hyz
    rw [hxy]
    exact hyz

-- 7.1.3 Setoid
-- 同値関係であることはEquivalenceで表現するが、
-- 「同値関係r : α → α → Prop」そのものはSetoid αという型クラスで表現する。(???)
--
-- NOTE:ふーん、こういうのって他にもあるんかな。順序関係であることはAで表現するが「順序関係r: α → α → Prop」は型クラスBで表現する。　みたいな？
-- モノイドであることはAだが(略)とか

/-
class Setoid (α : Sort u) where
  /-- 二項関係r : α → α → Prop -/
  r : α → α → Prop
  /-- 二項関係rは同値関係である-/ 
  iseqv : Equivalence r
-/ 

-- Setoid αのインスタンスsr: Setoid αがあるとき、二項関係sr.rを ≈  という記号で表せる。
-- NOTE: この記号の打ち方は？
-- approxでした
example {α : Type} (sr : Setoid α) (x y : α) : sr.r x y = (x ≈ y) := by
  rfl

-- 練習問題 7.1.4
example  {α : Type} : Equivalence (fun _x _y : α => True) := by
  constructor
  ·
    intro x
    -- ⊢ True
    -- NOTE: これなんでsimpがうまくいくんかわかってない
    simp 
  ·
    intro x y
    intro h
    exact h
  ·
    intro x y z hx hy 
    exact hx






