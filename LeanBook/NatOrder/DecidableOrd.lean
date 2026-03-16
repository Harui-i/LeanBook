import LeanBook.NatOrder.PartialOrder

-- 6.7章　順序関係を決定可能にする

example : 0 ≤ 5 := by
  apply MyNat.le.step
  apply MyNat.le.step
  apply MyNat.le.step
  apply MyNat.le.step
  apply MyNat.le.step
  apply MyNat.le.refl

-- 6.7.1 Decidable 型クラス
-- Decidable型クラスは命題が決定可能(decidable)であることを表す。
-- Leanの標準ライブラリでは下記のように定義されている。
-- 証明または反証ができるならDecidableということね。
/- 
class inductive Decidable (p : Prop) where 
  | isFalse (h: ¬ p) : Decidable p
  | isTrue (h : p) : Decidable p 
-/
-- 6.7.2 例: 等号を決定可能にする
-- a=b なのか a ≠ bなのかを決定可能にする。a=bをDecidableのインスタンスにすることはよくあるので、
-- DecidableEqという型クラスが用意されている。
-- なので、DecidableEq型クラスのインスタンスを作ればいい。
-- さらに、Leanにはよくつかう型クラスのインスタンス生成をできる仕組みがある。
-- deriving という構文を使うことでDecidableEq型クラスのインスタンスを作れる。
deriving instance DecidableEq for MyNat

-- すげー derive macroってRustにあったな。 #[derive(serde::Serialize)]みたいな。

example : 32 + 13 ≠ 46 := by
  -- 証明が通る！
  decide

-- 6.7.3 順序関係を計算する
-- 順序関係はderivingで型クラスのインスタンスを作るのはできないらしい。
-- なので、自分で実装する必要がある。
-- Leanの言葉でいうと、そのような関数を実装する必要がある！
--
-- おもしろいっすね。発展した数学を扱うと、同値関係とかイコールの定義はわかりやすいけど、
-- 具体例については同値なのかそうでないのか簡単にはわからない状況があったりして、そういうのに出会って初めて、定義と判定のギャップに気がつくけど、
-- Leanだと自然数という基本的なものを通じてそういう感覚を味わえるのは面白い。
-- 逆にLeanだけで学んでいると、「定義から簡単に判定できるのってあたりまえじゃね？保守的すぎるだろ」みたいに思ったりするのかな？

-- 
def MyNat.ble (a b : MyNat) : Bool :=
  match a, b with
  | 0, _ => true
  -- こうやってa+1みたいに変数作れるの面白い。引き算とかいらないんだ
  | _a+1, 0 => false
  | a+1, b+1 => MyNat.ble a b

-- これで、順序関係を判定するアルゴリズムは定義できた。
-- 6.7.4 function induction
-- 上で計算される順序が、今までの定義の順序と整合していることを示す必要がある。
-- MyNat.ble m n = true ↔ m ≤ n 
-- を示す。

/-
instance (a b : MyNat) : Decidable (a ≤ b) := by
  apply decidable_of_iff (MyNat.ble a b = true)
  -- ↓この証明が必要
  guard_target =ₛ MyNat.ble a b  = true ↔ a ≤ b
  sorry
-/ 

-- どう証明すればいい？
-- 上の再帰では2変数の再帰をしている。いままでの帰納法は0かどうかの場合分けだったが、
-- 今回は２つの変数で3つの場合分けをしている。
-- このような状況で帰納法が使えるように、Leanにはfunctional inductionという仕組みがある。
-- これは「任意の再帰関数fに対して、帰納法の原理f.inductが自動的に生成される」というもの。
-- これをinductionタクティクのusing以下に渡せば、この関数の場合分けに沿った帰納法が可能。

@[simp]
theorem MyNat.ble_zero_left (n : MyNat) : MyNat.ble 0 n = true := by
  rfl

@[simp]
theorem MyNat.ble_zero_right (n : MyNat) : MyNat.ble (n+1) 0 = false := by
  rfl

@[simp]
theorem MyNat.ble_succ (m n : MyNat) : MyNat.ble (m+1) (n+1) = MyNat.ble m n := by 
  rfl

#check MyNat.ble.induct 
-- MyNatのときと同様に、帰納法で記法が崩れる問題の対策をする。
-- MyNa.ble.inductの型を真似て補助関数を定義する
def MyNat.ble.inductAux (motive : MyNat → MyNat → Prop)
  (case1 : ∀ (n : MyNat), motive 0 n)
  (case2 : ∀ (n : MyNat), motive (n+1) 0)
  (case3 : ∀ (m n : MyNat), motive m n → motive (m+1) (n+1))
  (m n : MyNat) : motive m n := by
    induction m, n using MyNat.ble.induct with
    | case1 n => apply case1
    | case2 n => apply case2
    | case3 m n h => apply case3; assumption

-- MyNat.ble m n = true ↔ m ≤ nの証明
theorem MyNat.le_impl (m n : MyNat) : MyNat.ble m n = true ↔ m ≤ n := by
  induction m, n using MyNat.ble.inductAux with
  | case1 n =>
    simp
  | case2 n =>
    dsimp [MyNat.ble]
    -- ⊢ (n+1).ble 0  = true ↔ n+1 ≤ 0
    constructor <;> simp_all
  | case3 m n h =>
    -- simpするだけで通るんだ
    -- ⊢ (m+1).ble (n+1) = true ↔ m+1 ≤ n+1
    simp_all

-- 6.7.5 順序関係を決定可能にする
-- 順序関係が決定可能である　ことを主張するための省略形 DecidableLEという型クラスが用意されている。

instance : DecidableLE MyNat := fun n m => 
  decidable_of_iff (MyNat.ble n m = true) (MyNat.le_impl n m)

#eval 1 ≤ 3 -- true
#eval 5 ≤ 1 -- false

theorem MyNat.lt_impl (m n : MyNat) : MyNat.ble (m+1) n ↔ m < n := by
  rw [MyNat.le_impl]
  rfl

instance : DecidableLT MyNat := fun n m =>
  decidable_of_iff (MyNat.ble (n+1) m = true) (MyNat.lt_impl n m)

example : 2 < 5 := by
  decide

-- 練習問題 6.7.6
example : 23 < 32 ∧ 12 ≤ 24 := by
  decide
