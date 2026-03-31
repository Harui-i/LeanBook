-- 7.3: 整数を作る
import LeanBook.NatOrder.DecidableOrd

-- 整数の構成には何通りかあるが、「自然数のペアに同値関係を入れて、その商集合を整数とみなす」方法をとる。
-- Lean標準ライブラリでは自然数２つをくっつけるという別の方法で構成している。

abbrev PreInt := MyNat × MyNat
-- (a,b) → a-bという対応でPreIntの項を構成することにする
-- が、単射ではない。

def PreInt.r (m n : PreInt) : Prop :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => m₁+ n₂ = m₂ + n₁ 


theorem PreInt.r.refl : ∀ (m : PreInt), r m m := by
  intro m
  rw [PreInt.r]
  ac_rfl

theorem PreInt.r.symm : ∀ {m n : PreInt}, r m n → r n m := by
  intro m n
  intro h
  dsimp [PreInt.r] at *
  -- h: m.fst + n.snd = m.snd + n.fst
  -- ⊢ n.fst + m.snd = n.snd + m.fst
  -- ゴールの等式=の向きを変える
  symm
  rw [show n.snd + m.fst = m.fst + n.snd from by ac_rfl]
  rw [show n.fst + m.snd= m.snd + n.fst from by ac_rfl]
  exact h

-- これダルくね
theorem PreInt.r.trans : ∀ {l m n : PreInt}, r l m → r m n → r l n := by
  intro l m n
  intro hlm hmn
  dsimp [PreInt.r] at *
  -- hlm : l.fst + m.snd = l.snd + m.fst
  -- hmn : m.fst + n.snd = m.snd + n.fst
  -- ⊢ l.fst + n.snd = l.snd + n.fst

  have h1 : l.fst + m.snd + m.fst + n.snd = l.snd + m.fst + m.snd + n.fst := by
    calc 
      _ = (l.fst + m.snd) + (m.fst + n.snd) := by ac_rfl
      _ = (l.snd + m.fst) + (m.fst + n.snd) := by simp [hlm]
      _ = (l.snd + m.fst) + (m.snd + n.fst) := by rw [hmn]
      _ = l.snd + m.fst + m.snd + n.fst := by ac_rfl
  
  have h2 : l.fst + n.snd + (m.fst + m.snd) = l.snd + n.fst + (m.fst + m.snd) := by
    rw [show l.fst + n.snd + (m.fst + m.snd) = l.fst + m.snd + m.fst + n.snd from by ac_rfl]
    rw [show l.snd + n.fst + (m.fst + m.snd) = l.snd + m.fst +m.snd + n.fst from by ac_rfl]
    exact h1

  exact MyNat.add_right_cancel h2


theorem PreInt.r.equiv : Equivalence r := 
  { refl := r.refl, symm := r.symm, trans := r.trans}

/-- PreInt上の同値関係 -/
@[instance] def PreInt.sr : Setoid PreInt := ⟨r, r.equiv⟩ 

/-- MyNat × MyNat を同値関係で割ることで構成した整数 -/
abbrev MyInt := Quotient PreInt.sr 

#check
  let a : PreInt := (1, 3)
  Quotient.mk _ a 

-- notationコマンドで専用の記法をつくる
-- 打ち方↓
-- 〚 : \llb
-- 〛 : \rrb
notation:arg (priority := low) "〚" a "〛" => Quotient.mk _ a

#check (〚(1,3) 〛: MyInt)

def MyInt.ofNat (n : Nat) : MyInt := 〚(MyNat.ofNat n, 0)〛

-- ofNat型クラスのインスタンスを作る
instance {n : Nat} : OfNat MyInt n where
  ofNat := MyInt.ofNat n

#check (4 : MyInt)
#check_failure (-4 : MyInt) -- マイナス記号は使えない

def PreInt.neg : PreInt → MyInt
  | (m, n) => 〚(n,m)〛 

@[notation_simp]
theorem MyInt.sr_def (m n : PreInt) : m ≈ n  ↔ m.1 + n.2 = m.2 + n.1 := by
  rfl

def MyInt.neg : MyInt → MyInt := Quotient.lift PreInt.neg <| by
  -- defなのに急にintroとかしだすのなに？
  -- なんでgoalがあるの？
  -- ⊢ : ∀ (a b : PreInt) , a ≈ b → a.neg = b.neg
  intro (a₁, a₂) (b₁, b₂) hab
  suffices (a₂, a₁) ≈ (b₂, b₁) from by
    dsimp [PreInt.neg]
    rw [Quotient.sound]
    assumption

  notation_simp at *
  simp_all

-- マイナス記号を使うための型クラス
instance : Neg MyInt where
  neg := MyInt.neg


@[simp]
theorem MyInt.neg_def (x y : MyNat) : - 〚(x, y)〛 = (〚(y,x)〛: MyInt) := by
  -- ⊢ -Quotient.mk PreInt.sr (x,y) = Quotient.mk PreInt sr (y,x)
  dsimp [Neg.neg]
  rfl

-- #check (-4 : MyInt)

-- 7.3.4 練習問題
section

variable {α : Type} { r : α → α → Prop}

private theorem Ex.symm (refl : ∀ x, r x x) (h : ∀ x y z, r x y → r y z → r z x)
  : ∀ {x y : α}, r x y → r y x := by
    intro x y hxy
    -- ⊢ r y x
    have hyy : r y y := refl y

    exact h x y y hxy hyy

private theorem Ex.equiv (refl : ∀ x, r x x) (h : ∀ x y z, r x y → r y z → r z x) : Equivalence r := by
  constructor
  ·
    intro x
    exact refl x
  ·
    intro x y hxy
    -- ⊢ : r y x
    have hyy : r y y := refl y
    exact h x y y hxy hyy
  ·
    intro x y z hxy hyz
    -- ⊢ r x z

    have hzx : r z x := by
      exact h x y z hxy hyz

    have hzy : r z y := by
      exact h y y z (refl y) hyz

    have hyx : r y x := by
      exact h x y y hxy (refl y)

    exact h z y x hzy hyx

end
