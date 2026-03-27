-- 7.2 商とQuotient
-- 二項関係によって同じとみなされるものを同一視することを、
-- 「商」をとる　という。
-- Leanでは、型α上の同値関係sr: Setoid αに対し、Quotient srによって商が取れる。
-- Quotient srは「sr.r x yが成り立つときにx y: α は同じとみなす」という同一視で商をとったもの。
-- この節ではQuotientを通して、商のさまざまな概念を紹介する。
-- それらの概念を前提として、次節ではQuotientによりMyNatから整数を構成する方法の一つを説明する。
-- 7.2.1 Quotient.mk: 同値類を取る操作
-- 同値関係によって同じとみなされる項からなる集まりを、その項の同値類(equivalence class)と呼ぶ。
-- ℤにおいて、「4で割ったあまりが同じ」という同値関係を考えると、0の同値類は{0, -4,+4,-8,+8 ⋯ }
-- Leanでは、項x:αに対しては同値関係sr:Setoid αによる同値類を取る操作はQuotient.mk srで表せる

section
  variable {α β : Type} (sr: Setoid α)
  variable (f: β → α)
  #check (Quotient.mk sr : α → Quotient sr)

  -- 元の型αのすべての項は「どれかの項の同値類」に属してる。複数の同値類に属する項はない。
  -- 型αは同値類たちの直和。
  -- 言い換えると、同値類の全体が「α上の同値関係sr:Setoid αによる商」であり(?? NOTE: どういうこと？)
  -- Quotient srである。
  -- 同値類を取る操作 Quotient.mk srはこの商Quotient srへの関数になる。
  -- これは恣意的なところがない、構造的に導かれる操作なので、よく自然(canonical)な関数であると形容される。
  -- へー。

  -- 7.2.2 Quotient.inductionOn: 同値類の代表元をとる
  -- sr: Setoid αに関して同値な要素の集まりである同値類a: Quotient srに対し、a = Quotient.mk sr xとなるxが代表元

  example (a : Quotient sr) : True := by
    induction a using Quotient.inductionOn with
    | h x =>
      guard_hyp x : α
      trivial

  -- 7.2.3 Quotient.lift : 関数を商へ持ち上げる操作
  -- α : Type上の同値関係sr: Setoid αと、srによるαの商Quotient srについて考える。
  -- β→Quotient srの関数を得るには？ たとえば、Quotient.mk sr : α → Quotient sr と関数β → αを合成すればいい
  -- ∘は\compで入力できる
  #check (Quotient.mk sr ∘ f : β → Quotient sr)
  -- では、商からの関数を得るには？
  -- Quotient srの各要素は同値類なので、αの要素の集まり。もしg:α → βが与えられていて、
  -- 同値類as: Quotient srのどの要素a∈asについても同じ値を返すならば、gの定義域をQuotient srに持ち上げて
  -- Quotient sr → β という関数が得られる。
  -- この操作はQuotient.liftで実現できる。
  -- もしα: Type上の同値関係sr : Setoid αと関数g: α → βが与えられていてh : ∀ x, x ≈ y → g x = g yが成り立つなら,
  -- 商への持ち上げQuotient.lift g h : Quotient sr → βが得られる。
end
section
  variable {α β : Type} (sr: Setoid α)
  variable (g : α → β) (hg: ∀ x y, x ≈ y → g x = g y)
  #check (Quotient.lift g hg : Quotient sr → β)
end


-- 7.2.4 Quotient.sound : 同値なら商へ送って等しい
-- 型αの同値関係sr: Setoid αによる商α/sr := Quotient.srにおいてx,yが同値であるとする。(x ≈ yであるとする)
-- このとき、自然な関数α → α/sr による像が等しくなっているはず。言い換えると「商に送って等しい」と言える
-- (NOTE: どういうこと？？？？まず商においてx,yが同値ってなに？xの同値類とyの同値類が等しいということ？)
-- (NOTE: x≈yなら Quotient.mk sr x = Quotient.mk sr yということ？それは当たり前じゃない→そういうことでした)
-- Leanではこの事実にQuotient.soundという名前がついている
--
section
  variable {α : Type} (sr: Setoid α)
  variable (x y : α) (h : x≈y)

  example : Quotient.mk sr x = Quotient.mk sr y := by
    apply Quotient.sound
    exact h
end

-- 7.2.5 Quotient.exact: 商に送って等しいなら同値
-- Quotient.soundとは逆に、商に送って等しいなら同値というのもある。
-- これにはQuotient.exactという名前がついている。
section
  variable {α : Type} (sr : Setoid α)
  variable (x y : α)
  example (h : Quotient.mk sr x = Quotient.mk sr y) : x ≈ y := by
    apply Quotient.exact
    exact h
end

-- 練習問題7.2.6

private def Rel.comap {α β : Type} (f: α → β) (r : β → β → Prop)
  : α → α → Prop :=
  fun x y => r (f x) (f y)

private def Setoid.comp {α β : Type} (f : α → β) (sr : Setoid β) : Setoid α where
  r := Rel.comap f (· ≈ ·)
  iseqv := by
    -- f: α → β
    -- sr : Setoid β 
    -- ⊢ Equivalence (Rel.comap f fun x1 x2 => x1 ≈ x2)
    constructor
    ·
      intro x
      rw [Rel.comap]
      apply sr.refl
    · 
      intro x y
      intro h
      simp_all [Rel.comap]
      -- h : f x ≈ f y
      -- ⊢ f y ≈ f x
      apply sr.symm
      exact h
    · 
      intro x y z
      intro hxy
      intro hyz
      simp_all [Rel.comap]
      -- hxy : f x ≈ f y
      -- hyz : f y ≈ f z
      apply sr.trans hxy hyz
