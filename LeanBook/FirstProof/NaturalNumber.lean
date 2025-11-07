-- 2.2 自然数を定義して 1+1 = 2を証明する

-- `inductive` コマンドを使って定義されるデータ型は「帰納型」, 帰納型の項を与える関数は「コンストラクタ」と呼ばれる。
-- MyNat: 帰納型
-- zero, succ: コンストラクタ
inductive MyNat where
    | zero
    | succ(n : MyNat)


#check MyNat.zero -- MyNat.zero : MyNat (MyNat型の定数であることがわかる)
#check MyNat.succ -- MyNat.succ (n : MyNat) : MyNat
#check MyNat.succ (MyNat.zero) -- MyNat.zero.succ : MyNat

/-- 自前で定義した1 -/
def MyNat.one := MyNat.succ .zero

/-- 自前の2-/
def MyNat.two := MyNat.succ .one

def MyNat.add (m n : MyNat) : MyNat :=
    -- MyNat.add関数の定義中なので、 `MyNat.` を省略できる
    match n with
    | .zero => m -- MyNatの定義から、値は zeroか succ(n)のどちらかなので、matchで場合わけ
    | .succ l => succ (add m l) -- m + succ(l) = succ(m + l)
    -- | .succ n => succ (add m n) ともかける。

#check MyNat.add .one .one = .two -- 型は Prop

set_option pp.fieldNotation.generalized false

#reduce MyNat.add .one .one
#reduce MyNat.two

-- `example` は命題に名前をつけずに証明するためのコマンド。
example : MyNat.add .one .one = .two := by
    rfl
