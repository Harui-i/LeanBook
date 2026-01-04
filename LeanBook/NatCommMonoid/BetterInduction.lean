-- 4.5 帰納法を改善する
import LeanBook.NatCommMonoid.AcRfl

def MyNat.recAux.{u} {motive : MyNat → Sort u}
  (zero : motive 0)
  (succ : (n : MyNat) → motive n → motive (n+1)) (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)


-- これでinductionタクティクで使えるように
attribute [induction_eliminator] MyNat.recAux

example (m n : MyNat): m + n = n + m := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    ac_rfl


-- 一つ前の自然数を返す。0に対しては0を返す
private def MyNat.pred (n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => n

-- MyNat.pred n + 1って、 n=0なら1、そうでないならnなんだよな

-- これRFLでいけるんや！？！！？！？？！
example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  induction n with
  | zero =>
    --rw [zero_pred_add_1_eq_0]
    rfl
  | succ m ih =>
    rfl
