import LeanBook.NatCommMonoid.TypeClass
-- 4.2 帰納法で 0 + n = n を証明する
--example (n : MyNat) : 0 + n = 0 := by
 -- rfl -- 通らない

#reduce fun (n : MyNat) => n+0 -- fun n => n
#reduce fun (n : MyNat) => 0+n -- fun => (MyNat.rec (MyNat.zero, PUnit.unit) (fun n n_ih....))

set_option pp.fieldNotation.generalized false

theorem MyNat.add_succ (m n : MyNat) : m + MyNat.succ n = MyNat.succ (m + n) := by
  rfl

example (n : MyNat) : 0 + n = n := by
  induction n with
  | zero =>
    -- goal : 0 + MyNat.zero = 0
    rfl
  | succ n' ih=>
    -- ih: 0 + n' = n'
    -- goal: 0 + MyNat.succ n' = MyNat.succ n'
    -- 足し算の定義から、 0 + MyNat.succ n'は (0 + n').succになる
    rw [MyNat.add_succ]
    rw [ih]
    -- これで終わりか！？？！！！！

example (n : MyNat) : 1 + n = .succ n :=  by
  induction n with
  | zero =>
    rfl
  | succ n' ih =>
    -- ih: 1 + n' = MyNat.succ n'
    -- Goal: 1 + MyNat.succ n' = MyNat.succ (MyNat.succ n')
    rw [MyNat.add_succ]
    -- Goal: MyNat.succ (1 + n') = MyNat.succ(MyNat.succ n')
    rw [ih]
    -- Solved!
