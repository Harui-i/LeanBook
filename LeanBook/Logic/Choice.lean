#check Classical.em -- 排中律

#print axioms Classical.em -- `Classical.em` depends on axioms: [propext, Classical.choice, Quot.sound]


/-- 関数の全射性 -/
def Surjective {X Y : Type} (f: X → Y) : Prop :=
  ∀ y : Y, ∃ x, f x = y

example : Surjective (fun x : Nat => x) := by

  intro y
  exists y


variable {X Y : Type}

/-- 全射である関数 f: X → Y に対してその右逆関数 g: Y→X を返すような高階関数 -/
noncomputable def inverse (f: X→Y)(hf: Surjective f) : Y → X := by
  intro y

  -- fは全射なので {x // f x = y}は空ではない
  -- {x // P x}という表記は、ある型の要素のうちPという述語が成り立つものだけを集めたもの　を表す
  have : Nonempty {x // f x = y} := by
    let ⟨x, hx⟩ := hf y
    exact ⟨x, hx⟩

  -- 選択原理を用いて f x = yなるx: Xを構成する
  have x := Classical.choice this
  exact x.val


theorem double_negation_of_contra_equiv (P: Prop)
  (contra_equiv : ∀ (P Q : Prop), (¬P → ¬ Q) ↔ (Q → P)) : ¬¬P → P := by
  intro hnnp
  -- ¬¬P
  -- ¬(P → False)
  -- (¬P → False)
  -- ↓対偶をつかう
  -- (True → P)
  have h_neg_true : ¬True ↔ False := by
    --ここの証明きれいにならないかな
    simp_all

  have h_np_imp_false : ¬P → ¬True  := by
    rw [h_neg_true]
    exact hnnp

  rw [contra_equiv P True] at h_np_imp_false

  -- Goal: True → P
  have h_true : True := by
    -- True項を取るのにこんな面倒なことしなきゃいけないの？
    simp

  exact h_np_imp_false h_true

#print axioms double_negation_of_contra_equiv

-- 演習の解答をみた
-- 結局simpを使うのは同じだけど、rw [show Q from by simp] at h1 みたいな書き方で省略してる
example (P: Prop)
  (contra_equiv : ∀ (P Q : Prop), (¬P → ¬ Q) ↔ (Q → P)) : ¬¬P → P := by

  have := contra_equiv P True
  -- this : ¬P → ¬True ↔ True → P
  rw [show ¬True ↔ False from by simp] at this
  -- this: ¬P → False ↔ True → P
  rw [show (True → P) ↔ P from by simp] at this
  -- this : ¬P → False ↔ P
  rw [show (¬P → False) ↔ ¬¬P from by simp] at this
  -- this: ¬¬P ↔ P
  rw [this]
  -- goal: P → P
  intro hp
  assumption
