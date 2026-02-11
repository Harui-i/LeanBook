import LeanBook.NatOrder.StrictOrder
import LeanBook.NatOrder.NotationSimpTag

-- 6.4章　記法の展開を楽にする
-- 前回の証明では `dsimp [(· < ·), MyNat.lt]`というフレーズが何度も登場した
-- こういった記法を定義式へと展開するのを楽にする方法を考え、それを証明で使う

theorem MyNat.lt_def (m n : MyNat) : m < n ↔ m + 1 ≤ n := by
  rfl

section
  attribute [local simp] MyNat.lt_def

  /-
  example (m n : MyNat) : m < n := by
    simp 
    guard_target =ₛ m +1 ≤ n
    sorry
  -/

  -- これで展開をすることもできるが、`simp`を実行したときに、記法の展開以外も行われてしまう。
end

section
open Lean Parser Tactic

/-- +,≤など、演算子や記法を定義に展開する -/
syntax "notation_simp" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) => 
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp only [notation_simp, $args,*] $[at $location]?)

-- (simpArgs)? や (location?)などの?は省略可能であることを意味する。
-- simpArgsはsimpタクティクに渡す引数を表す構文。
-- simp [MyNat.add_zero]などと書いたときの[MyNat.add_zero]の部分にそうとうする
-- locationはatのあと(笑)に続く部分で、rw[lem] at hなどと書いたときのat hの部分に相当する
end

-- <の定義を展開する定理に[notation_simp]属性を付与する
attribute [notation_simp] MyNat.lt_def

/-
example (m n : MyNat) : m < n := by
  notation_simp
  guard_target =ₛ m+1≤n
  sorry
-/
example (m n : MyNat) (h: m < n) : m+1≤n := by
  notation_simp at *
  assumption

-- 6.4.3 notation_simp?属性を定義する
-- notation_simpは使ったときに展開が進みすぎてしまったので戻したいという場合もあり得る。
-- そんなときのためにどんな展開ルールが使われたかを表示するタクティクを定義する
section
open Lean Parser Tactic
/-- +や≤など、演算子や記法を定義に展開する-/
syntax "notation_simp?" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) => 
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)
end

/-
example (m n : MyNat) : m < n := by
  notation_simp?
  sorry
-/

example (a b : MyNat) (h1 : a < b) (h2 : b < a) : False := by
  notation_simp at *
  simp [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h1 
  obtain ⟨l, hl⟩ := h2

  -- hk : a+1+k=b
  -- hl : b+1+l=a
  have h3: b=a+1+k := by
    simp [hk]
  simp [h3] at hl
  --hl: a+1+k+1+l = a
  --
  rw [show a+1+k+1+l = a+(k+l+2) from by ac_rfl] at hl
  --rw [show a=a+0 from by ac_rfl] at hl
  rw (config := {occs := .pos [2]}) [show a = a+0 from by ac_rfl] at hl
  -- hl : a + (k+l+2) = a + 0
  simp at hl
  -- hl : (k=0 ∧ l=0) ∧ 2 = 0
  have hlr : 2 = 0 := hl.right
  -- hlr : 2=0
  -- 帰納型で定義されているので単射。証明が通る
  injections


  



