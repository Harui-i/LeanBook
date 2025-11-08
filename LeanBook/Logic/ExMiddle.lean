-- 3.4.2 直観論理

/-- 二重否定の除去-/
example (P : Prop) : ¬¬ P → P := by
  intro hn2p
  by_cases h : P
  ·
    exact h
  ·
    contradiction

-- 3.4.3 練習問題

/-- 二重否定の除去 --/
example (P: Prop) : ¬¬ P → P := by
  intro hn2p
  -- ¬(P → False)
  -- (P → False) → False
  -- ¬P → False

  by_cases h : P
  ·
    exact h
  ·
    contradiction


/-- ド・モルガンの法則-/
example (P Q : Prop) : ¬(P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  ·
    intro h1
    -- h1: ¬(P ∧ Q)
    -- P ∧ Q → False
    by_cases h2 : P
    ·
      by_cases h3 : Q
      ·
        exfalso
        have h4 : P ∧ Q := by
          exact And.intro h2 h3
        exact h1 h4
      ·
        exact Or.inr h3
    ·
      exact Or.inl h2
  ·
    intro h1 -- ¬P ∨ ¬Q
    intro h2 -- P ∧ Q
    cases h1 with -- ¬P と ¬Qで場合分け
    | inl h3 => -- ¬Pの場合
      exact h3 h2.left
    | inr h3 => -- ¬Q の場合
      exact h3 h2.right

/-- 対偶が元の命題と同値 -/
example (P Q : Prop) : (P → Q) ↔ (¬Q → ¬ P) := by
  constructor
  ·
    -- (P → Q) → (¬Q → ¬P)
    intro hpq
    intro hnq
    intro hp
    exact hnq (hpq hp)
  ·
    intro h1
    intro hP
    by_cases hq : Q
    ·
      exact hq
    ·
      exfalso

      have hnp : ¬ P := h1 hq
      contradiction
