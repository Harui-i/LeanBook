
example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro h1
  intro h2
  cases h1 with
  | inl hnp =>
    exfalso
    contradiction
  | inr hq =>
    exact hq

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor
  ·
    intro h1
    constructor
    ·
      intro hP
      have hPorQ : P ∨ Q := Or.inl hP
      exact h1 hPorQ
    ·
      intro hQ
      have hPorQ : P ∨ Q := Or.inr hQ
      exact h1 hPorQ
  ·
    intro h1
    intro h2
    cases h2 with
    | inl hP =>
      exact h1.left hP
    | inr hQ =>
      exact h1.right hQ
