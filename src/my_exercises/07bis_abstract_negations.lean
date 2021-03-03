import data.real.basic

open_locale classical

/-
Theoretical negations.

This file is for people interested in logic who want to fully understand
negations.

Here we don't use `contrapose` or `push_neg`. The goal is to prove lemmas
that are used by those tactics. Of course we can use
`exfalso`, `by_contradiction` and `by_cases`.

If this doesn't sound like fun then skip ahead to the next file.
-/

section negation_prop

variables P Q : Prop

-- 0055
example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split,
  { intros h hnotQ hP,
    apply hnotQ,
    apply h,
    exact hP,
  },
  { intros h hP,
    by_contradiction hnotQ,
    specialize h hnotQ,
    apply h,
    exact hP,
  }
end

-- 0056
lemma non_imp (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q :=
begin
  split,
  { intros h,
    by_contradiction H,
    apply h,
    intro hP,
    by_contradiction hnotQ,
    apply H,
    exact ⟨hP, hnotQ⟩,
  },
  { rintros ⟨hP, hnotQ⟩ h,
    specialize h hP,
    apply hnotQ,
    exact h,
  }
end

-- In the next one, let's use the axiom
-- propext {P Q : Prop} : (P ↔ Q) → P = Q

-- 0057
example (P : Prop) : ¬ P ↔ P = false :=
begin
  split,
  { intro hnotP,
    apply propext,
    split, 
    { exact hnotP, },
    { intro contra, exfalso, exact contra, }
  },
  { rintro rfl,
    intro contra, exfalso, exact contra,
  }
end

end negation_prop

section negation_quantifiers
variables (X : Type) (P : X → Prop)

-- 0058
example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
begin
  split,
  { intro h,
    by_contradiction H,
    apply h,
    intro x,
    by_contradiction hnotP,
    apply H,
    use x,
  },
  { rintros ⟨x, hnotP⟩ h',
    apply hnotP,
    exact h' x,
  }
end

-- 0059
example : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x :=
begin
  split,
  { intros h x hP,
    apply h,
    use [x, hP],
  },
  { rintros h ⟨x, hnotP⟩,
    exact h x hnotP,
  }
end

-- 0060
example (P : ℝ → Prop) : ¬ (∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬ P ε :=
begin
  split,
  { intros h ε hε hP,
    apply h,
    use [ε, hε, hP],
  },
  { rintros h ⟨ε, hε, hP⟩,
    exact h ε hε hP,
  }
end

-- 0061
example (P : ℝ → Prop) : ¬ (∀ x > 0, P x) ↔ ∃ x > 0, ¬ P x :=
begin
  split,
  { intros h,
    by_contradiction H,
    apply h,
    intros x hx,
    by_contradiction hnotP,
    apply H,
    use [x, hx, hnotP],
  },
  { rintros ⟨x, hx, hnotP⟩ h,
    apply hnotP,
    exact h x hx,
  }
end

end negation_quantifiers

