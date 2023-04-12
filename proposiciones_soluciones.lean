import tactic


/-
# Ejercicios
-/

variables p q r s: Prop

/- 
## Demuestra la conmutatividad de ∧ y ∨ 
-/
example : p ∧ q ↔ q ∧ p  :=
begin
  split,
  repeat {
    intro h,
    cases h with h1 h2,
    split,
    {
      exact h2,
    },
    {
      exact h1,
    }
  },
end

example : p ∨ q ↔ q ∨ p  :=
begin
  split,
  repeat  {
    intro h,
    cases h,
    {
      right,
      exact h,
    },
    {
      left,
      exact h,
    },
  },
end





/- 
## Demuestra la asociatividad de  ∧ y  ∨
-/
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
begin
  split,
  {
    intro h,
    cases h with hpq hr,
    cases hpq with hp hq,
    split,
    {
      exact hp,
    },
    {
      split,
      {
        exact hq,
      },
      {
        exact hr,
      }
    }
  },
  {
    intro h,
    cases h with hp hqr,
    cases hqr with hq hr,
    split,
    {
      split,
      {
        exact hp,
      },
      {
        exact hq,
      },
    },
    {
      exact hr,
    }
  }
end

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin
  split,
  {
    intro h,
    cases h,
    {
      cases h,
      {
        left,
        exact h,
      },
      {
        right,
        left,
        exact h,
      },
    },
    {
      right,
      right,
      exact h,
    }
  },
  {
    intro h,
    cases h,
    {
      left,
      left,
      exact h,
    },
    {
      cases h,
      {
        left,
        right,
        exact h,
      },
      {
        right,
        exact h,
      }
    }
  }
end 


/- 
## Demuestra la distributividad de ∧ respecto de ∨ y viceversa
-/

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  split,
  {
    intro h,
    {
      cases h with hp hqr,
      cases hqr,
      {
        left,
        split,
        {
          exact hp,
        },
        {
          exact hqr,
        },
      },
      {
        right,
        split,
        {
          exact hp,
        },
        {
          exact hqr,
        },
      },
    },
  },
  {
    intro h,
    cases h,
    {
      cases h with hp hq,
      split,
      {
        exact hp,
      },
      {
        left,
        exact hq,
      },
    },
    {
      cases h with hp hr,
      split,
      {
        exact hp,
      },
      {
        right,
        exact hr,
      }
    }
  }
end

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)  :=
begin
  split,
  {
    intro h,
    {
      cases h,
      {
        split,
        {
          left,
          exact h,
        },
        {
          left,
          exact h,
        },
      },
      {
        cases h with hq hr,
        {
          split,
          {
            right,
            exact hq,
          },
          {
            right,
            exact hr,
          },
        },
      },
    },
  },
  {
    intro h,
    cases h with hpq hpr,
    cases hpq,
    {
      left,
      exact hpq,
    },
    {
      cases hpr,
      {
        left,
        exact hpr,
      },
      {
        right,
        split,
        {
          exact hpq,
        },
        {
          exact hpr,
        },
      },
    },
  },
end



/-
## Demuestra las siguientes propiedades
-/
example : (p → (q → r)) ↔ (p ∧ q → r) :=
begin
  split,
  {
    intro h,
    intro h2,
    cases h2 with hp hq,
    apply h,
    {
      exact hp,
    },
    {
      exact hq,
    },
  },
  {
    intro h,
    intro hp,
    intro hq,
    apply h,
    split,
    {
      exact hp,
    },
    {
      exact hq,
    },
  },
end

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r)  :=
begin
  split,
  {
    intro h,
    split,
    {
      intro hp,
      apply h,
      left,
      exact hp,
    },
    {
      intro hq,
      apply h,
      right,
      exact hq,
    },
  },
  {
    intro h,
    intro hpq,
    cases h with h1 h2,
    cases hpq,
    {
      apply h1,
      exact hpq,
    },
    {
      apply h2,
      exact hpq,
    },
  },
end
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q  :=
begin
  split,
  {
    intro h,
    split,
    {
      intro hn,
      apply h,
      left,
      exact hn,
    },
    {
      intro hn,
      apply h,
      right,
      exact hn,
    },
  },
  {
    intro h,
    intro hn,
    cases h with hnp hnq,
    cases hn,
    {
      apply hnp,
      exact hn,
    },
    {
      apply hnq,
      exact hn,
    },
  },
end

example :¬p ∨ ¬q → ¬(p ∧ q)  :=
begin
  intro h,
  intro hn,
  cases hn with hp hq,
  cases h,
  {
    apply h,
    exact hp,
  },
  {
    apply h,
    exact hq,
  },
end

example : ¬(p ∧ ¬p)  :=
begin
  intro hn,
  cases hn with hp hnp,
  apply hnp,
  exact hp,
end

example : p ∧ ¬q → ¬(p → q)  :=
begin
  intro h,
  intro hn,
  cases h with hp hnq,
  apply hnq,
  apply hn,
  exact hp,
  
end

example : ¬p → (p → q)  :=
begin
  intro hnp,
  intro hp,
  specialize hnp hp,
  cases hnp,
end

example : (¬p ∨ q) → (p → q) :=
begin
  intro h,
  intro hp,
  cases h,
  {
    specialize h hp,
    cases h,
  },
  {
    exact h,
  }
end

example : p ∨ false ↔ p :=
begin
  split,
  {
    intro h,
    cases h,
    {
      exact h,
    },
    {
      cases h,
    },
  },
  {
    intro h,
    left,
    exact h,
  }
end

example : p ∧ false ↔ false :=
begin
  split,
  {
    intro h,
    cases h with hp hf,
    exact hf,
  },
  {
    intro h,
    cases h,
  },
end



/-
## Algunas demostraciones que requieren razonamiento clásico

Estas demostraciones requieren usar algunas tácticas nuevas:

- `by_contradiction` asume la negación del objetivo, y tenemos que demostrar una contradicción
- `by_cases`  h : P crea dos nuevos contextos: uno en el que tenemos que demostrar el objetivo
  suponiendo P, y otro en el que tenemos que demostrarlo suponiendo ¬ P
- `push_neg` "mete las negaciones" en una expresión. Por ejemplo cambia ¬ (P ∧ Q) por ¬ P ∨ ¬ Q
-/

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
begin
  by_cases hp : p,
  {
    intro h,
    specialize h hp,
    cases h,
    {
      left,
      intro hp2,
      exact h,
    },
    {
      right,
      intro hp2,
      exact h,
    },
  },
  {
    intro h,
    left,
    {
      intro hpc,
      specialize hp hpc,
      cases hp,
    }
  }
end

example : ¬(p ∧ q) → ¬p ∨ ¬q  :=
begin
  intro h,
  by_cases hcases : p,
  {
    right,
    intro hq,
    apply h,
    split,
    {
      exact hcases,
    },
    {
      exact hq,
    }
  },
  {
    left,
    exact hcases,
  },
end


example : ¬(p → q) → p ∧ ¬q  :=
begin
  intro h,
  push_neg at h,
  exact h,
end

example :  (p → q) → (¬p ∨ q)  :=
begin
  intro h,
  by_cases hp : p,
  {
    right,
    apply h,
    exact hp,
  },
  {
    left,
    exact hp,
  }
end

example : (¬q → ¬p) → (p → q)  :=
begin
  intro h,
  intro hp,
  by_contradiction hnq,
  specialize h hnq,
  apply h,
  exact hp,
end

example : p ∨ ¬p :=
begin
  by_cases h : p,
  {
    left,
    exact h,
  },
  {
    right,
    exact h,
  }
end

example : (((p → q) → p) → p)  :=
begin
  by_cases hp : p,
  {
    intro h,
    exact hp,
  },
  {
    intro h,
    apply h,
    intro hpa,
    specialize hp hpa,
    cases hp,
  },
end
