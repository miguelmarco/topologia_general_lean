import tactic

open set

example {X : Type} (A B : set X) : A ⊆ B ↔ A ∩ B = A :=
begin
  split,
  {
    intro h,
    ext x,
    split,
    {
      intro hx,
      cases hx with hxa hxb,
      exact hxa,
    },
    {
      intro hxa,
      split,
      {
        exact hxa,
      },
      {
        apply h,
        exact hxa,
      }
    }
  },
  {
    intro h,
    intros x hxa,
    suffices haux : x ∈ A ∩ B,   -- vamos a ver que basta ver esta otra afirmación
    {
      cases haux with hxA hxB,
      exact hxB,
    },
    -- y ahora probamos la afirmación
    rw h,   -- reescribimos usando h
    exact hxa,
  }
end

example {X : Type} (A B C : set X) : A ⊆ B → B ⊆ C → A ⊆ C :=
begin
  intros h1 h2,
  intros x hx,
  apply h2,
  apply h1,
  exact hx,
end

example {X : Type} (A B C : set X) : A ⊆ B ∧ A ⊆ C → A ⊆ B ∩ C :=
begin
  intro h,
  cases h with h1 h2,
  intros x hx,
  split,
  {
    apply h1,
    exact hx,
  },
  {
    apply h2,
    exact hx,
  }
end

example {X : Type} (A B C : set X) : A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C :=
begin
  intro h,
  cases h with h1 h2,
  intros x hx,
  cases hx,
  {
    apply h1,
    exact hx,
  },
  {
    apply h2,
    exact hx,
  }
end



/-
Algunas fórmulas con uniones e intersecciones
-/

variables (X : Type) (A B C : set X)

example : A ∪ A = A :=
begin
  ext x,
  split,
  {
    intro h,
    cases h with h1 h2,
    {
      use h1,
    },
    {
      use h2,
    },
  },
  {
    intro h,
    left,
    exact h,
  }
end

example : A ∩ A = A :=
begin
  ext x,
  split,
  {
    intro h,
    cases h with h1 h2,
    use h1,
  },
  {
    intro h,
    split,
    use h, use h,
  }
end

example : A ∩ ∅ = ∅ :=
begin
  ext x,
  split,
  {
    intro h,
    cases h with h1 h2,
    exact h2,
  },
  {
    intro h,
    cases h,
  }
end

example : A ∪ univ = univ :=
begin
  ext,
  split,
  {
    intro h,
    trivial,
  },
  {
    intro h,
    right,
    exact h,
  }
end

example : A ⊆ B → B ⊆ A → A = B :=
begin
  intros h1 h2,
  ext,
  split,
  {
    intro h,
    apply h1,
    exact h,
  },
  {
    intro h,
    apply h2,
    exact h,
  }
end

example : A ∩ B = B ∩ A :=
begin
  ext x,
  split,
  {
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
  {
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

example : A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
begin
  ext x,
  split,
  {
    intro h,
    cases h with h1 h2,
    cases h2 with h3 h4,
    split,
    {
      split,
        exact h1,
        exact h3,
    },
    {
      exact h4,
    }
  },
  {
    intro h,
    cases h with h1 h2,
    cases h1 with h3 h4,
    split,
    {
      exact h3,
    },
    {
      split,
        exact h4,
        exact h2,
    }
  }
end

example : A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
  ext x,
  split,
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
  },
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
      }
    },
    {
      right,
      right,
      exact h,
    }
  }
end

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
  ext x,
  split,
  {
    intro h,
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
      cases h with hb hc,
      split,
      {
        right,
        exact hb,
      },
      {
        right,
        exact hc,
      }
    }
  },
  {
    intro h,
    cases h with h1 h2,
    cases h1,
    {
      left,
      exact h1,
    },
    {
      cases h2,
      {
        left,
        exact h2,
      },
      {
        right,
        split,
        {
          exact h1,
        },
        {
          exact h2,
        }
      }
    }
  }
end

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext x,
  split,
  {
    intro h,
    cases h with h1 h2,
    cases h2,
    {
      left,
      split,
      {
        exact h1,
      },
      {
        exact h2,
      },
    },
    {
      right,
      split,
      {
        exact h1,
      },
      {
        exact h2,
      }
    }
  },
  {
    intro h,
    cases h,
    {
      cases h with ha hb,
      split,
      {
        exact ha,
      },
      {
        left,
        exact hb,
      }
    },
    {
      cases h with ha hc,
      split,
      {
        exact ha,
      },
      {
        right,
        exact hc,
      }
    }  
  }
end

/-
## uniones e intersecciones de familias
-/

example (X : Type) (F1 F2 : set (set X)) : (⋃₀ F1) ∩  (⋃₀ F2) = ⋃ (a ∈ F1) (b ∈ F2), a ∩ b :=
begin
  ext x,
  split,
  {
    intro h,
    cases h with h1 h2,
    cases h1 with a ha,
    cases ha with haF1 hxa,
    cases h2 with b hb,
    cases hb with hbF2 hxb,
    simp,
    use a,
    split,
    {
      exact haF1,
    },
    {
      use b,
      split, exact hbF2,
      split,
      exact hxa,
      exact hxb,
    }
  },
  {
    intro h,
    cases h with S hS,
    simp at hS,
    cases hS with Y hxY,
    cases Y with Y hY,
    rw ← hY at hxY,
    simp at hxY,
    cases hxY with hYF1 hY2,
    cases hY2 with Z hZ,
    cases hZ with hZF2 hZ2,
    cases hZ2 with hxY hxZ,
    split,
    {
      use Y,
      split,
      exact hYF1,
      exact hxY,
    },
    {
      use Z,
      split,
      exact hZF2,
      exact hxZ,
    },
  },
end

example (X : Type) (A : set X) (F : set (set X)) (hF : ∃ C, (C ∈ F)) : A ∩ (⋂₀ F) = ⋂ (B ∈ F), A ∩ B :=
begin
  ext x,
  split,
  {
    intro h,
    cases h with hxA hxF,
    simp,
    intros B hB,
    split,
    exact hxA,
    apply hxF,
    exact hB,
  },
  {
    intro h,
    split,
    {
      cases hF with C hC,
      simp at h,
      specialize h C hC,
      cases h with hxA hxC,
      exact hxA,
    },
    {
      intros B hB,
      simp at h,
      specialize h B hB,
      cases h with hxA hxB,
      exact hxB,
    }
  }
end 

/-
## Funciones
-/


-- la imagen es monótona

lemma subconjunto_imagen { X Y : Type} {f  : X → Y} (U V : set X) (huv : U ⊆ V) :
f '' U ⊆ f '' V :=
begin
  intros x hx,
  cases hx with a ha,
  cases ha with haU hfax,
  use a,
  split,
  {
    apply huv,
    exact haU,
  },
  exact hfax,
end

-- y la preimagen también

lemma subconjunto_preimagen { X Y : Type} {f  : X → Y} (U V : set Y) (huv : U ⊆ V) :
f  ⁻¹' U ⊆ f ⁻¹' V :=
begin
  intros x hx,
  apply huv,
  exact hx,
end



example (X Y : Type) (f : X → Y) (F : set (set X)) : f '' ⋃₀ F = ⋃₀ {V : set Y | ∃ U ∈ F, V = f '' U} :=
begin
 ext y,
 split,
 {
  intro h,
  cases h with x hx,
  cases hx with hxF hfxy,
  simp,
  cases hxF with U hU,
  cases hU with hUF hxU,
  use f '' U,
  use U,
  {
    split,
    {
      exact hUF,
    },
    {
      refl,
    },
  },
  use x,
  split,
  exact hxU,
  exact hfxy,
 },
 {
  intro h,
  cases h with V hV,
  cases hV with hV2 hyV,
  cases hV2 with U hU,
  cases hU with hUF hVfU,
  rw hVfU at hyV,
  cases hyV with x hx,
  cases hx with hxU hfxy,
  use x,
  split,
  {
    use U,
    split,
    exact hUF,
    exact hxU,
  },
  {
    exact hfxy,
  }
 }
end


-- La imagén de la intersección está contenida en intersección de las imágenes

example (X Y : Type) (f : X → Y) (U V : set X) : f '' (U  ∩ V ) ⊆  (f '' U) ∩  (f '' V ) :=
begin
  intros y hy,
  cases hy with x hx,
  cases hx with hxUV hfxy,
  cases hxUV with hxU hxV,
  split,
  {
    use x,
    split,
      exact hxU,
      exact hfxy,
  },
  {
    use x,
    split,
    exact hxV,
    exact hfxy,
  }
end

example (X Y : Type) (f : X → Y) (F : set (set X)) : f '' ⋂₀ F ⊆ ⋂₀ {V : set Y | ∃ U ∈ F, V = f '' U} :=
begin
  intros y hyf,
  intros V hV,
  cases hV with U hU,
  cases hU with hUF hVfU,
  cases hyf with x hx,
  cases hx with hxF hxy,
  rw hVfU,
  rw ← hxy,
  use x,
  split,
  {
    apply hxF,
    exact hUF,
  },
  {
    refl,
  }
end

-- La intersección de las preimagenes es la preimagen de la intersección

example (X Y : Type) (f : X → Y) (U V : set Y) : f ⁻¹' (U  ∩ V ) = (f ⁻¹' U) ∩ (f ⁻¹' V )  :=
begin
  ext,
  split,
  {
    intro h,
    cases h with hfxU hfxV,
    split,
    {
      exact hfxU,
    },
    {
      exact hfxV,
    },
  },
  {
    intro h,
    cases h with hxfU hxfV,
    split,
    {
      exact hxfU,
    },
    {
      exact hxfV,
    }
  }
end



example (X Y : Type) (f : X → Y) (F : set (set Y)) : f ⁻¹' (⋂₀ F ) = ⋂ (V : set Y) (hV: V ∈  F), f ⁻¹' V :=
begin
  ext x,
  split,
  {
    intro h,
    intros V,
    intro h2,
    cases h2 with W hW,
    rw ← hW,
    clear hW,
    intros hV hxfW,
    dsimp at hxfW,
    cases hxfW with hWF hfW,
    rw ← hfW,
    specialize h W hWF,
    exact h,
  },
  {
    intro h,
    intros V hV,
    apply h,
    dsimp,
    use V,
    ext x,
    split,
    {
      intro hx,
      apply hx,
      dsimp,
      use hV,
      refl,
    },
    {
      intro hx,
      intros W hW,
      dsimp at hW,
      cases hW with hVF hW,
      rw ← hW,
      exact hx,
    }
  }
end

-- La unión de las preimagenes es la imagen de la unión

example (X Y : Type) (f : X → Y) (U V : set Y) :  f ⁻¹' (U  ∪ V ) = (f ⁻¹' U) ∪ (f ⁻¹' V ) :=
begin
  ext x,
  split,
  {
    intro h,
    cases h,
    {
      left,
      exact h,
    },
    {
      right,
      exact h,
    }
  },
  {
    intro h,
    cases h,
    {
      left,
      exact h,
    },
    {
      right,
      exact h,
    }
  }
end

example (X Y : Type) (f : X → Y) (F : set (set Y)) : f ⁻¹' (⋃₀ F ) = ⋃ (V : set Y) (hV: V ∈  F), f ⁻¹' V :=
begin
  ext x,
  split,
  {
    intro hx,
    cases hx with U hU,
    cases hU with hUF hfxU,
    use f ⁻¹' U,
    dsimp,
    split,
    {
      use U ,
      ext y,
      split,
      {
        intro hy,
        cases hy with V hV,
        cases hV with hV hyV,
        dsimp at hV,
        cases hV with hUF hV,
        rw hV,
        exact hyV,
      },
      {
        intro hy,
        use f ⁻¹' U,
        dsimp,
        split,
        {
          use hUF,
        },
        {
          exact hy,
        }
      }
    },
    {
      exact hfxU,
    }
  },
  {
    intro hx,
    cases hx with U hU,
    dsimp at hU,
    cases hU with hU hxU,
    cases hU with V hV,
    rw ← hV at hxU,
    cases hxU with W hW,
    dsimp at hW,
    cases hW with H hxW,
    cases H with hWF H,
    use V,
    split,
    {
      use hWF,
    },
    {
      rw ← H at hxW,
      exact hxW,
    }
  }
end

