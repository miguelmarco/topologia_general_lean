import .cerrados
import .clausura
import tactic

open topologicos topologicos.espacio_topologico set

namespace topologicos

/-
# Interiores

En lo sucesivo, `X` será un espacio topológico.
-/
variables {X : Type} [espacio_topologico X]

/-
## Definición 3.3.1

Llamaremos interior de A en X al siguiente conjunto:
-/
def interior (A : set X ) : set X := ⋃₀ {S ∈ abiertos | S ⊆ A}

lemma interior_def (A : set X) : interior A = ⋃₀ {S ∈ abiertos | S ⊆ A} :=
begin
  refl,
end

/-
## Propiedades 3.3.3
-/
-- 1
lemma interior_abierto (A : set X) : abierto (interior A ) :=
begin
  apply abierto_union,
  intros S hS,
  exact hS.1,
end

-- 2
lemma interior_mayor_abierto (A U : set X) (hU : abierto U) (hUA : U ⊆ A) : U ⊆ interior A :=
begin
  intros x hx,
  use U,
  split,
  split,
  all_goals { assumption},
end

-- 3
lemma interior_contenido (A : set X) : interior A ⊆ A :=
begin
  apply set.sUnion_subset,
  intros S hS,
  exact hS.2,
end

-- 4
lemma interior_monotono (A B : set X) (hAB : A ⊆ B) : interior A ⊆ interior B :=
begin
  apply set.sUnion_subset_sUnion,
  intros S hS,
  cases hS with hSab hSA,
  split, assumption,
  tauto,
end

-- 5
lemma interior_eq_sii_abierto (A : set X) :    interior A = A  ↔ abierto A :=
begin
  split,
    {
    intro h,
    rw ← h,
    apply interior_abierto,
  },
  {
    intro hA,
    apply doble_contenido,
    {
      apply interior_contenido,
    },
    {
      apply interior_mayor_abierto,
      exact hA,
      tauto,
    },
  },
end

-- 6
@[simp]
lemma interior_interior (A : set X ) : interior (interior A ) = interior A :=
begin
  rw interior_eq_sii_abierto,
  apply interior_abierto,
end

-- 7
lemma interior_interseccion (A B : set X) : interior (A ∩ B) = interior A ∩ interior B :=
begin
  apply doble_contenido,
  {
    intros x hx,
    split,
    {
      calc 
        x    ∈ interior (A ∩ B )   : by {exact hx,}
        ...  ⊆ interior A          : by {simp [interior_monotono],}
    },
    {
      calc 
        x    ∈ interior (A ∩ B )   : by {exact hx,}
        ...  ⊆ interior B          : by {simp [interior_monotono],}
    },
  },
  {
    apply interior_mayor_abierto,
    {
      apply abierto_interseccion,
      repeat {apply interior_abierto, },
    },
    {
      intros x hx,
      cases hx with hxa hxb,
      split,
      {
        calc 
          x    ∈   interior A : by {exact hxa,}
          ...  ⊆   A          : by {apply interior_contenido,}
      },
      {
        calc
          x    ∈  interior B : by {exact hxb,}
          ...  ⊆   B         : by {apply interior_contenido,}
      },
    },
  },
end

-- 8
lemma interior_carac_entornos (A : set X) : interior A = { x | entorno x A} :=
begin
  apply doble_contenido,
  {
    intros x hx,
    use interior A,
    split,
      { apply interior_abierto,},
      split,
        {exact hx,},
        {apply interior_contenido,},
  },
  {
    intros y hy,
    cases hy with U hU,
    cases hU with hUab hU2,
    cases hU2 with hyU hUA,
    have hUinta := interior_mayor_abierto _ _ hUab hUA,
    apply hUinta,
    exact hyU,
  }
end

-- 9
lemma complementario_interior_clausura_complementario (A : set X) : (interior A)ᶜ = clausura (Aᶜ) :=
begin
  unfold interior,
  unfold clausura,
  ext x,
  split,
  {
    intro hx,
    simp only [set.mem_compl_iff] at hx,
    intros C hC,
    cases hC with hCcer hCAc,
    by_contradiction hnxC,
    apply hx,
    use Cᶜ,
    split,
    split,
    {
      exact hCcer,
    },
    {
      simp only [],
      rw compl_subset_comm,
      exact hCAc,
    },
    {
      exact hnxC,
    },
  },
  {
    intro hx,
    intro hnx,
    cases hnx with U hU,
    cases hU with hU2 hxU,
    cases hU2 with hUab hUA,
    specialize hx Uᶜ,
    apply hx,
    split,
    {
      simp only [compl_compl, hUab, topologicos.abierto_def, topologicos.cerrados_def],
    },
    {
      simp only [],
      simp [set.compl_subset_comm],
      exact hUA,
    },
    {
      exact hxU,
    }
  }
end

-- 10
lemma interior_complementario_clausura_complementario (A : set X) : (clausura A)ᶜ = interior (Aᶜ ) :=
begin
  have haux := complementario_interior_clausura_complementario Aᶜ,
  simp only [compl_compl] at haux,
  rw ← haux,
  simp only [compl_compl, eq_self_iff_true],
end


-- 11
lemma interior_union (A B : set X) : interior A ∪ interior B ⊆ interior (A ∪ B ) :=
begin
  apply interior_mayor_abierto,
  {
    apply abierto_union_2,
    repeat {
      apply interior_abierto,
    },
  },
  {
    intros x hx,
    cases hx,
    {
      left,
      apply interior_contenido,
      exact hx,
    },
    {
      right,
      apply interior_contenido,
      exact hx,
    }
  }
end



/-
## Proposición 3.3.4.

Sea A ⊂ X y x ∈ X, entonces las siguientes afirmaciones son equivalentes:
1. x ∈ Int(A).
2. ∃U ⊂ X abierto tal que x ∈ U ⊂ A.
3. ∃V x ⊂ X entorno de x en X tal que V x ⊂ A.
-/
@[simp]
lemma interior_caracterizacion_abiertos (A : set X) (x : X) : x ∈ interior A ↔ ∃ U ∈ (abiertos: set (set X)), U ⊆ A ∧ x ∈ U :=
begin
  simp [interior_def],
  tauto,
end

@[simp]
lemma interior_caracterizacion_entornos (A : set X) (x : X) : x ∈ interior A ↔ ∃ U ∈ 𝓝 X x, U ⊆ A :=
begin
  rw interior_caracterizacion_abiertos,
  split,
  {
    intro h,
    cases h with U hU,
    cases hU with hUab hU2,
    cases hU2 with hUA hxU,
    use U,
    split,
    {
      use U,
      tauto,
    },
    {
      exact hUA,
    },
  },
  {
    intro hx,
    cases hx with N hN,
    cases hN with hNent hNA,
    cases hNent with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUN,
    use U,
    split,
      exact hUab,
    split,
    {
      calc
        U   ⊆  N  : by {assumption,}
        ... ⊆  A  : by {assumption,}
    },
    {
      exact hxU,
    },
  },
end

/-
# Exteriores
-/

def exterior (A : set X) := interior Aᶜ

/-
## Propiedades 3.3.6
-/

-- 1
lemma exterior_abierto (A : set X) : abierto (exterior A) :=
begin
  unfold exterior,
  apply interior_abierto,
end
-- 2
lemma exterior_union_clausura_es_total (A : set X) : univ = (exterior A) ∪ (clausura A) :=
begin
  apply doble_contenido,
  {
    intros  x hx,
    by_cases  hxclau : x ∈ (clausura A)ᶜ,
    {
      left,
      rw interior_complementario_clausura_complementario at hxclau,
      exact hxclau,
    },
    {
      right,
      rw mem_compl_iff at hxclau,
      push_neg at hxclau,
      exact hxclau,
    },
  },
  {
   tauto,
  }
end

lemma exterior_disjunto_clausura (A : set X) : exterior A ∩ clausura A = ∅ :=
begin
  ext x,
  simp only [set.mem_empty_iff_false, not_and, set.mem_inter_iff, iff_false],
  intros hxext hxclau,
  unfold exterior at hxext,
  cases hxext with U hU,
  cases hU with hU2 hxU,
  cases hU2 with hUab hUAc,
  specialize hxclau Uᶜ,
  apply hxclau,
  {
    split,
    {
      simp only [compl_compl, topologicos.abierto_def, topologicos.cerrados_def],
      exact hUab,
    },
    {
      simp only [],
      tauto,
    }
  },
  {
    exact hxU,
  },
end

-- 3
lemma interior_disjunto_exterior (A : set X) : exterior A ∩ interior A = ∅ :=
begin
  ext x,
  have h1 := interior_contenido A,
  have h2 := interior_contenido Aᶜ,
  unfold exterior,
  split,
  {
    intro h,
    cases h with he hi,
    specialize h1 hi,
    specialize h2 he,
    apply h2,
    exact h1,
  },
  {
    simp only [mem_empty_iff_false, is_empty.forall_iff],
  }
end

/-
## Proposición 3.3.7

Sea `A ⊂ X` y `x ∈ X`, entonces las siguientes afirmaciones son equivalentes:

1. x ∈ Ext(A).
2. ∃ U ⊂ X abierto tal que x ∈ U y U ∩ A = ∅.
3. ∃V x ⊂ X entorno de x en X tal que V x ∩ A = ∅
-/
lemma x_en_exterior_sii_abierto_disjunto (x : X) (A : set X) : x ∈ exterior A ↔ ∃ U, abierto U ∧ x ∈ U ∧ U ∩ A = ∅  := 
begin
  split,
  {
    intro h,
    cases h with U hU,
    cases hU with hU2 hxU,
    cases hU2 with hUab hUAc,
    use U,
    split,
      exact hUab,
    split,
      exact hxU,
    rw disjuntos_sii_contenido_en_complemento,
    exact hUAc,
  },
  {
    intro h,
    cases h with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUA,
    use U,
    split,
    split,
      exact hUab,
    {
      dsimp,
      rw ← disjuntos_sii_contenido_en_complemento,
      exact hUA,
    },
      exact hxU,
  }
end

lemma x_en_exterior_sii_entorno_disjunto (x : X) (A : set X) : x ∈ exterior A ↔ ∃ V ∈ 𝓝 X x,  V ∩ A = ∅  :=
begin
  rw x_en_exterior_sii_abierto_disjunto,
  split,
  {
    intro h,
    cases h with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUA,
    use U,
    split,
    {
      use U,
      split,
        exact hUab,
      split,
        exact hxU,
        tauto,
    },
    exact hUA,
  },
  {
    intro h,
    cases h with V hV,
    cases hV with hVent hVA,
    cases hVent with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUV,
    use U,
    split,
      exact hUab,
    split,
      exact hxU,
    {
      apply doble_contenido,
      {
        rw ← hVA,
        apply inter_subset_inter,
          assumption,
          tauto,
      },
      {
        tauto,
      }
    }
  }
end

/-
# Fronteras
-/
def frontera (A : set X) := { x | x ∉ interior A ∧ x ∉ exterior A}

/-
## Propiedades 3.3.9
-/

lemma complementario_frontera (A  : set X) : (frontera A)ᶜ = interior A ∪ exterior A :=
begin
  ext x,
  dsimp [frontera],
  push_neg,
  tauto,
end

lemma frontera_cerrado (A : set X) : cerrado (frontera A) := 
begin
  unfold cerrado,
  rw complementario_frontera,
  apply abierto_union_2,
    apply interior_abierto,
    apply exterior_abierto,
end

lemma frontera_de_complementario (A : set X) : frontera A = frontera Aᶜ :=
begin
  dsimp [frontera,exterior],
  ext x,
  simp only [not_and, mem_set_of_eq, compl_compl],
  tauto,
end

lemma frontera_interseccion_clausura_compl (A : set X) : frontera A = clausura A ∩ clausura Aᶜ :=
begin
  calc 
    frontera A  = (frontera A)ᶜᶜ                 : by {rw compl_compl,}
    ...         = (interior A ∪ exterior A)ᶜ     : by {rw complementario_frontera,}
    ...         = (interior A)ᶜ ∩ (exterior A)ᶜ  : by {rw complemento_union,}
    ...         = (interior A)ᶜ ∩ (interior Aᶜ)ᶜ : by {rw exterior,}
    ...         = clausura Aᶜ ∩ (interior Aᶜ)ᶜ   : by {rw complementario_interior_clausura_complementario,}
    ...         = clausura Aᶜ ∩ clausura Aᶜᶜ     : by {rw complementario_interior_clausura_complementario,}
    ...         = clausura Aᶜ ∩ clausura A       : by {rw compl_compl,}
    ...         = clausura A ∩ clausura Aᶜ       : by {rw inter_comm,}
end

end topologicos