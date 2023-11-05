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
lemma interior_caracterizacion_abiertos (A : set X) (x : X) : x ∈ interior A ↔ ∃ U ∈ (abiertos: set (set X)),  x ∈ U ∧  U ⊆ A:=
begin
  simp [interior_def],
  tauto,
end


lemma interior_caracterizacion_entornos (A : set X) (x : X) : x ∈ interior A ↔ ∃ U ∈ 𝓝 X x, U ⊆ A :=
begin
  rw interior_caracterizacion_abiertos,
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
      exact hxU,
    },
    {
      calc
        U   ⊆  N  : by {assumption,}
        ... ⊆  A  : by {assumption,}
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

lemma exterior_complementario_clausura (A : set X) : exterior A = (clausura A)ᶜ :=
begin
  have h1 := exterior_union_clausura_es_total A,
  have h2 := exterior_disjunto_clausura A,
  ext x,
  split,
  {
    intro hx,
    intro hc,
    have haux : x ∈ exterior A ∩ clausura A,
    {
      split,
      assumption,
      assumption,
    },
    rw h2 at haux,
    exact haux,
  },
  {
    intro hx,
    have haux : x ∈ (univ : set X),
    {
      tauto,
    },
    rw h1 at haux,
    cases haux,
    {
      exact haux,
    },
    {
      tauto,
    },
  },
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
def frontera (A : set X) : set X := (interior A ∪ exterior A)ᶜ 

/-
## Propiedades 3.3.9
-/

lemma complementario_frontera (A  : set X) : (frontera A)ᶜ = interior A ∪ exterior A :=
begin
  simp [frontera],
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
  simp,
  rw inter_comm,
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

lemma clausura_union_frontera_interior (A : set X ) : clausura A = interior A ∪ frontera A :=
begin
  unfold frontera,
  rw exterior_complementario_clausura,
  simp only [compl_compl, complemento_union],
  rw union_inter_distrib_left,
  simp only [set.univ_inter, set.union_compl_self],
  apply doble_contenido,
  {
    simp only [set.subset_union_right],
  },
  {
    simp only [set.union_subset_iff],
    split,
    {
      calc
        interior A ⊆  A           :  by {apply interior_contenido}
        ...        ⊆  clausura A  :  by {apply clausura_contiene}
    },
    tauto,
  },
end

lemma total_union_interior_frontera_exterior (A : set X) : univ = interior A ∪ frontera A ∪ exterior A :=
begin
  unfold frontera,
  simp only [complemento_union],
  ext x,
  simp only [true_iff, set.mem_univ, set.mem_compl_iff, set.mem_union, set.mem_inter_iff],
  rw or_and_distrib_left,
  rw and_or_distrib_right,
  split,
  {
    left,
    tauto,
  },
  {
    rw or_assoc,
    right,
    rw or_comm,
    tauto,
  }
end

lemma frontera_disjunta_interior (A : set X) : frontera A ∩ interior A = ∅ :=
begin
  unfold frontera,
  ext x,
  simp only [and_imp,set.mem_empty_iff_false, not_and, complemento_union, set.mem_compl_iff, set.mem_inter_iff, iff_false],
  tauto,
end

lemma frontera_disjunta_exterior (A : set X) : frontera A ∩ exterior A = ∅  :=
begin
  rw frontera_de_complementario,
  unfold exterior,
  apply frontera_disjunta_interior,
end

/-
## Proposición 3.3.10
-/
lemma caracterizacion_puntos_frontera_abiertos (x : X) (A : set X) : x ∈ frontera A ↔ ∀ U,  abierto U → x ∈ U → U ∩ A ≠ ∅ ∧ U ∩ Aᶜ ≠ ∅ :=
begin
  unfold frontera,
  rw exterior,
  simp only [complemento_union, set.mem_compl_iff, set.mem_inter_iff],
  rw interior_caracterizacion_abiertos,
  rw interior_caracterizacion_abiertos,
  simp only [exists_prop, not_exists, not_and, abierto_def, ne.def],
  split,
  {
    intro h,
    cases h with h1 h2,
    intros U hU hxU,
    specialize h1 U hU hxU,
    specialize h2 U hU hxU,
    split,
    {
      rw disjuntos_sii_contenido_en_complemento,
      assumption,
    },
    {
      rw disjuntos_sii_contenido_en_complemento,
      rw compl_compl,
      exact h1,
    },
  },
  {
    intro h,
    split,
    {
      intros U hU hxU,
      specialize h U hU hxU,
      cases h with h1 h2,
      rw disjuntos_sii_contenido_en_complemento at h2,
      simp only [compl_compl] at h2,
      exact h2,
    },
    {
      intros U hU hxU,
      specialize h U hU hxU,
      cases h with h1 h2,
      rw disjuntos_sii_contenido_en_complemento at h1,
      exact h1,
    }
  }
end

lemma caracterizacion_puntos_frontera_entornos (x : X) (A : set X) : x ∈ frontera A ↔ ∀ E ∈ 𝓝 X x, E ∩ A ≠ ∅ ∧ E ∩ Aᶜ ≠ ∅ :=
begin
  rw caracterizacion_puntos_frontera_abiertos,
  split,
  {
    intro h,
    intros E hE,
    cases hE with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUE,
    specialize h U hUab hxU,
    cases h with h1 h2,
    simp [disjuntos_sii_contenido_en_complemento] at *,
    split,
    {
      intro hn,
      apply h1,
      calc
        U    ⊆ E  : by {exact hUE,} 
        ...  ⊆ Aᶜ : by {exact hn,}
    },
    {
      intro hn,
      apply h2,
      calc
        U    ⊆ E  : by {exact hUE,} 
        ...  ⊆ A : by {exact hn,}
    }
  },
  {
    intro h,
    intros U hUab hxU,
    specialize h U _,
    {
      use U,
      tauto,
    },
    exact h,
  }
end

/-
# Aislado

## Definición 3.3.10
-/
def aislado (A : set X) := { x ∈ A | ∃ U, abierto U ∧ U ∩ A = {x}}

/-
## Propiedades 3.3.11
-/
lemma aislado_contenido (A : set X) : aislado A ⊆ A :=
begin
  unfold aislado,
  simp only [set.sep_subset],
end

lemma aislado_caracterizacion_entornos (A : set X) : aislado A = {x ∈ A | ∃ E ∈ 𝓝 X x, E ∩ A = {x}} :=
begin
  unfold aislado,
  ext x,
  split,
  {
    intro h,
    cases h with hx hx2,
    cases hx2 with U hU,
    cases hU with hUab hUinter,
    split,
      exact hx,
    simp only [],
    use U,
    split,
    {
      use U,
      split,
        exact hUab,
      split,
      {
        have haux : x ∈ {x},
        {
          exact mem_singleton x,
        },
        rw ← hUinter at haux,
        exact haux.1,
      },
      tauto,
    },
    exact hUinter,
  },
  {
    intro h,
    cases h with hx hx2,
    cases hx2 with E hE,
    cases hE with hEent hEinter,
    cases hEent with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUE,
    split,
      exact hx,
    {
      simp only [],
      use U,
      split,
        exact hUab,
      {
        ext y,
        split,
        {
          intro hy,
          cases hy with hy hy2,
          rw ← hEinter,
          split,
          {
            apply hUE,
            exact hy,
          },
            exact hy2,
        },
        {
          intro h,
          simp only [set.mem_singleton_iff] at h,
          rw h,
          split,
            assumption,
            assumption,
        }
      }
    }
  }
end

lemma aislado_abierto_relativo (A : set X) (x : X) (hx : x ∈ aislado A) : abierto ( {x} ↓∩ A ) :=
begin
  cases hx with hxA hx2,
  cases hx2 with U hU,
  cases hU with hUab hUinter,
  use U,
  split,
    exact hUab,
  {
    simp only [restringe_igual],
    rw hUinter,
    ext y,
    simp only [iff_self_and, set.mem_singleton_iff, set.mem_inter_iff],
    intro hy,
    rw hy,
    exact hxA,
  }
end


/-
# Derivado
-/
def derivado (A : set X)  := {x : X | ∀ U, x ∈ U → abierto U → (U ∩ {x}ᶜ) ∩ A ≠ ∅ }

/-
## Propiedades 3.3.14
-/
lemma caracterizacion_derivado_entornos (A : set X) : derivado A  = {x : X | ∀ E ∈ 𝓝 X x, (E ∩ {x}ᶜ) ∩ A ≠ ∅ } :=
begin
  unfold derivado,
  ext x,
  split,
  {
    intro h,
    intros E hE,
    cases hE with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUE,
    specialize h U hxU hUab,
    simp only [disjuntos_sii_contenido_en_complemento,ne.def] at *,
    intro hn,
    apply h,
    intros y hy,
    apply hn,
    split,
    {
      apply hUE,
      exact hy.1,
    },
    {
      exact hy.2,
    },
  },
  {
    intro h,
    intros U hxU hUab,
    specialize h U _,
    {
      use U,
      simp only [true_and, hUab, hxU],
    },
    exact h,
  }
end

lemma clausura_aislado_union_derivado (A : set X) : clausura A = aislado A ∪ derivado A :=
begin
  ext x,
  rw clausura_caracterizacion,
  split,
  intro h,
   {
    by_cases hcas : x ∈ aislado A,
    {
      left,
      exact hcas,
    },
    right,
    unfold aislado at hcas,
    simp only [set.mem_sep_iff, not_and] at hcas,
    intros U hxU hUab,
    specialize h U hUab hxU,
    by_cases hxA : x ∈ A,
    {
      specialize hcas hxA,
      push_neg at hcas,
      specialize hcas U hUab,
      by_contradiction hneg,
      apply hcas,
      ext y,
      simp only [set.mem_singleton_iff, set.mem_inter_iff],
      split,
      {
        intro hy,
        cases hy with hyU hyA,
        rw  [conjunto_vacio_sii_todo_elemento_no] at hneg,
        specialize hneg y,
        simp only [and_imp, not_and, set.mem_singleton_iff, set.mem_compl_iff, set.mem_inter_iff] at hneg,
        specialize hneg hyU,
        by_contradiction hny,
        specialize hneg hny,
        exact hneg hyA,
      },
      {
        intro hy,
        rw [hy],
        tauto,
      },
    },
    {
      simp? [conjunto_vacio_sii_todo_elemento_no] at ⊢ h,
      cases h with y hy,
      cases hy with hyA hyU,
      use y,
      split,
        exact hyU,
      split,
        {
          by_contradiction hxy,
          rw hxy at hyA,
          exact hxA hyA,
        },
        exact hyA,
    },
   },
   {
    intro h,
    intros V hVab hxV,
    simp only [conjunto_vacio_sii_todo_elemento_no, ne.def, not_forall, mem_inter_iff, not_and, not_not_mem, exists_prop],
    cases h,
    {
      use x,
      cases h with hxa hU,
      tauto,
    },
    {
      specialize h V hxV hVab,
      simp only [conjunto_vacio_sii_todo_elemento_no, ne.def, not_forall] at h,
      cases h with y hy,
      simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, not_and, and_imp, not_forall, not_not_mem, exists_prop] at hy, 
      use y,
      tauto,
    },
   },
end

lemma derivado_aislado_disjuntos (A : set X) : derivado A ∩ aislado A = ∅ :=
begin
  rw conjunto_vacio_sii_todo_elemento_no,
  intro x,
  simp only [not_and, set.mem_inter_iff],
  intros hxder hxais,
  unfold derivado at hxder,
  unfold aislado at hxais,
  cases hxais with hxA hU,
  cases hU with U hU2,
  cases hU2 with hUab hUinter,
  specialize hxder U _ hUab,
  {
    calc 
      x   ∈ U ∩ A   : by {rw hUinter, simp only [set.mem_singleton],}
      ... ⊆  U      : by {simp only [set.inter_subset_left],}
  },
  apply hxder,
  calc
    U ∩ {x}ᶜ ∩ A = {x}ᶜ ∩ U ∩ A   : by {rw inter_comm {x}ᶜ U,} 
    ...          = {x}ᶜ ∩ (U ∩ A) : by {rw inter_assoc,}
    ...          = {x}ᶜ ∩ {x}     : by {rw hUinter,}
    ...          = ∅              : by {apply set.compl_inter_self,}
end

lemma total_union_aislado_derivado_exterior (A : set X) : aislado A ∪ derivado A ∪ exterior A = univ :=
begin
  rw ← clausura_aislado_union_derivado,
  rw exterior_complementario_clausura,
  simp only [set.union_compl_self, eq_self_iff_true],
end

lemma aislado_disjunto_exterior (A : set X) : aislado A ∩ exterior A = ∅ :=
begin
  rw exterior_complementario_clausura,
  rw clausura_aislado_union_derivado,
  simp only [complemento_union],
  rw ← inter_assoc,
  simp only [eq_self_iff_true, set.inter_compl_self, set.empty_inter],
end

lemma derivado_disjunto_exterior (A : set X) : derivado A ∩ exterior A = ∅ :=
begin
  rw exterior_complementario_clausura,
  rw clausura_aislado_union_derivado,
  rw inter_comm,
  simp only [complemento_union],
  rw inter_assoc,
  simp only [set.compl_inter_self, eq_self_iff_true, set.inter_empty],
end



end topologicos