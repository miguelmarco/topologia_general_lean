import .topologicos
import .conjuntos
import tactic

open topologicos
open set
open topologicos.espacio_topologico

variables {X Y Z : Type} [ espacio_topologico X] [espacio_topologico Y] [espacio_topologico Z]


def topologia_metrico_solucion {X : Type} [metricos.espacio_metrico X] : espacio_topologico X :=
{ abiertos := {U : set X | ∀ x ∈ U, metricos.entorno x U},
  abierto_total := 
  begin
    intros x h,
    use 1,
    simp only [set.subset_univ, gt_iff_lt, and_self, zero_lt_one],
  end,
  abierto_vacio := 
  begin
    intros x h,
    cases h,
  end,
  abierto_union := 
  begin
    intros F hF x hx,
    cases hx with U hU,
    cases hU with hUF hxU,
    specialize hF hUF x hxU,
    cases hF with r hr,
    cases hr with hrpos hrx,
    use r,
    split, assumption,
    intros y hy,
    use U,
    split, assumption,
    apply hrx hy,
  end,
  abierto_interseccion := 
  begin
    intros U V hU hV,
    intros x hx,
    cases hx with hxU hxV,
    specialize hU x hxU,
    specialize hV x hxV,
    cases hU with r1 hr1,
    cases hr1 with hr1pos hr1bola,
    cases hV with r2 hr2,
    cases hr2 with hr2pos hr2bola,
    use min r1 r2,
    split,
    {
      simp only [gt_iff_lt, lt_min_iff],
      split,
        linarith,
        linarith,
    },
    {
      intros y hy,
      simp only [metricos.bola_carac, lt_min_iff] at hy,
      cases hy with hy1 hy2,
      split,
      {
        apply hr1bola,
        exact hy1,
      },
      {
        apply hr2bola,
        exact hy2,
      }
    }
  end }

def discreta_solucion (X : Type) : espacio_topologico X :=
{ abiertos := univ,
  abierto_total := by triv,
  abierto_vacio := by triv,
  abierto_union := 
  begin
    intros,
    triv,
  end,
  abierto_interseccion := 
  begin
    intros,
    triv,
  end
}



def indiscreta_solucion (X : Type) : espacio_topologico X :=
{ abiertos := {∅ , univ },
  abierto_total := 
  begin
    right,
    simp only [mem_singleton],
  end,
  abierto_vacio := 
  begin
    left,
    refl,
  end,
  abierto_union := 
  begin
    intros F  h,
    by_cases hF : univ ∈ F,
    {
      right,
      simp only [mem_singleton_iff],
      ext,
      simp only [mem_sUnion, exists_prop, mem_univ, iff_true],
      use univ,
      tauto,
    },
    {
      left,
      ext,
      simp only [mem_sUnion, exists_prop, mem_empty_eq, iff_false, not_exists, not_and],
      intros U hU hx,
      specialize h hU,
      cases h,
      {
        rw h at hx,
        exact hx,
      },
      {
        simp only [set.mem_singleton_iff] at h,
        rw h at hU,
        apply hF hU,
      }
    }
  end,
  abierto_interseccion := 
  begin
    intros U V hU hV,
    cases hU,
    {
      left,
      rw hU,
      simp only [empty_inter],
    },
    {
      simp only [mem_singleton_iff] at hU,
      rw hU,
      simp only [univ_inter],
      exact hV,
    }
  end
}

def punto_incluido_solucion (X : Type) (x : X) : espacio_topologico X :=
{ abiertos := {U : set X | x ∈ U} ∪ {∅},
  abierto_total := 
  begin
    left,
    tauto,
  end,
  abierto_vacio := 
  begin
    right,
    tauto,
  end,
  abierto_union := 
  begin
    intros F hF,
    by_cases h : ⋃₀ F = ∅,
    {
      rw h,
      right,
      tauto,
    },
    {
      simp only [sUnion_eq_empty, not_forall, exists_prop] at h,
      cases h with U hU,
      cases hU with hUF hUn,
      specialize hF hUF,
      cases hF,
      {
        use U,
        split,
          exact hUF,
          exact hF,
      },
      {
        simp only [mem_singleton_iff] at hF,
        tauto,
      }
    }
  end,
  abierto_interseccion := 
  begin
    simp only [union_singleton, mem_insert_iff, mem_set_of_eq, mem_inter_eq],
    intros U V hU hV,
    cases hU,
    {
      rw hU,
      simp only [empty_inter, mem_empty_eq, false_and, or_false],
    },
    {
      cases hV,
      {
        rw hV,
        simp only [inter_empty, mem_empty_eq, and_false, or_false],
      },
      {
        right,
        split,
        {
          exact hU,
        },
        {
          exact hV,
        }
      },
    },
  end
}

def imagen_inversa_solucion (X Y : Type) [τY : espacio_topologico Y] (f : X → Y) : espacio_topologico X :=
{ abiertos := {(f ⁻¹' V) | V ∈ τY.abiertos},
  abierto_total := 
  begin
    use univ,
    simp only [preimage_univ, eq_self_iff_true, and_true],
    apply abierto_total,
  end,
  abierto_vacio := 
  begin
    use ∅,
    simp only [preimage_empty, eq_self_iff_true, and_true],
    apply abierto_vacio,
  end,
  abierto_union := 
  begin
    intros F hF,
    have h : ∀ U : ↥F, ∃ V : set Y, V ∈ τY.abiertos ∧ f ⁻¹' V = ↑U,
    {
      intro U,
      cases U with U hU,
      specialize hF hU,
      simp only [exists_prop, mem_set_of_eq] at hF,
      exact hF,
    },
    choose g hg using h,
    simp only [exists_prop, mem_set_of_eq],
    use ⋃₀ (range g),
    split,
    {
      apply abierto_union,
      intros V hV,
      cases hV with U hgU,
      rw ← hgU,
      specialize hg U,
      exact hg.1,
    },
    {
      ext x,
      simp only [hg, sUnion_range, Union_coe_set, preimage_Union, subtype.coe_mk, mem_Union, mem_sUnion],
    }
  end,
  abierto_interseccion := 
  begin
    intros U1 U2 hU1 hU2,
    cases hU1 with V1 hV1,
    cases hV1 with hV1ab hV1U1,
    cases hU2 with V2 hV2,
    cases hV2 with hV2ab hV2U2,
    use V1 ∩ V2,
    split,
    {
      apply abierto_interseccion,
        exact hV1ab,
        exact hV2ab,
    },
    {
      simp only [preimagen_interseccion, hV1U1, hV2U2],
    }
  end
}

def imagen_directa_solucion (X Y: Type) [τX :espacio_topologico X] (f : X → Y): espacio_topologico Y :=
{ abiertos := {V : set Y | f ⁻¹' V ∈ τX.abiertos},
  abierto_total := 
  begin
    apply abierto_total,
  end,
  abierto_vacio := 
  begin
    apply abierto_vacio,
  end,
  abierto_union := 
  begin
    intros F hF,
    dsimp,
    rw preimagen_union_familia',
    apply abierto_union,
    intros U hU,
    cases hU with V hV,
    cases hV with hVF hfVU,
    rw ← hfVU,
    apply hF,
    exact hVF,
  end,
  abierto_interseccion := 
  begin
    intros U V hU hV,
    simp only [mem_set_of_eq, preimage_inter] at *,
    apply abierto_interseccion,
    repeat {assumption},
  end
}

def cofinita_solucion (X : Type) : espacio_topologico X :=
{ abiertos := {U : set X | set.finite Uᶜ } ∪ {∅},
  abierto_total := 
  begin
    left,
    simp only [set.compl_univ, set.finite_empty, set.mem_set_of_eq],
  end,
  abierto_vacio := 
  begin
    right,
    tauto,
  end,
  abierto_union := 
  begin
    intros F hF,
    by_cases h : F ⊆ {∅ },
    {
      right,
      dsimp,
      rw sUnion_eq_empty,
      intros U hU,
      apply h,
      exact hU,
    },
    {
      simp only [set.subset_singleton_iff, not_forall] at h,
      cases h with U hU,
      cases hU with hU hU1,
      left,
      refine finite.subset _ _,
      {
        use Uᶜ,
      },
      {
        specialize hF hU,
        cases hF,
        {
          exact hF,
        },
        {
          specialize hU1 hF,
          tauto,
        },
      },
      {
        simp only [set.compl_subset_compl],
        exact subset_sUnion_of_mem hU,
      }
    }
  end,
  abierto_interseccion := 
  begin
    intros U V hU hV,
    cases hU,
    {
      cases hV,
      {
        left,
        dsimp at *,
        rw compl_inter,
        rw finite_union,
        tauto,
      },
      {
        right,
        simp at *,
        rw hV,
        simp,
      }
    },
    {
      right,
      simp at *,
      rw hU,
      simp,
    }
end }

def conumerable_solucion (X : Type) : espacio_topologico X :=
{ abiertos := {U : set X | set.countable Uᶜ } ∪ {∅},
  abierto_total :=
  begin
    simp only [union_singleton, mem_insert_iff, mem_set_of_eq, compl_univ, countable_empty, or_true],
  end,
  abierto_vacio := 
  begin
    simp only [union_singleton, mem_insert_iff, eq_self_iff_true, true_or],
  end,
  abierto_union := 
  begin
    intros F hF,
    by_cases h : ⋃₀ F = ∅,
    {
      rw h,
      right,
      simp only [mem_singleton],
    },
    {
      left,
      simp only [sUnion_eq_empty, not_forall, exists_prop] at h,
      cases h with U hU,
      cases hU with hUF hUn,
      have hFU := hF hUF,
      cases hFU,
      {
        simp only [mem_set_of_eq] at ⊢ hFU,
        apply countable.mono _ hFU,
        simp only [compl_subset_compl],
        intros x hx,
        use U,
        split,
        exact hUF,
        exact hx,
      },
      {
        by_contra,
        apply hUn,
        exact hFU,
      },
    },
  end,
  abierto_interseccion := 
  begin
    intros U V hU hV,
    cases hU,
    {
      cases hV,
      {
        left,
        simp at *,
        tauto,
      },
      {
        right,
        simp at *,  
        rw hV,
        simp,
      }
    },
    {
      right,
      simp at *,
      rw hU,
      simp,
    }
  end
}

--Ejercicio 2.1.5(a)
example (X Y : Type) [espacio_topologico X] (f : X → Y) : @continua _ _ _ (indiscreta Y) f:=
begin
  intros U hU,
  cases hU,
  {
    rw hU,
    apply abierto_vacio,
  },
  {
    simp only [set.mem_singleton_iff] at hU,
    rw hU,
    exact abierto_total,
  }
end


lemma identidad_continua_solucion : continua (identidad : X → X) :=
begin
  intro U,
  simp only [identidad_preimagen, imp_self],
end