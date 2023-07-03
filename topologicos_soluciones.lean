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
    intros F hF hFin x hx,
    revert hF,
    revert hx,
    apply set.finite.induction_on hFin,
    {
      simp only [sInter_empty, mem_univ, empty_subset, forall_true_left],
      use 1,
      simp only [gt_iff_lt, zero_lt_one, subset_univ, and_self],
    },
    {
      intros V C hV hCf hCen hxv hind,
      simp only [set.sInter_insert],
      have hVen : metricos.entorno x V,
      {
        apply hind, simp only [set.mem_insert_iff, true_or, eq_self_iff_true],
        simp only [set.sInter_insert, set.mem_sInter, set.mem_inter_iff] at hxv,
        tauto,
      },
      have hInen : metricos.entorno x ⋂₀ C,
      {
        simp only [set.sInter_insert, set.mem_inter_iff] at hxv,
        specialize hCen hxv.2,
        apply hCen,
        intros A hA,
        apply hind,
        right,assumption,
      },
      cases hVen with r1 hr1,
      cases hr1 with hr1pos hr1,
      cases hInen with r2 hr2,
      cases hr2 with hr2pos hr2,
      use min r1 r2,
      split,
      {
        simp only [gt_iff_lt, lt_min_iff], tauto,
      },
      {
        simp only [set.subset_inter_iff],
        split,
        {
          intros y hy,
          apply hr1,
          simp only [set.sInter_insert,
 set.mem_sInter,
 gt_iff_lt,
 set.subset_sInter_iff,
 set.mem_set_of_eq,
 set.mem_inter_iff,
 metricos.bola.equations._eqn_1] at *,
          simp only [lt_min_iff] at hy,
          linarith,
        },
        {
          intros z hz,
          apply hr2,
          unfold metricos.bola at *,
          simp only [mem_set_of_eq, mem_sInter, sInter_insert, mem_inter_eq, gt_iff_lt, subset_sInter_iff, lt_min_iff] at *,
          exact hz.2,
        },
      },

    },
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
    intros F hF hFfin,
    by_cases hem: ∅ ∈ F,
    {
      left,
      rw sInter_eq_empty_iff,
      intro x,
      use ∅,
      tauto,
    },
    {
      right,
      rw mem_singleton_iff,
      ext,
      simp only [mem_sInter, mem_univ, iff_true],
      intros S hS,
      specialize hF hS,
      simp only [set.mem_insert_iff, set.mem_singleton_iff] at hF,
      cases hF,
      {
        rw hF at hS,
        by_contradiction,
        apply hem hS,
      },
      {
        rw hF,
        triv,
      }
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
    intros F hF hFfin,
    simp only [union_singleton, mem_insert_iff, mem_set_of_eq, mem_sInter],
    by_cases h : ⋂₀ F = ∅,
    {
      left,
      exact h,
    },
    {
      right,
      intros U hU,
      specialize hF hU,
      cases hF,
      {
        exact hF,
      },
      {
        by_contradiction hx,
        apply h,
        ext y,
        simp only [mem_sInter, mem_empty_eq, iff_false, not_forall, exists_prop],
        use U,
        split,
        exact hU,
        simp only [mem_singleton_iff] at hF,
        rw hF,
        tauto,
      }
    }
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
    intros F hF hFfin,
    choose g hg using hF, -- elegimos un conmjunto de Y para cada elemento de F
    use ⋂₀ {V : set Y | ∃ (U : set X) (hU : U ∈ F), V = g hU},
    split,
    {
      apply abierto_interseccion,
      {
        intros V hV,
        cases hV with U hU,
        cases hU with hUF hUV,
        rw hUV,
        specialize hg  hUF,
        cases hg with hgUab hgfU,
        exact hgUab,
      },
      {
        apply finite.dependent_image,
        exact hFfin,
      }
    },
    {
      ext x,
      split,
      {
        intro h,
        intros U hU,
        specialize h (g hU),
        specialize hg hU,
        cases hg with hgab hgfU,
        rw ← hgfU,
        apply h,
        use U,
        use hU,
      },
      {
        intro hx,
        intros V hV,
        cases hV with U hU,
        cases hU with hUF hUV,
        specialize hx U hUF,
        rw  hUV,
        specialize hg hUF,
        cases hg with hgUab hfgU,
        rw ← hfgU at hx,
        exact hx,
      },
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
    intros F hF hFfin,
    dsimp,
    rw preimagen_interseccion_familia',
    apply abierto_interseccion,
    {
      intros U hU,
      cases hU with V hV,
      cases hV with hVf hfVU,
      rw ← hfVU,
      apply hF,
      exact hVf,
    },
    {
      have haux0 := finite.image (preimage f) hFfin,
      simp only [preimage, image] at haux0,
      simp only [exists_prop],
      exact haux0,
    }
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
    intros F hF hFfin,
    revert hF,
    apply finite.induction_on hFfin,
    {
      simp only [union_singleton, empty_subset, sInter_empty, mem_insert_iff, mem_set_of_eq, compl_univ, finite_empty, or_true,
  forall_true_left],
    },
    {
      intros U S hUs hSfin hS hin,
      specialize hS _,
      {
        refine subset_trans _ hin,
        apply subset_insert,
      },
      dsimp at *,
      by_cases hUcompl : U = ∅,
      {
        right,
        rw hUcompl,
        simp only [set.sInter_insert, eq_self_iff_true, set.empty_inter],
      },
      cases hS,
      {
        left,
        refine finite.subset _ _,  exact Uᶜ ∪ (⋂₀ S)ᶜ,
        {
          rw finite_union,
          split,
          {
            specialize hin _, exact U,
            {
              apply mem_insert,
            },
            cases hin,
            {
              exact hin,
            },
            tauto,
          },
          exact hS,
        },
        simp only [set.sInter_insert, compl_inter],
      },
      right,
      simp only [hS, sInter_insert, inter_empty],
    },
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
    intros F hF hFfin,
    simp only [union_singleton, mem_insert_iff, mem_set_of_eq],
    by_cases hcases: ⋂₀ F = ∅,
    {
      left,
      exact hcases,
    },
    {
      right,
      simp [sInter_eq_compl_sUnion_compl],
      apply countable.bUnion,
      {
        exact finite.countable hFfin,
      },
      { 
        intros a ha,
        specialize hF ha,
        cases hF,
        {
          exact hF,
        },
        {
          simp only [mem_singleton_iff] at hF,
          by_contradiction,
          apply hcases,
          ext x,
          simp only [mem_sInter, mem_empty_eq, iff_false, not_forall, exists_prop],
          use a,
          split,
          {
            exact ha,
          },
          {
            rw hF,
            tauto,
          }
        },
      },
    },
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