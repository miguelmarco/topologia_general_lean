import .conjuntos
import .topologicos
import tactic

open set
open topologicos
open topologicos.espacio_topologico

variables {X : Type} [espacio_topologico X]

def base (B : set (set X)) := B ⊆ abiertos ∧ ∀ (U : set X), abierto U →  ∀ x ∈ U , ∃ V ∈ B, x ∈ V ∧ V ⊆ U 


lemma caracterizacion_base (B : set (set X)) : base B ↔ B ⊆ abiertos ∧ ∀ U : set X, abierto U → ∃ F ⊆ B, ⋃₀ F = U :=
begin
  split,
  {
    intro h,
    cases h with hBabiertos hBcubre,
    split,
    {
      exact hBabiertos,
    },
    {
      intros U hU,
      specialize hBcubre U hU,
      let F := {V : set X | V ∈ B ∧ V ⊆ U},
      use F,
      split,
      {
        intros V hV,
        cases hV with hVB hVU,
        exact hVB,
      },
      ext,
      split,
      {
        intro h,
        cases h with V hV,
        cases hV with hVF hxV,
        cases hVF with hVB hVU,
        apply hVU,
        apply hxV,
      },
      {
        intro hx,
        specialize hBcubre x hx,
        rcases hBcubre with ⟨V,hVB,hxV,hVU⟩ ,
        use V,

        split,
        {
          split,
          {
            exact hVB,
          },
          {
            exact hVU,
          },
        },
        {
          exact hxV,
        },
      },
      
    },
  },
  {
    intro h,
    cases h with hBab hB,
    split,
    {
      exact hBab,
    },
    {
      intros U hUab x hxU,
      specialize hB U hUab,
      cases hB with F hF,
      cases hF with hFB hFU,
      rw ← hFU at hxU,
      cases hxU with V hV,
      use V,
      cases hV with hVF hxV,
      split,
      {
        apply hFB,
        exact hVF,
      },
      split,
      {
        exact hxV,
      },
      {
        rw ← hFU,
        intros y hy,
        use V,
        split,
        assumption,
        assumption,
      }
    }
  }
end

def B1 {X : Type} (F : set (set X)) := ⋃₀ F = univ 
def B2 {X : Type} (F : set (set X)) := ∀ (A B : set X), A ∈ F → B ∈ F → ∃ S : set (set X), S ⊆ F ∧ ⋃₀ S = A ∩ B 

lemma propiedades_base {X : Type} [espacio_topologico X] (B : set (set X))  (h : base B) : B1 B ∧ B2 B :=
begin
  split,
  {
    unfold B1,
    unfold base at h,
    cases h with hBab hBbase,
    specialize hBbase univ,
    specialize hBbase abierto_total,
    apply doble_contenido,
    {
      simp only [subset_univ],
    },
    {
      intros x hx,
      specialize hBbase x hx,
      cases hBbase  with V hV,
      use V,
      cases hV with hVB hxV,
      simp only [mem_univ, subset_univ, and_true] at *,
      tauto,
    },
  },
  {
    intros a b ha hb,
    cases h with hBab hB,
    specialize hB (a ∩ b),
    have hain : abierto (a ∩ b),
    {
      apply abierto_interseccion_2,
      {
        apply hBab,
        exact ha,
      },
      {
        apply hBab,
        exact hb,
      },
    },
    specialize hB hain,
    use {C ∈  B | C ⊆ a ∩ b},
    split,
    {
      intros C hC,
      cases hC with hCB hC2,
      exact hCB,
    },
    apply doble_contenido,
    {
      intros x hx,
      cases hx with V hV,
      cases hV with hVp hxV,
      cases hVp with hVinC hCcontab,
      apply hCcontab,
      apply hxV,
    },
    {
      intros x hx,
      specialize hB x hx,
      cases hB with V hV,
      use V,
      split,
      split,
      {
        cases hV with hVB,
        exact hVB,
      },
      {
        cases hV,
        exact hV_h.2,
      },
      {
        cases hV,
        exact hV_h.1,
      }
    }
  },
end


def intersecciones_finitas {X : Type} (F : set (set X)) : (set (set X)) :=
{U : set X | ∃ (S : set (set X)), set.finite S ∧ S ⊆ F ∧ ⋂₀ S = U }

def abiertos_generados {X : Type} ( F : set (set X)) := {U : set X | ∃ FU : set (set X), FU ⊆ intersecciones_finitas F ∧ ⋃₀ FU = U}

inductive generados {X : Type} (F : set (set X)) : set X → Prop 
| elemento  (U : set X) (h : U ∈ F) :  generados  U
| interseccion_finita (S : set (set X)) (hS : ∀ U ∈ S,  generados U) (hF : set.finite S): generados ⋂₀ S
| union_familia (S : set (set X)) (hS : ∀ U ∈ S, generados U ) : generados ⋃₀ S


lemma generados_eq_abiertos_generados {X : Type} (F : set (set X)) : abiertos_generados F = generados F :=
begin
  ext U,
  split,
  {
    intro h,
    cases h with S hS,
    cases hS with hSinf hSU,
    rw ← hSU,
    apply generados.union_familia,
    intros V hV,
    specialize hSinf hV,
    cases hSinf with B hB,
    cases hB with hBfin hBV,
    cases hBV with hBV hBin,
    rw ← hBin,
    apply generados.interseccion_finita,
    {
      intros U hU,
      apply generados.elemento,
      apply hBV,
      exact hU,
    },
    {
      exact hBfin,
    },
  },
  {
    intro h,
    induction h with S hS1  S hS1 hS2 hS3 S hS4 hS5 hS6,
     {
      use {S},
      simp only [and_true, eq_self_iff_true, set.singleton_subset_iff, set.sUnion_singleton],
      use {S},
      simp only [true_and,  set.sInter_singleton,  and_true,  eq_self_iff_true,  set.finite_singleton, set.singleton_subset_iff, hS1],
     },
     {
      revert hS1 hS3,
      apply set.finite.induction_on hS2,
      {
        intros,
        simp only [set.sInter_empty],
        use {univ},
        simp only [and_true, eq_self_iff_true, set.singleton_subset_iff, set.sUnion_singleton],
        use ∅,
        simp only [set.empty_subset, set.sInter_empty, eq_self_iff_true, set.finite_empty, and_self],
      },
      {
        intros a s has hsfin h1 h2 h3,
        simp only [mem_insert_iff, forall_eq_or_imp] at h2,
        cases h2 with h2a h2s,
        specialize h1 h2s,
        simp only [mem_insert_iff, forall_eq_or_imp] at h3,
        cases h3 with h3a h3s,
        specialize h1 h3s,
        cases h1 with Fs hFs,
        cases hFs with hFsfin hFsinter,
        cases h3a with Fa hFa,
        cases hFa with hFafin hFainter,
        use {V : set X | ∃ W1 ∈ Fa, ∃ W2 ∈ Fs, V = W1 ∩ W2},
        split,
        {
          intros V hV,
          rcases hV with ⟨ W1,⟨hW1, ⟨  W2,⟨ hW2 ,hV⟩ ⟩ ⟩ ⟩,
          specialize hFafin hW1,
          specialize hFsfin hW2,
          rcases hFafin with ⟨ R1 ,⟨ hR1fin,⟨ hR1F,hR1W1⟩ ⟩⟩ ,
          rcases hFsfin with ⟨ R2 ,⟨ hR2fin,⟨ hR2F,hR2W2⟩ ⟩⟩ ,
          use R1 ∪ R2,
          split,
          {
            rw finite_union,
            exact ⟨ hR1fin,hR2fin⟩,
          },
          split,
          {
            exact union_subset hR1F hR2F,
          },
          {
            rw hV,
            rw sInter_union,
            rw hR1W1,
            rw hR2W2,
          },
        },
        {
          ext x,
          split,
          {
            intro hx,
            cases hx with V hV,
            cases hV with hV hxV,
            rcases hV with ⟨ W1,⟨hW1,⟨W2,⟨hW2,hV⟩⟩⟩⟩,
            simp only [sInter_insert, mem_inter_iff, mem_sInter],
            split,
            {
              rw ← hFainter,
              use W1,
              split,
              {
                exact hW1,
              } ,
              {
                rw hV at hxV,
                exact hxV.1,
              },
            },
            {

              intros t ht,
              rw hV at hxV,
              have haux : x ∈ ⋃₀ Fs,
              {
                use W2,
                exact ⟨ hW2,hxV.2⟩,
              },
              rw hFsinter at haux,
              exact haux t ht,
            },
          },
          {
            intro hx,
            simp only [sInter_insert, mem_sInter] at hx,
            cases hx with hxa hxs,
            rw  ← hFainter at hxa,
            rw  ← hFsinter at hxs,
            rcases hxa with ⟨W1,⟨hW1,hW1x⟩ ⟩ ,
            rcases hxs with ⟨W2,⟨hW2,hW2x⟩ ⟩ ,
            use W1 ∩ W2,
            split,
            {
              use W1,
              split, exact hW1,
              use W2,
              split, exact hW2,
              refl,
            },
            exact ⟨hW1x,hW2x⟩,
          },
        }
      }
     },
     {
      unfold abiertos_generados at *,
      have hS5' : ∀ (U : S), ∃ (FU : set (set X)), FU ⊆ intersecciones_finitas F ∧ ⋃₀ FU = ↑U,
      {
        rintro ⟨U,hU⟩,
        specialize hS5 U hU,
        exact hS5,
      },
      choose g Fu hFU using hS5',
      use ⋃₀ (range g),
      split,
      {
        intros V hV,
        cases hV with W hW,
        cases hW with hW hVW,
        cases hW with Z hZ,
        specialize Fu Z,
        apply Fu,
        rw hZ,
        exact hVW,
      },
      {
        ext x,
        split,
        {
          intro hx,
          cases hx with V hV,
          cases hV with hV hxV,
          cases hV with W hW,
          cases hW with hW hVW,
          cases hW with Z hZ,
          specialize hFU Z,
          rw hZ at hFU,
          use ⋃₀ W,
          split,
          {
            rw hFU,
            exact Z.2,
          },
          {
            use V,
            exact ⟨ hVW,hxV⟩,
          },
        },
        {
          intro hx,
          cases hx with V hV,
          cases hV with hVS hxV,
          have hFU2 := hFU ⟨ V,hVS⟩,
          dsimp  at hFU2,
          rw ← hFU2 at hxV,
          cases hxV with W hW,
          cases hW with hWgV hxW,
          use W,
          split,
          {
            use g ⟨V,hVS⟩,
            simp only [mem_range_self, true_and,hWgV],
          },
          {
            exact hxW,
          }
        },
      }
     },
      


    /- apply generados.rec,
    {
      intros U hU,
      use {U},
      simp only [intersecciones_finitas, singleton_subset_iff, mem_set_of_eq, sUnion_singleton, eq_self_iff_true, and_true],
      use {U},
      simp only [finite_singleton, singleton_subset_iff, sInter_singleton, eq_self_iff_true, and_true, true_and],
      exact hU,
    },
    {
      intros S hS hSfin,
      revert hS,
      apply set.finite.induction_on hSfin,
      {
        simp only [mem_empty_iff_false, forall_const, sInter_empty],
        use { univ},
        simp only [singleton_subset_iff, sUnion_singleton, eq_self_iff_true, and_true],
        use ∅,
        simp only [finite_empty, empty_subset, sInter_empty, eq_self_iff_true, and_self],
      },
      {
        intros U s hUnS hsfin h1 h2 h3,
        unfold abiertos_generados at *,
        simp only [sInter_insert, mem_insert_iff, forall_eq_or_imp] at *,
        specialize h1 h2.2 h3.2,
        cases h1 with FU hFU,
        cases hFU with hFU1 hFU2,
        cases h3.1 with A hA,
        let mF := {V : set X | ∃ V1 ∈ FU, ∃ V2 ∈ A, V = V1 ∩ V2},
        use mF,
        split,
        {
          intros V hV,
          cases hV with V1 hV1,
          cases hV1 with hV1 hV,
          cases hV with V2 hV2,
          cases hV2 with hV2 hV,
          cases hA with hA1 hA2,
          specialize hA1 hV2,
          cases hA1 with FA2 hFA2,
          specialize hFU1 hV1,
          cases hFU1 with FA1 hFA1,
          use FA1 ∪ FA2,
          split,
          {
            rw finite_union,
            tidy,
          },
          split,
          {
            apply union_subset hFA1.2.1 hFA2.2.1,
          },
          {
            rw sInter_union,
            rw hV,
            rw hFA1.2.2,
            rw hFA2.2.2,
          },
        },
        {
          ext x,
          split,
          {
            intro hx,
            cases hx with V hV,
            cases hV with hVV hVV2,
            r,cases hVV with ⟨V1,⟨hV1,⟨V2,⟨hV2,hV⟩⟩⟩⟩,
            rw hV at hVV2,
            cases hVV2 with hxV2 hxV2,
            split,
            {
              rw ← hA.2,
              use V2, finish, 
            },
            {
              rw ← hFU2,
              use V1, finish,
            },
          },
          {
            intro hx,
            cases hx with hx1 hx2,
            cases hA with hA1 hA2,
            rw ← hFU2 at hx2,
            rw ← hA2 at hx1,
            cases hx1 with x1 hx1,
            cases hx1 with hx1 hx1F,
            cases hx2 with x2 hx2,
            cases hx2 with hx2 hx2F,
            use x1 ∩ x2,
            split,
            {
              use x2,
              split,
              use hx2,
              use x1,
              split,
              use hx1,
              rw inter_comm,
            },
            {
              tidy,
            },
          },
        }
      }
    },
    {
      intros S hSgen hSgenab,
      unfold abiertos_generados at *,
      let g := {V ∈ intersecciones_finitas F | ∃ W ∈ S, V ⊆ W },
      use g,
      split,
      {
        intros x hx,
        cases hx with hx1 hx2,
        exact hx1,
      },
      {
        ext x,
        split,
        {
          intro hx,
          cases hx with V hV,
          cases hV with hV hxV,
          cases hV with hVF hW,
          cases hW with W hW,
          use W,
          cases hW,
          split, assumption,
          apply hW_h, assumption,

        },
        {
          intro hx,
          cases hx with V hV,
          cases hV with hVS hxV,
          specialize hSgenab V hVS,
          cases hSgenab with FU hFU,
          cases hFU with hFUin hFUV,
          rw ←  hFUV at hxV,
          cases hxV with W hW,
          cases hW with hWFU hxFU,
          use W,
          split,
          {
            split,
            {
              apply hFUin,
              exact hWFU,
            },
            {
              use V,
              split, exact hVS,
              rw ← hFUV,
              intros x hx,
              use W,
              split,
              assumption, assumption,
            },
          },
          exact hxFU,
        },
      },
    },
    exact h, -/
  }
end



instance topologia_generada {X : Type} (F : set (set X)) (h1 : B1 F) (h2 : B2 F) : espacio_topologico X :=
{ abiertos := abiertos_generados F,
  abierto_total := begin
    use F,
    split,
    {
      intros U hU,
      use {U},
      simp only [hU, set.sInter_singleton, eq_self_iff_true, set.finite_singleton, and_self, set.singleton_subset_iff],
    },
    exact h1,
  end,
  abierto_vacio := begin
    use ∅,
    simp only [set.empty_subset, set.sUnion_empty, eq_self_iff_true, and_self],
  end,
  abierto_union := begin
    intros F1 hF1,
    unfold abiertos_generados at hF1,
    choose g hg using hF1,
    let f : ↥F1 → set (set X),
    {
      intro U,
      apply g,
      apply U.2,
    },
    have hf : ∀ x : ↥F1, f x ⊆ intersecciones_finitas F ∧ ⋃₀ f x  = x,
    {
      intro x,
      apply hg,
    },
    let UF1 := ⋃₀ (range f),
    use UF1,
    split,
    {
      intros U hU,
      cases hU with V hV,
      cases hV with hfV hV,
      cases hfV with A hA,
      specialize hf A,
      cases hf with hf1 hf2,
      apply hf1,
      rw   hA,
      exact hV,
    },
    {
      ext x,
      split,
      {
        intro hx,
        cases hx with hU hU,
        cases hU with hfU hxU,
        cases hfU with V hV,
        cases hV with hfV hUV,
        cases hfV with B hB,
        specialize hf B,
        cases hf with hf1 hf2,
        rw hB at hf2,
        use B,
        split, apply B.2,
        rw ← hf2,
        use hU,
        split,
        assumption,
        assumption,
      },
      {
        intro hx,
        cases hx with U hU,
        cases hU with hU hxU,
        have hfU := hf ⟨U,hU⟩,
        cases hfU with elim hfU,
        clear elim,
        have hxUU : x ∈ ⋃₀ (f ⟨U,hU⟩),
        {
          rw hfU,
          exact hxU,
        },
        cases hxUU with V hV,
        cases hV with hV hxV,
        use V,
        split,
        {
          use f ⟨ U,hU⟩,
          simp only [set.mem_range_self, and_self, hV],
        },
        {
          exact hxV,
        }
      }
    }
  end,
  abierto_interseccion := begin
    intros S hS hSfin,
    revert hS,
    revert hSfin,
    revert S,
    have puniv : univ ∈ abiertos_generados F,
    {
      use F,
      split,
      {
        intros U hU,
        use {U},
       simp only [hU,  set.sInter_singleton, eq_self_iff_true, set.finite_singleton, and_self, set.singleton_subset_iff],  
      },
      exact h1,
    },
    have pif := propiedad_interseccion_finita ( X) (abiertos_generados F) puniv, 
    cases pif with pif1 pif2,
    apply pif1,
    clear pif2 pif1,
    intros U V hU hV,
    cases hU with fU hfU,
    cases hV with fV hfV,
    use { A : set X | ∃ u ∈ fU, ∃ v ∈ fV, A = u ∩ v},
    split,
    {
      intros A hA,
      rcases hA with ⟨u,hU,v,hV,hA⟩,
      have hfU1 := hfU.1 hU,
      have hfV1 := hfV.1 hV,
      rw hA,
      cases hfU1 with AU hAU,
      cases hfV1 with AV hAV,
      use AU ∪ AV,
      split,
      {
        rw finite_union,
        split,
          exact hAU.1,
          exact hAV.1,
      },
      {
        split,
        {
          apply union_subset,
            exact hAU.2.1,
            exact hAV.2.1,
        },
        {
          rw ← hAU.2.2,
          rw ← hAV.2.2,
          ext,
          split,
          {
            intro hx,
            split,
            {
              intros B hB,
              apply hx,
              left,
              exact hB,
            },
            {
              intros B hB,
              apply hx,
              right,
              exact hB,
            },
          },
          {
            intro hx,
            cases hx with hx1 hx2,
            intros B hB,
            cases hB,
            {
              apply hx1,
              exact hB,
            },
            {
              apply hx2,
              exact hB,
            },
          },
        },
      },
    },
    {
      ext,
      split,
      {
        intro hx,
        rcases hx with ⟨ A,⟨u,hu,v,hv,hA⟩ ,hxA⟩ ,
        rw ← hfU.2,
        rw ← hfV.2,
        rw hA at hxA,
        cases hxA with hxu hxv,
        split,
        {
          use u,
          tauto,
        },
        {
          use v,
          tauto,
        },
      },
      {
        intro hx,
        cases hx with hxU hxV,
        rw ← hfU.2 at hxU,
        rw ← hfV.2 at hxV,
        rcases hxU with ⟨ u, hu,hxu⟩,
        rcases hxV with ⟨v,hv,hxv⟩,
        use u ∩ v,
        split,
        {
          use u,
          use hu,
          use v,
          use hv,
        },
        split,
        assumption, assumption,
      },
    },
  end }