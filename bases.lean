import .conjuntos
import .topologicos
import tactic

open set
open topologicos
open topologicos.espacio_topologico


/-
En esta sección, `X` va a ser un espacio topológico
-/
variables {X : Type} [espacio_topologico X]

/-
Definimos base como una familia de abiertos que genera toda la topología mediante uniones
-/
def base (B : set (set X)) := 
B ⊆ abiertos ∧ 
∀ (U : set X), abierto U →  ∀ x ∈ U , ∃ V ∈ B, x ∈ V ∧ V ⊆ U 



lemma caracterizacion_base (B : set (set X)) : 
base B ↔ B ⊆ abiertos ∧ ∀ U : set X, abierto U → ∃ F ⊆ B, ⋃₀ F = U :=
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
        exact hVF,
        exact hy,
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

lemma interseccion_intersecciones_finitas {X : Type} (F : set (set X)) (A B : set X) (ha : A ∈ intersecciones_finitas F) (hb : B ∈ intersecciones_finitas F) :
A ∩ B ∈ intersecciones_finitas F :=
begin
  cases ha with Fa hFa,
  cases hb with Fb hFb,
  use Fa ∪ Fb,
  {
    split,
    {
      simp only [finite_union],
      exact ⟨ hFa.1,hFb.1⟩,
    },
    split,
    {
      simp only [union_subset_iff],
      exact ⟨ hFa.2.1,hFb.2.1⟩,
    },
    {
      rw ← hFa.2.2,
      rw ← hFb.2.2,
      rw sInter_union,
    },
  },
end

def abiertos_generados {X : Type} ( F : set (set X)) := {U : set X | ∃ FU : set (set X), FU ⊆ intersecciones_finitas F ∧ ⋃₀ FU = U}



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
    use {U ∈ intersecciones_finitas F | U ⊆ ⋃₀ F1},
    split,
    {
      simp only [sep_subset],
    },
    {
      ext x,
      split,
      {
        intro hx,
        rcases hx with ⟨ U,⟨ ⟨ hUint, hUF⟩ ,hxu⟩⟩ ,
        apply hUF hxu,
      },
      {
        intro hx,
        rcases hx with ⟨ U ,⟨ hUF1,hxU⟩ ⟩ ,
        specialize hF1 hUF1,
        rcases hF1 with ⟨FU ,⟨ hFUinf,hFU⟩ ⟩ ,
        rw ← hFU at hxU,
        rcases hxU with ⟨ V, ⟨ hVF1,hxV⟩⟩ ,
        use V,
        split,
        {
          split,
          {
            exact hFUinf hVF1,
          },
          {
            dsimp,
            intros y hyV,
            use U,
            split,
            {
              exact hUF1,
            },
            {
              rw ← hFU,
              use V,
              exact ⟨ hVF1,hyV⟩,
            },
          },
        },
        {
          exact hxV,
        },
      },
    },
  end,
  abierto_interseccion := begin
    intros S hS hSfin,
    revert hS,
    apply set.finite.induction_on hSfin,
    {
      simp only [empty_subset, sInter_empty, forall_true_left],
      use {univ},
      simp only [singleton_subset_iff, sUnion_singleton, eq_self_iff_true, and_true],
      use ∅ ,
      simp only [finite_empty, empty_subset, sInter_empty, eq_self_iff_true, and_self],
    },
    {
      intros a s hnins hsfin hinds h,
      have hagen : a ∈ abiertos_generados F,
      {
        apply h,
        left,
        refl,
      },
      have hsgen : s ⊆ abiertos_generados F,
      {
        intros x hx,
        apply h,
        right,
        exact hx,
      },
      specialize hinds hsgen,
      rcases hagen with ⟨ Fa ,⟨ hFafin, hFa⟩ ⟩ ,
      rcases hinds with ⟨ fS, ⟨ hFsfin, hFs⟩⟩,
      use {U ∈ intersecciones_finitas F | U ⊆ a ∩ (⋂₀ s)},
      split,
      {
        rintros U ⟨hU,hU2⟩ ,
        exact hU,
      },
      {
        ext x,
        split,
        {
          intro hx,
          rcases hx with ⟨ U ,⟨ hUF,hUas⟩ ,hxU⟩,
          simp only [sInter_insert],
          exact hUas hxU,
        },
        {
          intro hx,
          simp only [sInter_insert] at hx,
          cases hx with hxa hxs,
          induction hFa,
          induction hFs,
          rcases hxa with ⟨ Ua , ⟨ hUaF, hxUa⟩⟩ ,
          rcases hxs with ⟨ Us , ⟨ hUsF, hxUs⟩⟩ ,
          use Ua ∩ Us,
          split,
          {
            split,
            {
              specialize hFafin hUaF,
              specialize hFsfin hUsF,
              apply interseccion_intersecciones_finitas ,
              exact hFafin,
              exact hFsfin,
            },
            {
              simp only [subset_inter_iff],
              split,
              {
                intros x hx,
                use Ua,
                exact ⟨hUaF,hx.1 ⟩,
              },
              {
                intros x hx,
                use Us,
                exact ⟨hUsF,hx.2⟩,
              },
            },
          },
          {
            exact ⟨hxUa,hxUs⟩,
          },
        },
      },
    },
  end }