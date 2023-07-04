import .conjuntos
import .topologicos
import tactic


namespace topologicos

open topologicos.espacio_topologico
open set

/-
En esta sección, `X` va a ser un espacio topológico
-/
variables {X : Type} [espacio_topologico X]

/-
Definimos base como una familia de abiertos que genera toda la topología mediante uniones
-/
def base (ℬ : set (set X)) := 
ℬ ⊆ abiertos ∧ 
∀ (U : set X), abierto U →  ∃ F ⊆ ℬ, U = ⋃₀ F 

lemma base_discreto : @base X (discreta X) { ({x}) | x : X} :=
begin
  sorry,
end




lemma caracterizacion_base (ℬ : set (set X)) (hB :ℬ ⊆ abiertos) : 
base ℬ ↔  ∀ (U : set X), abierto U → ∀ x ∈ U, ∃ Bₓ ∈ ℬ, x ∈ Bₓ ∧ Bₓ ⊆ U :=
begin
  split,
  {
    intros hBbase U hU x hx,
    cases hBbase with hBab hBF,
    specialize hBF U hU,
    cases hBF with ℱ hℱ,
    cases hℱ with hℱℬ hUℱ,
    rw  hUℱ at hx,
    cases hx with Bₓ hBₓ,
    cases hBₓ with hBₓℱ hxBₓ,
    use Bₓ,
    split,
    {
      apply hℱℬ,
      exact hBₓℱ,
    },
    split,
    {
      exact hxBₓ,
    },
    {
      rw hUℱ,
      intros y hy,
      use Bₓ,
      split,
        exact hBₓℱ,
        exact hy,
    }
  },
  {
    intro h,
    split,
    {
      exact hB,
    },
    {
      intros U hU,
      specialize h U hU,
      use { B ∈ ℬ | B ⊆ U },
      split,
      {
        simp only [set.sep_subset],
      },
      {
        ext x,
        split,
        {
          intro hxU,
          specialize h x hxU,
          cases h with Bₓ hBₓ,
          cases hBₓ with hBₓℬ hBₓ,
          cases hBₓ with hxBₓ hBₓU,
          use Bₓ,
          split,
          split,
            repeat {assumption},
        },
        {
          intro hx,
          cases hx with Bₓ hBₓ,
          cases hBₓ with hBₓ hxBₓ,
          cases hBₓ with hBₓℬ hBₓU,
          apply hBₓU,
          exact hxBₓ,
        },
      },
    },
  },
end

def B1 {X : Type} (F : set (set X)) := ⋃₀ F = univ 
def B2 {X : Type} (F : set (set X)) := ∀ (A B : set X), A ∈ F → B ∈ F → ∃ S : set (set X), S ⊆ F ∧ A ∩ B = ⋃₀ S  

lemma propiedades_base {X : Type} [espacio_topologico X] ( ℬ : set (set X))  (h : base ℬ) : B1 ℬ ∧ B2 ℬ :=
begin
  split,
  {
    unfold B1,
    cases h with hBab hB,
    specialize hB univ abierto_total,
    apply doble_contenido,
    {
      simp only [subset_univ],
    },
    {
      cases hB with ℱ hℱ,
      cases hℱ with hℱℬ huniv,
      rw huniv,
      apply sUnion_subset_sUnion,
      exact hℱℬ,
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
    simp only [exists_prop] at hB,
    exact hB,
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

end topologicos