import .topologicos
import .conjuntos

noncomputable theory

open topologicos topologicos.espacio_topologico 

variables {X : Type} [espacio_topologico X]

def clausura (U : set X)  : set X :=  ⋂₀ { C ∈ cerrados | U ⊆ C }

lemma clausura_def (U : set X) : clausura U  = ⋂₀ { C ∈ cerrados | U ⊆ C } :=
begin
  refl,
end

lemma clausura_cerrado (U : set X) : cerrado (clausura U) :=
begin
  unfold clausura,
  apply cerrado_inter,
  simp only [set.sep_subset],
end

lemma clausura_menor_cerrado (U : set X) (C : set X) (hC : cerrado C ) (hUC : U ⊆ C) :
clausura U ⊆ C :=
begin
  unfold clausura,
  apply set.sInter_subset_of_mem,
  split,
  {
    exact hC,
  },
  {
    exact hUC,
  },
end



@[simp]
lemma clausura_caracterizacion (U : set X) (x : X) : x ∈ clausura U ↔ ∀ V ∈ (abiertos : set (set X)), x ∈ V → U ∩ V ≠ ∅ :=
begin
  split,
  {
    intros hx V hVab hxV hintervac,
    suffices haux : x ∈ Vᶜ,
    {
      exact haux hxV,
    },
    specialize hx Vᶜ,
    apply hx,
    split,
    {
      simp only [compl_compl, topologicos.abierto_def, topologicos.cerrados_def],
      exact hVab,
    },
    {
      dsimp,
      rw contenido_sii_interseccion_compl_vacio,
      simp only [compl_compl,hintervac],
    }
  },
  {
    intros h V hV,
    specialize h Vᶜ,
    cases hV with hVcer hUV,
    specialize h hVcer,
    by_contradiction hxnoenV,
    specialize h hxnoenV,
    apply h,
    rw ← contenido_sii_interseccion_compl_vacio,
    exact hUV,
  }
end

lemma clausura_contiene (U : set X) : U ⊆ clausura U :=
begin
  intros x hx,
  intros C hC,
  cases hC with hCcerr hCU,
  apply hCU,
  exact hx,
end

lemma clausura_monotona (U V : set X) (h : U  ⊆ V) : clausura U ⊆ clausura V :=
begin
  intros x hx,
  intros C hC,
  apply hx,
  cases hC with hCcer hCV,
  split, assumption,
  intros z hz,
  apply hCV,
  apply h,
  exact hz,
end

lemma clausura_eq_sii_cerrado (A : set X) : cerrado A ↔ clausura A = A:=
begin
  split,
  {
    intro h,
    ext,
    split,
    {
      intro hx,
      specialize hx A,
      apply hx,
      split, assumption,
      simp only [],
    },
    {
      intro hx,
      intros C hC,
      cases hC with hC1 hC2,
      apply hC2,
      exact hx,
    },
  },
  {
    intro h,
    rw  ← h,
    apply clausura_cerrado,
  }
end

@[simp]
lemma clausura_clausura (A  : set X) : clausura (clausura A) = clausura A :=
begin
  rw ← clausura_eq_sii_cerrado,
  apply clausura_cerrado,
end

@[simp]
lemma clausura_union (A B: set X) : clausura (A ∪ B) = clausura A ∪ clausura B :=
begin
  ext x,
  split,
  {
    intro h,
    apply h,
    split,
    {
      apply cerrado_union,
      all_goals { apply clausura_cerrado,},
    },
    {
      apply set.union_subset_union,
      all_goals { apply clausura_contiene,},
    },
  },
  {
    intro h,
    intros C hC,
    cases hC with hCcer hCcont,
    cases h,
    all_goals {
      apply h,
      split, assumption,
      apply subset_trans _ hCcont,
      simp only [set.subset_union_left, set.subset_union_right],
    },
  }
end

lemma clausura_inter (A B : set X) : clausura (A ∩ B) ⊆ clausura A ∩ clausura B :=
begin
  intros x hx,
  split,
  all_goals {
    intros C hC,
    cases hC with hCcer hCcont,
    apply hx,
    split, assumption,
    apply subset_trans _ hCcont,
    simp only [set.inter_subset_left,set.inter_subset_right],
  },
end

def interior (A : set X ) : set X := ⋃₀ {S ∈ abiertos | S ⊆ A}

lemma interior_def (A : set X) : interior A = ⋃₀ {S ∈ abiertos | S ⊆ A} :=
begin
  refl,
end


lemma interior_abierto (A : set X) : abierto (interior A ) :=
begin
  apply abierto_union,
  intros S hS,
  exact hS.1,
end

lemma interior_contenido (A : set X) : interior A ⊆ A :=
begin
  apply set.sUnion_subset,
  intros S hS,
  exact hS.2,
end

lemma interior_mayor_abierto (A U : set X) (hU : abierto U) (hUA : U ⊆ A) : U ⊆ interior A :=
begin
  intros x hx,
  use U,
  split,
  split,
  all_goals { assumption},
end

@[simp]
lemma interior_caracterizacion (A : set X) (x : X) : x ∈ interior A ↔ ∃ U ∈ (abiertos: set (set X)), U ⊆ A ∧ x ∈ U :=
begin
  simp [interior_def],
  tauto,
end

lemma interior_monotono (A B : set X) (hAB : A ⊆ B) : interior A ⊆ interior B :=
begin
  apply set.sUnion_subset_sUnion,
  intros S hS,
  cases hS with hSab hSA,
  split, assumption,
  tauto,
end

lemma interior_eq_sii_abierto (A : set X) :   abierto A ↔  interior A = A :=
begin
  split,
  {
    intro hA,
    ext x,
    split,
    {
      apply interior_contenido,
    },
    {
      intros hx,
      use A,
      split,
      split,
      assumption,
      simp only [],
      assumption,
    }
  },
  {
    intro h,
    rw ← h,
    apply interior_abierto,
  }
end

@[simp]
lemma interior_interior (A : set X ) : interior (interior A ) = interior A :=
begin
  rw ← interior_eq_sii_abierto,
  apply interior_abierto,
end


lemma interior_union (A B : set X) : interior A ∪ interior B ⊆ interior (A ∪ B ) :=
begin
  intros x hx,
  cases hx,
  {
    use interior A,
    split,
    split,
    apply interior_abierto,
    {
      intros y hy,
      left,
      apply interior_contenido,
      exact hy,
    },
    {
      exact hx,
    },
  },
  {
    use interior B,
    split,
    split,
    {
      apply interior_abierto,
    },
    {
     intros y hy,
     right,
     apply interior_contenido,
     exact hy,
    },
    {
      exact hx,
    }
  }
end

lemma interior_interseccion (A B : set X) : interior (A ∩ B) = interior A ∩ interior B :=
begin
  ext,
  simp only [interior_caracterizacion, set.mem_inter_iff],
  split,
  {
    intro h,
    cases h with U hU,
    cases hU with hUab hUcont,
    cases hUcont with hUcont hUx,
    split,
    all_goals {
      use U,
      split, assumption,
      split,
      {
        refine subset_trans hUcont _,
        simp,
      },
      assumption,
    },
  },
  {
    intro h,
    cases h with hA hB,
    cases  hA with U hU,
    cases hU with hUab hU,
    cases hU with hUA hUx,
    cases hB with V hV,
    cases hV with hVab hV,
    cases hV with hVB hVx,
    use U ∩ V,
    split,
    exact abierto_interseccion_2 U V hUab hVab,
    split,
    apply set.inter_subset_inter hUA hVB,
    exact ⟨ hUx,hVx⟩,
  }
end
