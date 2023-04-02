import .topologicos
import .conjuntos

noncomputable theory

open topologicos topologicos.espacio_topologico 

namespace clausura

variables {X : Type} [espacio_topologico X]



def clausura (U : set X)  : set X :=  ⋂₀ { C ∈ cerrados | U ⊆ C }


lemma clausura_def (U : set X) : clausura U  = ⋂₀ { C ∈ cerrados | U ⊆ C } :=
begin
  refl,
end

lemma pert_clausura (U : set X) (x : X) : x ∈ clausura U ↔ ∀ C : set X,  cerrado C → U ⊆ C → x ∈ C :=
begin
  unfold clausura,
  simp,
end

lemma clausura_cerrado (U : set X) : cerrado (clausura U) :=
begin
  rw clausura_def,
  apply cerrado_inter,
  intros C hC,
  cases hC with hC1 hC2,
  exact hC1,
end

lemma clausura_contiene (U : set X) : U ⊆ clausura U :=
begin
  intros x hx,
  intros C hC,
  cases hC with hCcerr hCU,
  apply hCU,
  exact hx,
end

lemma clausura_menor_cerrado (U : set X) (C : set X) (hC : cerrado C ) (hUC : U ⊆ C) :
clausura U ⊆ C :=
begin
  intros x hx,
  apply hx,
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
      simp only [cerrados_def, compl_compl, abierto_def],
      exact hVab,
    },
    {
      dsimp,
      rw contenido_sii_interseccion_compl_vacio,
      simp only [compl_compl,hintervac],
    }
  },
  {
    intros h,
    rw pert_clausura,
    intros V hVcer hUV,
    specialize h Vᶜ,
    specialize h hVcer,
    by_contradiction hxnoenV,
    specialize h hxnoenV,
    apply h,
    rw contenido_sii_interseccion_compl_vacio at hUV,
    exact hUV,
  }
end



lemma clausura_monotona (U V : set X) (h : U  ⊆ V) : clausura U ⊆ clausura V :=
begin
  intros x hx,
  rw pert_clausura at *,
  intros C hCcer hCV,
  apply hx,
  assumption,
  calc 
    U    ⊆   V    : h
    ...  ⊆   C    : hCV
end

@[simp]
lemma clausura_eq_sii_cerrado (A : set X) : clausura A = A ↔ cerrado A :=
begin
  split,
    {
    intro h,
    rw  ← h,
    apply clausura_cerrado,
  },
  {
    intro h,
    apply doble_contenido,
    {
      apply clausura_menor_cerrado,
      exact h,
      tauto,
    },
    {
      apply clausura_contiene,
    }
  }
end

@[simp]
lemma clausura_clausura (A  : set X) : clausura (clausura A) = clausura A :=
begin
  rw clausura_eq_sii_cerrado,
  apply clausura_cerrado,
end

@[simp]
lemma clausura_union (A B: set X) : clausura (A ∪ B) = clausura A ∪ clausura B :=
begin
  apply doble_contenido,
  {
    apply clausura_menor_cerrado,
    {
      apply cerrado_union,
      repeat { apply clausura_cerrado, },
    },
    {
      apply union_contenida_union,
      repeat {apply clausura_contiene,},
    },
  },
  {
    rw union_contenido,
    split,
    repeat {
      apply clausura_monotona,
      simp,
    },
  }
end

lemma clausura_inter (A B : set X) : clausura (A ∩ B) ⊆ clausura A ∩ clausura B :=
begin
  rw contenido_interseccion,
  split,
  repeat {
    apply clausura_monotona,
    simp,
  },
end

end clausura

namespace interior

variables {X : Type} [espacio_topologico X]

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

@[simp]
lemma interior_interior (A : set X ) : interior (interior A ) = interior A :=
begin
  rw interior_eq_sii_abierto,
  apply interior_abierto,
end


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
    apply union_contenida_union,
    repeat { apply interior_contenido,  },
  }
end

lemma interior_interseccion (A B : set X) : interior (A ∩ B) = interior A ∩ interior B :=
begin
  apply doble_contenido,
  {
    rw contenido_interseccion,
    split,
    {
      apply interior_monotono,
      apply interseccion_contenida_izda,
    },
    {
      apply interior_monotono,
      apply interseccion_contenida_derecha,
    },
  },
  {
    apply interior_mayor_abierto,
    {
      apply abierto_interseccion_2,
      repeat {apply interior_abierto, },
    },
    {
      rw contenido_interseccion,
      split,
      {
        calc 
          interior A ∩ interior B ⊆  interior A : by {apply interseccion_contenida_izda,}
          ...                     ⊆   A         : by {apply interior_contenido,}
      },
      {
        calc
          interior A ∩ interior B ⊆  interior B : by {apply interseccion_contenida_derecha,}
          ...                     ⊆   B         : by {apply interior_contenido,}
      },
    },
  },
end

end interior