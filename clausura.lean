import .topologicos
import .cerrados
import .conjuntos
import .entornos

noncomputable theory

open topologicos topologicos.espacio_topologico 

namespace topologicos

/-
En lo sucesivo, `X` será un espacio topológico.
-/
variables {X : Type} [espacio_topologico X]


/-
## Definición 3.2.1

La **clausura** de un conjunto `U` es la intersección de los cerrados que lo contienen.
-/
def clausura (U : set X)  : set X :=  ⋂₀ { C ∈ cerrados | U ⊆ C }

/-
Damos el lema que permite reescribir si lo necesitamos:
-/
lemma clausura_def (U : set X) : clausura U  = ⋂₀ { C ∈ cerrados | U ⊆ C } :=
begin
  refl,
end

/-
Y el correspondiente para la pertenencia de un elemento.
-/
lemma pert_clausura (U : set X) (x : X) : x ∈ clausura U ↔ ∀ C : set X,  cerrado C → U ⊆ C → x ∈ C :=
begin
  unfold clausura,
  simp only [set.mem_sInter, set.mem_sep_iff, cerrados_def, and_imp, cerrado_def],
end


/-
## Propiedades de la clausura:

La clausura de cualquier conjunto es un cerrado.
-/
lemma clausura_cerrado (U : set X) : cerrado (clausura U) :=
begin
  rw clausura_def,
  apply cerrado_inter,
  simp only [set.sep_subset],
end

/-
Si un cerrado contiene a `U`, entonces contiene a su clausura.
-/
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

/-
La clausura de un conjunto contiene al conjunto.
-/
lemma clausura_contiene (U : set X) : U ⊆ clausura U :=
begin
  intros x hx,
  intros C hC,
  cases hC with hCcerr hCU,
  apply hCU,
  exact hx,
end

/-
Clausurar respeta la relación de contenido.
-/
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

/-
Un conjunto es igual a su clausura si y sólo si es cerrado.
-/
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

/-
La clausura de la clausura es la clausura.
-/
@[simp]
lemma clausura_clausura (A  : set X) : clausura (clausura A) = clausura A :=
begin
  rw clausura_eq_sii_cerrado,
  apply clausura_cerrado,
end

/-
La clausura de una unión es la unión de las clausuras.
-/
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
      intros x hx,
      cases hx with hxa hxb,
      {
        left,
        apply clausura_contiene,
        exact hxa,
      },
      {
        right,
        apply clausura_contiene,
        exact hxb,
      },
    },
  },
  {
    intros x hx,
    cases hx,
    {
    calc 
      x   ∈   clausura  A        : by {exact hx,}
      ... ⊆   clausura  (A ∪ B)  : by {simp [clausura_monotona],}
    },
    {
    calc 
      x   ∈   clausura  B        : by {exact hx,}
      ... ⊆   clausura  (A ∪ B)  : by {simp [clausura_monotona],}
    },
  }
end


/-
Un punto está en la clausura de un conjunto si y sólo si el complementario no es entorno suyo.
-/
lemma en_clausura_sii_no_entorno (A : set X) (x : X) : x ∈ clausura A ↔ ¬ (entorno x Aᶜ ) :=
begin
  rw pert_clausura,
  unfold entorno,
  push_neg,
  split,
  {
    intro hx,
    intros U hUab hxU,
    specialize hx Uᶜ,
    intro hn,
    apply hx,
    {
      unfold cerrado,
      simp only [compl_compl],
      exact hUab,
    },
    {
      tauto,
    },
    {
      exact hxU,
    },
  },
  {
    intro hx,
    intros C hC hAC,
    by_contradiction hn,
    specialize hx Cᶜ,
    apply hx,
    {
      exact hC,
    },
    {
      exact hn,
    },
    {
      tauto,
    }
  },
end

/-
La clausura de la intersección está contenida en la intersección de las clausuras.
-/
lemma clausura_inter (A B : set X) : clausura (A ∩ B) ⊆ clausura A ∩ clausura B :=
begin
  intros x hx,
  split,
  {
    calc 
      x   ∈   clausura ( A ∩ B ) : by {exact hx,}
      ... ⊆   clausura A         : by {simp [clausura_monotona],}
  },
  {
    calc 
      x   ∈   clausura ( A ∩ B ) : by {exact hx,}
      ... ⊆   clausura B         : by {simp [clausura_monotona],}
  },
end

/-
Vamos a demostrar un lema sencillo que luego usaremos:
-/

lemma contenido_sii_interseccion_compl_vacio (X : Type) (A B : set X) : A ⊆ Bᶜ ↔ A ∩ B = ∅ :=
begin
  split,
  {
    intro h,
    ext x,
    simp,
    apply h,
  },
  {
    intro h,
    intros x hxa,
    intro hxb,
    have hx : x ∈ A ∩ B,
    {
      split,
      exact hxa,
      exact hxb,
    },
    rw h at hx,
    exact hx,
  }
end



/-
## Proposición 3.2.4.a
Un punto está en la clausura de un conjunto si todo abierto que lo contenga interseca al conjunto.
-/
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
      assumption,
    },
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
    rw ← contenido_sii_interseccion_compl_vacio ,
    simp,
    exact hUV,
  }
end


/-
## Proposición 3.2.4.b
Un punto está en la clausura de un conjunto si todo entorno suyo interseca al conjunto.
-/
@[simp]
lemma clausura_caracterizacion_entorno (U : set X) (x : X) : x ∈ clausura U ↔ ∀ V , entorno x V → U ∩ V ≠ ∅ :=
begin
  split,
  {
    rw clausura_caracterizacion,
    intros h V hV,
    cases hV with W hW,
    cases hW with hWab hW2,
    cases hW2 with hxW hWV,
    specialize h W hWab hxW,
    intro hne,
    apply h,
    ext x,
    rw ← hne,
    split,
    {
      simp only [set.mem_inter_iff, and_imp],
      intros hxU hxW,
      split,
        assumption,
        apply hWV,
        assumption,
    },
    {
      intro hx,
      rw hne at hx,
      cases hx,
    }
  },
  {
    intro h,
    by_contradiction hn,
    rw en_clausura_sii_no_entorno at hn,
    simp at hn,
    specialize h _ hn,
    apply h,
    simp,
  }
end

/-
## Definición 3.2.7

Un subconjunto es denso si su clausura es el total.
-/
def denso (A : set X) := clausura A = set.univ


/-
## Proposición 3.2.8
Un conjunto es denso si cualquier abierto no vacío lo interseca.
-/
lemma denso_sii_todo_abierto_interseca (A : set X) :  denso A ↔ ∀ U,  abierto U →  U ≠ ∅ → A ∩ U ≠ ∅ :=
begin
 split,
 {
  intro h,
  intros U hU hUemp,
  rw no_vacio_sii_existe_elemento at hUemp,
  unfold denso at h,
  cases hUemp with x hx,
  have hxA : x ∈ clausura A,
    { simp [h], },
  rw clausura_caracterizacion at hxA,
  apply hxA U hU hx,
 },
 {
  intro h,
  unfold denso,
  ext x,
  simp only [set.mem_univ, iff_true, clausura_caracterizacion],
  intros U hU hxU,
  apply h U hU,
  {
    rw no_vacio_sii_existe_elemento,
    use x,
    exact hxU,
  },
 },
end 



end topologicos