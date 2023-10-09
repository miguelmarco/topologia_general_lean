import .topologicos
import .cerrados
import .subconjuntos
import tactic


open set
open topologicos
open topologicos.espacio_topologico

variables {X : Type} [espacio_topologico X] {A : set X} 


instance topologia_inducida {X : Type} [espacio_topologico X] (A : set X)  : espacio_topologico A := 
{ abiertos := {( (U ↓∩ A) )  | U ∈ (abiertos : set (set X))},
  abierto_total := 
  begin
    use univ,
    simp only [and_true, eq_self_iff_true, restringe_total],
    exact abierto_total,
  end,
  abierto_vacio := 
  begin
    use ∅,
    simp only [and_true, eq_self_iff_true, restringe_vacio],
    exact abierto_vacio,
  end,
  abierto_union := 
  begin
    intros F hF,
    use ⋃₀ {U : set X | abierto U ∧ (U ↓∩  A) ∈ F},
    split,
    {
      apply abierto_union,
      intros U hU,
      exact hU.1,
    },
    {
      ext x,
      simp only [restringe_union_familia],
      split,
      {
        intro hx,
        cases hx with U hU,
        cases hU with hUF hxU,
        cases hUF with V hV,
        cases hV with hV hVU,
        cases hV with hVab hVF,
        use (V ↓∩ A),
        split, exact hVF,
        rw hVU,
        exact hxU,
      },
      {
        intro hx,
        cases hx with U hU,
        cases hU with hUF hxU,
        specialize hF hUF,
        cases hF with V hV,
        cases hV with hVab hVU,
        use (V ↓∩ A),
        split,
        {
          use V,
          simp [hVab, hVU, hUF],
        },
        {
          rw hVU,
          exact hxU,
        },
      },
    },
  end,
  abierto_interseccion := 
  begin
    intros U V hU hV,
    simp only [exists_prop, mem_set_of_eq] at *,
    cases hU with UX hUX,
    cases hUX with hUXab hUXU,
    cases hV with VX hVX,
    cases hVX with hVXab hVXV,
    use UX ∩ VX,
    split,
    {
      apply abierto_interseccion,
      assumption,
      assumption,
    },
    {
      simp only [restringe_interseccion, hUXU, hVXV],
    },
  end,
  }


def  TA (A : set X)  := topologia_inducida A


@[simp]
lemma abierto_inducido_sii (C : set A) : abierto C ↔ ∃ U  ∈ (abiertos : set (set X)),   (U ↓∩ A) = C:=
begin 
  refl,
end




lemma cerrado_inducido_sii (C : set A) : cerrado C ↔ ∃ U  ∈ (cerrados : set (set X)),   (U ↓∩ A) = C :=
begin
  simp only [cerrado, abierto_inducido_sii],
  split,
  {
    intro h,
    cases h with U hU,
    cases hU with hUab hUC,
    use Uᶜ,
    simp only [hUab,hUC, cerrados_def, compl_compl, abierto_def, restringe_complementario, eq_self_iff_true, and_true],
  },
  {
    simp only [cerrados_def, abierto_def, exists_prop, forall_exists_index, and_imp],
    intros U hUab hUC,
    use Uᶜ,
    simp only [hUab, hUC, restringe_complementario, eq_self_iff_true, and_self],
  }
end

def ι : A → X := λ x, x.val



lemma inclusion_continua : continua (ι : A → X ) :=
begin
  intros U hU, 
  use U,
  simp only [hU, true_and],
  refl,
end

def extiende (X : Type)  (A : set X) : set A →  set X := coe

example (X : Type) [TX : espacio_topologico X] (A : set X) (B : set A) : extiende X A  '' ((extiende ↥A B) '' (@abiertos ↥B (topologia_inducida B))) = (extiende X B) ''  @abiertos (B : set X) (topologia_inducida (B : set X)) :=
begin
  ext U,
  simp only [extiende, mem_image, abiertos_imagen_inversa_def, restringe_coe, exists_prop, mem_set_of_eq, exists_exists_and_eq_and,
  restringe_eleva, eleva_interseccion, interseccion_elevacion],
end


def aplicacion_restriccion_imagen {X Y : Type} (f : X → Y ) (A : set Y) (hFA : range f ⊆ A ) : X → A :=
begin
  intro x,
  fconstructor,
  {
    exact f x,
  },
  {
    apply hFA,
    use x,
  }
end


notation f `|_` hFA  := aplicacion_restriccion_imagen f _ hFA 



lemma continua_restriccion_imagen (X Y : Type) [espacio_topologico X] [espacio_topologico Y]
      (A : set Y) (f : X → Y ) (hFA : range f ⊆ A )
      (hcont : continua (f |_  hFA) ) :
      continua f 
      :=
begin
  intros U hU,
  have haux : f ⁻¹' U = (f |_ hFA) ⁻¹' (U ↓∩ A),
  {
    refl,
  },
  {
    rw haux,
    apply hcont,
    use U,
    simp,
    exact hU,
  },
end

lemma continua_a_trozos (X Y : Type) [espacio_topologico X] [espacio_topologico Y] (A B : set X) (f : X → Y)
(hAB : A ∪ B = univ ) (hA : abierto A) (hB : abierto B) (hfA : continua (f ∘ ι : A → Y)) (hfB : continua (f ∘ ι : B → Y)) :
continua f :=
begin
  intros U hU,
  specialize hfA U hU,
  specialize hfB U hU,
  have hUA : (f ∘ ι ⁻¹' U) = ((f ⁻¹' U) ↓∩ A) := rfl,
  have hUB : (f ∘ ι ⁻¹' U) = ((f ⁻¹' U) ↓∩ B) := rfl,
  simp only [hUA, abiertos_imagen_inversa_def, restringe_coe, exists_prop, mem_set_of_eq, restringe_igual] at hfA,
  simp only [hUB, abiertos_imagen_inversa_def, restringe_coe, exists_prop, mem_set_of_eq, restringe_igual] at hfB,
  clear hUA,
  clear hUB,
  cases hfA with UA hUA,
  cases hUA with hUAab hfUA,
  cases hfB with UB hUB,
  cases hUB with hUBab hfUB,
  rw ←inter_univ (f ⁻¹' U),
  rw ← hAB,
  rw inter_distrib_left,
  rw ← hfUA,
  rw ← hfUB,
  apply abierto_union_2,
  repeat {
    apply abierto_interseccion,
    assumption,
    assumption
  },
end

