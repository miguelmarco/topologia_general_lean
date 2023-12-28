import ..interior
import ..subespacios
import tactic


open topologicos topologicos.espacio_topologico

variables (X : Type) [espacio_topologico X]
/-
# Tarea 8. 

Apartado 3

Sean `A ⊆ B ⊆ X`. ¿Qué relación hay entre Intₓ(A) e Int_b(A)?
-/
lemma tarea_8_3_a_sol (A B : set X) (h: A ⊆ B) : ((interior A) ↓∩ B) ⊆ interior (A ↓∩ B) :=
begin
  intro x,
  simp only [interior_caracterizacion_abiertos, pert_restringe_def,  abiertos_imagen_inversa_def, restringe_coe],
  intro h,
  cases h with U hU,
  cases hU with hUab hU2,
  cases hU2 with hxU hUA,
  use (U ↓∩ B),
  simp,
  split,
  {
    use U,
    split,
    {
      exact hUab,
    },
    {
      refl,
    },
  },
  split,
  {
    exact hxU,
  },
  {
    intros y hy,
    apply hUA,
    exact hy.1,
  }
end 

/-
Da condiciones sobre `B` para garantizar la igualdad de dichos conjuntos.
-/
lemma tarea_8_3_b_sol (A B : set X) (h: A ⊆ B) (hB : abierto B) : interior (A ↓∩ B) = ((interior A) ↓∩ B) :=
begin
  apply doble_contenido,
  {
    intros x hx,
    rw interior_caracterizacion_abiertos at hx,
    rcases hx with ⟨U,⟨hU,⟨hxU,hUcont⟩⟩⟩,
    simp only [pert_restringe_def],
    rcases hU with ⟨V,⟨hVab,hVU⟩⟩,
    use V ∩ B,
    simp only [set.mem_sep_eq, and_true, set.mem_inter_eq, subtype.coe_prop],
    split,
    split,
    {
      apply abierto_interseccion,
        exact hVab,
        exact hB,
    },
    {
      rw [← hVU] at hUcont,
      simp only [restringe_contenido, set.subset_inter_iff, set.inter_subset_right, and_true] at hUcont,
      exact hUcont,
    },
    {
      rw ← hVU at hxU,
      simp only [pert_restringe_def] at hxU,
      exact hxU,
    }
  },
  {
    apply tarea_8_3_a,
    exact h,
  }
end