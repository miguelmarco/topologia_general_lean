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
lemma tarea_8_3_a (A B : set X) (h: A ⊆ B) : ((interior A) ↓∩ B) ⊆ interior (A ↓∩ B) :=
begin
  sorry,
end 

/-
Da condiciones sobre `B` para garantizar la igualdad de dichos conjuntos.
-/
lemma tarea_8_3_b (A B : set X) (h: A ⊆ B) (hB : abierto B) : interior (A ↓∩ B) = ((interior A) ↓∩ B) :=
begin
  sorry,
end