import ..bases
import ..cerrados
import tactic

open topologicos topologicos.espacio_topologico



/-
Podemos usar el resultado de caracterizacion de las bases:

caracterizacion_base : ∀ (ℬ : set (set X)),
    ℬ ⊆ abiertos →
    (base ℬ ↔
       ∀ (U : set X),
         abierto U →
         ∀ (x : X), x ∈ U → (∃ (Bₓ : set X) (H : Bₓ ∈ ℬ), Bₓ ⊆ U ∧ x ∈ Bₓ))

-/


lemma ejer_2_2_8  (X : Type) [espacio_topologico X] (S : set (set X)) (hsAb : S ⊆ abiertos) : 
subbase S ↔ ∀ (U : set X), abierto U →  ∀ x ∈ U, ∃ (ℱ : set (set X)), set.finite ℱ ∧ ℱ ⊆ S ∧ x ∈ ⋂₀ ℱ ∧ ⋂₀ ℱ ⊆ U:=
begin
  sorry,
end


open metricos metricos.espacio_metrico


lemma ejer_2_4_4_1 (X : Type) [espacio_metrico X] (x : X) (r : ℝ ) : cerrado (disco x r) :=
begin
  sorry,
end

lemma ejer_2_4_4_2 (X : Type) [espacio_metrico X] (x : X) (r : ℝ ) : cerrado (esfera x r)  :=
begin
  sorry,
end

