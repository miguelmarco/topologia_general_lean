import ..metricos
import ..entornos
import tactic

open topologicos topologicos.espacio_topologico

/-
## Ejercicio 3.1.2
-/

lemma ejercicio_3_1_2 (X : Type) [metricos.espacio_metrico X] (x : X) (U : set X) : metricos.entorno x U ↔ entorno x U :=
begin
  sorry,
end


/-
## Ejercicio 3.1.6
-/
lemma ejercicio_3_1_6 (X : Type) [espacio_topologico X] (x : X) (𝓑 : set (set X)) (h𝓑 : base_de_entornos x 𝓑 ) (U : set X) (hU : abierto U)  (hx : x ∈ U) :
    base_de_entornos x { B ∈ 𝓑 | B ⊆ U} :=
begin
  sorry,
end

lemma ejer_3_1_7 (X : Type) [espacio_topologico X] (A : set X) (x : A) (𝓑 : set (set X)) (h𝓑 : base_de_entornos ↑x 𝓑)  :
    base_de_entornos x {(E ↓∩ A) | E ∈ 𝓑} :=
begin
  sorry,
end