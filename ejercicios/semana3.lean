import ..topologicos
import tactic

open topologicos
open topologicos.espacio_topologico

open set 

/-
# Ejercicio 2.1.3
-/

lemma ejer_2_1_3 (X : Type) [τ : espacio_topologico X] : τ = (discreta X) ↔ ∀ x : X, abierto ({x} : set X) :=
begin
  sorry,
end



/-
# Ejercicio 2.1.5
-/

lemma  ejer_2_1_5_a (X Y : Type) [espacio_topologico X] (f : X → Y) : @continua _ _ _ (indiscreta Y) f:=
begin
  sorry,
end


/-
# Ejercicio 2.1.6
-/
lemma ejer_2_1_6 (X Y : Type) [Tx : espacio_topologico X] [Ty: espacio_topologico Y] (f : X → Y) : continua f ↔ (@imagen_inversa _ _ _  f).abiertos ⊆ Tx.abiertos :=
begin
  sorry,
end

/-
# Ejercicio 2.1.7
-/
lemma ejer_2_1_7 (X Y : Type) [Tx : espacio_topologico X] [Ty: espacio_topologico Y] (f : X → Y) : continua f ↔ Ty.abiertos ⊆  (@imagen_directa _ _ _  f).abiertos  :=
begin
  sorry,
end
