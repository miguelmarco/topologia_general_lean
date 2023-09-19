import ..metricos
import ..continuidad_metricos
import tactic

noncomputable theory

open set
open real
open metricos
open metricos.espacio_metrico
open metricos.continuidad


variables {X Y Z : Type} [espacio_metrico X] [espacio_metrico Y] [espacio_metrico Z]


/-
# Ejercicio 1.2.1

En este caso lo hacemos para `ℝ` en lugar de `ℝⁿ`, aunque los argumentos son los mismos:
-/
lemma ejercicio_1_2_1 (A B : set ℝ ) (h : abierto A) : abierto { (x + y) | (x ∈ A) (y ∈ B) } := 
begin
  sorry,
end

/-
# Ejercicio 1.2.3
-/

lemma ejercicio_1_2_3 (X : Type) (S : set X) [espacio_metrico X] : 
 abierto {x : X | entorno x S } :=
begin
  sorry,
end


/-
# Continuidad


-/

variables (f : X → Y) (g : Y → Z)

/-
# Ejercicio 1.3.2
-/
lemma ejer_1_3_2 (x₀ : X) (hf : continua_en f x₀) (hg : continua_en g (f x₀)) :
continua_en (g ∘ f)  x₀ :=
begin
  sorry,
end 

