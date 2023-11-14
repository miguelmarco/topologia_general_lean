import ..clausura
import tactic

open topologicos topologicos.espacio_topologico set

section ejer_3_2_5
open metricos metricos.espacio_metrico

/-
## Ejercicio 3.2.5

En este serán útiles los siguientes lemas sobre ínfimos:

`le_antisymm` : a ≤ b → b ≤ a → a = b
`real.Inf_le_iff` :  bdd_below S → S.nonempty →  ∀ {a : ℝ}, Inf S ≤ a ↔ ∀ (ε : ℝ), 0 < ε → (∃ (x : ℝ) (H : x ∈ S), x < a + ε)
`real.Inf_nonneg` : ∀ (S : set ℝ), (∀ (x : ℝ), x ∈ S → 0 ≤ x) → 0 ≤ Inf S
-/
example (X : Type) [espacio_metrico X] (A : set X) (hA : A ≠ ∅ ): clausura A = {x : X | Inf  {(d x y) | y ∈ A } = 0 } :=
begin
  sorry,
end

end ejer_3_2_5

open function


/-
## Ejercicio 3.2.7
-/
example (X Y : Type) [espacio_topologico X] [espacio_topologico Y] (f : X → Y) (hfsup : surjective f) (hcon : continua f) 
    (D : set X) (hD : denso D): denso (f '' D) :=
begin
  sorry,
end


/-
## Ejercicio 3.2.8

En este es un poco pesado ir cambiando de conjuntos en `X` (con suu respectiva topología) a conjuntos en `↥Y` con la suya.

Recordar que los elementos de `↥Y` son parejas del tipo `⟨x, x ∈ Y⟩`. Convertir un elemento de `↥Y` al correspondente de `X`,
o un conjunto de `↥Y` a uno de `X` se hace con `↑x`. Convertir un conjunto de `X` a uno de `↥Y` se hace con `A ↓∩ Y`.

Es recomendable usar `simp` a menudo.
-/


example (X : Type) [espacio_topologico X] (Y : set X) (A : set Y) : ↑(clausura A) = (clausura ↑A) ∩ Y :=
begin
  sorry,
end