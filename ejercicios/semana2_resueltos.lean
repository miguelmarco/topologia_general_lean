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
lemma ejercicio_1_2_1_sol (A B : set ℝ ) (h : abierto A) : abierto { (x + y) | (x ∈ A) (y ∈ B) } := 
begin
  intros z hz,
  simp at hz,
  cases hz with x hx,
  cases hx with hx hy,
  cases hy with y hy,
  cases hy with hy hz,
  specialize h x hx,
  cases h with r hr,
  cases hr with hrpos hbolr,
  use r,
  split, exact hrpos,
  intros t ht, 
  simp [d,← hz] at ht,
  simp,
  use t - y,
  split,
  {
    apply hbolr,
    simp [d],
    ring_nf at ⊢ ht,
    exact ht,
  },
  use y,
  split,
  {
    exact hy,
  },
  {
    ring_nf,
  }
end

/-
# Ejercicio 1.2.3
-/

lemma ejercicio_1_2_3_sol (X : Type) (S : set X) [espacio_metrico X] : 
 abierto {x : X | entorno x S } :=
begin
  intros x hx,
  cases hx with r hr,
  cases hr with hrpos hrbol,
  use r,
  split, exact hrpos,
  intros y hy,
  simp at hy,
  use (r - d x y),
  split,
  {
    linarith,
  },
  {
    intros z hz,
    apply hrbol,
    simp at *,
    have htri := d4 x y z,
    linarith,
  }
end


/-
# Continuidad


-/

variables (f : X → Y) (g : Y → Z)

/-
# Ejercicio 1.3.2
-/
lemma ejer_1_3_2_sol (x₀ : X) (hf : continua_en f x₀) (hg : continua_en g (f x₀)) :
continua_en (g ∘ f)  x₀ :=
begin
  rw prop_1_3_8 at *,
  intros W hW,
  specialize hg W hW,
  cases hg with V hV,
  cases hV with hVent hgV,
  specialize hf V hVent,
  cases hf with U hU,
  use U,
  cases hU with hUent hfU,
  split,
  {
    exact hUent,
  },
  {
    intros z hz,
    apply hgV,
    cases hz with x hx,
    cases hx with hxU hgfx,
    use (f x),
    split,
    {
      apply hfU,
      use x,
      simp,
      exact hxU,
    },
    {
      exact hgfx,
    }
  }
end 

