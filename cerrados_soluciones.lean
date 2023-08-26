import .cerrados
import tactic


open topologicos
open topologicos.espacio_topologico

variables {X : Type} [espacio_topologico X]  

lemma ejer_2_4_1_sol : ∀ S : set X, S ∈ @cerrados X (discreta X) :=
begin
  intro S,
  trivial,
end

section ejercicios_metricos
open metricos
open metricos.espacio_metrico

lemma ejer_2_4_4_sol (X : Type) [espacio_metrico X] (x : X) (ε : ℝ ) (hε : ε > 0) :
cerrado (disco x ε) :=
begin
  intros y hy,
  simp at hy,
  use d x y - ε,
  split,
  {
    linarith,
  },
  {
    intros z hz,
    simp at *,
    have htriang := d4 x  z y,
    have hsim := d3 y z,
    linarith,
  }
end


/-
puede ser util este lema:

`nt.lt_of_le : x ≠ y → ?x ≤ y → x < y`
-/

lemma ejer_2_4_4_2_sol (X : Type) [espacio_metrico X] (x : X) (ε : ℝ ) (hε : ε > 0) :
cerrado (esfera x ε) :=
begin
  intros y hy,
  by_cases hcas: d x y > ε,
  {
    use d x y - ε,
    split,
    {
      linarith,
    },
    {
      intros z hz,
      simp at *,
      have htriang := d4 x z y,
      have hsim := d3 y z,
      linarith,  
    },
  },
  {
    use ε - d x y,
    split,
    {
      simp at *,
      exact ne.lt_of_le hy hcas,
    },
    {
      intros z hz,
      simp at *,
      have htriang := d4 x y z,
      linarith,
    }
  }
end

end ejercicios_metricos
