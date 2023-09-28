import data.real.basic
import tactic

noncomputable theory

open set
open real


class espacio_metrico (X : Type) :=
( d : X → X → ℝ )
( d1 : ∀ x y : X, d x y ≥ 0)
( d2 : ∀ x y: X , d x y = 0 ↔ x = y)
( d3 : ∀ x y : X, d x y = d y x)
( d4 : ∀ x y z : X, d x z ≤ d x y + d y z )


open espacio_metrico
variables {X : Type} [espacio_metrico X]


def bola (x : X) (r : ℝ )  := {y : X | d x y < r}
def disco (x : X) (r : ℝ )  := { y : X | d x y ≤ r }
def esfera (x : X )(r : ℝ ) := {y : X | d x y = r}


/-
## Ejercicio 1.1.1

Prueba que `ℝ` con la norma usual es un espacio métrico.

Vamos a usar algunos resultados sobre el valor absoluto que
ya están probados en lean:

`abs_nonneg : ∀ (a : ℝ), 0 ≤ |a|`
`abs_sub_comm : ∀ (a b : ℝ), |a - b| = |b - a|`
`abs_sub_le : ∀ (a b c : ℝ), |a - c| ≤ |a - b| + |b - c|`

-/
instance : espacio_metrico ℝ := 
{ d := λ x y, | x - y |,  
  d1 :=   
  begin
    sorry,
  end,
  d2 := 
  begin
    sorry,
  end,
  d3 := 
  begin
    sorry,
  end,
  d4 := 
  begin
    sorry,
  end 
}

/-
## Ejercicio1 1.1.6

Sea (X,d) un espacio métrico, demuestra que `x ∈ B(y, r) ↔ y ∈ B(x, r)`  
-/

lemma ejer_1_1_6 : 
∀ (x y : X) (r > 0), x ∈ bola y r ↔ y ∈ bola x r :=
begin
  sorry,
end

/-
## Ejercicio 1.1.7

Demuestra que si d1 y d2 son distancias en X de modo que
d1(x, y) ≤ d2(x, y) ∀x, y ∈ X, entonces Bd2 (x; ε) ⊂ Bd1 (x; ε)
-/

lemma ej_1_1_7  (M1 M2 : espacio_metrico X) (h : ∀ x y : X, (@d X M1) x y ≤ (@d X M2) x y) : ∀ x : X, ∀ ε > 0,  (@bola X M2) x ε ⊆ (@bola X M1) x ε  :=
begin
  sorry,
end  


/-
## Ejercicio 1.1.8
Demuestra que la distancia entre los puntos de una bola es
menor que el doble del radio, es decir, si y, z ∈ Bd(x; ε) entonces d(y, z) < 2ε.
-/

lemma ej_1_1_8 (x y z: X) (r : ℝ) (h : r > 0) (hy : y ∈ bola x r) (hz : z ∈ bola x r): d y z < 2 * r :=
begin
  sorry,
end