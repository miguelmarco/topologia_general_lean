import data.real.basic
import data.set.countable
import tactic

noncomputable theory

open set
open real


namespace metricos

/-
# Espacios métricos

Un espacio métrico es un conjunto (que en Lean representaremos como un tipo)
con una estructura añadida.

Esta estructura está formada por
- Una aplicación que toma dos elementos del conjunto, y da un número real, llamada *distancia*
- Una serie de propiedades (en Lean, demostraciones de ciertas proposiciones):
  - `d1` : la distancia entre dos puntos es no negativa
  - `d2` : la distancia entre dos puntos es cero si y sólo si los puntos coinciden
  - `d3` : la distancia es simétrica
  - `d4` : la distancia cumple la desigualdad triangular

La forma de representar este tipo de estructuras es mediante una **clase**:
-/

class espacio_metrico (X : Type) :=
( d : X → X → ℝ )
( d1 : ∀ x y : X, d x y ≥ 0)
( d2 : ∀ x y: X , x = y ↔ d x y = 0)
( d3 : ∀ x y : X, d x y = d y x)
( d4 : ∀ x y z : X, d x z ≤ d x y + d y z )


open espacio_metrico

-- a partir de ahora, supondremos que tenemos un espacio métrico llamado `X`
variables {X : Type} [espacio_metrico X]
-- esto es equivalente a añadir estas hipótesis implíctiamente en cada 
-- resultado que probemos



def bola (x : X) (r : ℝ ) : set X := {y : X | d x y < r}

lemma bola_radio_monotono {X : Type} [espacio_metrico X] (x : X)  (r1 r2 : ℝ ) (hr : r1 < r2) :
 bola x r1 ⊆ bola x r2 :=
begin 
  intros y hy,
  simp only [set.mem_set_of_eq, metricos.bola.equations._eqn_1] at *,
  linarith,
end

lemma ej_1_1_6  (x y : X) (r : ℝ ): x ∈ bola y r ↔ y ∈ bola x r :=
begin
  simp only [set.mem_set_of_eq, bola],
  rw d3,
end

lemma ej_1_1_6_b   (x y : X) (r : ℝ ): x ∉  bola y r ↔ y ∉ bola x r :=
begin
  simp only [not_lt, set.mem_set_of_eq, bola],
  rw d3,
end

lemma ej_1_1_8  (x y z : X) (r : ℝ ) (hz : z ∈ bola x r) (hy : y ∈ bola x r) :
d y z < 2 * r :=
begin
  simp [bola] at *,
  calc 
    d y z    ≤ d y x + d x z       : by {apply d4,}
    ...      = d x y + d x z       : by {simp [d3],}
    ...      < r + r               : by {apply add_lt_add hy hz,}
    ...      = 2 * r               : by {ring,}
end

/-
Un conjunto del espacio es un *entorno* de un punto si hay una bola centrada en el punto contenida en el 
conjunto
-/

def entorno  (x : X) (E : set X) := ∃ (r : ℝ) (hr : r > 0), bola x r ⊆ E


-- Trivialmente, una bola centrada en un punto es entorno del mismo
example  (x : X) (r : ℝ ) (hr : r > 0) : entorno x (bola x r) :=
begin
  simp only [entorno, bola, gt_iff_lt, set_of_subset_set_of, exists_prop],
  use r,
  tauto,
end



def abierto (U : set X) := 
∀ (x : X) (hx : x ∈ U), ∃ (r : ℝ ) (hr : r > 0), bola x r ⊆ U

def abiertos  : set (set X) := abierto

lemma ab_total  : abierto (univ : set X) :=
begin
  intros x hx,
  use 1,
  simp only [set.subset_univ, gt_iff_lt, and_self, zero_lt_one],
end



lemma ab_total' : (univ : set X)  ∈  (abiertos : set (set X)):=
begin 
   exact ab_total,
end

lemma ab_vacio : abierto ( ∅  : set X)  :=
begin
  tauto,
end

lemma ab_union (F : set (set X)) (hab : F ⊆ abierto) : abierto ⋃₀ F  :=
begin
  intros x hx,
  cases hx with U hU,
  cases hU with hUF hxU,
  specialize hab hUF,
  specialize hab x hxU,
  cases hab with r hr,
  cases hr with hrpos hrU,
  use r,
  split, assumption,
  intros z hz,
  specialize hrU hz,
  use U,
  tauto,
end

lemma ab_inter (A B : set X) (hA : abierto A) (hB : abierto B ) : abierto (A ∩ B) :=
begin
  intros x hx,
  cases hx with hxA hxB,
  specialize hA x hxA,
  cases hA with ra hra,
  cases hra with hrapos hrabol,
  specialize hB  x hxB,
  cases hB with rb hrB,
  cases hrB with hrbpos hrbbol,
  by_cases hmax : ra < rb,
  {
    use ra,
    split, assumption,
    apply subset_inter hrabol,
    refine subset_trans _ hrbbol,
    apply bola_radio_monotono , exact hmax,
  },
  {
    use rb,
    split, assumption,
    apply subset_inter _ hrbbol,
    intros y hy,
    simp [bola] at hy,
    apply hrabol,
    simp [bola],
    linarith,
  }

end

end metricos
