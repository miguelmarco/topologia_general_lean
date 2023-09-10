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
- Una aplicación `d` que toma dos elementos del conjunto, y da un número real, llamada *distancia*
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
( d2 : ∀ x y: X , d x y = 0 ↔ x = y)
( d3 : ∀ x y : X, d x y = d y x)
( d4 : ∀ x y z : X, d x z ≤ d x y + d y z )


open espacio_metrico

/-
## Ejemplo:

veamos que de hecho los reales tienen una estructura de espacio métrico:
-/
instance : espacio_metrico ℝ := 
{ d := λ x y, | x - y |,  -- definimos la función que da la distancia entre dos puntos
  d1 :=   -- y ahora vemos que cumple las propiedades
  begin
    intros x y,
    exact abs_nonneg (x - y),  -- estas propiedades ya están demostradas en la biblioteca, así que las usamos
  end,
  d2 := 
  begin
    intros x y,
    simp,
    split,
    {
      intro h,
      linarith,
    },
    {
      intro h,
      rw  [h],
      simp,
    },
  end,
  d3 := 
  begin
    intros x y,
    exact abs_sub_comm x y,
  end,
  d4 := 
  begin
    intros x  y z,
    exact abs_sub_le x y z,
  end 
}


-- a partir de ahora, supondremos que tenemos un espacio métrico llamado `X`
variables {X : Type} [espacio_metrico X]
-- esto es equivalente a añadir estas hipótesis implíctiamente en cada 
-- resultado que probemos

-- demostramos un lema sencillo y lo marcamos para que el simplificador lo use
-- automáticamente
@[simp] lemma distancia_cero (x : X) : d x x = 0 :=
begin
  rw d2, -- reescribiendo la propiedad d2 se convierte en algo trivial
end


/-
Definimos las bolas, discos y esferas
-/
def bola (x : X) (r : ℝ )  := {y : X | d x y < r}
def disco (x : X) (r : ℝ )  := { y : X | d x y ≤ r }
def esfera (x : X )(r : ℝ ) := {y : X | d x y = r}

/-
Para cada uno de estos conjuntos, probamos una caracterización de sus elementos
(es cierta por definición, pero puede ser útil para simplificar situaciones en el futuro)
-/
@[simp]  -- con esto marcamos que este lema se puede usar para simplificar automáticamente expresiones
lemma bola_carac (x y : X) (r : ℝ ) : y ∈ bola x r ↔ d x y < r :=
begin
  refl,
end

@[simp]  
lemma disco_carac (x y : X) (r : ℝ ) : y ∈ disco x r ↔ d x y ≤ r :=
begin
  refl,
end

@[simp]  
lemma esfera_carac (x y : X) (r : ℝ ) : y ∈ esfera x r ↔ d x y = r :=
begin
  refl,
end

/-
las bolas de un radio contienen a las bolas del mismo centro y radio menor
-/
lemma bola_radio_monotono {X : Type} [espacio_metrico X] (x : X)  (r1 r2 : ℝ ) (hr : r1 < r2) :
 bola x r1 ⊆ bola x r2 :=
begin 
  intros y hy,  -- tomamos un elemento de la bola de radio menor
  simp only [bola_carac] at *,  -- aquí es donde es útil el lema anterior
  linarith,  -- esta táctica automatiza el deducir (des)igualdades lineales
end

lemma bola_disjunta_esfera {X : Type} [espacio_metrico X] (x : X) (r : ℝ ) :
bola x r ∩ esfera x r = ∅ :=
begin
  ext y, -- veamos que un punto `y` está en un conjunto si y sólo si está en el otro
  split,  -- separamos la doble implicación en dos
  {
    intro h,  -- asumimos la premisa como hipótesis
    cases h with hb hs, -- la hipótesis se puede a su vez separar en dos
    simp only [bola_carac, esfera_carac] at *, -- usamos las caracterizaciones
    linarith,  -- la aritmética lineal me da la contradicción
  },
  {  -- ahora la otra implicación
    intro h, -- asumimos la hipótesis
    cases h, -- como la hipótesis no puede darse en ningún caso, no hay nada que demostrar 
  }
end

/-
Veamos una forma más rápida de demostrar esto mismo, usando algunas
cosas que Lean puede hacer automáticamente
-/
example  {X : Type} [espacio_metrico X] (x : X) (r : ℝ ) :
bola x r ∩ esfera x r = ∅ :=
begin
  ext y,  -- como antes, veamos que un `y` está en un conjunto sii está en el otro
  simp,  -- el simplificador reduce la expresión
  intro h, -- tomando la hipótesis, sólo hay que demostrar una desigualdad
  linarith, -- es consecuencia de la hipótesis
end


/-
Usemos este mismo enfoque de aprovechar lo que Lean pueda automatizar para ver otra igualdad
-/
lemma disco_es_esfera_mas_bola (x : X) (r : ℝ ) : disco x r = bola x r ∪ esfera x r :=
begin
  ext y,
  squeeze_simp, -- esto nos muestra exactamente qué lemas ha usado para simplificar
  --               haciendo click en la expresión que nos da, la sustituye

  /-
  Ahora hay que  demostrar que un número es menor o igual que otro sí y sólo si
  es menor o es igual.
  Esto tan básico debería estar demostrado ya, así que vamos a buscar si en la biblioteca
  hay algo así ya demostrado.
  -/

  library_search,   -- esto busca en la biblioteca de demostraciones un resultado que diga
  --                   justo lo que queremos demostrar
  --                    como antes, una vez encontrado, podemos hacer click y sustituir
end



lemma ej_1_1_6  (x y : X) (r : ℝ ): x ∈ bola y r ↔ y ∈ bola x r :=
begin
  simp only [bola_carac],  -- lo reescribimos en términos de distancias
  rw d3,                   -- y usamos la simetría de las distancias
end

lemma ej_1_1_6_b   (x y : X) (r : ℝ ): x ∉  bola y r ↔ y ∉ bola x r :=
begin
  rw ej_1_1_6,  -- símplemente, usamos el caso anterior
end

lemma ej_1_1_7  (M1 M2 : espacio_metrico X) (h : ∀ x y : X, @d X M1 x y ≤ @d X M2 x y) : ∀ x : X, ∀ ε > 0,  @bola X M2 x ε ⊆ @bola X M1 x ε  :=
begin
  intros x ε hε y hy,
  unfold bola at hy,
  simp at hy,
  unfold bola,
  simp,
  specialize h x y,
  calc           -- esta táctica permite encadenar (des)igualdades, demostrando cada paso por separado
    @d X M1 x y ≤ @d X M2 x y : by {exact h,}
    ...         < ε           : by {exact hy,}
end

lemma ej_1_1_8  (x y z : X) (r : ℝ ) (hz : z ∈ bola x r) (hy : y ∈ bola x r) :
d y z < 2 * r :=
begin
  simp only [bola_carac] at *,
  calc      
    d y z    ≤ d y x + d x z       : by {apply d4,}
    ...      = d x y + d x z       : by {rw d3,}
    ...      < r + r               : by {linarith,}
    ...      = 2 * r               : by {ring,}
end

lemma ej_1_1_12_1 (h : ∀ x y z : X, d x z ≤ max (d x y) (d y z)) : ∀ x y : X, ∀ ε > 0, x ∈ bola y ε → bola x ε = bola y ε :=
begin
  intros x y ε hε hx,
  unfold bola at hx,
  simp at hx,
  ext z,
  split,
  {
    simp [bola],
    intro hz,
    specialize h y x z,
    simp at h,
    cases h,
    {
      calc
        d y z ≤ d y x   : by {exact h,}
        ...   < ε        : by {exact hx,}
    },
    {
      linarith,
    }
  },
  {
    simp [bola],
    intro hz,
    specialize h x y z,
    simp at h,
    cases h,
    rw d3 at hx,
    repeat {linarith,},
  }
end

lemma ej_1_1_14 (X : Type) (M1 M2 : espacio_metrico X) : espacio_metrico X := 
{ d := λ x y, max (@d X M1 x y) (@d X M2 x y),
  d1 := begin
    intros x y,
    simp,
    left,
    apply d1,
  end,
  d2 := begin
    intros x y,
    rw max_eq_iff,
    split,
    {
      intro h,
      cases h,
      repeat
      {
        cases h with h1 h2,
        rw d2 at h1,
        exact h1
      },
    },
    {
      intro h,
      rw h,
      simp,
    }
  end,
  d3 := begin
    intros x y,
    rw @d3 X M1 x y,
    rw @d3 X M2 x y,
  end,
  d4 := begin
    intros x y z,
    rw max_le_iff,
    have h2 := le_max_left (@d X M1 x y) (@d X M2 x y),
    have h2' := le_max_right (@d X M1 x y) (@d X M2 x y),
    have h3 := le_max_left (@d X M1 y z) (@d X M2 y z),
    have h3' := le_max_right (@d X M1 y z) (@d X M2 y z),
    have hd4 := @d4 X M1 x y z,
    have hd4' := @d4 X M2 x y z,
    split,
    repeat 
    {
      linarith,
    },
  end }


/-
Un conjunto del espacio es un *entorno* de un punto si hay una bola centrada en el punto contenida en el 
conjunto
-/

def entorno  (x : X) (E : set X) := ∃ (r : ℝ) (hr : r > 0), bola x r ⊆ E


-- Trivialmente, una bola centrada en un punto es entorno del mismo
lemma bola_entorno_centro  (x : X) (r : ℝ ) (hr : r > 0) : entorno x (bola x r) :=
begin
  simp only [entorno, bola, gt_iff_lt, set_of_subset_set_of, exists_prop],
  use r,
  tauto,
end

-- los discos de radio positivo también son entornos de su centro
lemma disco_entorno_centro  (x : X) (r : ℝ ) (hr : r > 0) : entorno x (disco x r)  :=
begin
  use r,
  split,
  {
    exact hr,
  },
  {
    intros y hy,
    dsimp [bola] at hy,
    dsimp [disco],
    linarith,
  },
end

lemma entorno_superconjunto (x : X) (U V : set X) (hU : entorno x U) (hV : U  ⊆ V) : entorno x V :=
begin
  cases hU with r hr,
  cases hr with hrpos hrbol,
  use r,
  split,
  {
    exact hrpos,
  },
  {
    intros y hy,
    apply hV,
    apply hrbol,
    exact hy,
  }
end

/-
Un conjunto es abierto si es entorno de todos sus puntos
-/
def abierto (U : set X) := 
∀ x ∈ U, entorno x U

def abiertos  : set (set X) := abierto


/-
Las bolas son abiertas
-/
lemma bola_abierta (x : X) (r : ℝ ) (hr : r > 0) : abierto (bola x r) :=
begin
  intros y hy,
  dsimp [bola] at hy,
  use r - (d x y),
  split,
  {
    linarith,
  },
  {
    intros z hz,
    dsimp [bola] at *,
    have haux := d4 x y z,
    linarith,
  }
end

lemma complementario_disco_abierto (x : X) (r : ℝ ) : abierto (disco x r)ᶜ :=
begin
  intros y hy,
  simp [disco] at hy,
  use d x y - r,
  split,
  {
    linarith,
  },
  {
    intros z hz,
    simp [disco, bola] at *,
    have haux := d4 x z y,
    have haux := d3 y z,
    linarith,
  }
end

/-
El total es abierto
-/
lemma ab_total  : abierto (univ : set X) :=
begin
  intros x hx,
  use 1,
  simp only [set.subset_univ, gt_iff_lt, and_self, zero_lt_one],
end

/-
Otra forma equivalente de decirlo es que el total pertenece a la
familia de los abiertos
-/

lemma ab_total' : (univ : set X)  ∈  (abiertos : set (set X)):=
begin 
   exact ab_total,
end


/-
el vacío es abierto
-/
lemma ab_vacio : abierto ( ∅  : set X)  :=
begin
  tauto,  -- no hay nada que demostrar, porque no hay puntos
end


/-
La unión de una familia de abiertos, es abierto
-/
lemma ab_union (F : set (set X)) (hab : F ⊆ abiertos) : abierto ⋃₀ F  :=
begin
  intros x hx,           -- tomamos un punto en la union
  cases hx with U hU,    -- como está en la unión, está en uno de sus conjuntos, `U`
  cases hU with hUF hxU,
  specialize hab hUF,     -- como `F` está formada por abiertos, `U` lo es
  specialize hab x hxU,   -- y como `x` está en `U`, es un entorno
  cases hab with r hr,    -- o sea, que hay una bola intermedia
  cases hr with hrpos hrU,
  use r,                  -- esa misma bola va a estar en la unión
  split, assumption,
  intros z hz,
  specialize hrU hz,
  use U,
  tauto,
end

/-
La intersección de dos abiertos es abierto
-/
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

/-
La intersección de una familia finita de abiertos es abierto
-/
lemma ab_inter_finita (F : set (set X)) (hab : F ⊆ abiertos) (hf : set.finite  F ): abierto ⋂₀ F :=
begin
  apply finite.induction_on' hf,
  {
    simp,
    apply ab_total,
  },
  {
    intros U G hUF hGF hUG hGab,
    simp,
    apply ab_inter,
    {
      apply hab,
      exact hUF,
    },
    {
      apply hGab,
    }
  }
end


-- un conjunto es entorno de un punto si y sólo si hay un abierto intermedio 
theorem entorno_sii_abierto_intermedio (x : X) (V : set X) : entorno x V ↔ ∃ (U : set X), (abierto U ∧ x ∈ U ∧ U ⊆ V) :=
begin
  split,
  {
    intro h,
    cases h with r hr,
    cases hr with hrpos hrbol,
    use bola x r,
    split,
    {
      apply bola_abierta,
      exact hrpos,
    },
    split,
    {
      simp [bola],
      linarith,
    },
    {
      exact hrbol,
    },
  },
  {
    intro h,
    cases h with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUV,
    specialize hUab x hxU,
    apply entorno_superconjunto,
    {
      exact hUab,
    },
    {
      exact hUV,
    }
  }
end



/-
## Ejercicios
-/

lemma ejercicio_1_2_1 (A B : set ℝ ) (h : abierto A) : abierto  { (x + y) | (x ∈ A) (y ∈ B) } := 
begin
  sorry,
end


-- para este ejetrcicio, pueden ser útiles estos lemas ya demostrados:
-- `le_abs_self` : ∀ (a : ℝ ), a ≤ |a|
-- `abs_sub_comm` : ∀ (a b : ℝ ), |a - b| = |b - a|
-- 
lemma ejercicio_1_2_2 (a b : ℝ ) (h : a < b) : abierto {x | a < x ∧ x < b } :=
begin
  sorry,
end

lemma ejercicio_1_2_3 (X : Type) (S : set X) [espacio_metrico X] : 
 abierto {x : X | entorno x S } :=
begin
  sorry,
end

end metricos
