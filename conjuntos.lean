import data.set.basic
import tactic


open set

/-
# Introducción a Lean

Vamos a ver algunos ejemplos de cómo demostrar teoremas con Lean.

Los comentarios se encierran entre `/-` y `-/`, o en una línea después de `--`

la estructura básica del enunciado es:

`lemma nombre hipótesis : resultado := demostración`

la demostración generalmente se escribe es una secuencia de *tácticas* entre `begin`y `end`.

Si ponemos el cursor en un punto en el bloque de tácticas, vemos a la deerecha el estado de la demustración,
formada por uno o más objetivos. Para cada objetivo se ven las hipótesis que se dan por conocidas
(y los objetos involucrados), y debajo la tésis a probar.

Cada táctica cambia el estado del objetivo, según unas reglas. Al final, el objetivo debería quedar resuelto.

Vamos a ver algunos ejemplos:

En este vamos a ver que dos formas equivalentes de afirmar que dos afirmaciones implican
una tercera. Asumimos que `P`, `Q` y `R` son proposiciones
-/
lemma equivalencia_implicacion (P Q R : Prop) : (P ∧ Q → R) ↔ (P → Q → R) :=
begin
  split, -- como queremos demostrar una equivalencia, la separamos en dos implicaciones
  {   -- estas llaves las usamos para trabajar por separado en cada sub-objetivo
    intro h,  -- asumimos el antecedente como hipótesis, a la que llamaremos `h`
    intro hp,  -- asumimos que se cumple `P`, y a esa afirmación la llamamos `hp`
    intro hq,  -- asumimos que se cumple `Q`, y a esa afirmación la llamamos `hq`
    apply h, -- como queremos demostrar que  se cumple`R`, aplicamos una hipótesis que lo implica
    split,  -- hemos pasado a tener que demostrar algo de la forma `∧`, así que de nuevo lo separamos en dos
    {
      exact hp, -- tenemos una hipótesis que dice justo lo que queremos ver,
    },
    {
      exact hq,
    },
  },
  {
    intro h,
    intro h2,
    cases h2 with hp hq,  -- como tenemos una hipótesis de tipo `∧`, podemos separarla en dos
    apply h,
    {
      exact hp,
    },
    {
      exact hq,
    }
  }
end

-- Veamos otro ejemplo similar, pero con `∨`
lemma ejer_1 (P Q R : Prop) :  (P → Q) ∨ (P → R) → (P  → (Q ∨ R))  :=
begin
  intro h,   -- introducimos la hipótesis
  cases h,  -- al tener una hipótesis  de tipo `∨`, con `cases` separamos en dos casos posibles
  {
    intro hp,
    left,   -- si tenemos que demostrar un objetivo de tipo `∨`, con `left` decimos que vamos a ver la opción de la izquierda
    apply h,
    exact hp,
  },
  {
    intro hp,
    right,   -- con `right` decimos que vamos a demostrar la opción de la izquierda
    apply h,
    exact hp,
  },
end

/-
# Conjuntos

Los conjuntos en Lean son homogéneos: sus elementos tienen el mismo *tipo*. Podemos pensar
en el tipo como un "conjunto ambiente", dentro del cual consideramos subconjuntos.

Una táctica útil con conjuntos es `ext`. Aplica el principio de extensionalidad: dos conjuntos
son iguales si un elemento pertenece a uno si y sólo si pertenece al otro

Algunos ejemplos de cómo tratar con connuntos.
-/
lemma union_conmuta (X : Type) (A B : set X) : A ∪ B = B ∪ A :=
begin
  ext x, -- pasamos a ver que un elemento x pertenece a uno si y sólo si pertenece al otro.
  split,
  {
    intro h,
    cases h,  -- pertenecer a una unión de dos conjuntos es lo mismo que pertenecer a uno o al otro
    {         -- así que podemos usar `cases` en la hipótesis igual que con `∨`
      right, -- y podemos usar `left`o `right` en el objetivo
      exact h,
    },
    {
      left,
      exact h,
    }
  },
  {
    sorry,  -- esta tácica demuestra cualquier cosa, pero dejando el aviso de que no está realmente demostrado
    -- # Ejercicio:
    -- terminar este caso sin usar `sorry`
  }
end

/-
# Ejercicio:
Demostrar que la intersección también conmuta
Notar que, al igual que pertenecer a una unión es internamente una afirmación de tipo `∨`, pertenecer
a una intersección es de tipo `∧`.

-/
lemma interseccion_conmuta (X : Type) (A B : set X) : A ∩ B = B ∩ A :=
begin
  sorry,
end


/-
El conjunto formado por todos los elementos de un tipo se llama `univ`, y el formado por ninguno,
se llama `∅`. Como se usa el mismo nombre independientemente del tipo, Lean intenta deducir
a qué tipo nos estamos refiriendo, pero a veces se lo tenemos que especificar. Así, escribir
`(univ : set X)` se refiere al conjunto formado por todos los objetos de tipo `X`,
y `(∅ : set X)` se refiere al subconjunto de `X` formado por ningún elemento.


Vemos algunos ejemplos de lemas que luego usaremos

En este ejemplo, `contenido_sii_interseccion_compl_vacio` va a ser el nombre que le damos al lema.
Las hipótesis son que `X` es un tipo (o sea, un conjunto ambiente), y `U` y `V` son dos subconjuntos de `X`.

La tésis a demostrar es que `U` es un subconjunto de `V` si y sólo si la intersección entre `U`
y el complementario de `V` es el subconjunto vacío de `X`.
-/
lemma contenido_sii_interseccion_compl_vacio (X : Type) (U V : set X) : U ⊆ V ↔ U ∩ Vᶜ  = (∅ : set X):=
begin   -- vemos que hay que demostrar un si y sólo si
  split, -- con esta táctica, el objetivo de si y sólo si se separa en dos implicaciones.
  {     -- con las llaves, marcamos que vamos a trabajar en el primer objetivo
    intro h, -- tomamos el antecedente de la implicación como hipótesis
    ext x,   -- para demostrar la igualdad de conjuntos, aplicamos el principio de extensionalidad
    simp,    -- Lean incluye un simplificador de expresiones (usar con cuidado)
    apply h, -- aplicamos una de las hipótesis, que implica el resultado
  },
  {  -- ahora trabajamos en el segundo objetivo
    intro h, -- asumimos la hipótesis
    intro x,  -- sea x un elemento de X
    intro hx,  -- asumamos que x ∈ U
    by_contradiction hxv, -- lo vamos a demostrar por contradicción, supongamos la negación
    change x ∈ (∅ : set X),  -- por definición, que `x` esté en el conjunto vacío es falso
    rewrite ← h,      -- usamos la hipótesis h para reescribir el resultado
    split,   -- demostrar la pertenencia a una intersección también se puede separar en dos demostraciones
    {
      exact hx,  -- lo que hay que demostrar es exactamente una de las hipótesis
    },
    {
      exact hxv,  -- y la otra parte también
    },
  }
end

lemma union_contenida_union (X : Type) (A B C D : set X) (h1 : A ⊆ C) (h2 : B ⊆ D) : A ∪ B ⊆ C ∪ D :=
begin
  intros x hx,
  cases hx,
  {
    left,
    apply h1,
    exact hx,
  },
  {
    right,
    apply h2,
    exact hx,
  }
end

/-
# Uniones e intersecciones de familias

Si tenemos una familia de subconjuntos (es decir, algo del tipo `set (set X)` ),
la intersección de todos sus miembros se denota con `⋃₀`, y la unión de todos ellos
como `⋃₀`.

Veamos cómo son internamente estos conceptos:
-/
lemma ejer_2 (X : Type) (F : set (set X)) (x : X) : x ∈ ⋃₀ F ↔ ∃ (U ∈ F), x ∈ U :=
begin
  refl,    -- esta táctica comprueba que una igualdad se da **por definición**
end

lemma ejer_3 (X : Type) (F : set (set X)) (x : X) : x ∈ ⋂₀ F ↔ ∀  (U ∈ F), x ∈ U :=
begin
  refl,
end

/-
Si tenemos una hipótesis de tipo `∃`, la táctica `cases` nos la separa en dos partes:
el objeto cuya existencia nos asegura, y la propiedad que cumple dicho objeto.

Para demostrar un objetivo de tipo `∃`, podemos dar expresamente el objeto que existe,
con `use`,  y luego demostrar la propiedad que debe cumplir.


Una hipótesis de tipo `∀`, se puede aplicar a un caso concreto usando `specialize`.
Para demostrar un objetivo de este tipo, podemos usar `intro` para tomar un elemento
genérico y dmostrar la propiedad aplicada a ese elemento concreto.

Veamos ejemplos.
-/

lemma ejer_4 (X :Type) (F G: set (set X)) (hFG : F ⊆ G) : ⋃₀ F   ⊆ ⋃₀ G :=
begin
  intro x,
  intro hx,
  cases hx with U hU,    -- como estar en la unión es en el fondo un ∃, podemos usar `cases`
  cases hU with hFU hxU,
  use U,                 -- para demostrar que algo existe, usamos el conjunto S.
  split,
  {
    apply hFG,
    exact hFU,
  },
  {
    exact hxU,
  }
end

-- # Ejercicio
-- (pista: usar `intro` y `specialize` )
lemma ejer_5 (X :Type) (F G: set (set X)) (hFG : F ⊆ G) : ⋂₀ G   ⊆ ⋂₀ F :=
begin
  sorry,
end


-- Un subconjunto se puede dar por extensión (listando sus elementos entre llaves)
lemma interseccion_2_eq {X : Type}  ( U V : set X) : U ∩ V = ⋂₀ {U,V} :=
begin
  simp,  -- el simplificador es capaz de hacer esto
end

lemma union_2_eq {X : Type} ( U V : set X) : U ∪ V = ⋃₀ {U,V} :=
begin
  simp,
end

-- En este ejemplo vamos a ver cómo usar la inducción sobre conjuntos finitos
-- Esto se hace aplicando el lema `set.finite.induction_on` con la hipótesis de que el conjunto
-- es finito
-- `P` es una propiedad que puede ser cierta o no para cada subconjunto de `X`
-- `univ` es el subconjunto total
lemma propiedad_interseccion_finita (X : Type) (P : set X → Prop) (htot : P univ):
(∀ U V : set X, P U → P V → P (U ∩ V)) ↔ ∀ F : set (set X), set.finite F → F ⊆ P → P ⋂₀ F :=
begin
  split,  -- como antes, separamos una doble implicación en dos
  {
    intro h, -- asumimos la hipótesis
    intros F hFfin,  -- esto es lo mismo que `intro F, intro hFfin`
    apply set.finite.induction_on hFfin, -- aplicamos el principio de inducción
    {   -- primero hay que demostrar lo que queremos para el conjunto vacío
      simp,   -- que en este caso, es fácil
      exact htot,
    },
    {
      /-
        En el objetivo vemos que aparece `insert a s`, esto es el conjunto que se  obtiene al añadir
        al conjunto `s` el elemento `a`
      -/
      intros A S haS hSfin hSP hsIN,
      simp,
      apply h,
      {
        apply hsIN,
        simp,
      },
      {
        apply hSP,
        intros x hx,
        apply hsIN,
        simp,
        right,    -- podemos decir cual de las dos opciones queremos demostrar usando `left`o `right`
        exact hx,
      },
    },
  },
  {
    intro h,
    intros U V hU hV,
    specialize h {U,V},   -- `specialize` permite aplicar una hipótesis a un caso particular
    simp  at h,           -- algunas tácticas se pueden aplicar a hipótesis en ligar del objetivo, con `at`
    apply h,
    intros x hx,
    simp at hx,     -- cuando una hipótesis está formada de varias opciones, `cases` la separa en casos
                    -- si fuera un ∧, nos daría dos hipótesis en lugar de dos objetivos
    cases hx,
    {
      rw hx,
      exact hU,
    },
    {
      rw hx,
      exact hV,
    },
  }
end

/-
# Ejercicio:

Demostrar el análogo para uniones
-/

lemma propiedad_union_finita (X : Type) (P : set X → Prop) (htot : P ∅ ):
(∀ U V : set X, P U → P V → P (U ∪ V)) ↔ ∀ F : set (set X), set.finite F → F ⊆ P → P ⋃₀ F :=
begin

  split,
  {
    intro h2,
    intros F hF,
    --revert htot,
    apply set.finite.induction_on hF,
    {
      simp [htot],
    },
    {
      intros U S hU hSf hind,
      intros  hUS,
      specialize hind,
      simp only [sUnion_insert],
      apply h2,
      {
        apply hUS,
        simp only [mem_insert_iff, eq_self_iff_true, true_or],
      },
      {
        apply hind,
        refine subset_trans _ hUS,
        simp only [subset_insert],
      }
    }
  },
  {
    intro h,
    intros U V hU hV,
    specialize h {U,V},
    simp only [finite.insert, finite_singleton, sUnion_insert, sUnion_singleton, forall_true_left] at h,
    apply h,
    intros x hx,
    induction hx,
    {
      induction hx,
      exact hU,
    },
    {
      induction hx,
      exact hV,
    }
  }
end

lemma doble_contenido (X : Type) (A B : set X) (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B :=
begin
  ext,
  split,
  {
    intro h,
    apply h1,
    exact h,
  },
  {
    intro h,
    apply h2,
    exact h,
  }
end

lemma union_contenido (X : Type) (A B C : set X) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C :=
begin
  split,
  {
    intro h,
    split,
    {
      intros x hx,
      apply h,
      left,
      exact hx,
    },
    {
      intros x hx,
      apply h,
      right,
      exact hx,
    }
  },
  {
    intro h,
    cases h with hA hB,
    intros x hx,
    cases hx,
    {
      apply hA,
      exact hx,
    },
    {
      apply hB,
      exact hx,
    }
  }
end


lemma contenido_interseccion (X : Type) (A B C : set X) : A  ⊆ (B ∩ C) ↔ A ⊆ B ∧ A ⊆ C :=
begin
  split,
  {
    intro h,
    split,
    repeat  {
      intros x hx,
      specialize h hx,
      cases h with h1 h2,
      assumption,
    },
  },
  {
    intro h,
    cases h with hB hC,
    intros x hx,
    split,
    {
      apply hB hx,
    },
    {
      exact hC hx,
    }
  }
end

lemma contenido_en_union_izqda (X : Type) (A B : set X) : A ⊆ A ∪ B :=
begin
  intros x hx,
  left,
  exact hx,
end

lemma contenido_en_union_dcha (X : Type) (A B : set X) : B ⊆ A ∪ B :=
begin
  intros x hx,
  right,
  exact hx,
end


lemma interseccion_contenida_izda (X : Type) (A B  : set X) : (A ∩ B ) ⊆ A :=
begin
  intros x hx,
  cases hx with hx1 hx2,
  exact hx1,
end

lemma interseccion_contenida_derecha (X : Type) (A B  : set X) : (A ∩ B ) ⊆ B :=
begin
  intros x hx,
  cases hx with hx1 hx2,
  exact hx2,
end

