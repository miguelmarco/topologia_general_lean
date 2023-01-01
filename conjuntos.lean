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


-- La intersección de dos conjuntos se denota con `U ∩ V`, mientras que la intersección de 
-- todos los miembros de una familia, se denota con `⋃₀`.
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

lemma propiedad_union_finita (X : Type) (P : set X → Prop) (htot : P ∅ ): 
(∀ U V : set X, P U → P V → P (U ∪ V)) ↔ ∀ F : set (set X), set.finite F → F ⊆ P → P ⋃₀ F :=
begin
  split,
  {
    intros h F hFfin,
    apply set.finite.induction_on hFfin,
    {
      simp only [empty_subset, sUnion_empty, forall_true_left, htot],
    },
    {
      intros A S hAS hSfin hSP hASP,
      simp only [set.sUnion_insert],
      apply h,
      {
        apply hASP,
        simp only [set.mem_insert_iff, true_or, eq_self_iff_true],
      },
      {
        apply hSP,
        intros x hx,
        apply hASP,
        right,
        exact hx,
      }
    }
  },
  {
    intros h U V hU hV,
    rw union_2_eq,
    apply h,
    {
      simp only [finite.insert, finite_singleton],
    },
    {
      intros x hx,
      cases hx,
      {
        rw hx,
        assumption,
      },
      {
        simp only [set.mem_singleton_iff] at hx,
        rw hx,
        exact hV,
      }
    }
  }
end

