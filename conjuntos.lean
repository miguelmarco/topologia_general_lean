import tactic
 
/-!

# Conjuntos en Lean

En Lean los conjuntos son siempre homogéneos, es decir: todos sus elementos
tienen el mismo tipo. Podemos pensar en la situación en que tenemos un universo de objetos
(el tipo), y dentro de ese universo, tenemos subconjuntos.

Para un tipo  `X : Type`, el tipo de los subconjuntos de `X` se llama `set X`.

Un objeto del tipo `set X` se puede interpretar de tres formas distintas
1) Un conjunto cuyos elementos tienen tipo `X`
2) Un subconjunto de  `X`;
3) Una función de `X` a `Prop` (es decir, la propiedad de estar o no en el conjunto)

Notar que `X` es un tipo, pero un conjunto `A` es un término de tipo `set X`.
Es decir `a : A` no tiene sentido, ya que el tipo de `a` sería `X`.
Lo que tiene sentido es  `a : X` y `a ∈ A`. 
`a ∈ A` es cierto o falso, así que el tipo de  `a ∈ A` es `Prop`. 
-/


open set  -- así podemos usar cosas como `univ` en lugar de `set.univ`

-- dos conjuntos son iguales si y sólo si los elementos de uno son del otro y viceversa
-- esto en particular, permite demostrar el principio del doble contenido
lemma doble_contenido {X : Type} (A B : set X) (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B :=
begin
  ext x,  -- tomamos un elemento, y veamos que esté en A sii está en B
  split,  -- separamos en dos implicaciones
  {
    intro hx,  -- asumimos la hipótesis de la implicación
    specialize h1 hx,  -- como `A ⊆ B`, un elemento de `A` está en `B`.
    exact h1,
  },
  {
    intro hx,  -- ahora vamos a usar otro enfoque:
    apply h2,  -- en lugar de especializar la hipótesis, vamos "hacia atrás" desde la tésis
    exact hx,
  }
end

-- por definición, siempre es falso que un elemento pertenezca al vacío
lemma vacio_defin {X : Type} : (∅ : set X) = {x : X | false} :=
begin
  refl,  -- la táctica `refl` comprueba que una igualdad se cumple por definición
end

-- el subconjunto formado por todos los elementos de `X` se llama `univ`.
-- por definición, todos los elementos de tipo `X` pertenecen a `univ`
lemma total_defin {X : Type} : (univ : set X) = {x : X | true} :=
begin
  refl,
end

-- por definición, un elemento está en la intersección de dos conjuntos si y sólo si 
-- está en ambos
lemma inter_defin {X : Type} (A B : set X) : A ∩ B = {x: X | x ∈ A ∧ x ∈ B} :=
begin
  refl,
end

-- por definición, el complementario de un conjunto está formado por los elementos que no
-- le pertenecen ( el símbolo ᶜ se consigue con \^c )
lemma compl_defin {X : Type} (A : set X ) : Aᶜ = {x : X | x ∉ A} :=
begin
  refl,
end

-- el complemento del total es el vacío
lemma compl_total {X : Type} : (univ : set X)ᶜ = ∅  :=
begin
  simp only [set.compl_univ, eq_self_iff_true],  
  -- la táctica `simp` simplifica 
  -- (usando resultados anteriores o en la biblioteca)
  -- usa los resultados que le pasemos entre corchetes,
  -- y los que estén marcados como @[simp]
end  

@[simp]
lemma complemento_union {X : Type} (A B : set X) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ :=
begin
  ext x,
  simp [compl_defin],
  push_neg,
  refl,
end


@[simp]
lemma complemento_interseccion {X : Type} (A B : set X) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ :=
begin
  ext x,
  simp [compl_defin],
  split,
  {
    intro hx,
    by_cases hA :x ∈ A,
    {
      right,
      apply hx,
      exact hA,
    },
    {
      left,
      exact hA,
    }
  },
  {
    intro hx,
    intro hxA,
    cases hx,
    {
      by_contra,
      apply hx,
      exact hxA,
    },
    {
      exact hx,
    }
  }
end



-- un conjunto `A` es el vacío si y solo si es falso que cualquier
-- elemento le pertenezca
lemma conjunto_vacio_sii_todo_elemento_no {X : Type} (A : set X) :
 A = ∅ ↔ ∀ x : X, ¬(x ∈ A) :=
begin
  split,
  {
    intro h,  -- cuando tenemos que probar una implicación, `intro` nos permite tomar
    -- el lado izquierdo como hipótesis, y pasar a probar el lado detrecho 
    intro x, -- también cuando hay que probar algo de la forma ∀, nos permite tomar un 
    -- elemen to cualquiera, y probar el enunciado para ese elemento concreto
    rewrite h,  -- se puede usar una igualdad que tenemos como cierta para reescribir
    -- partes del resultado
    change ¬false, 
     -- la táctica `change` cambia el objetivo por algo que sea igual por definición 
    simp only [not_false_iff],
  },
  {
    intro h,
    ext, -- el principio de extensionalidad
    -- dice que dos conjuntos son iguales si un elemento pertenece a uno si y sólo si
    -- pertenece al otro. También sirve para probar, por ejemplo, igualdad de funciones 
    split, -- si hay un objetivo que está formado de varias partes (como por ejemplo, un ∧ ),
    -- `split` nos permite separarlo en varios objetivos, y trabajar cada uno por separado
    {
      intro hx,
      specialize h x, -- esto aplica una hipótesis a un caso concreto
      --simp,
      exact h hx, -- `exact` demuestra el resultado dando algo que es exactamente igual,
      -- en este caso, h aplicado a hx nos da una contradicción (que, resulta ser el objetivo)
    },
    {
      intro h,
      cases h, -- `cases` separa una hipótesis en sus partes.
      -- si es una hipótesis de tipo ∧, la separa en dos hipótesis
      -- si es de tipo ∨, separa en dos objetivos, para cada uno de los casos
      -- si es imposible, demuestra que el caso en el que estamos no se puede dar
      -- si es de tipo ∃, nos da el objeto que existe, y la propiedad que cumple 
    }
  }
end

@[simp]
lemma no_vacio_sii_existe_elemento {X : Type} (A : set X) : A ≠ ∅ ↔ ∃ x, x ∈ A :=
begin
  simp [conjunto_vacio_sii_todo_elemento_no],
end

-- dos conjuntos son disjuntos si y solo si uno está contenido en el complemento del otro:
lemma disjuntos_sii_contenido_en_complemento {X : Type} (A B : set X):
A ∩ B =  ∅ ↔ A ⊆ Bᶜ :=
begin
  rw conjunto_vacio_sii_todo_elemento_no,
  split,
  {
    intro h, 
    intros x, dsimp,
    intro ha, 
    by_contradiction hb,  -- si queremos demostrar algo por reducción al absurdo,
    -- `by_contradiction` asume la negación del resultado como hipótesis,
    -- y pasamos a demostrar `false` (es decir, que hay contradicción)
    specialize h x,
    apply h,
    split,
    exact ha, exact hb,
  },
  {
    intro h,
    intro x,
    by_contradiction h2,
    cases h2 with ha hb,
    specialize h ha,
    exact h hb,
  }
end




example {X : Type} ( A B : set X) : A ⊆ B ↔ A ∪ B = B :=
begin
 split,
 {
  intro h,
  ext,
  split,
  {
    intro h2,
    cases h2,
    {
      apply h,
      exact h2,
    },
    {
      exact h2,
    },
  },
  {
    intro h2,
    right,  -- si tenemos que probar un ∨, decidimos si probamos el lado izquierdo o el derecho
    exact h2,
  },
 },
 {
  intro h,
  rewrite ←h,
  intro x,
  intro hx,
  left,   
  exact hx,
 }
end



example {X : Type} (A B : set X) : A ⊆ B ↔ A ∩ B = A :=
begin
  sorry,
end

example {X : Type} (A B C : set X) : A ⊆ B → B ⊆ C → A ⊆ C :=
begin
  sorry,
end

example {X : Type} (A B C : set X) : A ⊆ B ∧ A ⊆ C → A ⊆ B ∩ C :=
begin
  sorry,
end

example {X : Type} (A B C : set X) : A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C :=
begin
  sorry,
end



/-

## Uniones e intersecciones de familias

Fijado un tipo `X`, si tenemos dos conjuntos `U` y `V`, las operaciones `∪` y `∩` (\cup y \cap
o \union y \inter respectivamente) operan entre ellos y producen un nuevo conjunto en el mismo tipo.

Sin embargo, a veces queremos tomar la unión o intersección de una familia más amplia de conjuntos.
Es decir, dada una familia `F : set (set X)` podemos tomar `⋃₀ F` (\Union\0)  la unión de todos
sus elementos. También podemos tomar `⋂₀ F` ( \Inter\0) la intersección de todos ellos.

Los símbolos `⋃₀` y `⋂₀` son notaciones para las operaciones `sUnion` y `sInter`.
-/

example (X : Type) (F : set (set X)) : ⋃₀ F = { x : X | ∃ U ∈ F, x ∈ U} :=
begin
  refl,
end

example (X : Type) (F : set (set X)) : ⋂₀ F = { x : X | ∀ U ∈ F, x ∈ U} :=
begin
  refl,
end

example (X : Type) ( F : set (set X)) (x : X) : x ∈ ⋂₀ F ↔ ∀ U ∈ F, x ∈ U :=
begin
  refl,
end


-- la union de  de una familia es el complementario de las intersecciones de los complementarios
@[simp]
lemma union_familia_es_complementario_de_interseccion_complementarios 
      {X : Type} (F : set (set X)) :
      (⋂₀ (compl '' F))ᶜ  = ⋃₀ F :=   -- veremos luego por qué `compl '' F` es el conjunto de los complementarios
begin
  -- por doble contenido. tomamos un elemento arbitrario
  ext,
  split,
  { 
    intro h,  --suponiendo que está en el complementaro de la intersección
    dsimp at *,  -- `dsimp` simplifica usando sólo definiciones
    push_neg at h,  -- `push_neg` "mete" negaciones dentro de cuantificadores
    cases h with U hU,  -- desgajamos ahora las hipótesis en sus componentes
    cases hU with hU1 hU2,
    cases hU1 with V hV,
    cases hV with hV1 hV2, -- El conjunto que buscamos es V
    use V,
    split,
    {   -- está en F por hipótesis
      assumption,
    },
    rw ← hV2 at hU2, -- tenemos que usar que U es el complementario de V
    simp  at hU2,  -- no estar en el complementario de V
    -- es lo mismo que estar en V
    exact hU2,
  },
  { -- veamos el otro contenido
    -- suponiendo que está en la unión
    intro h,
    -- quiere decir que hay algún conjunto de la familia en el que está el elemento
    dsimp at h,  -- `dsimp` simplifica usando sólo igualdades por definición 
    cases h with S hS,
    cases hS with SF xS,

    -- supongamos que x está en la intersección de los complementarios, y demostramos que hay contradicción
    intro hn, 
    
    -- como hemos supuesto que x está en la intersección, en particular está en el complemento de S
    specialize hn Sᶜ ,
    -- veamos que el complemento de S está en la familia de los complementos de F
    have haux : Sᶜ ∈ compl '' F,
    {
      -- concretamente, es el complemento de S
      use S,
      split,
      exact SF,
      refl,
    },
    -- como consecuencia, x está en el complementario de S
    specialize hn haux,
    -- y eso nos da la contradicción
    apply hn,
    exact xS,
  },
end

-- Este caso anterior es un buen ejemplo de la potencia de las herramientas automáticas

example {X : Type} (F : set (set X)) :  (⋂₀ (compl '' F))ᶜ = ⋃₀ F  := 
begin
  ext,
  simp,
end 

/-
Se pueden definir también conjuntos por extensión, es decir, listando sus elementos.

Esto se hace con la sintaxis `{x1, x2, x3}`. Internamente, estos conjuntos están creados
empezando con un `singleton` (un conjunto que tiene un único elemento), y sobre
ese conjunto ir realizando la operación `insert` (agregar un elemento a un conjunto)

-/


@[simp]
lemma union_familia_dos_conjuntos (X : Type) (A B : set X) :  ⋃₀ {A,B} = A ∪ B :=
begin
  unfold insert,
  unfold singleton,
  dsimp,
  ext,
  split,
  {
    intro h,
    cases h with U hu,
    cases hu with hU1 hU2,
    cases hU1,
    {
      left,
      rw ← hU1,
      exact hU2,
    },
    {
      right,
      rw ← hU1,
      exact hU2,
    },
  },
  {
    intro h,
    cases h,
    {
      use A,
      split,
      {
        dsimp,
        left,
        refl,
      },
      {
        exact h,
      },
    },
    {
      use B,
      split,
      {
        right,
        refl,
      },
      {
        exact h,
      },
    }
  },
end

-- de nuevo, veamos la potencia de Lean (no es normal tener tanta suerte)

@[simp]
lemma interseccion_familia_dos_conjuntos (X : Type) (A B : set X) :  ⋂₀ {A,B} = A ∩ B :=
begin
  ext,
  simp,
end

/-
## Conjuntos y funciones

Si tenemos una función entre dos tipos `f : X → Y`, actúa también sobre los conjuntos.

En particular:

- Dado un `V : set Y`, la preimagen es `f ⁻¹' V`
- Dado un `U : set Y`, la imagen es `f '' U`
- La imagen de todo el conjunto es `range f`


Las uniones e interseciones parametrizadas se dan como funciones que devuelven conjuntos.
Es decir, si tenemos alguna función `f : X → set Y`, tomar todos la unión de todos los conjuntos
de la forma `f x` se hace mediante la expresión `⋃ (x : X), (f x)`. Análogamente para la intersección.

También se puede hacer recorriendo sólo un subconjunto `S` de `X`, escribiendo `⋂ (x : X) (hx : x ∈ S), f x`

-/

example (X Y : Type) (f : X → Y) (V : set Y) : f ⁻¹' V = {x : X | f x ∈ V} :=
begin
  refl,
end

example (X Y : Type) (f : X → Y) (U : set X) : f '' U = {y : Y | ∃ x : X, x ∈ U ∧  f x = y} :=
begin
  refl,
end

example (X Y : Type) (f : X → Y) : range f = {y : Y | ∃ x : X, f x = y} :=
begin
  refl,
end

example (X Y : Type) (f : X → Y) : range f = f '' univ :=
begin
  simp only [set.image_univ],
end


example (X Y : Type) (f : X → set Y) : ⋃₀ range f = ⋃ (x : X), f x :=
begin
  refl,
end


example (X Y : Type) (f : X → set Y) (S : set X) : (⋂ (x : X) (hx : x ∈ S), f x) = {y : Y | ∀ x ∈ S, y ∈ f  x } :=
begin
  ext y,
  simp only [iff_self, set.mem_Inter, set.mem_set_of_eq],
end


-- ### Ejercicios

-- la imagen es monótona

lemma subconjunto_imagen { X Y : Type} {f  : X → Y} (U V : set X) (huv : U ⊆ V) :
f '' U ⊆ f '' V :=
begin
  sorry,
end

-- y la preimagen también

lemma subconjunto_preimagen { X Y : Type} {f  : X → Y} (U V : set Y) (huv : U ⊆ V) :
f  ⁻¹' U ⊆ f ⁻¹' V :=
begin
  sorry,
end

-- La unión de las imágenes es la imagen de la unión

lemma imagen_union (X Y : Type) (f : X → Y) (U V : set X) : f '' (U ∪ V) = (f '' U) ∪ (f '' V ) :=
begin
  ext y,
  split,
  {
    intro h,
    unfold image at h,
    rcases h with ⟨x ,⟨hxu,hxy ⟩ ⟩ ,
    cases hxu,
    {
      left,
      dsimp,
      use x,
      exact ⟨ hxu,hxy⟩,
    },
    {
      right,
      use x,
      exact ⟨hxu,hxy⟩,
    },
  },
  {
    intro h,
    cases h,
    {
      exact subconjunto_imagen  U _ (subset_union_left U V) h,
    },
    {
      exact subconjunto_imagen  V _ (subset_union_right U V) h,
    }
  }
end

lemma imagen_union_familia (X Y : Type) (f : X → Y) (F : set (set X)) : f '' ⋃₀ F = ⋃₀ {V : set Y | ∃ U ∈ F, V = f '' U} :=
begin
 sorry,
end




-- SI una familia está contenida en otra, su unión está contenida en la unión de la otra

lemma union_familia_contenida (X : Type) (F G : set (set X)) (h : F ⊆ G) :
⋃₀ F ⊆ ⋃₀ G :=
begin
  sorry,
end


-- y con las intersecciones ocurre al revés


lemma interseccion_familia_contenida (X : Type) (F G : set (set X)) (h : F ⊆ G) :
⋂₀ G ⊆ ⋂₀ F :=
begin
  sorry,
end






-- La imagen de la intersección está contenida en intersección de las imágenes

lemma imagen_interseccion (X Y : Type) (f : X → Y) (U V : set X) : f '' (U  ∩ V ) ⊆  (f '' U) ∩  (f '' V ) :=
begin
  sorry,
end

lemma imagen_interseccion_familia (X Y : Type) (f : X → Y) (F : set (set X)) : f '' ⋂₀ F ⊆ ⋂₀ {V : set Y | ∃ U ∈ F, V = f '' U} :=
begin
  sorry,
end

-- La intersección de las preimagenes es la preimagen de la intersección

lemma preimagen_interseccion (X Y : Type) (f : X → Y) (U V : set Y) : f ⁻¹' (U  ∩ V ) = (f ⁻¹' U) ∩ (f ⁻¹' V )  :=
begin
  sorry,
end


lemma preimagen_interseccion_familia (X Y : Type) (f : X → Y) (F : set (set Y)) : f ⁻¹' (⋂₀ F ) = ⋂ (V : set Y) (hV: V ∈  F), f ⁻¹' V :=
begin
  sorry,
end

lemma preimagen_interseccion_familia' (X Y : Type) (f : X → Y) (F : set (set Y)) : f ⁻¹' (⋂₀ F ) = ⋂₀ { (f ⁻¹' V) | V ∈ F} :=
begin
  sorry,
end



-- La unión de las preimagenes es la imagen de la unión

lemma preimagen_union (X Y : Type) (f : X → Y) (U V : set Y) :  f ⁻¹' (U  ∪ V ) = (f ⁻¹' U) ∪ (f ⁻¹' V ) :=
begin
  sorry,
end

lemma preimagen_union_familia (X Y : Type) (f : X → Y) (F : set (set Y)) : f ⁻¹' (⋃₀ F ) = ⋃ (V : set Y) (hV: V ∈  F), f ⁻¹' V :=
begin
  sorry,
end

lemma preimagen_union_familia' (X Y : Type) (f : X → Y) (F : set (set Y)) : f ⁻¹' (⋃₀ F ) = ⋃₀ {(f ⁻¹' V) | V ∈  F} :=
begin
  sorry,
end

-- relación entre la imagen de la preimagen de un conjunto, y el conjunto
lemma imagen_preimagen_contenida (X Y : Type) (f : X → Y) (V : set Y) : f '' (f ⁻¹' V ) ⊆ V :=
begin
  sorry,
end

-- relación entre un conjunto, y la preimagen de su imagen
lemma contenido_en_preimagen_imagen (X Y : Type) (f : X → Y) (U : set X) :
U ⊆ f ⁻¹' (f '' U) :=
begin
  sorry,
end 

/-
Algunas fórmulas con uniones e intersecciones
-/

variables (X : Type) (A B C : set X)

example : A ∪ A = A :=
begin
  sorry
end

example : A ∩ A = A :=
begin
  sorry
end

example : A ∩ ∅ = ∅ :=
begin
  sorry
end

example : A ∪ univ = univ :=
begin
  sorry
end

example : A ⊆ B → B ⊆ A → A = B :=
begin
  sorry
end

example : A ∩ B = B ∩ A :=
begin
  sorry
end

example : A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
begin
  sorry
end

example : A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
  sorry
end

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
  sorry,
end

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  sorry,
end

/-
# Subconjuntos como tipos

Hemos visto que lo que en matemáticas habitualmente llamamos conjuntos, en Lean corresponden a tipos,
y los subconjuntos de estos tipos son de una naturaleza distinta. Sim embargo, en ocasiones 
podemos querer considerar un suconjunto de un tipo, como un tipo en sí mismo (por ejemplo, 
para definir una función en él). La forma de hacerlo es definiendo un subconjunto `S`
a un tipo `↥S` (el símbolo ↥ se consigue tecleando \u-| )

Si `S` es un subconjunto del tipo `X`, los objetos de tipo `↥S` constan de dos partes:
- un objeto `x` de tipo `X`
- un objeto `hx` de tipo `x ∈ S` (es decir, una demostración, o garantía de que `x` es un elemento de `S`)
 
 y se escribe de la forma `⟨x,h⟩` (los símbolos `⟨` y `⟩` se escriben con \< y \>  )

 Si tenemos un objeto `y` de tipo `↥S`, sus dos componentes (el objeto del tipo ambiente, y la 
 demostración de que está en el subconjunto), podemos recuperarlas usando `y.1`y `y.2` o con la 
 táctica `cases`.

 Además hay automáticamente una función de `↥S` a `X` (la inclusión). Dado un elemento `x : ↥S`,
 el correspondiente elemento de `X` se denota con `↑x` (el símbolo ↑ se obtiene con \u- )

-/

-- Ejemplo: construimos la aplicación inclusión entre dos conjuntos encajados.

example (X : Type) (U V : set X) (h : U ⊆ V) : ∃ i : ↥U → ↥V , ∀ x : U, (x : X) = (i x) :=
begin
  let  i : ↥U → ↥V,
  {
    intro x,
    cases x with x1 x2,
    fconstructor,
    use x1,
    apply h x2,
  },
  use i,
  intro x,
  cases x with xv xp,
  refl,
end 


/-
Así como los conjuntos se pueden definir usando la notación `{x : X | P x}`, los correspondientes
tipos se pueden construir usando `{x : X // P x}`
-/

example (X : Type) (P : X → Prop) : ↥{x : X | P x} = {x : X // P x} :=
begin
  refl,
end

/-
## Conjuntos finitos

Si queremos probar una propiedad sobre conjuntos finitos, podemos
hacerlo por inducción: primero demostramos que la propiedad se cumple
para el conjunto vacío, y luego que si se cumple para un conjunto,
se cumple también si le añadimos un elemento más.
-/

lemma imagen_insert (X Y : Type) (f : X → Y) (S : set X) (a : X) :
{y : Y | ∃ x ∈ (insert a S), f x = y} = insert (f a) {y : Y | ∃ x ∈ S, f x = y } :=
begin
  ext y,
  simp,
  split,
  {
    intro h,
    cases h with x hx,
    cases hx with hx1 hxy,
    cases hx1,
    {
      left,
      rw ← hx1,
      rw hxy,
    },
    {
      right,
      use x,
      tauto,
    }
  },
  {
    intro h,
    cases h,
    {
      use a,
      tauto,
    },
    {
      cases h with x hx,
      use x,
      tauto,
    }
  }
end

lemma familia_parametrizada_finita (X Y: Type) (S : set X) (h : set.finite S) (f : X → Y) :
set.finite { y : Y | ∃ x ∈ S,  f x = y } :=
begin
  apply set.finite.induction_on h,
  {
    simp,
  },
  {
    intros a s ha hs hind,
    rw imagen_insert,
    apply finite.insert,
    exact hind,
  }
end

