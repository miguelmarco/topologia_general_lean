import tactic


/- 
# Proposiciones en Lean

Una proposición representa una afirmación que puede ser cierta o falsa.

Por ejemplo, `(P : Prop)` quiere decir que con la letra `P` vamos a representar una 
cierta afirmación.

Para una proposición `P`, podemos tener (o no) la certeza de que es cierta, (porque contamos
 con una demostración de la misma,  o porque la asumimos como hipótesis). 
 
 Esto se escribe como `(h : P)`. Ahí estamos diciendo que h es una demostración de `P`.


 # Implicaciones

 Una implicación `P → Q`  (el símbolo → se puede obtener tecleando \to  \->  o \r ) 
 representa el hecho de que "si `P` es cierta, entonces `Q` también lo es".
 También puede interpretarse como una función, que dada una demostración para `P`,
 produce una demostración para `Q`.
-/

-- Ejemplo: vamos a demostrar un ejemplo muy básico: si sabemos que `P` es cierta
-- podemos demostrar que `P` es cierta:

-- para ello se puede usar la táctica `exact`

example (P : Prop) (h : P) : P :=
begin
  exact h,
end


-- Otra forma de escribir el "mismo" resultado sería con una implicación.
-- Como el objetivo es `P → P` debemos describir una función que tome una 
-- demostración de `P` y nos devuelva otra también de `P`. Lo más simple
-- es considerar la identidad. Para describir es función debemos tomar 
-- el argumento de la misma (en este caso `hp`) con la táctica `intro` 
-- y construir su salida como antes

example (P : Prop) : P → P :=
begin
  intro hp,       -- tomamos el 'input'
  exact hp,       -- devolvemos la misma cosa
end


-- Otro ejemplo en la misma línea.  Si queremos demostrar una implicación, 
-- podemos tomar la premisa como hipótesis, y demostrar la tesis. Para ello 
-- se usa la táctica `intro`. 
-- Es algo tautológico, ya que, estamos asumiendo `Q`

example (P Q : Prop) (hq : Q) : P → Q :=
begin
 intro hp,
 exact hq,
end


-- La táctica `apply` se puede usar cuando tenemos como hipótesis una implicación `h`
-- que implica nuestro objetivo. Al usarla, el objetivo cambia y pasamos a tener que
-- demostrar la premisa de `h`

example (P Q : Prop) (hI : P → Q) (hp : P) : Q :=
begin
  apply hI,
  exact hp,
end


-- La táctica `split` divide un objetivo que consiste de dos afirmaciones, en dos 
-- objetivos separados

example (P : Prop) : P ↔ P :=
begin
  split,
  {
    intro h,
    exact h,
  },
  {
    intro h,
    exact h,
  }
end


-- Sirve tanto para dobles implicaciones como para conjunciones

example (P : Prop) : P → (P ∧ P) :=
begin
  intro h,
  split,
  {
    exact h,
  },
  {
    exact h,
  }
end


-- Si tenemos que demostrar una disyunción, tenemos que usar `left` o `right` para decidir
-- cual de los dos lados vamos a demostrar

example (P Q : Prop) : P → P ∨ Q :=
begin
  intro h,
  left,
  exact h,
end

example (P Q : Prop) : Q → P ∨ Q  :=
begin
  intro h,
  right,
  exact h,
end


-- Si tenemos una hipótesis que consiste de varias afirmaciones, `cases` nos la separa en varias
-- hipótesis. Si la hipótesis es una disyunción, nos separa el objetivo en varios casos

example (P  Q : Prop) (h : P ∧ Q) : Q :=
begin
  cases h with h1 h2,
  exact h2,
end

example (P Q : Prop) (h : P ∨ Q ) : P ∨ Q :=
begin
  cases h,
  {
    left,
    exact h,
  },
  {
    right,
    exact h,
  }
end


-- Si tenemos una hipótesis de implicación `h : P → Q`, y otra que nos da la premisa, `hp : P`,
-- podemos convertir la primera en una del consecuente con `specialize` 
example  (P Q : Prop) (h : P → Q) (hp : P) : Q :=
begin
  specialize h hp,
  exact h,
end


/-Negar una poposición es lo mismo que afirmar que esa proposición implica una contradicción,
 es decir `¬P` (tecleado con `\not`) es lo mismo que `P → false`.

Si tenemos que demostrar `⊢ false`, tendremos que aplicar alguna hipótesis que sea una negación
-/

example (P Q : Prop) (h : P → Q) : ¬Q →  ¬P :=
begin
  intro hnq,
  intro hp,
  apply hnq,
  apply h,
  exact hp,
end

/-
`false` es  una proposición que no se puede dar en ningún caso. Si la tenemos una hipótesis `h : false`,
 podemos demostrar cualquier cosa haciendo `cases h`, ya que los casos en que se puede dar `h`
 no existen.
-/
example (P : Prop) (h : false) : P :=
begin
  cases h,
end




/-
# Ejercicios
-/

variables p q r s: Prop -- así no tenemos que poner (p : Prop) (q : Prop)... en cada definición 

/- 
## Demuestra la conmutatividad de ∧ y ∨ 
p ∧ q ↔ q ∧ p 
p ∨ q ↔ q ∨ p 
-/




/- 
## Demuestra la asociatividad de  ∧ y  ∨
(p ∧ q) ∧ r ↔ p ∧ (q ∧ r) 
(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
-/

/- 
## Demuestra la distributividad de ∧ respecto de ∨ y viceversa
p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) 
-/


/-
## Demuestra las siguientes propiedades

(p → (q → r)) ↔ (p ∧ q → r) 
((p ∨ q) → r) ↔ (p → r) ∧ (q → r) 
¬(p ∨ q) ↔ ¬p ∧ ¬q 
¬p ∨ ¬q → ¬(p ∧ q) 
¬(p ∧ ¬p) 
p ∧ ¬q → ¬(p → q) 
¬p → (p → q) 
(¬p ∨ q) → (p → q) 
p ∨ false ↔ p 
p ∧ false ↔ false 
-/

/-
## Algunas demostraciones que requieren razonamiento clásico

Estas demostraciones requieren usar algunas tácticas nuevas:

- `by_contradiction` asume la negación del objetivo, y tenemos que demostrar una contradicción
- `by_cases`  h : P crea dos nuevos contextos: uno en el que tenemos que demostrar el objetivo
  suponiendo P, y otro en el que tenemos que demostrarlo suponiendo ¬ P
- `push_neg` "mete las negaciones" en una expresión. Por ejemplo cambia ¬ (P ∧ Q) por ¬ P ∨ ¬ Q,
  se puede aplicar sobre el objetivo, o sobre una hipótesis `h` escribiendo `push_neg at h`

(p → r ∨ s) → ((p → r) ∨ (p → s)) 
¬(p ∧ q) → ¬p ∨ ¬q 
¬(p → q) → p ∧ ¬q 
(p → q) → (¬p ∨ q) 
(¬q → ¬p) → (p → q) 
p ∨ ¬p 
(((p → q) → p) → p) 
-/
