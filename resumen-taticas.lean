/-
# Cómo introducir algunos símbolos

→   `\to`   `\->`
↔   `\iff`  
←   `\<-`
≤   `\le`   `\<=`
≥   `\ge`   `\>=`
ℝ   `\R`
ℕ   `\N`
ℤ    `\Z`
ε   `\epsilon`    `\eps`
δ   `\delta`
∀   `\forall`
∃   `\exists`
∈  `\in`
∉  `\notin`
≠   `\neq`
¬   `\not`
∧   `\and`
∨   `\or`
⊆   `\subseteq`
∅   `\empty`
⟨   `\<`
⟩   `\>`



# Resumen de algunas tácticas

- `refl`      principio de reflexividad (algo es igual a sí mismo), demuestra un objetivo que consista en la igualdad de dos objetos que son iguales por definición
- `exact h`   demuestra el objetivo si es exactamente igual que la hipótesis `h`
- `apply h`   si la hipótesis `h` es una implicación cuyo consecuente es el objetivo, sustituye el objetivo por los antecedentes de `h`
- `intro h`   si el objetivo es de la forma  `P → Q` , introduce la hipótesis `h : P` y deja por demostrar `Q`.
              Análogamente, si el objetivo es de la forma `∀ x , P`, introduce un elemento arbitrario y deja a demostrar `P` para ese elemento concreto
- `intros a b c`   Equivalente a `intro a, intro b, intro c`
- `split`     Si el objetivo está formado por varias partes (por ejemplo, si es de tipo `∧` o  `\iff`), lo separa en varios subobjetivos.
- `cases h with h1 h2`   Si la hipótesis `h` está formada por varias partes, la separa en varias hipótesis. Si `h` está formada por varios posibles casos, separa el objetivo en un objetivo por cada uno de esos casos.
- `by_cases h : P`  Separa el objetivo en dos subobjetivos, en uno asumiento la hipótesis `h : P` y otro asumiendo lo contrario (es decir `h : ¬ P`)
- `by_contradiction h`  Demostración por reducción al absurdo: introduce una hipótesis `h` negando el objetivo, y el objetivo a demostrar parsa a ser `false`
- `rw h`       Si `h` dice que `a = b` (o que `a ↔ b`), reescribe `a`, cambiándolo por `b`
- `rw h at h2` Lo mismo, pero sobre la hipótesis `h2`
- `simp`       Simplifica la expresión, aplicando los lemas que haya marcados como `@[simp]`
- `simp at h`  Lo mismo, pero sobre la hipótesis `h`
- `ext x`      Si el objetivo es demostrar la igualdad de dos conjuntos, toma un elemento `x` arbitrario y el objetivo pasa a ser demostrar que está en uno si y sólo si está en el otro.
               Análogamente, si hay que ver la igualdad de dos funciones, pasa a haber que demostrar que la imagen de un elemento es la misma.
- `unfold d`   Si se está usando un objeto `d` que se ha definido, lo sustituye por su definición. También se puede aplicar a una hipótesis con `at`
- `specialize h x` Cambia la hipótesis `h` al caso particular reultante de aplicarla a `x`
- `have h : P` introduce un nuevo subobjetivo consistente en demostrar `P`, una vez demostrado, la hipótesis `h : P` está disponible para demostrar el objetivo inicial
- `suffices h : P` igual que la anterior, pero el orden es el contrario: primero hay que demostrar el objetivo inicial usando `h : P` y despúes hay que demostrar `P`
- `calc`      Permite demostrar (des)igualdades encadenando varias (des)igualdades seguidas.
- `linarith`  Intenta demostrar automáticamente (des)igualdades usando aritmética lineal.
- `use p`     Si el objetivo es de tipo `∃ x, P(x)`, usa exactamente `p` para ver que existe, así el objetivo pasa a ser demostrar `P(p)`
- `tauto`     Intenta demostrar automáticamente tautologías.


-/