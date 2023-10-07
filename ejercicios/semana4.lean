import ..topologicos
import ..bases

import tactic

open topologicos
open topologicos.espacio_topologico


/-
# Ejercicio 2.2.5

Sea `X` e.t. discreto. Demuestra que `ℬ(d,X) := {{x} | x ∈ X}` es base de `X`.
-/

lemma ejer_2_2_5 (X : Type) : @base X (discreta X) { ({x}) | x : X} :=
begin
  sorry,
end

/-
# Ejercicio 2.2.6 

Sea `ℬ` base de abiertos de una topología `τ` y consideremos `τ′` otra topología de modo que 
`ℬ ⊂ τ′`, entonces `τ ⊂ τ′`.
-/

lemma ejer_2_2_6  {X : Type} [τ : espacio_topologico X] (B : set (set X))
(hB : base B) (τ' : espacio_topologico X) (h : B ⊆ τ'.abiertos) :
τ.abiertos ⊆ τ'.abiertos :=
begin
  sorry,
end


open metricos metricos.espacio_metrico



/-
En este ejercicio, puede ser util este lema:

`existe_topologia_base_sii_B1_B2 : ∀ (X : Type) (B : set (set X)), (∃ (τ : espacio_topologico X), base B) ↔ B1 B ∧ B2 B `

y la función `min`, que da el mínimo de dos números.
-/

example (X : Type) [espacio_metrico X] (o : X) : ∃ (τ : espacio_topologico X), @base X τ { ( disco o ε ) | ε > 0 } :=
begin
  sorry,
end
