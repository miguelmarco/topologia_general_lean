import ..metricos
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
  split,
  {
    tauto, -- cualquier conjunto es abierto en la topologia discreta 
  },
  {
    intros U hU,    -- tomamos un abierto en la topologia discreta
    use { ({x}) | x ∈ U},  -- la familia de abiertos básicos
    split,
    {
      intros A hA,
      cases hA with x hx,
      cases hx with hxU hxA,
      use x,
      exact hxA,
    },
    {
      ext y,
      split,
      {
        intro hy,
        use {y},
        split,
        {
          use y,
          split, 
            exact hy,
            refl,
        },
        tauto,
      },
      {
        intro hy,
        cases hy with V hV,
        cases hV with hVx hyV,
        cases hVx with x hx,
        cases hx with hxU hxV,
        rw ← hxV at hyV,
        cases hyV,
        exact hxU,
      }
    }
  }
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
  intros U hU,
  cases hB with B1 B2,
  specialize B2 U hU,
  cases B2 with ℱ hℱ,
  cases hℱ with hℱB hUℱ,
  rw hUℱ,
  apply abierto_union,
  calc
      ℱ   ⊆ B             : by {exact hℱB,}
      ...  ⊆  abiertos     : by {exact h,}
end

open metricos metricos.espacio_metrico



/-
En este ejercicio, puede ser util este lema:

`existe_topologia_base_sii_B1_B2 : ∀ (X : Type) (B : set (set X)), (∃ (τ : espacio_topologico X), base B) ↔ B1 B ∧ B2 B `

y la función `min`, que da el mínimo de dos números.
-/

example (X : Type) [espacio_metrico X] (o : X) : ∃ (τ : espacio_topologico X), @base X τ { ( disco o ε ) | ε > 0 } :=
begin
  rw existe_topologia_base_sii_B1_B2,
  split,
  {
    unfold B1,
    ext x,
    simp,
    use d o x + 1,
    simp,
    have haux := d1 o x,
    linarith,
  },
  {
    unfold B2,
    intros B1 B2 hB1 hB2 x hx,
    cases hB1 with ε₁ hε₁,
    cases hε₁ with hε₁pos hε₁disco,
    cases hB2 with ε₂ hε₂,
    cases hε₂ with hε₂pos hε₂disco,
    cases hx with hx1 hx2,
    rw ← hε₁disco at *,
    rw ← hε₂disco at *,
    let r := (min ε₁ ε₂),
    use disco o r,
    split,
    {
      use r,
      split,
      {
        simp [r],
        split,
        linarith,
        linarith,
      },
      {
        refl,
      },
    },
    {
      simp [disco] at hx1 hx2,
      split,
      {
        simp [disco],
        split,
        assumption, assumption,
      },
      {
        intros y hy,
        simp [disco] at hy,
        cases hy with hy1 hy2,
        split,
        exact hy1,
        exact hy2,
      }
      
    }
  }
end