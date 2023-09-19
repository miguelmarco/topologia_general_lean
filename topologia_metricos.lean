import .metricos
import .topologicos
import tactic

/-
# Topologias determinadas por una métrica

En este archivo vemos sólo dos resultados de la sección 2.3

Son bastante pesados de demostrar por tener que trabajar con distintas estructuras de espacio métrico y espacio topológico,
lo que fuerza a dar explícitamente todos los datos cada vez, en lugar de usar uno fijado implícitamente.

Además, hay conflictos entre las definiciones: por ejemplo, en `metricos` definíamos `abierto` de una forma, y en `topologicos` damos
otra definición. Para evitar conflictos, habría que llamarlos `metricos.abierto` y `topologicos.abierto`.

Si abrieramos tanto `topologicos` como `espacio_topologico`, tendríamos un conflicto, así que sólo abrimos uno de ellos.
-/

open topologicos
open topologicos.espacio_topologico

/-
El precio a pagar por evitar el conflicto es que tendríamos que usar el nombre completo para lo que está en ese espacio de nombres,

es decir, tendríamos que decir `metricos.bola`, o `metricos.espacio_metrico.d`. Para aligerar este problema, definimos
notación ad-hoc para los conceptos que vayamos a usar (evitando de nuevo conflictos)
-/

notation `@bola` := @metricos.bola
notation `@topologia` := @topologicos.topologia_metrico
notation `espacio_metrico` := metricos.espacio_metrico

/-
Notar que la `@` que hay al principio de algunos nombres significa que hay que dar expresamente la estructura que se va a usar.
-/


def metrizable (X : Type) [T : espacio_topologico X] := ∃ M : espacio_metrico X , @topologia X M = T 

lemma metrizable_es_topologica (X Y : Type) [TX : espacio_topologico X] [TY : espacio_topologico Y] (f : X → Y) 
(hh : homeomorfismo f) : metrizable X →  metrizable Y :=
begin
  cases hh with hf hg,
  cases hg with g hg,
  cases hg with hg hfg,
  cases hfg with hgf hfg,

  {
    intro h,
    cases h with M hM,
    fconstructor,
    {
      fconstructor,
      {
        intros y1 y2,
        exact @metricos.espacio_metrico.d  X M (g y1) (g y2),
      },
      {
        intros y1 y2,
        simp,
        apply metricos.espacio_metrico.d1,
      },
      {
        intros y1 y2,
        simp,
        rw metricos.espacio_metrico.d2,
        split,
        {
          intro hy1y2,
          change identidad y1 = identidad y2,
          rw  ← hfg,
          simp,
          rw hy1y2,
        },
        {
          intro hy1y2,
          rw hy1y2,
        },
      },
      {
        intros y1 y2,
        simp,
        apply metricos.espacio_metrico.d3,
      },
      {
        intros x y z,
        simp,
        apply metricos.espacio_metrico.d4,
      },
    },
    ext V,
    unfold abiertos,
    split,
    {
      intro h,
      simp at h,
      suffices hV : f ⁻¹' V ∈ abiertos,
      {
        specialize hg _ hV,
        have haux : g ⁻¹' (f ⁻¹' V) = V,
        {
          ext y,
          simp,
          change (f ∘ g) y ∈ V ↔ y ∈ V,
          rw [hfg],
          simp,
        },
        rw haux at hg,
        exact hg,
      },
      rw ← hM,
      unfold abiertos,
      simp,
      intros x hx,
      specialize h (f x) hx,
      cases h with r hr,
      cases hr with hrpos hrbol,
      unfold metricos.bola at hrbol,
      simp at hrbol,
      use r,
      split, assumption,
      intros y hy,
      simp,
      apply hrbol,
      simp,
      unfold metricos.bola at hy,
      simp at hy,
      have haux1 : g (f x) = x,
      {
        change (g ∘ f) x = x,
        simp [hgf],
      },
      have haux2 : g (f y) = y,
      {
        change (g ∘ f) y = y,
        simp [hgf],
      },
      rw haux2,
      rw haux1,
      exact hy,
    },
    {
      intro hV,
      specialize hf _ hV,
      rw ← hM at hf,
      simp [abiertos] at hf,
      simp,
      intros y hy,
      specialize hf (g y) _,
      {
        change (f ∘ g) y ∈ V,
        rw hfg,
        exact hy,
      },
      cases hf with r hr,
      cases hr with hrpos hr,
      simp [metricos.bola] at hr,
      use r,
      split, assumption,
      intros z hz,
      simp [metricos.bola] at hz,
      specialize hr hz ,
      change (f ∘ g) z ∈ V at hr,
      simp [hfg ] at hr,
      exact hr,
    }
  },
  
end




def metricas_equivalentes {X : Type} (D1  D2: espacio_metrico X) := @topologia X D1 = @topologia X D2

lemma carac_equivalentes  {X : Type} (D1  D2 : espacio_metrico X) : metricas_equivalentes D1 D2 ↔ ( ∀ x, ∀ r1 > 0, ∃ r2 > 0, (@bola X D1) x r2 ⊆ (@bola X D2) x r1) ∧ 
( ∀ x, ∀ r1 > 0, ∃ r2 > 0, (@bola X D2) x r2 ⊆ (@bola X D1) x r1 ):=
 begin
  let T1 := @topologia X D1,
  let T2 := @topologia X D2,
  split,
  {
    intro h,
    have hT1T2 : T1 = T2,
    {
      exact h,
    },
    split,
    {
      intros x r1 hr1,
      have hab2 :  (@abierto X T2) ((@bola X D2) x r1),
      {
        apply metricos.bola_abierta ,
        exact hr1,
      },
      simp at hab2,
      rw ← hT1T2 at hab2,
      specialize hab2 x,
      simp   at hab2,
      specialize hab2 _,
      {
        linarith,
      },
      cases hab2 with r2 hr2,
      cases hr2 with hr2pos hr2,
      use r2,
      split, assumption,
      exact hr2,
    },
    {
      intros x r1 hr1,
      have hab2 :  (@abierto X T1) ((@bola X D1) x r1),
      {
        apply metricos.bola_abierta ,
        exact hr1,
      },
      simp at hab2,
      rw hT1T2 at hab2,
      specialize hab2 x,
      simp   at hab2,
      specialize hab2 _,
      {
        linarith,
      },
      cases hab2 with r2 hr2,
      cases hr2 with hr2pos hr2,
      use r2,
      split, assumption,
      exact hr2,
    },
  },
  {
    intro h,
    cases h with h1 h2,
    ext U,
    unfold abiertos,
    unfold metricos.entorno,
    split,
    {
      intro hU,
      intros x hx,
      specialize hU x hx,
      cases hU with r1 hr1,
      cases hr1 with hr1pos hr1bo,
      specialize h2 x r1 hr1pos,
      cases h2 with r2 hr2,
      cases hr2 with hr2pos hr2bol,
      use r2,
      split, assumption,
      intros y hy,
      apply hr1bo,
      apply hr2bol,
      exact hy,
    },
    {
      intro hU,
      intros x hx,
      specialize hU x hx,
      cases hU with r1 hr1,
      cases hr1 with hr1pos hr1bo,
      specialize h1 x r1 hr1pos,
      cases h1 with r2 hr2,
      cases hr2 with hr2pos hr2bol,
      use r2,
      split, assumption,
      intros y hy,
      apply hr1bo,
      apply hr2bol,
      exact hy,
    },
  },
 end

 