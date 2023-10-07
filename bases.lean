import data.set.finite
import .conjuntos
import .topologicos
import tactic


namespace topologicos

open topologicos.espacio_topologico
open set

/-
En esta sección, `X` va a ser un espacio topológico
-/
variables {X : Type} [espacio_topologico X]

/-
Definimos base como una familia de abiertos que genera toda la topología mediante uniones
-/
def base (ℬ : set (set X)) := 
ℬ ⊆ abiertos ∧ 
∀ (U : set X), abierto U →  ∃ ℱ ⊆ ℬ, U = ⋃₀ ℱ 

lemma base_discreto : @base X (discreta X) { ({x}) | x : X} :=
begin
  sorry,  --completar como ejercicio
end


lemma caracterizacion_base (ℬ : set (set X)) (hB :ℬ ⊆ abiertos) : 
base ℬ ↔  ∀ (U : set X), abierto U → ∀ x ∈ U, ∃ Bₓ ∈ ℬ, Bₓ ⊆ U ∧ x ∈ Bₓ :=
begin
  split,
  {
    intros hBbase U hU x hx,
    cases hBbase with hBab hBℱ,
    specialize hBℱ U hU,
    cases hBℱ with ℱ hℱ,
    cases hℱ with hℱℬ hUℱ,
    rw  hUℱ at hx,
    cases hx with Bₓ hBₓ,
    cases hBₓ with hBₓℱ hxBₓ,
    use Bₓ,
    split,
    {
      apply hℱℬ,
      exact hBₓℱ,
    },
    split,
    {
      rw hUℱ,
      intros y hy,
      use Bₓ,
      split,
        exact hBₓℱ,
        exact hy,
    },
    {
      exact hxBₓ,
    },
  },
  {
    intro h,
    split,
    {
      exact hB,
    },
    {
      intros U hU,
      specialize h U hU,
      use { B ∈ ℬ | B ⊆ U },
      split,
      {
        simp only [set.sep_subset],
      },
      {
        ext x,
        split,
        {
          intro hxU,
          specialize h x hxU,
          cases h with Bₓ hBₓ,
          cases hBₓ with hBₓℬ hBₓ,
          cases hBₓ with hxBₓ hBₓU,
          use Bₓ,
          split,
          split,
            repeat {assumption},
        },
        {
          intro hx,
          cases hx with Bₓ hBₓ,
          cases hBₓ with hBₓ hxBₓ,
          cases hBₓ with hBₓℬ hBₓU,
          apply hBₓU,
          exact hxBₓ,
        },
      },
    },
  },
end

lemma continua_sii_preimagen_abierto_basico {X Y : Type} 
[𝒯ₓ:espacio_topologico X]
[espacio_topologico Y]
(ℬ : set (set Y))
(hℬ : base ℬ)
(f : X → Y)
:
continua f ↔ ∀ U ∈ ℬ, f ⁻¹' U ∈ 𝒯ₓ.abiertos  :=
begin
  unfold base at hℬ,
  cases hℬ with hℬab hℬUn,
  split,
  {
    intro h,
    intros U hU,
    apply h,
    apply hℬab,
    exact hU,
  },
  {
    intro h,
    intros U hU,
    specialize hℬUn U hU,
    cases hℬUn with  ℱ hℱ,
    cases hℱ with hℱℬ hℱU,
    rw hℱU,
    rw preimagen_union_familia',
    apply abierto_union,
    intros U2 hU2,
    cases hU2 with V hV,
    cases hV with hVℱ hVU2,
    rw ← hVU2,
    apply h,
    apply hℱℬ,
    exact hVℱ,
  }
end


def B1 {X : Type} (ℱ : set (set X)) := univ = ⋃₀ ℱ 
def B2 {X : Type} (ℱ : set (set X)) := ∀ (B1 B2 : set X), B1 ∈ ℱ → B2 ∈ ℱ → ∀ x ∈ B1 ∩ B2, ∃ B3 ∈ ℱ, x ∈ B3 ∧ B3 ⊆ B1 ∩ B2    

lemma propiedades_base {X : Type} [espacio_topologico X] 
( ℬ : set (set X))  (h : base ℬ) 
:
B1 ℬ ∧ B2 ℬ :=
begin
  split,
  {
    unfold B1,
    cases h with hBab hB,
    specialize hB univ abierto_total,
    cases hB with ℱ hℱ,
    cases hℱ with hℱℬ huniv,
    apply doble_contenido,
    {
      rw huniv,
      apply union_familia_contenida,
      exact hℱℬ,
    },
    {
      tauto,
    },
  },
  {
    intros B1 B2 hB1 hB2 x hx,
    cases h with hℬab h,
    have hB1B2 : abierto (B1 ∩ B2),
    {
      apply abierto_interseccion,
      {
        apply hℬab,
        exact hB1,
      },
      {
        apply hℬab,
        exact hB2,
      },
    },
    specialize h _ hB1B2,
    cases h with ℱ hℱ,
    cases hℱ with hℱℬ hℱU,
    rw hℱU at hx,
    cases hx with B3 hB3,
    cases hB3 with hB3ℱ hxB3,
    use B3,
    split,
    {
      apply hℱℬ,
      assumption,
    },
    split,
    {
      assumption,
    },
    {
      rw hℱU,
      intros y hy,
      use B3,
      split,
        assumption,
        assumption,
    },
  },
end
--definimos los abiertos generados por un conjunto, como todas las posibles uniones 
def abiertos_generados {X : Type} ( ℱ : set (set X)) := {U : set X | ∃ ℱU : set (set X), ℱU ⊆  ℱ ∧ U = ⋃₀ ℱU }


--veamos que hay una topología dada por una familia que cumple B1 y B2
def  topologia_generada {X : Type} (ℱ : set (set X)) (h1 : B1 ℱ) (h2 : B2 ℱ) : espacio_topologico X :=
{ abiertos := abiertos_generados ℱ,
  abierto_total := begin
    use ℱ,
    split,
    {
      tauto,
    },
    exact h1,
  end,
  abierto_vacio := begin
    use ∅,
    simp only [set.empty_subset, set.sUnion_empty, eq_self_iff_true, and_self],
  end,
  abierto_union := begin
    intros ℱ1 hℱ1,
    use {U ∈ ℱ | U ⊆ ⋃₀ ℱ1},
    split,
    {
      intros U hU,
      cases hU with hU1 hU2,
      exact hU1,
    },
    {
      ext x,
      split,
      {
        intro hx,
        cases hx with U hU,
        cases hU with hUℱ1 hxU,
        specialize hℱ1 hUℱ1,
        cases hℱ1 with ℱU hℱU,
        cases hℱU with hℱUℱ hℱU,
        rw hℱU at hxU,
        cases hxU with V hV, 
        cases hV with hVℱ1 hxV,
        use V,
        split,
        {
          split,
          {
            exact hℱUℱ hVℱ1,
          },
          {
            dsimp,
            intros y hyV,
            use U,
            split,
            {
              exact hUℱ1,
            },
            {
              rw hℱU,
              use V,
              exact ⟨ hVℱ1,hyV⟩,
            },
          },
        },
        {
          exact hxV,
        },
      },
      {
        intro hx,
        cases hx with U hU,
        cases hU with hUℱ hxU,
        cases hUℱ with hUℱ hUUℱ,
        apply hUUℱ hxU,
      },
    },
  end,
  abierto_interseccion := begin
    intros U V hU hV,
    cases hU with FU hFU,
    cases hFU with hFUℱ hFUU,
    cases hV with FV hFV,
    cases hFV with hFVℱ hFVV,
    use { S ∈ ℱ | S ⊆ U ∩ V},
    split,
    {
      simp only [sep_subset],
    },
    {
      ext x,
      split,
      {
        intro hx,
        cases hx with hxU hxV,
        rw hFUU at hxU,
        cases hxU with Ux hUx,
        cases hUx with hUxFU hxUx,
        rw hFVV at hxV,
        cases hxV with Vx hVx,
        cases hVx with hVxFV hxVx,
        specialize h2 Ux Vx _ _ x _,
        {
          tauto,
        },
        {
          tauto,
        },
        {
          split,
          assumption,
          assumption,
        },
        cases h2 with W hW,
        cases hW with hWℱ hW,
        cases hW with hxW hWUxVx,
        use W,
        split,
        {
          split,
          {
            assumption,
          },
          {
            simp at *,
            cases hWUxVx with hWUx hWVx,
            split,
            {
              rw hFUU,
              intros y hy,
              use Ux,
              tauto,
            },
            {
              rw hFVV,
              intros y hy,
              use Vx,
              tauto,
            },
          },
        },
        {
          exact hxW,
        },
      },
      {
        intro hx,
        cases hx with S hS,
        cases hS with hSProp hxS,
        cases hSProp with hSℱ hSUV,
        apply hSUV,
        exact hxS,
      },
    },
  end }

-- veamos también que la familia es base de esa topología

lemma base_de_topologia_generada (ℬ : set (set X)) (h1 : B1 ℬ) (h2 : B2 ℬ) :
@base X (topologia_generada ℬ h1 h2 ) ℬ :=
begin
  rw caracterizacion_base,
  {
    intros U hU x hxU,
    cases hU with ℱ hℱ,
    cases hℱ with hℱℬ hℱU,
    rw hℱU at hxU ⊢,
    cases hxU with Bₓ hBₓ,
    cases hBₓ with hBₓℱ hxBₓ,
    use Bₓ,
    split,
    {
      apply hℱℬ,
      exact hBₓℱ,
    },
    split,
    {
      intros y hy,
      use Bₓ,
      split,
        assumption,
        assumption,
    },
    {
      exact hxBₓ,
    },
  },
  {
    intros U hU,
    use {U},
    simp,
    exact hU,
  }
end

lemma topologia_determinada_base {X : Type} 
[τ1 : espacio_topologico X]
(B : set (set X)) 
(h1 : base B)
:
τ1 = topologia_generada B (propiedades_base B h1).1 (propiedades_base B h1).2:=
begin
  ext U,
  unfold base at h1,
  cases h1 with h1ab h1U, 
  split,
  { 
    intro h,
    specialize h1U U h,
    cases h1U with ℱ hℱ,
    cases hℱ with hℱB hUℱ,
    use ℱ,
    tauto,
  },
  {
    intro h,
    cases h with ℱ hℱ,
    cases hℱ with hℱB hℱU,
    rw hℱU,
    apply abierto_union,
    tauto,
  },
end

lemma existe_topologia_base_sii_B1_B2 (X : Type) (B : set (set X)) : (∃ (τ : espacio_topologico X), @base X τ B) ↔ B1 B ∧ B2 B :=
begin
  split,
  {
    intro h,
    cases h with τ hB,
    apply @propiedades_base X τ, 
    exact hB,
  },
  {
    intro h,
    cases h with hB1 hB2,
    let τ := topologia_generada B hB1 hB2,
    use τ,
    apply @base_de_topologia_generada X τ,
  }
end

lemma prop_2_2_8 (ℬ ℬ': set (set X)) (h1 : base ℬ) (hab : ℬ' ⊆ abiertos) :
 base ℬ' ↔ ∀ B ∈ ℬ, ∀ x ∈ B, ∃ B' ∈ ℬ', B' ⊆ B ∧ x ∈ B' :=
begin
  split,
  {
    intro hBase,
    intros B hB x hx,
    cases h1 with hℬab hℬ,
    rw caracterizacion_base ℬ' hab at hBase,
    apply hBase,
    {
      apply hℬab,
      exact hB,
    },
    {
      exact hx,
    },
  },
  {
    intro h,
    rw caracterizacion_base ℬ' hab,
    rw caracterizacion_base at h1,
    {
      intros U hU x hx,
      specialize h1 U hU x hx,
      cases h1 with Bₓ hBₓ,
      cases hBₓ with hBₓℬ hxBₓ,
      cases hxBₓ with hBₓU hxBₓ,
      specialize h  Bₓ hBₓℬ x hxBₓ,
      cases h with B' hB',
      cases hB' with hB'ℬ' hxB',
      cases hxB' with hxBₓ hBₓU,
      use B',
      tauto,
    },
    {
      apply h1.1,
    },
  }
end 


def subconjuntos_finitos (F : set (set X)) := { I | I ⊆ F ∧ I.finite}

def subbase (S : set (set X))  := S ⊆ abiertos ∧ base { (⋂₀ F) | F ∈ subconjuntos_finitos S}


lemma continua_sii_preimagen_abierto_subbasico {X Y : Type} 
[𝒯ₓ:espacio_topologico X]
[espacio_topologico Y]
(S : set (set Y))
(hS : subbase S)
(f : X → Y)
:
continua f ↔ ∀ U ∈ S, f ⁻¹' U ∈ 𝒯ₓ.abiertos  :=
begin
  cases hS with hSab hSbas,
  split,
  {
    intro h,
    intros U hU,
    apply h,
    apply hSab,
    exact hU,
  },
  {
    rw continua_sii_preimagen_abierto_basico _ hSbas,
    intro h,
    intros V hV,
    simp at hV,
    cases hV with W hW,
    cases hW with hWfin hVW,
    cases hWfin with hWsub hWfin,
    rw ← hVW,
    rw preimagen_interseccion_familia',
    apply abierto_interseccion_finita,
    {
      intros U hU,
      cases hU with V' hV',
      cases hV' with hV'W hV'U,
      rw ← hV'U,
      apply h,
      apply hWsub,
      exact hV'W,
    },
    {
      apply familia_parametrizada_finita,
      exact hWfin,
    } 
  }
end

def topologia_generada_subbase (S : set (set X)) : espacio_topologico X :=
begin
  apply topologia_generada { (⋂₀ F) | F ∈ subconjuntos_finitos S},
  {
    ext x,
    simp,
    use ∅,
    simp,
    split,
    {
      tauto,
    },
    {
      simp only [finite_empty],
    }
  },
  {
    intros B1 B2 hB1 hB2 x hx,
    simp  at *,
    cases hB1 with S1 hS1,
    cases hS1 with hS1fin hS1B1,
    cases hS1fin with hS1S hS1fin,
    cases hB2 with S2 hS2,
    cases hS2 with hS2fin hS2B2,
    cases hS2fin with hS2S hS2fin,
    cases hx with hxB1 hxB2,
    use (S1 ∪ S2),
    split,
    {
      split,
      {
        intros y hy,
        cases hy,
        {
          apply hS1S,
          exact hy,
        },
        {
          apply hS2S,
          exact hy,
        }
      },
      {
        simp only [finite_union],
        tauto,
      }
    },
    {
      split,
      {
        intros T hT,
        cases hT,
        {
          rw ← hS1B1 at hxB1,
          specialize hxB1 T hT,
          exact hxB1,
        },
        {
          rw ← hS2B2 at hxB2,
          specialize hxB2 T hT,
          exact hxB2,
        }
      },
      split,
      {
        intros y hy,
        rw ← hS1B1,
        intros A hA,
        apply hy,
        left,
        exact hA,
      },
      {
        intros y hy,
        rw ← hS2B2,
        intros A hA,
        apply hy,
        right,
        exact hA,
      }
    }
  }
end

lemma subbase_topologia_generada_subbase (S : set (set X)) :
@subbase X (topologia_generada_subbase S) S :=
begin
  split,
  {
    intros U hU,
    use {U},
    simp only [exists_prop, singleton_subset_iff, mem_set_of_eq, sUnion_singleton, eq_self_iff_true, and_true],
    use {U},
    simp only [sInter_singleton, eq_self_iff_true, and_true],
    split,
    {
      simp only [singleton_subset_iff],
      exact hU,
    },
    {
      simp only [finite_singleton],
    },
  },
  {
    simp only [exists_prop],
    split,
    {
      intros U hU,
      use {U},
      simp only [exists_prop, singleton_subset_iff, mem_set_of_eq, sUnion_singleton, eq_self_iff_true, and_true],
      exact hU,
    },
    {
      simp only [abierto_def, exists_prop],
      intros U hU,
      cases hU with I hI,
      simp only [exists_prop] at hI,
      use I,
      tauto,
    }
  },
end

/-
## Ejercicios
-/


/-
En este ejercicio, necesitamos las definiciones del archivo de espacios métricos

para evitar conflictos con lo definido en otro sitio, lo "encerramos" en una sección separada.
y así, podemos importar los nombres de lo definido para espacios métricos
-/
section base_metricos
open metricos
open metricos.espacio_metrico

-- la forma de especificar la topologia que se usa es con el @ 
lemma ejer_2_2_4 (X : Type) [espacio_metrico X] : base {(bola x r) | (x : X) ( r > 0 )} :=
begin
  sorry,
end

end base_metricos

lemma ejer_2_2_6 {X : Type} [τ : espacio_topologico X] (B : set (set X))
(hB : base B) (τ' : espacio_topologico X) (h : B ⊆ τ'.abiertos) :
τ.abiertos ⊆ τ'.abiertos :=
begin
  sorry,
end

lemma ejer_2_2_8 (S : set (set X)) (hsAb : S ⊆ abiertos) : 
subbase S ↔ ∀ (U : set X), abierto U →  ∀ x ∈ U, ∃ (ℱ : set (set X)), set.finite ℱ ∧ ℱ ⊆ S ∧ x ∈ ⋂₀ ℱ ∧ ⋂₀ ℱ ⊆ U:=
begin
  sorry,
end


end topologicos