import .topologicos
import .subespacios
import .aplicaciones_abiertas
import .bases
import tactic

open topologicos topologicos.espacio_topologico
open set

namespace topologicos

variables {X : Type} [espacio_topologico X]

/-
## Definición: 
en un espacio topológico, un conjunto `S` es **entorno** de `x`, si hay
un abierto intermedio.
-/

def entorno {X : Type} [espacio_topologico X] (x : X) (S : set X ) := ∃ U : set X, abierto U ∧ x ∈ U ∧ U ⊆ S 

/-
## Ejemplo:

Todo punto tiene al menos un entorno (el total)
-/

example : ∀ (x : X), ∃ (S : set X), entorno x S :=
begin
  intro x,    -- sea `x` un punto
  use univ,   -- veamos que el total es entorno
  use univ,   -- para ello, veamos que el total es un abierto intermedio
  simp,       -- que `x` está en el total, y que el total está contenido en sí mismo es inmediato
  apply abierto_total,  -- y que es abierto es por la propiedad de la topología.
end


lemma entornos_subespacio (A : set X) (x : A) (V : set A)  : entorno x V ↔ ∃ (V' : set X), entorno ↑x V' ∧ V = (V' ↓∩ A) :=
begin
  split,
  {
    intro h,
    cases h with U hU,
    cases hU with hUab hUint,
    cases hUint with hxU hUV,
    cases hUab with U' hU',
    cases hU' with hU'ab hU'U,
    use U' ∪ V,
    split,
    {
      use U',
      split,
      {
        exact hU'ab,
      },
      split,
      {
        rw ← hU'U at hxU,
        exact hxU,
      },
      simp,
    },
    {
      simp,
      rw hU'U,
      ext  y,
      split,
      {
        intro hy,
        right,
        exact hy,
      },
      {
        intro hy,
        cases hy,
        {
          apply hUV,
          exact hy,  
        },
        exact hy,
      },
    },
  },
  {
    intro h,
    cases h with V' hV',
    cases hV' with hV'ent hVV'A,
    cases hV'ent with U' hU',
    cases hU' with hU'ab hU'2,
    cases hU'2 with hxU' hU'V,
    use (U' ↓∩ A),
    simp,
    use U',
    simp,
    {
      exact hU'ab,
    },
    split, assumption,
    {
      rw hVV'A,
      simp only [restringe_contenido, subset_inter_iff, inter_subset_right, and_true],
      calc
        U' ∩ A    ⊆   U'  : by {simp,}
        ...       ⊆   V'  : by {assumption,}
    },
  },
end


/-
## Proposición 3.1.4
Un conjunto es abierto si i sólo si es entorno de todos sus puntos
-/
lemma abierto_sii_entorno_puntos (U : set X) : abierto U ↔ ∀ x ∈ U, entorno x U :=
begin
  split,
  {
    intro h,
    intros x hx,
    use U,
    tauto,
  },
  {
    intro h,
    have haux : U = ⋃₀ { V | abierto V ∧ V ⊆ U},
    {
      ext x,
      split,
      {
        intro hx,
        specialize h x hx,
        cases h with V hV,
        cases hV with hVab hV2,
        cases hV2 with hxV hVU,
        use V,
        simp,
        tauto,
      },
      {
        intro hx,
        cases hx with V hV,
        cases hV with hV2 hxV,
        cases hV2 with hVab hVU,
        apply hVU,
        exact hxV,
      },
    },
    rw haux,
    apply abierto_union,
    simp,
    intros V hV,
    cases hV with hVab hVU,
    exact hVab,
  },
end

 /-
## Proposición 3.1.5

 Una aplicación `f : X → Y` es contínua si y sólo para todo punto `x ∈ X`, y todo entorno `V` de `f(x)`, `f⁻¹(V)` es entorno de x.
 -/
lemma continua_sii_preimagen_entorno_entorno {X Y : Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y) : 
      continua f ↔ ∀ x , ∀ V , entorno (f x) V → entorno x (f ⁻¹' V) :=
begin
  split,
  {
    intro h,
    intros x V hV,
    cases hV with U hU,
    cases hU with hUab hU2,
    cases hU2 with hfxU hUV,
    use f ⁻¹' U,
    split,
    {
      apply h,
      exact hUab,
    },
    split,
    {
      exact hfxU,
    },
    {
      intros y hy,
      specialize hUV hy,
      exact hUV,
    },
  },
  {
    intro h,
    intros U hU,
    change abierto _,
    rw abierto_sii_entorno_puntos,
    intros x hx,
    apply h,
    use U,
    split,
      exact hU,
    split,
      exact hx,
    tauto,
  }
end

/-
## Proposición 3.1.6

Sea `f : X → Y` aplicación. Entonces las siguientes afirmaciones son equivalentes:
-  `∀ x ∈ X` y `∀ V`  entorno de `x`, se tiene que `f(V)` es entorno de `f(x)`.
- La aplicación `f` es abierta
-/
lemma abierta_sii_imagen_entorno_entorno {X Y : Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y) :
      abierta f ↔ ∀ x, ∀ V, entorno x V → entorno (f x) (f '' V) :=
  begin
    split,
    {
      intro h,
      intros x V hV,
      cases hV with U hU,
      cases hU with hUab hU2,
      cases hU2 with hxU hUV,
      use (f '' U),
      split,
      {
        apply h,
        exact hUab,
      },
      split,
      {
        use x,
        simp only [and_true, eq_self_iff_true],
        exact hxU,
      },
      {
        simp only [set.image_subset_iff],
        intros y hy,
        use y,
        simp only [and_true, eq_self_iff_true],
        apply hUV,
        exact hy,
      },
    },
    {
      intro h,
      intros U hU,
      rw abierto_sii_entorno_puntos at *,
      intros y hy,
      cases hy with x hx,
      cases hx with hxU hxy,
      rw ← hxy,
      apply h,
      apply hU,
      exact hxU,
    }
  end

/-
En lo que sigue, `E x` denotará una familia de conjuntos para cada punto.
-/



/-
Definimos una serie de propiedades que se pueden cumplir
-/
variable (E :  X → set (set X))

def N1 {X : Type} (E : X → set (set X)) := ∀ (x : X), ∃ U , U ∈ E x
def N2 {X : Type} (E : X → set (set X)) := ∀ x, ∀ Uₓ ∈ E x, x ∈ Uₓ
def N3 {X : Type} (E : X → set (set X)) := ∀ x, ∀ U₁ ∈ E x, ∀ U₂ ∈ E x, U₁ ∩ U₂ ∈ E x
def N4 {X : Type} (E : X → set (set X)) := ∀ x, ∀ Uₓ ∈ E x, ∀ A, Uₓ ⊆ A → A ∈ E x
def N5 {X : Type} (E : X → set (set X)) := ∀ x, ∀ Uₓ ∈ E x, ∃ Vₓ ∈ E x, ∀ y ∈ Vₓ, Uₓ ∈ E y

/-
Denotaremos por `𝓝` la familia de entornos de un punto.
-/

def 𝓝 (X : Type) [espacio_topologico X]:  X → set (set X) := entorno


/-
Veamos que la familia de entornos cumplen estas propiedades
-/

lemma entornos_N1 : N1 (𝓝 X) := 
begin
  intro x,
  use univ,
  use univ,
  split,
    apply abierto_total,
  tauto,
end

lemma entornos_N2 : N2 (𝓝 X) :=
begin
  intros x U hU,
  cases hU with V hV,
  cases hV with hVab hV2,
  cases hV2 with hxV hVU,
  apply hVU,
  exact hxV,
end

lemma entornos_N3 : N3 (𝓝 X) :=
begin
  intros x U₁ hU₁ U₂ hU₂,
  cases hU₁ with V₁ hV₁,
  cases hV₁ with hV₁ab hV₁2,
  cases hV₁2 with hxV₁ hV₁U₁,
  cases hU₂ with V₂ hV₂,
  cases hV₂ with hV₂ab hV₂2,
  cases hV₂2 with hxV₂ hV₂U₂,
  use V₁ ∩ V₂,
  split,
  {
    apply abierto_interseccion,
    assumption,
    assumption,
  },
  split,
  {
    split,
    assumption,
    assumption,
  },
  {
    apply inter_subset_inter,
    assumption,
    assumption,
  }
end

lemma entornos_N4 : N4 (𝓝 X) :=
begin
  intros x U hU A hA,
  cases hU with V hV,
  cases hV with hVab hV2,
  cases hV2 with hxV hVU,
  use V,
  split,
    assumption,
  split,
    assumption,
    calc
      V   ⊆   U : by {assumption,}
      ... ⊆   A : by {assumption,}
end


lemma entornos_N5 : N5 (𝓝 X)  :=
begin
  intros x U hU,
  cases hU with V hV,
  cases hV with hVab hV2,
  cases hV2 with hxV hUV, 
  use V,
  split,
  {
    rw  abierto_sii_entorno_puntos at hVab,
    apply hVab,
    exact hxV,
  },
  {
    intros y hy,
    use V,
    split,
      assumption,
    split,
      assumption,
    assumption,
  }
end


/-
Dada una familia que cumpla las propiedades anteriores, hay una topología para la que esa familia son exactamente los entornos.
-/

def topologia_determinada_familia_entornos {X : Type} (𝓔 : X → set (set X)) (h1 : N1 𝓔) (h2 : N2 𝓔) (h3 : N3 𝓔) (h4 : N4 𝓔) (h5 : N5 𝓔) :
espacio_topologico X := {
  abiertos := {U | ∀ x ∈ U, U ∈ 𝓔 x},
  abierto_total := 
  begin
    intros x hx,
    specialize h1 x,
    cases h1 with U hU,
    apply h4 x U hU,
    tauto,
  end,
  abierto_vacio := 
  begin
    intros x hx,
    cases hx,
  end,
  abierto_union := 
  begin
    intros F hF,
    intros x hx,
    cases hx with U hU,
    cases hU with hUF hxU,
    specialize hF hUF x hxU,
    apply h4 x U hF,
    intros y hy,
    use U,
    tauto,
  end,
  abierto_interseccion := 
  begin
    intros U V hU hV,
    intros x hx,
    cases hx with hxU hxV,
    specialize hU x hxU,
    specialize hV x hxV,
    apply h3,
      apply  hU,
      apply  hV,
  end
}

/-
Los entornos en la topología  generada por una familia `F` que satisface `N1` ... `N5`, son exactamente `F`.
-/

lemma entornos_topologia_generada_coinciden {X : Type} (𝓔 : X → set (set X)) (h1 : N1 𝓔) (h2 : N2 𝓔) (h3 : N3 𝓔) (h4 : N4 𝓔) (h5 : N5 𝓔) :
@𝓝 X (topologia_determinada_familia_entornos 𝓔 h1 h2 h3 h4 h5) = 𝓔 :=
begin
  ext x E,
  split,
  {
    intro hE,
    cases hE with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUE,
    specialize hUab x hxU,
    apply h4  x U hUab,
    exact hUE,
  },
  {
    intro hE,
    let U := { y | E ∈ 𝓔 y},
    use U,
    split,
    {
      intros y hy,
      dsimp at hy,
      specialize h5 y E hy,
      cases h5 with V hV,
      cases hV with hV𝓔y hV,
      apply h4 _ _ hV𝓔y,
      intros z hz,
      specialize hV z hz,
      exact hV,
    },
    split,
    {
      exact hE,
    },
    {
      intros z hz,
      apply h2,
      exact hz,
    }
  }
end


/-
Los entornos determinan la topología.
-/
lemma entornos_determinan_topologia {X : Type} (T1 : espacio_topologico X) (T2 : espacio_topologico X) : T1 = T2 ↔  @𝓝 X T1 = @𝓝 X T2 :=
begin
  split,
  {
    intro h,
    rw h,
  },
  {
    intro h,
    ext U,
    simp only [𝓝] at h,
    simp only [ h, abierto_sii_entorno_puntos, ← abierto_def],
  }
end


/-
# Bases de entornos

Una familia de entornos `Bx` de un punto `x` se dice `base de entornos` si `∀ V entorno de x ∃ B ∈ Bx al que Bx ⊂ V`.
-/

def base_de_entornos (x : X) (𝓑ₓ : set (set X) ) := 𝓑ₓ ⊆ 𝓝 X x ∧ ∀ V ∈ 𝓝 X x, ∃ U ∈ 𝓑ₓ, U ⊆ V

/-
La familia de todos los entornos es base de entornos:
-/


lemma entornos_son_base_entornos {x : X}: base_de_entornos x (𝓝 X x) :=
begin
  split,
    tauto,
  {
    intros V hV,
    use V,
    split, 
      assumption,
      tauto,
  }
end


/-
Los entornos abiertos son una base de entornos:
-/



lemma entornos_abiertos_son_base_entornos {x : X}: base_de_entornos x (𝓝 X x ∩ abiertos)  :=
begin
  split,
    {
      simp only [set.inter_subset_left],
    },
    {
      intros V hV,
      cases hV with U hU,
      cases hU with hUab hU2,
      cases hU2 with hxU hUV,
      use U,
      split,
      {
        split,
        {
          rw abierto_sii_entorno_puntos at hUab,
          apply hUab,
          exact hxU,
        },
        exact hUab,
      },
      exact hUV,
    }
 
end

/-
Un espacio es discreto si y sólo si los conjuntos unipuntuales forman una base de entornos.
-/

lemma discreto_sii_puntos_son_base_entornos (X : Type) [T : espacio_topologico X] : T = discreta X ↔ ∀ x : X, base_de_entornos x {{x}} :=
begin
  split,
  {
    intro h,
    rw h,
    intro x,
    split,
    {
      intros U hU,
      use {x},
      split, tauto,
      split, tauto,
      change U = {x} at hU,
      rw hU,
    },
    {
      intros V hV,
      use {x},
      simp only [true_and, set.mem_singleton, set.singleton_subset_iff],
      apply entornos_N2,
      rw h,
      exact hV,
    }
  },
  {
    intro h,
    ext U,
    simp only [set.mem_univ, topologicos.abiertos_discreta_def, iff_true],
    change abierto U,
    rw abierto_sii_entorno_puntos,
    intros x hx,
    specialize h x,
    cases h with hxab h,
    simp only [set.singleton_subset_iff] at hxab,
    apply entornos_N4 x _ hxab,
    simp only [set.singleton_subset_iff],
    exact hx,
  }
end



/-
## Lema 3.1.5

Si para cualquier `x ∈ X` tenemos `Bx` una base de entornos abiertos de `x`, entonces `BX := ⋃₀ {Bx | x ∈ X}` 
es una base de abiertos de X
-/


lemma base_entornos_abiertos_es_base (B : X → set (set X)) (hNab : ∀ x, B x ⊆ abiertos) (hNen : ∀ x, base_de_entornos x (B x)) :
 base ⋃₀ { (B x) | x : X} :=
begin
  rw caracterizacion_base,
  {
    intros U hU x hx,
    rw abierto_sii_entorno_puntos at hU,
    specialize hU x hx,
    specialize hNen x,
    cases hNen with hN𝓝 hN,
    specialize hN U hU,
    cases hN with V hV,
    cases hV with hVN hVU,
    use V,
    split,
    {
      use B x,
      use x,
      exact hVN,
    },
    split,
      exact hVU,
    {
      apply entornos_N2,
      apply hN𝓝,
      exact hVN,
    },
  },
  {
    simp only [hNab, sUnion_subset_iff, mem_set_of_eq, forall_exists_index, forall_apply_eq_imp_iff', implies_true_iff],
  }
end

/-
## Proposición 3.1.16

Sea `X` e.t. y sea `x ∈ X`. Sean `Bx` una base de entornos
de `x` y `Dx` una familia de entornos de `x`. Entonces, `Dx` es una base de entornos si
y solo si `∀B ∈ Bx` existe `D ∈ Dx` tal que `D ⊂ B`.
-/

lemma otra_base_de_entornos (x : X) (B : set (set X)) (hB : base_de_entornos x B) (D : set (set X)) (hD : D ⊆ 𝓝 X x) :
base_de_entornos x D ↔ ∀ U ∈ B, ∃ V ∈ D, V ⊆ U :=
begin 
  cases hB with hBent hB,
  split,
  {
    intro h,
    intros U hU,
    cases h with hDent hD,
    specialize hBent hU,
    specialize hD U hBent,
    exact hD,
  },
  {
    intro h,
    split,
      assumption,
    {
      intros V hV,
      specialize hB V hV,
      cases hB with U hU,
      cases hU with hUB hUV,
      specialize h U hUB,
      cases h with W hW,
      cases hW with hWD hWU,
      use W,
      split, assumption,
      calc
        W   ⊆ U   : by {assumption,}
        ... ⊆ V   : by {assumption,}
    },
  },
end


/-
Propiedades de las bases de entornos
-/


def BE1 (B : X → set (set X)) := ∀ x, ∃ U, U ∈ B x
def BE2 (B : X → set (set X)) := ∀ x, ∀ U ∈ B x, x ∈ U
def BE3 (B : X → set (set X)) := ∀ x, ∀ B1 ∈ B x, ∀ B2 ∈ B x, ∃ B3 ∈ B x, B3 ⊆ B1 ∩ B2
def BE4 (B : X → set (set X)) := ∀ x, ∀ Bx ∈ B x, ∃ Wx ∈ B x, ∀ y ∈ Wx, ∃ By, By ∈ B y ∧ By ⊆ Bx


/-
Veamos que las bases de entornos cumplen estas propiedades
-/

lemma bases_de_entornos_B1 (B : X → set (set X)) (hB : ∀ x, base_de_entornos x (B x)) : BE1 B  :=
begin
  intros x,
  specialize hB x,
  have hexen := entornos_N1 x,
  cases hexen with U hU,
  cases hB with hB1 hB2,
  specialize hB2 U hU,
  cases hB2 with V hV,
  cases hV with hV1 hV2,
  use V,
  exact hV1,
end


lemma bases_de_entornos_B2 (B : X → set (set X)) (hB : ∀ x, base_de_entornos x (B x)) : BE2 B  :=
begin
  intros x,
  specialize hB x,
  intros U hU,
  cases hB with hB1 hB2,
  apply entornos_N2,
  apply hB1,
  apply hU,
end


lemma bases_de_entornos_B3 (B : X → set (set X)) (hB : ∀ x, base_de_entornos x (B x)) : BE3 B  :=
begin
  intros x,
  specialize hB x,
  intros U hU V hV,
  cases hB with hB1 hB2,
  have hUN : U ∈ 𝓝 X x,
  {
    apply hB1,
    exact hU,
  },
  have hVN : V ∈ 𝓝 X x,
  {
    apply hB1,
    exact hV,
  },
  have hUV : U ∩ V ∈ 𝓝 X x,
  {
    apply entornos_N3,
    exact hUN,
    exact hVN,
  },
  specialize hB2 _ hUV,
  cases hB2 with W hW,
  use W,
  cases hW with hWB hWUV,
  split, assumption,
  exact hWUV,
end

lemma bases_de_entornos_B4 (B : X → set (set X)) (hB : ∀ x, base_de_entornos x (B x)) : BE4 B :=
begin
  intros x Bx hBx,
  have hbasex := hB x,
  cases hbasex with hBxN hBxV,
  have hBxNx := hBxN hBx,
  cases hBxNx with W hW,
  cases hW with hWab hW,
  cases hW with hxW hWBx,
  rw abierto_sii_entorno_puntos at hWab,
  have hWentx :=  hWab x hxW,
  have h2 := hBxV W hWentx,
  cases h2 with V hV,
  cases hV with hVBx hVW,
  use V,
  split, assumption,
  intros y hy,
  specialize hWab y _,
  {
    apply hVW,
    exact hy,
  },
  have hBy := hB y,
  cases hBy with hByNy hByprop,
  specialize hByprop W hWab,
  cases hByprop with S hS,
  use S,
  cases hS with hSBy hSW,
  split, assumption,
  calc
    S   ⊆  W  : by {assumption,}
    ... ⊆  Bx : by {assumption,}

end


/-
Ahora veremos que una familia que cumpla estas propiedades da lugar a una familia que cumple `N1...N5`

Esta familia es la que definimos aquí:
-/
def superentornos (B : X → set (set X)) (x : X) : set (set X) := { U | ∃ V ∈ B x, V ⊆ U}

/-
Y veamos ahora que si `B` cumple `BE1...BE4`, esta familia que acabamos de definir cumple `N1...N5`
-/
lemma BE1_implica_N1 (B : X → set (set X))  (h : BE1 B) : N1 (superentornos B ) :=
begin 
  intro x,
  specialize h x,
  cases h with U hU,
  use U,
  use U,
  split,
    assumption,
    tauto,
end

lemma BE2_implica_N2 (B : X → set (set X))  (h : BE2 B) : N2 (superentornos B ) :=
begin
  intros x U hU,
  cases hU with V hV,
  cases hV with hVBx hVU,
  apply hVU,
  apply h,
  exact hVBx,
end

lemma BE3_implica_N3 (B : X → set (set X))  (h : BE3 B) : N3 (superentornos B ) :=
begin
  intros x U1 hU1 U2 hU2,
    cases hU1 with  V1 hV1,
    cases hV1 with hV1B hV1U1,
    cases hU2 with V2 hV2,
    cases hV2 with hV2B hV2U2,
    specialize h x V1 hV1B V2 hV2B,
    cases h with W hW,
    cases hW with hWBx hWV1V2,
    use W,
    split,
      assumption,
    {
      intros y hy,
      specialize hWV1V2 hy,
      cases hWV1V2 with hy1 hy2,
      split,
      {
        apply hV1U1,
        exact hy1,
      },
      {
        apply hV2U2,
        exact hy2,
      },
    },
end

lemma  superentornos_N4 (B : X → set (set X)) : N4 (superentornos B) :=
begin
  intros x Ux hUx A hA,
  cases hUx with Vx hVx,
  cases hVx with hVxBx hVxUx,
  use Vx,
  split, assumption,
  calc
    Vx    ⊆   Ux : by {assumption,}
    ...   ⊆   A  : by {assumption,}
end

lemma BE4_implica_N5 (B : X → set (set X)) (h : BE4 B) : N5 (superentornos B) :=
begin
  intros x U hU,
  cases hU with V hV,
  cases hV with hVBx hVU,
  specialize h x V hVBx,
  cases h with W hW,
  cases hW with hWBx hW,
  use W,
  split,
  {
    use W,
    split,
      assumption,
      tauto,
  },
  {
    intros y hy,
    specialize hW y hy,
    cases hW with By hBy,
    cases hBy with hByB hByV,
    use By,
    split, assumption,
      intros z hz,
      apply hVU,
      apply hByV,
      exact hz,
  },
end

/-
Por lo tanto, podemos construir una topología donde esta familia son los entornos:
-/

def topologia_generada_base_entornos (B : X → set (set X))  (h1 : BE1 B) (h2 : BE2 B) (h3 : BE3 B) (h4 : BE4 B) : espacio_topologico X :=
begin
  apply topologia_determinada_familia_entornos (superentornos B),
  {
    apply BE1_implica_N1,
    exact h1,
  },
  {
    apply BE2_implica_N2,
    exact h2,
  },
  {
    apply BE3_implica_N3,
    exact h3,
  },
  {
    apply superentornos_N4,
  },
  {
    apply BE4_implica_N5,
    exact h4,
  },
end


/-
Y por lo tanto, la familia `B` inicial es una base de entornos:
-/
lemma base_entornos_topologia_generada_base_de_entornos (B : X → set (set X))  (h1 : BE1 B) (h2 : BE2 B) (h3 : BE3 B) (h4 : BE4 B) : ∀ x, @base_de_entornos X (topologia_generada_base_entornos B h1 h2 h3 h4 ) x (B x) :=
begin
  intro x,
  split,
  {
    rw entornos_topologia_generada_coinciden,
    intros U hU,
    use U,
    simp [hU],
  },
  {
    rw entornos_topologia_generada_coinciden,
    intros U hU,
    cases hU with V hV,
    cases hV with hVB hVU,
    use V,
    split,
      assumption,
      assumption,
  },
end


/-
Hemos visto que a partir de `B` cumpliento `BE1...BE4` obtenemos una topología para la cual `B` es base de entornos. Veamos
que es única.
-/
lemma base_de_entornos_determina_topologia (X : Type) (B : X → set (set X))  (T1 : espacio_topologico X) (T2 : espacio_topologico X) 
(h1 :  ∀ x : X, @base_de_entornos X T1 x (B x)) (h2 :  ∀ x : X, @base_de_entornos X T2 x (B x)) : T1 = T2 :=
begin
  ext U,
  change @abierto X T1 U ↔ @abierto X T2 U,
  simp only [topologicos.abierto_sii_entorno_puntos],
  split,
  {
    intro h,
    intros x hx,
    specialize h1 x,
    specialize h2 x,
    specialize h x hx,
    cases h1 with h1en h1p,
    cases h2 with h2en h2p,
    specialize h1p U h,
    cases h1p with V hV,
    cases hV with hVB hVU,
    specialize h2en hVB,
    cases h2en with W hW,
    use W,
    simp only [true_and, hW],
    calc
      W   ⊆ V   : by {tauto,}
      ... ⊆ U   : by {assumption,}
  },
  {
    intro h,
    intros x hx,
    specialize h1 x,
    specialize h2 x,
    specialize h x hx,
    cases h1 with h1en h1p,
    cases h2 with h2en h2p,
    specialize h2p U h,
    cases h2p with V hV,
    cases hV with hVB hVU,
    specialize h1en hVB,
    cases h1en with W hW,
    use W,
    simp only [true_and, hW],
    calc
      W   ⊆ V   : by {tauto,}
      ... ⊆ U   : by {assumption,}
  }
end

/-
## Proposición 3.1.21.

Sea `f : X → Y` aplicación continua y abierta entre espacios topológicos y sea `Bx` base de entornos de `x ∈ X`. 
Entonces `f Bx := {f (B) | B ∈ Bx}` es base de entornos de `f (x)`.
-/

lemma prop_3_1_21 {X Y : Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y) (hc : continua f) (hab : abierta f) 
(x : X) (Bₓ : set (set X)) (hB : base_de_entornos x Bₓ) : base_de_entornos (f x) { (f '' U) | U ∈ Bₓ } :=
begin
  cases hB with hBent hBbase,
  split,
  {
    intros V hV,
    simp only [set.mem_set_of_eq, exists_prop] at hV,
    cases hV with U hU,
    cases hU with hUB hUV,
    rw ← hUV,
    rw abierta_sii_imagen_entorno_entorno at hab,
    apply hab,
    specialize hBent hUB,
    apply hBent,
  },
  {
    simp only [exists_prop, mem_set_of_eq, exists_exists_and_eq_and, image_subset_iff],
    intros V hV,
    rw continua_sii_preimagen_entorno_entorno at hc,
    specialize hc x V hV,
    specialize hBbase _ hc,
    cases hBbase  with U hU,
    cases hU with hUB hUV,
    use U,
    split,
      assumption,
      assumption,
  }
end

/-
# Ejercicios
-/

lemma ejer_3_1_2 (Y : Type) [metricos.espacio_metrico Y] (x : Y) (E : set Y) : entorno x E ↔ metricos.entorno x E :=
begin
  sorry,
end

lemma ejer_3_1_3 (X : Type) (x : X) (A : set X) : @entorno X (cofinita X)  x A ↔ x ∈ A ∧ A ∈ @abiertos X (cofinita X) :=
begin
  sorry,
end


lemma ejer_3_1_6_sol (X : Type) [espacio_topologico X] (x : X) (𝓑ₓ : set (set X)) (h𝓑ₓ : base_de_entornos x 𝓑ₓ)
(U : set X) (hx : x ∈ U) (hU : abierto U) : base_de_entornos x { B ∈ 𝓑ₓ | B ⊆ U } :=
begin
  sorry,
end

lemma ejer_3_1_10 (X : Type) [espacio_topologico X] (B : set (set X)) (hB : base B) (x : X) :
base_de_entornos x { U ∈ B | x ∈ U } :=
begin
  sorry,
end

end topologicos

