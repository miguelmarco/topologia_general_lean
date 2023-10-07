import ..bases
import ..cerrados
import tactic

open topologicos topologicos.espacio_topologico



/-
Podemos usar el resultado de caracterizacion de las bases:

caracterizacion_base : ∀ (ℬ : set (set X)),
    ℬ ⊆ abiertos →
    (base ℬ ↔
       ∀ (U : set X),
         abierto U →
         ∀ (x : X), x ∈ U → (∃ (Bₓ : set X) (H : Bₓ ∈ ℬ), Bₓ ⊆ U ∧ x ∈ Bₓ))

-/


lemma ejer_2_2_8  (X : Type) [espacio_topologico X] (S : set (set X)) (hsAb : S ⊆ abiertos) : 
subbase S ↔ ∀ (U : set X), abierto U →  ∀ x ∈ U, ∃ (ℱ : set (set X)), set.finite ℱ ∧ ℱ ⊆ S ∧ x ∈ ⋂₀ ℱ ∧ ⋂₀ ℱ ⊆ U:=
begin
  split,
  {
    intro h,
    unfold subbase at h,
    cases h with hSab hSbase,
    rw caracterizacion_base at hSbase,
    {
      intros U hU,
      specialize hSbase U hU,
      intros x hxU,
      specialize hSbase x hxU,
      cases hSbase with B hB,
      cases hB with hBfam hB2,
      cases hB2 with hBU hxB,
      simp at hBfam,
      cases hBfam with F hF,
      cases hF with hFsubfin hFB,
      cases hFsubfin with hFS hFfin,
      use F,
      split,
      {
        exact hFfin,
      },
      split,
      {
        exact hFS,
      },
      split,
      {
        rw hFB,
        exact hxB,
      },
      {
        rw hFB,
        exact hBU,
      },
    },
    {
      intros U hU,
      simp at hU,
      cases hU with F hF,
      cases hF with hFsubfin hFU,
      cases hFsubfin with hFS hFfin,
      rw ← hFU,
      apply abierto_interseccion_finita,
      {
        calc 
          F   ⊆ S         : by {exact hFS,}
          ... ⊆ abiertos  : by {exact hSab,}
      },
      exact hFfin,
    },
  },
  {
    intro h,
    split,
    {
      exact hsAb,
    },
    {
      rw caracterizacion_base,
      {
        intros U hU x hxU,
        specialize h U hU x hxU,
        cases h with F hF,
        cases hF with hFfin hF2,
        cases hF2 with hFS hF3,
        cases hF3 with hxF hFU,
        use ⋂₀  F,
        use F,
        {
          split,
          {
            split,
            exact hFS,
            exact hFfin,
          },
          {
            refl,
          }
        },
        split,
        {
          exact hFU,
        },
        {
          exact hxF,
        },
      },
      {
        intros U hU,
        simp at hU,
        cases hU with F hF,
        cases hF with hFsubfin hFU,
        cases hFsubfin with hFS hFfin,
        rw ← hFU,
        apply abierto_interseccion_finita,
        {
          calc 
            F    ⊆ S         : by {exact hFS,}
            ...  ⊆ abiertos  : by {exact hsAb,}
        },
        {
          exact hFfin,
        },
      },
    },
  },
end


open metricos metricos.espacio_metrico


lemma ejer_2_4_4_1 (X : Type) [espacio_metrico X] (x : X) (r : ℝ ) : cerrado (disco x r) :=
begin
  unfold cerrado,
  intros x1 hx1,
  simp [disco] at *,
  use (d x x1) - r,
  split,
  {
    linarith,
  },
  {
    intros y hy,
    simp at *,
    have haux := d4 x y  x1,
    have haux2 := d3 x1 y,
    linarith,
  }
end

lemma ejer_2_4_4_2 (X : Type) [espacio_metrico X] (x : X) (r : ℝ ) : cerrado (esfera x r)  :=
begin
  unfold cerrado,
  intros y hy,
  simp at hy,
  by_cases hr : d x y > r,
  {
    use d x y - r,
    split,
    {
      linarith,
    },
    {
      intros z hz,
      simp at hz,
      simp,
      intro hneg,
      rw ← hneg at *,
      have haux := d4 x z y,
      have haux2 := d3 y z,
      linarith,
    },
  },
  {
    use r - d x y,
    split,
    {
      simp at *,
      by_contradiction,
      apply hy,
      linarith,
    },
    {
      intros z hz,
      simp at *,
      have haux := d4 x y z,
      linarith,
    },
  },
end

