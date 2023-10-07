import .conjuntos
import .topologicos
import .bases
import tactic


open set
open topologicos
open topologicos.espacio_topologico
open set.finite

variables {X : Type} [espacio_topologico X]

lemma base_discreto_solucion : @base X (discreta X) { ({x}) | x : X} :=
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

section base_metricos
open metricos
open metricos.espacio_metrico

lemma ejer_2_2_sol (X : Type) [espacio_metrico X] : base {(bola x r) | (x : X) ( r > 0)} :=
begin
  split,
  rw topologia_metrico_def,
  {
    intros B hB,
    cases hB with x hxB,
    cases hxB with r hr,
    cases hr with hr hB,
    rw ← hB,
    apply bola_abierta,
    exact hr,
  },
  {
    intros U hU,
    let bolas:= {(bola x r) | (x : X) (r > 0)  },
    let ℱ := {B ∈ bolas | B ⊆ U},
    use ℱ,
    split,
    {
      intros B hB,
      cases hB with hBbola hBU,
      exact hBbola,
    },
    {
      ext,
      split,
      {
        intro hx,
        specialize hU x hx,
        cases hU with r hr,
        cases hr with hrpos hrbolaU,
        use bola x r,
        split,
        {
          split,
          {
            use x,
            use r,
            split,
              exact hrpos,
              refl,
          },
          {
            simp,
            exact hrbolaU,
          },
        },
        {
          simp only [bola_carac, distancia_cero],
          linarith,
        },
      },
      {
        intros hx,
        cases hx with B hB,
        cases hB with hBℱ hxB,
        cases hBℱ with hBbola hBU,
        apply hBU,
        exact hxB,
      },
    },
  },
end

-- otra demostración, usando la caracterización de base
lemma ejer_2_2_sol_2 (X : Type) [metricos.espacio_metrico X] : base {(bola x r) | (x : X) ( r > 0)} :=
begin
  rw caracterizacion_base,
  {
    intros U hU x hxU,
    specialize hU x hxU,
    cases hU with r hr,
    cases hr with hrpos hrbola,
    use bola x r,
    split,
    {
      use x,
      use r,
      split, exact hrpos,
      refl,
    },
    split,
    {
      exact hrbola,
    },
    {
      simp,
      linarith,
    },
  },
  {
    intros B hB,
    intros x hx,
    cases hB with x' hx',
    cases hx' with r hr,
    cases hr with hrpos hrbol,
    simp [← hrbol] at *,
    use r - d x' x ,
    split,
    {
      linarith,
    },
    {
      intro y,
      simp [metricos.bola],
      intro hy,
      have haux := d4 x' x y,
      linarith,
    }
  }
end
end base_metricos

lemma ejer_2_2_6_sol {X : Type} [τ : espacio_topologico X] (B : set (set X))
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


lemma ejer_2_2_8_sol (S : set (set X)) (hsAb : S ⊆ abiertos) : 
subbase S ↔ ∀ (U : set X), abierto U →  ∀ x ∈ U, ∃ (ℱ : set (set X)), set.finite ℱ ∧ ℱ ⊆ S ∧ x ∈ ⋂₀ ℱ ∧ ⋂₀ ℱ ⊆ U:=
begin
  split,
  {
    intro h,
    cases h with hBab hBbas,
    rw caracterizacion_base at hBbas,
    {
      intros U hU x hx,
      specialize hBbas U hU x hx,
      cases hBbas with Bx hBx,
      cases hBx with hBxprop hBxU,
      cases hBxU with hBxU hxBx,
      cases hBxprop with F hF,
      cases hF with hFsfin hFBx,
      use F,
      cases hFsfin with hFS hFfin,
      rw hFBx,
      tauto,
    },
    {
      intros U hU,
      simp at *,
      cases hU with F hF,
      cases hF with hFsfin hFU,
      rw ← hFU,
      cases hFsfin with hFS hFfin,
      apply abierto_interseccion_finita,
        tauto,
        assumption,
    },
  },
  {
    intro h,
    split,
    {
      assumption,
    },
    rw caracterizacion_base,
    {
      intros U hU x hx,
      specialize h U hU x hx,
      cases h with F hF,
      cases hF with hFfin hF2,
      cases hF2 with hFs hxF,
      cases hxF with hxF hFU,
      use ⋂₀ F,
      split,
      {
        use F,
        split,
        split,
        {
          assumption,
        },
        {
          assumption,
        },
        refl,
      },
      split, assumption, assumption,
    },
    {
      intros U hU,
      simp at hU,
      cases hU with F hF,
      cases hF with hFsfin hFU,
      cases hFsfin with hFab hFfin,
      rw ← hFU,
      apply abierto_interseccion_finita,
      {
        tauto,
      },
      {
        exact hFfin,
      },
    },
  }
end

