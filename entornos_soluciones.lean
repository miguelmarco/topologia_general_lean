import .entornos
import tactic

open topologicos topologicos.espacio_topologico

lemma ejer_3_1_2_sol (Y : Type) [metricos.espacio_metrico Y] (x : Y) (E : set Y) : entorno x E ↔ metricos.entorno x E :=
begin
    split,
    {
      intro h,
      cases h with U hU,
      cases hU with hUab hU2,
      cases hU2 with hxU hUE,
      specialize hUab x hxU,
      cases hUab with r hr,
      cases hr with hrpos hrbol,
      use r,
      split,
        assumption,
        calc
          metricos.bola x r   ⊆   U  :  by {assumption,}
          ...                 ⊆   E  :  by {assumption,}
    },
    {
      intro h,
      {
        cases h with r hr,
        cases hr with hrpos hrbol,
        use metricos.bola x r,
        split,
        {
          apply metricos.bola_abierta,
          exact hrpos,
        },
        split,
        {
          simp only [metricos.bola_carac, metricos.distancia_cero],
          linarith,
        },
        {
          assumption,
        }
      }
    },
end

lemma ejer_3_1_3_sol (X : Type) (x : X) (A : set X) : @entorno X (cofinita X)  x A ↔ x ∈ A ∧ A ∈ @abiertos X (cofinita X) :=
begin
  split,
  {
    intro h,
    cases h with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUA,
    split,
    {
      apply hUA,
      exact hxU,
    },
    cases hUab,
    {
      left,
      simp only [set.mem_set_of_eq] at *,
      apply set.finite.subset  hUab,
      simp only [set.compl_subset_compl],
      exact hUA,
    },
    simp only [set.mem_singleton_iff] at hUab,
    rw hUab at hxU,
    cases hxU,
  },
  {
    intro h,
    cases h with hxA hAab,
    use A,
    tauto,
  }
end

lemma ejer_3_1_6_sol (X : Type) [espacio_topologico X] (x : X) (𝓑ₓ : set (set X)) (h𝓑ₓ : base_de_entornos x 𝓑ₓ)
(U : set X) (hx : x ∈ U) (hU : abierto U) : base_de_entornos x { B ∈ 𝓑ₓ | B ⊆ U } :=
begin
  cases h𝓑ₓ with h𝓑ₓ𝓝 h𝓑ₓ,
  split,
  {
    intros BV hV,
    cases hV with hV𝓑ₓ hBU,
    apply h𝓑ₓ𝓝,
    exact hV𝓑ₓ,
  },
  {
    intros V hV,
    have hU𝓝 : U ∈ 𝓝 X x,
    {
      rw abierto_sii_entorno_puntos at hU,
      apply hU,
      exact hx,
    },
    have hUV𝓝 : U ∩ V ∈ 𝓝 X x,
    {
      apply entornos_N3,
        assumption,
        assumption,
    },
    specialize h𝓑ₓ (U ∩ V) hUV𝓝,
    cases h𝓑ₓ with W hW,
    cases hW with hW𝓑ₓ hWUV,
    use W,
    split,
    {
      simp only [set.mem_sep_iff],
      split,
        exact hW𝓑ₓ,
      calc
        W     ⊆ U ∩ V : by {assumption,}
        ...   ⊆ U     : by {simp only [set.inter_subset_left],}
    },
    calc
      W       ⊆ U ∩ V : by {assumption,}
        ...   ⊆ V     : by {simp only [set.inter_subset_right],}
  }
end

lemma ejer_3_1_10 (X : Type) [espacio_topologico X] (B : set (set X)) (hB : base B) (x : X) :
base_de_entornos x { U ∈ B | x ∈ U } :=
begin

  split,
  {
    cases hB with hBab hBbas,
    intros U hU,
    cases hU with hUB hxU,
    specialize hBab hUB,
    change (abierto U) at hBab,
    rw abierto_sii_entorno_puntos at hBab,
    apply hBab,
    exact hxU,
  },
  {
    intros V hV,
    cases hV with W hW,
    cases hW with hWab hW2,
    cases hW2 with hxW hWU,
    rw caracterizacion_base at hB,
    {
      specialize hB W hWab x hxW,
      cases hB with Bₓ hBₓ,
      cases hBₓ with hBₓB hBₓ2,
      cases hBₓ2 with hBWₓ hxBₓ,
      use Bₓ,
      split,
      {
        simp only [set.mem_sep_iff],
        split,
          assumption,
          assumption,
      },
      calc
        Bₓ  ⊆ W : by {assumption,}
        ... ⊆ V : by {assumption,}
    },
    {
      exact hB.1,
    }
  }
end
