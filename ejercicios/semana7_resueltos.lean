import ..metricos
import ..entornos
import tactic

open topologicos topologicos.espacio_topologico

/-
## Ejercicio 3.1.2
-/

lemma ejercicio_3_1_2_sol (X : Type) [metricos.espacio_metrico X] (x : X) (U : set X) : metricos.entorno x U ↔ entorno x U :=
begin
  split,
  {
    intro h,
    cases h with r hr,
    cases hr with hrpos hrbola,
    use (metricos.bola x r),
    split,
    {
      apply metricos.bola_abierta,
      exact hrpos,
    },
    split,
    {
      simp only [metricos.bola_carac, metricos.distancia_cero],
      exact hrpos,
    },
      exact hrbola,
  },
  {
    intro h,
    cases h with V hV,
    cases hV with hVab hV2,
    cases hV2 with hxV hVU,
    specialize hVab x hxV,
    cases hVab with r hr,
    cases hr with hrpos hrbola,
    use r,
    split,
      exact hrpos,
    {
      calc
        metricos.bola x r ⊆ V   : by {exact hrbola,}
        ...               ⊆ U   : by {exact hVU,}
    },
  }
end


/-
## Ejercicio 3.1.6
-/
lemma ejercicio_3_1_6_sol (X : Type) [espacio_topologico X] (x : X) (𝓑 : set (set X)) (h𝓑 : base_de_entornos x 𝓑 ) (U : set X) (hU : abierto U)  (hx : x ∈ U) :
    base_de_entornos x { B ∈ 𝓑 | B ⊆ U} :=
begin
  cases h𝓑 with h𝓑𝓝 h𝓑bas,
  split,
  {
    intros B hB,
    apply h𝓑𝓝,
    exact hB.1,
  },
  {
    intros V hV,
    have nW := h𝓑bas V hV,
    cases nW with W hW,
    cases hW with hW𝓑 hWV,
    specialize h𝓑bas (W ∩ U) _,
    {
      apply entornos_N3,
      {
        apply h𝓑𝓝,
        exact hW𝓑,
      },
      {
        use U,
        tauto,
      },
    },
    cases h𝓑bas with Z hZ,
    cases hZ with hZ𝓑 hzWU,
    use Z,
    split,
    {
      simp only [true_and, set.mem_sep_iff, hZ𝓑],
      calc 
        Z     ⊆ W ∩ U : by {assumption,}
        ...   ⊆ U     : by {simp only [set.inter_subset_right],}
    },
    {
      calc 
        Z     ⊆ W ∩ U : by {assumption,}
        ...   ⊆ W     : by {simp only [set.inter_subset_left]}
        ...   ⊆ V     : by {assumption,}
    },
  },
end

lemma ejer_3_1_7_sol (X : Type) [espacio_topologico X] (A : set X) (x : A) (𝓑 : set (set X)) (h𝓑 : base_de_entornos ↑x 𝓑)  :
    base_de_entornos x {(E ↓∩ A) | E ∈ 𝓑} :=
begin
  split,
  cases h𝓑 with h𝓑1 h𝓑2,
  {
    intros EA hEA,
    cases hEA with E hE,
    cases hE with hE𝓑 hEEA,
    specialize h𝓑1 hE𝓑,
    cases h𝓑1 with U hU,
    cases hU with hUab hU2,
    cases hU2 with hxU hUE,
    use (U ↓∩ A),
    split,
    {
      use U,
      split,
        assumption,
        refl,
    },
    split,
    {
      simp only [pert_restringe_def],
      exact hxU,
    },
    {
      rw ← hEEA,
      simp only [restringe_contenido,and_true, set.subset_inter_iff, set.inter_subset_right],
      calc
        U ∩ A ⊆ U : by {simp only [set.inter_subset_left],}
        ...   ⊆ E : by {assumption,}
    },
  },
  {
    intros V hV,
    cases hV with W hW,
    cases hW with hWab hW2,
    cases hW2 with hxW hWV,
    simp only [exists_prop, set.mem_set_of_eq, exists_exists_and_eq_and],
    cases hWab with U hU,
    cases hU with hUab hUW,
    cases h𝓑 with h𝓑1 h𝓑2,
    specialize h𝓑2 U _,
    {
      use U,
      split,
        assumption,
      split,
      {
        rw ← hUW at hxW,
        simp only [pert_restringe_def] at hxW,
        exact hxW,
      },
      tauto,
    },
    cases h𝓑2 with Z hZ,
    cases hZ with hZ𝓑 hZU,
    use Z,
    split,
      assumption,
    {
      rw ← hUW at hWV,
      have haux : Z ∩ A ⊆ U,
      {
        calc
          Z ∩ A  ⊆ Z : by {simp only [set.inter_subset_left],}
          ...    ⊆ U : by {assumption,}
      },
      calc
        (Z ↓∩ A) ⊆ (U ↓∩ A)  : by {simp [haux],}
        ...      ⊆ V         : by {assumption,}
    }
  }
end