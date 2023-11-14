import ..clausura
import tactic

open topologicos topologicos.espacio_topologico set

section ejer_3_2_5
open metricos metricos.espacio_metrico

/-
## Ejercicio 3.2.5

En este serán útiles los siguientes lemas sobre ínfimos:

`le_antisymm` : a ≤ b → b ≤ a → a = b
`real.Inf_le_iff` :  bdd_below S → S.nonempty →  ∀ {a : ℝ}, Inf S ≤ a ↔ ∀ (ε : ℝ), 0 < ε → (∃ (x : ℝ) (H : x ∈ S), x < a + ε)
`real.Inf_nonneg` : ∀ (S : set ℝ), (∀ (x : ℝ), x ∈ S → 0 ≤ x) → 0 ≤ Inf S
-/
example (X : Type) [espacio_metrico X] (A : set X) (hA : A ≠ ∅ ): clausura A = {x : X | Inf  {(d x y) | y ∈ A } = 0 } :=
begin
  ext x,
  rw clausura_caracterizacion,
  split,
  {
    intro h,
    simp only [set.mem_set_of_eq],
    apply le_antisymm,
    {
      rw real.Inf_le_iff,
      {
        intros ε hε,
        specialize h (bola x ε) _ _,
        {
          apply bola_abierta,
          exact hε,
        },
        {
          simp only [metricos.bola_carac, metricos.distancia_cero,hε],
        },
        rw no_vacio_sii_existe_elemento at h,
        cases h with y hy,
        cases hy with hyA hyb,
        use d x y,
        use y,
          simp only [eq_self_iff_true, and_self, hyA],
          simp only [zero_add],
          exact hyb,
      },
      {
        use 0,
        intros z hz,
        cases hz with y hy,
        cases hy with hyA hyz,
        rw ← hyz,
        apply d1,
      },
      {
        specialize h univ abierto_total _,
        {
          triv,
        },
        rw no_vacio_sii_existe_elemento at h,
        cases h with y hy,
        use d x y,
        use y,
        simp only [and_true, eq_self_iff_true],
        simp only [set.inter_univ] at hy,
        exact hy,
      },
    },
    {
      apply real.Inf_nonneg,
      intros r hr,
      cases hr with y hy,
      cases hy with hyA hdxy,
      rw ← hdxy,
      apply d1,
    },
  },
  {
    intro h,
    simp only [set.mem_set_of_eq] at h,
    intros V hV hxV,
    rw no_vacio_sii_existe_elemento,
    have h2 := le_of_eq h,
    rw real.Inf_le_iff at h2,
    specialize hV x hxV,
    cases hV with r hr,
    cases hr with hr0 hrb,
    {
      specialize h2 r hr0,
      simp only [exists_prop, mem_set_of_eq, zero_add, exists_exists_and_eq_and] at h2,
      cases h2 with y hy,
      cases hy with hyA hdxy,
      use y,
      split,
        exact hyA,
      {
        apply hrb,
        exact hdxy,
      },
    },
    {
      use 0,
      intros r hr,
      rcases hr with ⟨z,⟨hz1,hz2⟩⟩,
      rw ← hz2,
      apply d1,
    },
    {
      rw no_vacio_sii_existe_elemento at hA,
      cases hA with y hy,
      use d x y,
      use y,
      tauto,
    }
  }
end

end ejer_3_2_5

open function


/-
## Ejercicio 3.2.7
-/
example (X Y : Type) [espacio_topologico X] [espacio_topologico Y] (f : X → Y) (hfsup : surjective f) (hcon : continua f) 
    (D : set X) (hD : denso D): denso (f '' D) :=
begin
  rw denso_sii_todo_abierto_interseca at ⊢ hD,
  intros U hU hnO,
  specialize hcon U hU,
  specialize hD (f ⁻¹' U) hcon _,
  {
    simp only [conjunto_vacio_sii_todo_elemento_no, ne.def, set.mem_preimage, not_forall, set.not_not_mem, abierto_def,
  set.mem_inter_iff, not_and, exists_prop, forall_exists_index] at *,
    cases hnO with y hy,
    specialize hfsup y,
    cases hfsup with x hx,
    use x,
    rw hx,
    exact hy,
  },
  simp at *,
  rw conjunto_vacio_sii_todo_elemento_no at ⊢  hD,
  push_neg at ⊢ hD,
  cases hD with x hx,
  cases hx with hx1 hx2,
  use f x,
  split,
  {
    use x,
    simp only [hx1, eq_self_iff_true, and_self],
  },
  assumption,
end


/-
## Ejercicio 3.2.8

En este es un poco pesado ir cambiando de conjuntos en `X` (con suu respectiva topología) a conjuntos en `↥Y` con la suya.

Recordar que los elementos de `↥Y` son parejas del tipo `⟨x, x ∈ Y⟩`. Convertir un elemento de `↥Y` al correspondente de `X`,
o un conjunto de `↥Y` a uno de `X` se hace con `↑x`. Convertir un conjunto de `X` a uno de `↥Y` se hace con `A ↓∩ Y`.

Es recomendable usar `simp` a menudo.
-/


example (X : Type) [espacio_topologico X] (Y : set X) (A : set Y) : ↑(clausura A) = (clausura ↑A) ∩ Y :=
begin
  ext x,
  split,
  {
    intro h,
    cases h with y hy,
    cases hy with hy hyx,
    rw clausura_caracterizacion at hy,
    split,
    {
      rw clausura_caracterizacion,
      intros V hV hxV,
      specialize hy (V ↓∩ Y) _,
      {
        use V,
        simp only [restringe_igual, eq_self_iff_true, and_self, hV],
      },
      rw no_vacio_sii_existe_elemento,
      specialize hy _,
      {
        simp only [pert_restringe_def],
        rw hyx,
        exact hxV,
      },
      rw no_vacio_sii_existe_elemento at hy,
      cases hy with z hz,
      cases hz with hzZ hzy,
      use z,
      split,
      {
        simp only [hzZ, pertenece_eleva_def],
      },
      simp only [pert_restringe_def] at hzy,
      exact hzy,
    },
    rw ←hyx,
    simp only [subtype.coe_prop],
  },
  {
    intro h,
    cases h with h1 h2,
    use ⟨x,h2⟩,
    split,
    {
      rw clausura_caracterizacion,
      intros V hV hxV,
      cases hV with U hU,
      cases hU with hUab hUV,
      rw clausura_caracterizacion at h1,
      specialize h1 U hUab _,
      {
        rw ← hUV at hxV,
        simp only [pert_restringe_def, subtype.coe_mk] at hxV,
        exact hxV,
      },
      rw no_vacio_sii_existe_elemento at ⊢ h1,
      cases h1 with y hy,
      cases hy with hyA hyU,
      cases hyA with z hz,
      cases hz with hzA hzy,
      use z,
      split,
      {
        exact hzA,
      },
      {
        rw ← hUV,
        simp only [pert_restringe_def,hzy,hyU],
      },
    },
    {
      refl,
    }
  },
end