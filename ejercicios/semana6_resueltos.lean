import ..aplicaciones_abiertas
import ..bases
import tactic


open topologicos topologicos.espacio_topologico function

lemma ejer_2_6_8_sol (X Y : Type) [espacio_topologico X] [espacio_topologico Y] (f : X → Y) 
    (hab : abierta f) (hsup : surjective f) (hcon : continua f) (𝓑 : set (set X)) (h𝓑 : base 𝓑) :
    base ({ (f '' B) | B ∈ 𝓑}) :=
  begin
    rw caracterizacion_base,
    {
      intros V hV y hy,
      specialize hsup y,
      cases hsup with x hx,
      specialize hcon V hV,
      rw caracterizacion_base at h𝓑,
      {
        specialize h𝓑 (f ⁻¹' V) hcon x,
        rw ← hx at hy,
        specialize  h𝓑 hy,
        cases h𝓑 with B hB,
        cases hB with hB𝓑 hB2,
        cases hB2 with hBV hxB,
        use (f '' B),
        split,
        {
          use B,
          split,
            exact hB𝓑,
            refl,
        },
        split,
        {
          simp only [set.image_subset_iff],
          exact hBV,
        },
        {
          use x,
          tauto,
        },
      },
      {
        cases h𝓑 with h𝓑ab h𝓑,
        exact h𝓑ab,
      },
    },
    {
      intros V hV,
      cases hV with B hB,
      cases hB,
      rw ← hB_h,
      apply hab,
      apply h𝓑.1,
      exact hB_w,
    }
  end