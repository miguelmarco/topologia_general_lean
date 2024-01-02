import ..clausura
import ..interior
import tactic

open topologicos topologicos.espacio_topologico

variables (X Y : Type) [espacio_topologico X] [espacio_topologico Y]


/-
# Ejercicio 3.3.13
Sea f : X → Y una aplicación continua y abierta entre espacios
topológicos. Demuestra que si B ⊂ Y , entonces f ⁻¹ ( clausura B) = clausura (f ⁻¹(B))
-/
lemma ejer_3_3_13_sol (B : set Y) (f : X → Y) (hfab : abierta f) (hfcont : continua f) :
    f ⁻¹' (clausura B) = clausura (f ⁻¹' B) :=
begin
  ext x,
  split,
  {
    intro h,
    rw clausura_caracterizacion,
    intros U hU hxU,
    dsimp at h,
    rw clausura_caracterizacion at h,
    specialize h (f '' U ) _ _,
    {
      apply hfab,
      exact hU,
    },
    {
      use x,
      split,
        exact hxU,
        refl,
    },
    rw no_vacio_sii_existe_elemento at ⊢ h,
    cases h with y hy,
    cases hy  with hyB hyim,
    cases hyim with z hz,
    cases hz with hzU hzy,
    use z,
    split,
    {
      simp,
      rw hzy,
      exact hyB,
    },
    {
      exact hzU,
    },
  },
  {
    dsimp,
    rw clausura_caracterizacion,
    intro h,
    rw clausura_caracterizacion,
    intros V hV hfxV,
    let U := f ⁻¹' V,
    specialize h U _ _,
    {
      apply hfcont,
      exact hV,
    },
    {
      exact hfxV,
    },
    rw no_vacio_sii_existe_elemento at ⊢ h,
    cases h with z hz,
    use f z,
    exact hz,
  }
end

/-
# Ejercicio 3.3.17

Sea (X, TX ) e.t. y S subbase de X; demuestra que si A ⊂ X
es denso en X entonces A ∩ S ≠ ∅ ∀S ∈ S, S ≠ ∅.
-/
lemma ejer_3_3_17_sol (S : set (set X)) (hS : subbase S) (A : set X) (hA : denso A) :
  ∀ s ∈ S, s ≠ ∅ → A ∩ s ≠ ∅  :=
begin
intros s hsS hs0,
rw denso_sii_todo_abierto_interseca at hA,
apply hA,
{
  cases hS with hSab hSgen,
  apply hSab,
  exact hsS,
},
{
  exact hs0,
},
end



/-
Ejercicio 3.3.20 Sea f : X → Y una aplicación entre dos espacios topológicos.
Demuestra que f es abierta si y sólo si f (Int A) ⊂ Int f (A).
-/
lemma ejer_3_3_20_sol (f : X → Y) : abierta f ↔ ∀ A , f '' (interior A) ⊆ interior (f '' A) :=
begin
  split,
  {
    intro h,
    intros A,
    let hU := interior_abierto A,
    let hfU := h _ hU,
    unfold interior at ⊢ hfU,
    apply set.subset_sUnion_of_mem,
    split,
    {
      exact hfU,
    },
    {
      simp only [set.image_subset_iff, set.sUnion_subset_iff],
      intros U hU x hx,
      use x,
      simp only [and_true, eq_self_iff_true],
      apply hU.2 hx,
    },
  },
  {
    intro h,
    intros U hU,
    rw ← interior_eq_sii_abierto at hU ⊢ ,
    apply doble_contenido,
    {
      apply interior_contenido,
    },
    {
      specialize h U,
      rw hU at h,
      exact h,
    }
  }
end