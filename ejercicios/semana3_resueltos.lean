import ..topologicos
import tactic

open set 
open topologicos
open topologicos.espacio_topologico


/-
# Ejercicio 2.1.3
-/




lemma ejer_2_1_3 (X : Type) [τ : espacio_topologico X] : τ = (discreta X) ↔ ∀ x : X, abierto ({x} : set X) :=
begin
  split,
  {
    intro hτ,
    intro x,
    simp,
    rewrite hτ,
    simp,
  },
  {
    intro h,
    ext U,
    simp,
    have hU : U = ⋃₀  { ({x}) | x ∈ U },
    {
      ext,
      simp,
    },
    rw hU,
    apply abierto_union,
    intros V hV,
    simp at hV,
    cases hV with x hx,
    cases hx with hxU hxV,
    rw ← hxV,
    apply h,
  }
end



/-
# Ejercicio 2.1.5
-/

lemma  ejer_2_1_5_a (X Y : Type) [espacio_topologico X] (f : X → Y) : @continua _ _ _ (indiscreta Y) f:=
begin
  intros U hU,
  simp at *,
  cases hU,
  {
    rw hU,
    apply abierto_vacio,
  },
  {
    rw hU,
    exact abierto_total,
  }
end


/-
# Ejercicio 2.1.6
-/
lemma ejer_2_1_6 (X Y : Type) [Tx : espacio_topologico X] [Ty: espacio_topologico Y] (f : X → Y) : continua f ↔ (@imagen_inversa _ _ _  f).abiertos ⊆ Tx.abiertos :=
begin
  simp,
  split,
  {
    intro h,
    intros U hU,
    simp at hU,
    cases hU with V hV,
    cases hV with hVab hfVU,
    specialize h V hVab,
    rw ← hfVU,
    exact h,
  },
  {
    intro h,
    intros U hU,
    apply h,
    simp,
    use U,
    split,
    {
      exact hU,
    },
    {
      refl,
    }
  }
end

/-
# Ejercicio 2.1.7
-/
lemma ejer_2_1_7 (X Y : Type) [Tx : espacio_topologico X] [Ty: espacio_topologico Y] (f : X → Y) : continua f ↔ Ty.abiertos ⊆  (@imagen_directa _ _ _  f).abiertos  :=
begin
  simp,
  split,
  {
    intro h,
    intros U hU,
    simp,
    apply h,
    exact hU,
  },
  {
    intro h,
    intros U hU,
    apply h,
    exact hU,
  }
end
