import .continuidad_metricos
import  tactic

open metricos
open metricos.espacio_metrico
open metricos.continuidad

variables {X Y Z : Type} [espacio_metrico X] [espacio_metrico Y] [espacio_metrico Z] 
variables (f : X → Y) (g : Y → Z)

example  : contractiva f → continua f :=
begin
  intro h,
  intro x,
  intros ε hε,
  use ε,
  split, exact hε,
  intros y hy,
  specialize h x y,
  calc 
  d (f x) (f y) ≤ d x y : by {exact h,}
  ...            < ε     : by {exact hy,}
end


lemma ejer_1_3_2_sol (x₀ : X) (hf : continua_en f x₀) (hg : continua_en g (f x₀)) :
continua_en (g ∘ f)  x₀ :=
begin
  rw prop_1_3_8 at *,
  intros W hW,
  specialize hg W hW,
  cases hg with V hV,
  cases hV with hVent hgV,
  specialize hf V hVent,
  cases hf with U hU,
  use U,
  cases hU with hUent hfU,
  split,
  {
    exact hUent,
  },
  {
    intros z hz,
    apply hgV,
    cases hz with x hx,
    cases hx with hxU hgfx,
    use (f x),
    split,
    {
      apply hfU,
      use x,
      simp,
      exact hxU,
    },
    {
      exact hgfx,
    }
  }
end 

lemma ejer_1_4_1_sol (x y z : X) :   |d x z - d z y | ≤ d x y :=
begin
  rw abs_le,
  split,
  {
    simp,
    calc 
      d z y   ≤ d z x + d x y  : by {apply d4,}      
      ...     = d x z + d x y  : by {rw d3 x z,}
  },
  {
    simp,
    calc 
      d x z     ≤ d x y + d y z    : by {apply d4,}
      ...       = d x y + d z y    : by {rw d3 y z,}
  }
end

