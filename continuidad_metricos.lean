import .metricos
import order.complete_lattice
import tactic

namespace metricos.continuidad
open metricos
open metricos.espacio_metrico
/-
# Continuidad en espacios métricos

En esta sección, `X`, `Y` y `Z` serán espacios métricos, 
y `f` y `g`, aplicaciones entre ellos
-/

variables {X Y Z : Type} [espacio_metrico X] [espacio_metrico Y] [espacio_metrico Z] 
variables (f : X → Y) (g : Y → Z)

--definimos que una función sea contínua en un punto
def continua_en (f : X → Y) (x₀ : X) := ∀ ε > 0, ∃ δ > 0, ∀ x, d x₀ x < δ → d (f x₀) (f x) < ε

-- y que sea contínua en sí
def continua (f : X → Y) := ∀ x , continua_en f x

--vemos la proposición 1.3.6
lemma continua_en_carac_1 (x₀ : X) : continua_en f x₀ ↔ ∀ ε >0, ∃ δ > 0, ∀ x, x ∈ bola x₀ δ → f x ∈ bola (f x₀) ε :=
begin
  refl,  -- es cierto por definición
end

-- y su segunda parte
lemma continua_carac_2 (x₀ : X) : continua_en f x₀ ↔ ∀ ε >0, ∃ δ > 0, f '' (bola x₀ δ ) ⊆ bola (f x₀) ε :=
begin
  simp [bola,continua_en_carac_1],
end

-- ## ejercicio:
-- demostrar esto mismo sin usar la simplificación directa (es decir, haciendo la doble implicación, tomando elementos , etc)


-- una aplicación es contractiva si reduce las distancias
def contractiva (f : X → Y) := ∀ x₀ x₁, d (f x₀) (f x₁) ≤ d x₀ x₁ 

-- # Ejercicio
-- las aplicaciones contractivas son contínuas
example : contractiva f → continua f :=
begin
  sorry,
end

-- definición de continua en términos de entornos
lemma prop_1_3_8 (x₀ : X) : 
continua_en f x₀  ↔ ∀ (V : set Y) , entorno (f x₀ ) V → ∃ (U : set X), (entorno x₀ U ∧ f '' U ⊆ V) :=
begin
  split,
  {
    intro h,
    intros V hV,
    cases hV with ε hε,
    cases hε with hεpos hbol,
    specialize h ε hεpos,
    cases h with δ hδ,
    cases hδ with hδpos hcon,
    use (bola x₀  δ),
    split,
    {
      use δ,
      split, exact hδpos,
      tauto,
    },
    {
      intros y hy,
      apply hbol,
      simp,
      simp at hy,
      cases hy with x hx,
      cases hx with hxd hxy,
      rw ← hxy,
      apply hcon,
      exact hxd,
    }
  },
  {
    intro h,
    intros ε hε,
    let V := bola (f x₀) ε,
    specialize h V,
    have hV : entorno (f x₀) V,
    {
      use ε,
      split, exact hε,
      intros y hy,
      exact hy,
    },
    specialize h hV,
    cases h with U hU,
    cases hU with hUent hfU,
    cases hUent with δ hδ,
    cases hδ with hδpos hδbola,
    use δ,
    split, exact hδpos,
    intros x hx,
    apply hfU,
    use x,
    split,
    {
      apply hδbola,
      exact hx,
    },
    {
      refl,
    }
  }
end

lemma prop_1_3_9 : continua f ↔ ∀ (V : set Y), abierto V → abierto (f ⁻¹' V) :=
begin
  split,
  {
    intro h,
    intros V hV,
    intros x hx,
    specialize h x,
    specialize hV (f x) hx,
    rw prop_1_3_8 at h,
    specialize h V hV,
    cases h with U hU,
    cases hU with hUent hfU,
    cases hUent with δ hδ,
    cases hδ with hδpos hδbola,
    use δ,
    split, exact hδpos,
    intros y hy,
    simp,
    apply hfU,
    use y,
    split,
    {
      apply hδbola,
      exact hy,
    },
    {
      refl,
    }
  },
  {
    intro h,
    intros x₀ ε hε ,
    let V := bola (f x₀) ε,
    specialize h V,
    have hV : abierto V,
    {
      apply bola_abierta,
      exact hε,
    },
    specialize h hV,
    specialize h x₀,
    have hx₀ : x₀ ∈ f ⁻¹' V,
    {
      simp,
      linarith,
    },
    specialize h hx₀,
    cases h with δ hδ,
    cases hδ with hδpos hδbola,
    use δ,
    split, exact hδpos,
    intros x hx,
    specialize hδbola hx,
    exact hδbola,
  },
end 

lemma prop_1_3_10 (hf: continua f) (hg :continua g) : continua (g ∘ f) :=
begin
  rw prop_1_3_9 at *,
  intros W hW,
  specialize hg W hW,
  specialize hf (g ⁻¹' W) hg,
  apply hf,
end

/-
## Ejercicios
-/

lemma ejer_1_3_2 (x₀ : X) (hf : continua_en f x₀) (hg : continua_en g (f x₀)) :
continua_en (g ∘ f)  x₀ :=
begin
  sorry,
end 

-- Añadimos aqui ejercicios de la sección 1.4, para espacios métricos en lugar de pseudométricos

lemma ejer_1_4_1 (x y z : X) :   |d x z - d z y | ≤ d x y :=
begin
  sorry,
end

def lipschitz (f : X → Y) := ∃ k > 0, ∀ x y, d (f x) (f y) ≤ k * (d x y)

lemma ejer_1_4_2 : lipschitz f → continua f :=
begin
  intro h,
  intros x₀  ε hε,
  cases h with k hk,
  cases hk with hkpos hkprop,
  use ε / k,
  split,
  {
    apply div_pos,
    linarith,
    linarith,
  },
  intros x hx,
  specialize hkprop x₀ x,
  have h1 := d1 x₀ x,
  have h2 := d1 (f x₀) (f x),
  have h3 : k * (ε / k) = ε,
  {
    apply mul_div_cancel',
    linarith,
  },
  calc
  d (f x₀ ) (f x)      ≤ k * d x₀ x  : by {exact hkprop,}
  ...                  < k * (ε / k) : by {apply mul_lt_mul', simp, repeat {linarith,}, }
  ...                  = ε          :  by {exact h3,}
end

lemma ejer_1_4_3 (x₀ : X) : continua (d x₀) :=
begin
  intros x ε hε,
  use ε,
  split, linarith,
  intros y hy,
  unfold d,
  have haux := d4 x₀ x  y,
  rw abs_lt,
  split,
  {
    simp,
    linarith,
  },
  {
    have haux2 := d4 x₀ y x,
    have haux3 := d3 x y,
    linarith,
  }
end



end metricos.continuidad