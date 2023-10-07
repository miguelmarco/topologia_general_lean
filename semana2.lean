import .metricos
import tactic

open metricos
open metricos.espacio_metrico

/-
Ver que si `A` es un abierto en ℝ^n  y `B` es otro conjunto, `A + B` es abierto.

Lo hacemos en particular para ℝ, aunque la demostración es la misma, una vez que demostramos este lema 
(que es cierto para las distancias usuales en  ℝ^n) :
-/
lemma distancia_invariante (a b c : ℝ ) : d a b = d (a + c) (b + c) :=
begin
  unfold d,
  ring_nf,
end

lemma ejer_1_2_1 (A B : set ℝ ) (hA : abierto A ) : abierto  { ( x + y ) | ( x ∈ A) (y ∈ B )} :=
begin
  intros p hp,
  cases hp with x hp,
  cases hp with hx hp,
  cases hp with y hp,
  cases hp with hy hp,
  specialize hA x hx,
  cases hA with ε hε,
  cases hε with hεpos hεbola,
  use ε,
  split,
  {
    exact hεpos,
  },
  {
    intros z hz,
    unfold bola at hz,
    simp at *,
    use z - y,
    split,
    {
      apply hεbola,
      unfold bola,
      simp,
      rw (distancia_invariante x (z - y) y),
      ring_nf,
      rw hp,
      exact hz,
    },
    {
      use y,
      split,
      {
        exact hy,
      },
      {
        ring_nf,
      },
    },
  },
end

lemma ejer_1_2_7 (X : Type) [espacio_metrico X] (A : set X)  (V : set A) (x : A) :  entorno x V ↔ ∃ (U : set X), entorno ↑x U ∧ {(↑y ) | y ∈ V} = U ∩ A :=
begin
  split,
  {
    intro h,
    cases h with r hr,
    cases hr with hrpos hrbol,
    use (bola ↑x r) ∪ {(↑y ) | y ∈ V} ,
    split,
    {
      use r,
      split,
      {
        exact hrpos,
      },
      {
        intros z hz,
        left,
        exact hz,
      },
    },
    {
      ext z,
      split,
      {
        intro h,
        cases h with y hy,
        cases hy with hyV hyz,
        split,
        {
          right,
          use y,
          split,
          exact hyV,
          exact hyz,
        },
        {
          rw ← hyz,
          exact y.2,
        },
      },
      {
        intro h,
        cases h with h1 h2,
        cases h1,
        {
          use ⟨ z,h2⟩,
          simp,
          apply hrbol,
          exact h1,
        },
        {
          exact h1,
        },
      },
    },
  },
  {
    intro h,
    cases h with U hU,
    cases hU with hUent hU2,
    cases hUent with r hr,
    cases hr with hrpos hrbol,
    use r,
    split, exact hrpos,
    intros z hz,
    cases z with z hzA,
    unfold bola at *,
    simp at hz,
    specialize hrbol hz,
    simp at hrbol,
    have haux : z ∈ U ∩ A,
    {
      split,
      {
        exact hrbol,
      },
      {
        exact hzA,
      },
    },
    rw ← hU2 at haux,
    cases haux with t ht,
    cases ht with htV htZ,
    have haux2 : t =  ⟨z,hzA⟩,
    {
      ext,
      exact htZ,
    },
    rw ← haux2,
    exact htV,
  }
end