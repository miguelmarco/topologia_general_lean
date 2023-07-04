import .conjuntos
import .topologicos
import .bases
import tactic


open set
open topologicos
open topologicos.espacio_topologico

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
