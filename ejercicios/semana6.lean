import ..aplicaciones_abiertas
import ..bases
import tactic


open topologicos topologicos.espacio_topologico function

lemma ejer_2_6_8 (X Y : Type) [espacio_topologico X] [espacio_topologico Y] (f : X → Y) 
    (hab : abierta f) (hsup : surjective f) (hcon : continua f) (𝓑 : set (set X)) (h𝓑 : base 𝓑) :
    base ({ (f '' B) | B ∈ 𝓑}) :=
begin
  sorry,
end