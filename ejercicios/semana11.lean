import ..sucesiones
import tactic

open topologicos topologicos.espacio_topologico

/-
## Ejercicio 4.4.7
Sea (X, T ) un e.t. Hausdorff y sea S ⊂ X una sucesión convergente. 
Demuestra que Agl S = Lim S y por tanto, toda subsucesión convergente
de S tiene el mismo límite que S.
-/
lemma ejer_4_4_7 (X : Type) [espacio_topologico X] (hX : hausdorff X) 
(s : ℕ → X) (x : X) (hx : x ∈ Lim s) : Agl s = Lim s :=
begin
  sorry,
end


/-
## Ejercicio 4.4.10
Sea X un conjunto infinito no numerable. Consideremos en
él las topologías (X, Tcn) (topología conumerable) y (X, Td) 
(topología discreta).
Demuestra que sólo las sucesiones casiconstantes en X tienen límite
-/
lemma ejer_4_4_10 (X : Type) (x : X) (s : ℕ → X) (hs : x ∈ @Lim X (discreta X) s) : 
  @casiconstante X (discreta X) s x:=
begin
  sorry,
end

lemma ejer_4_4_10_2 (X : Type) (hX : ¬ countable X) (x : X) (s : ℕ → X) (hs : x ∈ @Lim X (conumerable X) s) : 
  @casiconstante X (conumerable X) s x:=
begin
  sorry,
end