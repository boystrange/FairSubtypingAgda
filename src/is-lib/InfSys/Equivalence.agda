open import Agda.Builtin.Equality
open import Data.Product
open import Data.Sum
open import Codata.Thunk
open import Size

module is-lib.InfSys.Equivalence {l} where

  private
    variable
      U : Set l

  open import is-lib.InfSys.Base {l}
  open import is-lib.InfSys.Coinduction {l}
  open import is-lib.InfSys.SCoinduction {l}
  open IS
  
  -- Equivalence CoInd and SCoInd

  coind-size : {is : IS U} →  ∀ {u} → CoInd⟦ is ⟧ u → ∀ {i} → SCoInd⟦ is ⟧ u i
  coind-size p-coind with CoInd⟦_⟧.unfold p-coind
  ... | rn , c , refl , sd , pr = sfold (rn , c , refl , sd , λ i → λ where .force → coind-size (pr i) )

  size-coind : {is : IS U} → ∀ {u} → (∀ {i} → SCoInd⟦ is ⟧ u i) → CoInd⟦ is ⟧ u
  size-coind {is = is} p-scoind = coind[ is ] (λ u → ∀ {j} → SCoInd⟦ is ⟧ u j) scoind-postfix p-scoind