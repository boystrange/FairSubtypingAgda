open import Agda.Builtin.Equality
open import Data.Product
open import Size
open import Codata.Thunk

module is-meta.InfSys.Principles {l} where
  private
    variable
      U : Set l

  open import is-meta.InfSys.Base
  open IS

---------------------
-- Induction principle
  ind[_] : (is : IS U) →
           (S : U → Set l) →        -- specification
           ISClosed is S →          -- S is closed
           ∀ {u} → Ind⟦ is ⟧ u → S u
  ind[ is ] S cl (fold (rn , c , refl , sd , pr)) = cl rn sd λ i → ind[ is ] S cl (pr i)

-----------------------------------
-- coinduction proof principle
  coind[_] : (is : IS U) →
            (S : U → Set l) →              -- specification
            (∀ {u} → S u → ISF[ is ] S u) →   -- S is consistent
            ∀ {u}  → S u → CoInd⟦ is ⟧ u
  CoInd⟦_⟧.unfold (coind[ is ] S cn Su) with cn Su
  ... | rn , c , refl , sd , pr = rn , c , refl , sd , λ i → coind[ is ] S cn (pr i)

  scoind[_] : (is : IS U) →
            (S : U → Set l) →              -- specification
            (∀ {u} → S u → ISF[ is ] S u) →   -- S is consistent
            ∀ {u}  → S u → (∀{i} → SCoInd⟦ is ⟧ u i)
  scoind[ is ] S cn Su with cn Su
  ... | rn , c , refl , sd , pr = sfold (rn , c , refl , sd , λ i → λ where .force → scoind[ is ] S cn (pr i))
--------------------------------------------
-- Bounded Coinduction Principle

  bdc-lem : (I : IS U) → (S Q : U → Set l) →
            (∀ {u} → S u → Q u) →
            (∀ {u} → S u → ISF[ I ] S u) →
            ∀ {u} → S u → ISF[ I ⊓ Q ] S u
  bdc-lem I S Q bd cn Su with cn Su
  ... | rn , c , refl , sd , pr = rn , c , refl , (sd , bd Su) , pr

  bounded-coind[_,_] : (I C : IS U) →
                       (S : U → Set l) →                    -- specification
                       (∀ {u} → S u → Ind⟦ I ∪ C ⟧ u) →  -- S is bounded w.r.t. I ∪ C
                       (∀ {u} → S u → ISF[ I ] S u) →  -- S is consistent w.r.t. I
                       ∀ {u} → S u → Gen⟦ I , C ⟧ u
  bounded-coind[ I , C ] S bd cn Su = coind[ I ⊓ Ind⟦ I ∪ C ⟧ ] S (bdc-lem I S Ind⟦ I ∪ C ⟧ bd cn) Su

  bounded-scoind[_,_] : (I C : IS U) →
                       (S : U → Set l) →                    -- specification
                       (∀ {u} → S u → Ind⟦ I ∪ C ⟧ u) →  -- S is bounded w.r.t. I ∪ C
                       (∀ {u} → S u → ISF[ I ] S u) →  -- S is consistent w.r.t. I
                       ∀ {u} → S u → (∀{i} → SGen⟦ I , C ⟧ u i)
  bounded-scoind[ I , C ] S bd cn Su = scoind[ I ⊓ Ind⟦ I ∪ C ⟧ ] S (bdc-lem I S Ind⟦ I ∪ C ⟧ bd cn) Su
