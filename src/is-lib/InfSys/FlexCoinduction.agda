--------------------------------------------------------------------------------
-- This is part of Agda Inference Systems 

open import Agda.Builtin.Equality
open import Data.Product
open import Data.Sum
open import Level
open import Relation.Unary using (_⊆_)

module is-lib.InfSys.FlexCoinduction {𝓁} where

  private
    variable
      U : Set 𝓁
  
  open import is-lib.InfSys.Base {𝓁}
  open import is-lib.InfSys.Induction {𝓁}
  open import is-lib.InfSys.Coinduction {𝓁}
  open MetaRule
  open IS

  {- Generalized inference systems -}

  FCoInd⟦_,_⟧ : ∀{𝓁c 𝓁p 𝓁n 𝓁n'} → (I : IS {𝓁c} {𝓁p} {𝓁n} U) → (C : IS {𝓁c} {𝓁p} {𝓁n'} U) → U → Set _
  FCoInd⟦ I , C ⟧ = CoInd⟦ I ⊓ Ind⟦ I ∪ C ⟧ ⟧

  {- Bounded Coinduction Principle -}

  bdc-lem : ∀{𝓁c 𝓁p 𝓁n 𝓁' 𝓁''} 
      → (I : IS {𝓁c} {𝓁p} {𝓁n} U)
      → (S : U → Set 𝓁') 
      → (Q : U → Set 𝓁'')
      → S ⊆ Q
      → S ⊆ ISF[ I ] S
      → S ⊆ ISF[ I ⊓ Q ] S
  bdc-lem _ _ _ bd cn Su with cn Su
  ... | rn , c , refl , pr = rn , (c , bd Su) , refl , pr

  bounded-coind[_,_] : ∀{𝓁c 𝓁p 𝓁n 𝓁n' 𝓁'} 
      → (I : IS {𝓁c} {𝓁p} {𝓁n} U) 
      → (C : IS {𝓁c} {𝓁p} {𝓁n'} U)
      → (S : U → Set 𝓁')                   
      → S ⊆ Ind⟦ I ∪ C ⟧      -- S is bounded w.r.t. I ∪ C
      → S ⊆ ISF[ I ] S        -- S is consistent w.r.t. I
      → S ⊆ FCoInd⟦ I , C ⟧
  bounded-coind[ I , C ] S bd cn Su = coind[ I ⊓ Ind⟦ I ∪ C ⟧ ] S (bdc-lem I S Ind⟦ I ∪ C ⟧ bd cn) Su

  {- Get Ind from FCoInd -}

  fcoind-to-ind : ∀{𝓁c 𝓁p 𝓁n 𝓁n'}
      {is : IS {𝓁c} {𝓁p} {𝓁n} U}{cois : IS {𝓁c} {𝓁p} {𝓁n'} U} 
      → FCoInd⟦ is , cois ⟧ ⊆ Ind⟦ is ∪ cois ⟧
  fcoind-to-ind co with CoInd⟦_⟧.unfold co
  ... | _ , (_ , sd) , refl , _ = sd

  {- Apply Rule -}

  apply-fcoind : ∀{𝓁c 𝓁p 𝓁n 𝓁n'}
      {is : IS {𝓁c} {𝓁p} {𝓁n} U}{cois : IS {𝓁c} {𝓁p} {𝓁n'} U}
      → (rn : is .Names) → RClosed (is .rules rn) FCoInd⟦ is , cois ⟧
  apply-fcoind rn c pr = apply-coind rn (c , apply-ind (inj₁ rn) c λ i → fcoind-to-ind (pr i)) pr

  {- Postfix - Prefix -}
  
  fcoind-postfix : ∀{𝓁c 𝓁p 𝓁n 𝓁n'}
      {is : IS {𝓁c} {𝓁p} {𝓁n} U}{cois : IS {𝓁c} {𝓁p} {𝓁n'} U}
      → FCoInd⟦ is , cois ⟧ ⊆ ISF[ is ] FCoInd⟦ is , cois ⟧
  fcoind-postfix FCoInd with FCoInd .CoInd⟦_⟧.unfold
  ... | rn , (c , _) , refl , pr = rn , c , refl , pr

  fcoind-prefix : ∀{𝓁c 𝓁p 𝓁n 𝓁n'}
      {is : IS {𝓁c} {𝓁p} {𝓁n} U}{cois : IS {𝓁c} {𝓁p} {𝓁n'} U}
      → ISF[ is ] FCoInd⟦ is , cois ⟧ ⊆ FCoInd⟦ is , cois ⟧
  fcoind-prefix (rn , c , refl , pr) = apply-fcoind rn c pr