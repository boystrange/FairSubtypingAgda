open import Data.Product
open import Data.Vec
open import Data.Unit
open import Codata.Colist
open import Agda.Builtin.Equality
open import Size
open import Data.Nat
open import Data.Fin
open import Codata.Thunk
open import Relation.Unary using (_⊆_)
open import Examples.Colists.Auxiliary.Colist_member

open import is-lib.InfSys

module Examples.Colists.allPos where

  U = Colist ℕ ∞

  data allPosRN : Set where
    allp-Λ allp-t : allPosRN

  allP-Λ-r : FinMetaRule U
  allP-Λ-r .Ctx = ⊤
  allP-Λ-r .comp c =
    [] ,
    -----------------
    []

  allP-t-r : FinMetaRule U
  allP-t-r .Ctx = Σ[ (x , _) ∈ ℕ × Thunk (Colist ℕ) ∞ ] x > 0
  allP-t-r .comp ((x , xs) , _) = 
    xs .force ∷ [] ,
    -----------------
    x ∷ xs

  allPosIS : IS U
  allPosIS .Names = allPosRN
  allPosIS .rules allp-Λ = from allP-Λ-r
  allPosIS .rules allp-t = from allP-t-r

  allPos : U → Set
  allPos = CoInd⟦ allPosIS ⟧

  allPosSpec : U → Set
  allPosSpec xs = ∀{x} → x ∈ xs → x > 0

  allPosSound : allPos ⊆ allPosSpec
  allPosSound {x ∷ xs} ap mem with ap .CoInd⟦_⟧.unfold
  allPosSound {x ∷ xs} ap here | allp-t , ((.x , .xs) , x>0) , refl , prem = x>0
  allPosSound {x ∷ xs} ap (there mem) | allp-t , ((.x , .xs) , _) , refl , prem = allPosSound (prem zero) mem

  allPosSpecCons : ∀{xs} → allPosSpec xs → ISF[ allPosIS ] allPosSpec xs
  allPosSpecCons {[]} _ = allp-Λ , (tt , (refl , λ ()))
  allPosSpecCons {(x ∷ xs)} Sxs = allp-t , (((x , xs) , Sxs here) , (refl , λ {Fin.zero → λ mem → Sxs (there mem)}))

  allPosComplete : allPosSpec ⊆ allPos
  allPosComplete = coind[ allPosIS ] allPosSpec allPosSpecCons

  {- allPos as Container -}

  open import Data.Empty using (⊥)
  open import Data.Container.Indexed
  open import is-lib.InfSys.Container U
  open ISCont

  allPosCont : ISCont
  allPosCont .Command [] = ⊤
  allPosCont .Command (x ∷ xs) = x > 0
  allPosCont .Response {[]} tt = ⊥
  allPosCont .Response {_ ∷ _} _ = Fin 1
  allPosCont .next {_ ∷ xs} _ zero = xs .force

  allPosC : U → Set
  allPosC = ISCont.CoInd⟦ allPosCont ⟧