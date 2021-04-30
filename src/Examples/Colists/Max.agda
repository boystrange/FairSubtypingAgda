open import Data.Nat
open import Data.Vec
open import Data.Product
open import Data.Sum
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Bool
open import Data.Empty
open import Codata.Colist
open import Codata.Thunk
open import Size
open import Examples.Colists.Auxiliary.Colist_member
open import Examples.Colists.Auxiliary.MaxOf

open import is-lib.InfSys

module Examples.Colists.Max where

  U = ℕ × Colist ℕ ∞

  data maxElemRN : Set where 
    max-h max-t : maxElemRN

  data maxElemCoRN : Set where 
    co-max-h : maxElemCoRN

  max-h-r : FinMetaRule U
  max-h-r .Ctx = Σ[ (_ , xs) ∈ ℕ × Thunk (Colist ℕ) ∞ ] xs .force ≡ []
  max-h-r .comp ((x , xs) , _) =
    [] ,
    --------------
    (x , x ∷ xs)

  max-t-r : FinMetaRule U
  max-t-r .Ctx = Σ[ (x , y , z , _) ∈ ℕ × ℕ × ℕ × Thunk (Colist ℕ) ∞ ] z ≡ max x y
  max-t-r .comp ((x , y , z , xs) , _) =
    (x , xs .force) ∷ [] ,
    --------------
    (z , y ∷ xs)

  co-max-h-r : FinMetaRule U
  co-max-h-r .Ctx = ℕ × Thunk (Colist ℕ) ∞
  co-max-h-r .comp (x , xs) =
    [] ,
    --------------
    (x , x ∷ xs)


  maxElemIS : IS U
  maxElemIS .Names = maxElemRN
  maxElemIS .rules max-h = from max-h-r
  maxElemIS .rules max-t = from max-t-r

  maxElemCoIS : IS U
  maxElemCoIS .Names = maxElemCoRN
  maxElemCoIS .rules co-max-h = from co-max-h-r

  _maxElem_ : ℕ → Colist ℕ ∞ → Set
  x maxElem xs = FCoInd⟦ maxElemIS , maxElemCoIS ⟧ (x , xs)

  _maxElemᵢ_ : ℕ → Colist ℕ ∞ → Set
  x maxElemᵢ xs = Ind⟦ maxElemIS ∪ maxElemCoIS ⟧ (x , xs)

  maxSpec inSpec geqSpec : U → Set
  inSpec (x , xs) = x ∈ xs
  geqSpec (x , xs) = ∀{n} → n ∈ xs → x ≡ max x n
  maxSpec u = inSpec u × geqSpec u

  maxElemSound-in-ind : ∀{x xs} → x maxElemᵢ xs → inSpec (x , xs)
  maxElemSound-in-ind (fold (inj₁ max-h , _ , refl , _)) = here
  maxElemSound-in-ind (fold (inj₁ max-t , (_ , eq) , refl , prem)) with max-refl-eq eq
  maxElemSound-in-ind (fold (inj₁ max-t , (_ , eq) , refl , prem)) | inj₁ refl = there (maxElemSound-in-ind (prem zero))
  maxElemSound-in-ind (fold (inj₁ max-t , (_ , eq) , refl , prem)) | inj₂ refl = here
  maxElemSound-in-ind (fold (inj₂ co-max-h , _ , refl , _)) = here

  maxElemSound-in : ∀{x xs} → x maxElem xs → inSpec (x , xs)
  maxElemSound-in max = maxElemSound-in-ind (fcoind-to-ind max)

  maxElemSound-gr : ∀{x xs} → x maxElem xs → geqSpec (x , xs)
  maxElemSound-gr max here with max .CoInd⟦_⟧.unfold
  maxElemSound-gr max here | max-h , _ , refl , _ = max-self
  maxElemSound-gr max here | max-t , ((_ , eq) , _) , refl , _ with max-refl-eq eq
  ... | inj₁ refl = eq
  ... | inj₂ refl = max-self 
  maxElemSound-gr max (there mem) with max .CoInd⟦_⟧.unfold
  maxElemSound-gr max (there mem) | max-h , ((_ , eq) , _) , refl , _ = ⊥-elim (mem-abs mem eq)
  maxElemSound-gr max (there mem) | max-t , ((_ , eq) , _) , refl , pr with max-refl-eq eq
  ... | inj₁ refl = maxElemSound-gr (pr zero) mem
  ... | inj₂ refl =
    let rec = maxElemSound-gr (pr zero) mem in
    max-trans rec (max-comm eq)

  maxElemSound : ∀{x xs} → x maxElem xs → maxSpec (x , xs)
  maxElemSound max = maxElemSound-in max , maxElemSound-gr max

  maxSpecBounded : ∀{x xs} → inSpec (x , xs) → geqSpec (x , xs) → x maxElemᵢ xs
  maxSpecBounded here _ = apply-ind (inj₂ co-max-h) _ λ ()
  maxSpecBounded (there mem) gr = apply-ind (inj₁ max-t) (_ , gr here) λ{zero → maxSpecBounded mem λ m → gr (there m)}

  postulate
    old-max : ∀{n x y xs ys} → Thunk.force xs ≡ (y ∷ ys) →
                    maxSpec (n , (x ∷ xs)) → Σ[ m ∈ ℕ ] maxSpec (m , (y ∷ ys))

  maxSpecCons : ∀{x xs} → inSpec (x , xs) → geqSpec (x , xs) → ISF[ maxElemIS ] maxSpec (x , xs)
  maxSpecCons {x} {x ∷ xs} here gr with xs .force | inspect (λ t → t .force) xs
  maxSpecCons {x} {x ∷ xs} here gr | [] | [ eq ] = max-h , (_ , eq) , refl , λ ()
  maxSpecCons {x} {x ∷ xs} here gr | _ ∷ _ | [ eq ] =
    let old , mem , gr' = old-max eq (here , gr) in
    let mem-xs = subst (λ xs → old ∈ xs) (sym eq) mem in
    max-t , (_ , max-comm (gr (there mem-xs))) , refl , λ{zero → mem-xs , λ m → gr' (subst (λ xs → _ ∈ xs) eq m)}
  maxSpecCons {x} {.(_ ∷ _)} (there mem) gr = max-t , (_ , gr here) , refl , λ{zero → mem , λ m → gr (there m)}


  maxElemComplete : ∀{x xs} → maxSpec (x , xs) → x maxElem xs
  maxElemComplete =
    bounded-coind[ maxElemIS , maxElemCoIS ] maxSpec (λ{(x , xs) → maxSpecBounded x xs}) λ{(x , xs) → maxSpecCons x xs}