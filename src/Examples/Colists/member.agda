open import Data.Product
open import Data.Vec
open import Codata.Colist as Colist
open import Agda.Builtin.Equality
open import Size
open import Codata.Thunk
open import Data.Fin
open import Data.Nat
open import Data.Maybe
open import Examples.Colists.Auxiliary.Colist_member

open import is-lib.InfSys

module Examples.Colists.member {A : Set} where

  U = A × Colist A ∞

  data memberRN : Set where
    mem-h mem-t : memberRN
  
  mem-h-r : FinMetaRule U
  mem-h-r .Ctx = A × Thunk (Colist A) ∞
  mem-h-r .comp (x , xs) = 
    [] , 
    ----------------
    (x , x ∷ xs)

  mem-t-r : FinMetaRule U
  mem-t-r .Ctx = A × A × Thunk (Colist A) ∞
  mem-t-r .comp (x , y , xs) =
    ((x , xs .force) ∷ []) ,
    ----------------
    (x , y ∷ xs)

  memberIS : IS U
  memberIS .Names = memberRN
  memberIS .rules mem-h = from mem-h-r
  memberIS .rules mem-t = from mem-t-r

  _member_ : A → Colist A ∞ → Set
  x member xs = Ind⟦ memberIS ⟧ (x , xs)
  
  memSpec : U → Set
  memSpec (x , xs) = Σ[ i ∈ ℕ ] (Colist.lookup i xs ≡ just x)

  memSpecClosed : ISClosed memberIS memSpec
  memSpecClosed mem-h _ _ = zero , refl
  memSpecClosed mem-t _ pr =
    let (i , proof) = pr Fin.zero in
    (suc i) , proof

  memberSound : ∀{x xs} → x member xs → memSpec (x , xs)
  memberSound = ind[ memberIS ] memSpec memSpecClosed

  -- Completeness using memSpec does not terminate
  -- Product implemented as record. Record projections do not decrease
  memSpec' : U → ℕ → Set
  memSpec' (x , xs) i = Colist.lookup i xs ≡ just x

  memberCompl : ∀{x xs i} → memSpec' (x , xs) i → x member xs
  memberCompl {.x} {x ∷ _} {zero} refl = apply-ind mem-h _ λ ()
  memberCompl {x} {y ∷ xs} {suc i} eq = apply-ind mem-t _ λ{zero → memberCompl eq}

  memberComplete : ∀{x xs} → memSpec (x , xs) → x member xs
  memberComplete (i , eq) = memberCompl eq

  {- Correctness wrt to Agda DataType -}

  ∈-sound : ∀{x xs} → x ∈ xs → x member xs
  ∈-sound here = apply-ind mem-h _ λ ()
  ∈-sound (there mem) = apply-ind mem-t _ λ{zero → ∈-sound mem}

  ∈-complete : ∀{x xs} → x member xs → x ∈ xs
  ∈-complete (fold (mem-h , _ , refl , _)) = here
  ∈-complete (fold (mem-t , _ , refl , prem)) = there (∈-complete (prem zero))