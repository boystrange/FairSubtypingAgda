open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Level using (Lift) renaming (suc to _++)

module is-lib.InfSys.Ground {l} where

  open import is-lib.InfSys.Base {l}
  open MetaRule
  open IS

  {- Ground Inference Systems -}
  
  GroundIS : Set l → Set (l ++)
  GroundIS U = List U → U → Set l

  GroundF : (U : Set l) → GroundIS U → (U → Set l) → (U → Set l)
  GroundF U is P u = Σ[ pr ∈ List U ] (is pr u × (∀ i → P (lookup pr i)))


  {- Equivalence wrt InfSys -}

  metaR-to-is : ∀{U : Set l} → MetaRule U → GroundIS U
  metaR-to-is record{ C = C ; comp = comp } = λ x x₁ → Σ[ el ∈ C ]
    let pr , concl , side = comp el in
    x ≡ pr × x₁ ≡ concl × side

  F-to-groundF : ∀{U : Set l}{P u}(im : MetaRule U) → RF[ im ] P u → GroundF U (metaR-to-is im) P u
  F-to-groundF im (wit , u≡concl , side , p) = prems im wit , ((wit , refl , u≡concl , side) , p)

  groundF-to-F : ∀{U : Set l}{P u}(im : MetaRule U) → GroundF U (metaR-to-is im) P u → RF[ im ] P u
  groundF-to-F _ (_ , (wit , refl , u≡concl , side) , p) = wit , u≡concl , side , p
