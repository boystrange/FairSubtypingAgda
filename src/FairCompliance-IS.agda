-- MIT License

-- Copyright (c) 2021 Luca Ciccone and Luca Padovani

-- Permission is hereby granted, free of charge, to any person
-- obtaining a copy of this software and associated documentation
-- files (the "Software"), to deal in the Software without
-- restriction, including without limitation the rights to use,
-- copy, modify, merge, publish, distribute, sublicense, and/or sell
-- copies of the Software, and to permit persons to whom the
-- Software is furnished to do so, subject to the following
-- conditions:

-- The above copyright notice and this permission notice shall be
-- included in all copies or substantial portions of the Software.

-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
-- EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
-- OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
-- NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
-- HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
-- WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
-- FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
-- OTHER DEALINGS IN THE SOFTWARE.

{-# OPTIONS --guardedness #-}

open import Data.Product
open import Data.Empty
open import Data.Sum
open import Data.Vec
open import Data.Fin
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Unary using (_∈_; _⊆_; _∉_)
open import Relation.Binary.Definitions
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Common

open import is-lib.InfSys

module FairCompliance-IS {𝕋 : Set} (message : Message 𝕋) where
  
  open import SessionType message
  open import Session message
  open import Transitions message
  
  private
    U : Set
    U = SessionType × SessionType

  data FCompIS-RN : Set where
    client-end : FCompIS-RN
    oi io : FCompIS-RN

  data FCompCOIS-RN : Set where
    co-oi co-io : FCompCOIS-RN

  client-end-r : FinMetaRule U
  client-end-r .Ctx = Σ[ (S , T) ∈ SessionType × SessionType ] Win S × Defined T
  client-end-r .comp ((S , T) , _) =
    [] ,
    --------------------
    (S , T)

  OI-r : MetaRule U
  OI-r .Ctx = Σ[ (f , _) ∈ Continuation × Continuation ] Witness f
  OI-r .Pos ((f , _) , _) = Σ[ t ∈ 𝕋 ] t ∈ dom f
  OI-r .prems ((f , g) , _) (t , _) = f t .force , g t .force
  OI-r .conclu ((f , g) , _) = out f , inp g

  IO-r : MetaRule U
  IO-r .Ctx = Σ[ (_ , g) ∈ Continuation × Continuation ] Witness g
  IO-r .Pos ((_ , g) , _) = Σ[ t ∈ 𝕋 ] t ∈ dom g
  IO-r .prems ((f , g) , _) (t , _) = f t .force , g t .force
  IO-r .conclu ((f , g) , _) = inp f , out g

  co-OI-r : FinMetaRule U
  co-OI-r .Ctx = Σ[ (f , _ , x) ∈ Continuation × Continuation × 𝕋 ] x ∈ dom f
  co-OI-r .comp ((f , g , x) , _) =
    (f x .force , g x .force) ∷ [] ,
    --------------------
    (out f , inp g)

  co-IO-r : FinMetaRule U
  co-IO-r .Ctx = Σ[ (_ , g , x) ∈ Continuation × Continuation × 𝕋 ] x ∈ dom g
  co-IO-r .comp ((f , g , x) , _) =
    (f x .force , g x .force) ∷ [] ,
    --------------------
    (inp f , out g)

  FCompIS : IS U
  FCompIS .Names = FCompIS-RN
  FCompIS .rules client-end = from client-end-r
  FCompIS .rules oi = OI-r
  FCompIS .rules io = IO-r

  FCompCOIS : IS U
  FCompCOIS .Names = FCompCOIS-RN
  FCompCOIS .rules co-oi = from co-OI-r
  FCompCOIS .rules co-io = from co-IO-r

  _⊢_ : SessionType → SessionType → Set
  S ⊢ T = FCoInd⟦ FCompIS , FCompCOIS ⟧ (S , T)

  _⊢ᵢ_ : SessionType → SessionType → Set
  S ⊢ᵢ T = Ind⟦ FCompIS ∪ FCompCOIS ⟧ (S , T)

  {- Properties -}

  ¬nil-⊢ : ∀{S} → ¬ (nil ⊢ S)
  ¬nil-⊢ fc with fc .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (() , _)) , _) , refl , _

  ⊢ᵢ->succeed : ∀{S T} → S ⊢ᵢ T → MaySucceed (S # T)
  ⊢ᵢ->succeed (fold (inj₁ client-end , ((S , T) , (win , def)) , refl , _)) = (S # T) , ε , win#def win def
  ⊢ᵢ->succeed (fold (inj₁ oi , ((f , g) , (t , ok)) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ->succeed (pr (t , ok)) in
    Sys' , sync (out ok) inp ◅ red-Sys' , Succ
  ⊢ᵢ->succeed (fold (inj₁ io , ((f , g) , (t , ok)) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ->succeed (pr (t , ok)) in
    Sys' , sync inp (out ok) ◅ red-Sys' , Succ
  ⊢ᵢ->succeed (fold (inj₂ co-oi , (_ , ok-b) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ->succeed (pr zero) in
    Sys' , sync (out ok-b) inp ◅ red-Sys' , Succ
  ⊢ᵢ->succeed (fold (inj₂ co-io , (_ , ok-b) , refl , pr)) =
    let Sys' , red-Sys' , Succ = ⊢ᵢ->succeed (pr zero) in
    Sys' , sync inp (out ok-b) ◅ red-Sys' , Succ

  maysucceed->⊢ᵢ : ∀{S T Sys} → Reductions (S # T) Sys → Success Sys → S ⊢ᵢ T
  maysucceed->⊢ᵢ ε (win#def win def) = apply-ind (inj₁ client-end) (_ , (win , def)) λ ()
  maysucceed->⊢ᵢ (sync (out ok) inp ◅ red) Succ =
    let rec = maysucceed->⊢ᵢ red Succ in
    apply-ind (inj₂ co-oi) (_ , ok) λ{zero → rec}
  maysucceed->⊢ᵢ (sync inp (out ok) ◅ red) Succ =
    let rec = maysucceed->⊢ᵢ red Succ in
    apply-ind (inj₂ co-io) (_ , ok) λ{zero → rec}

  {- Soundness -}

  fc-sound : ∀{S T} → S ⊢ T → FairComplianceS (S # T)
  fc-sound fc ε = ⊢ᵢ->succeed (fcoind-to-ind fc)
  fc-sound fc (x ◅ red) with fc .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (win , def)) , _) , refl , _ = ⊥-elim (success-not-reduce (win#def win def) x)
  fc-sound fc (sync (out ok) (inp {x = t}) ◅ red) | oi , (((f , _) , _) , _) , refl , pr = fc-sound (pr (t , ok)) red
  fc-sound fc (sync (inp {x = t}) (out ok) ◅ red) | io , (((_ , g) , _) , _) , refl , pr = fc-sound (pr (t , ok)) red

  {- Boundedness -}

  fc-bounded : ∀{S T} → FairComplianceS (S # T) → S ⊢ᵢ T
  fc-bounded fc =
    let _ , red-Sys , Succ = fc ε in
    maysucceed->⊢ᵢ red-Sys Succ
    
  {- Consistency -}

  fc-consistent : ∀{S T} → FairComplianceS (S # T) → ISF[ FCompIS ] (λ{(S , T) → FairComplianceS (S # T)}) (S , T)
  fc-consistent fc with fc ε
  ... | _ , ε , win#def win def = client-end , (_ , (win , def)) , refl , λ ()
  ... | _ , sync (out ok) (inp {x = t}) ◅ _ , _ = 
    oi , (_ , (t , ok)) , refl , λ (t' , ok') red → fc (sync (out ok') (inp {x = t'}) ◅ red)
  ... | _ , sync (inp {x = t}) (out ok) ◅ _ , _ =
    io , (_ , (t , ok)) , refl , λ (t' , ok') red → fc (sync (inp {x = t'}) (out ok') ◅ red)

  {- Completeness -}
  
  fc-complete : ∀{S T} → FairComplianceS (S # T) → S ⊢ T
  fc-complete =
    let S = λ{(S , T) → FairComplianceS (S # T)} in
    bounded-coind[ FCompIS , FCompCOIS ] S fc-bounded fc-consistent

  
  {- Properties -}

  fci->defined : ∀{S T} → S ⊢ᵢ T → Defined S × Defined T
  fci->defined (fold (inj₁ client-end , (_ , (out _ , def)) , refl , _)) = out , def
  fci->defined (fold (inj₁ oi , _ , refl , _)) = out , inp
  fci->defined (fold (inj₁ io , _ , refl , _)) = inp , out
  fci->defined (fold (inj₂ co-oi , _ , refl , _)) = out , inp
  fci->defined (fold (inj₂ co-io , _ , refl , _)) = inp , out

  fc->defined : ∀{S T} → S ⊢ T → Defined S × Defined T
  fc->defined fc = fci->defined (fcoind-to-ind fc)

  no-fc-with-nil : ∀{S} → ¬ (S ⊢ nil)
  no-fc-with-nil fc with fc .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (_ , ())) , _) , refl , _

  {- Auxiliary for FS -}

  win⊢def : ∀{S} → Defined S → win ⊢ S
  win⊢def ok = apply-fcoind client-end (_ , (Win-win , ok)) λ ()

  ⊢-after-out : ∀{f g t} → t ∈ dom f → out f ⊢ inp g → f t .force ⊢ g t .force
  ⊢-after-out ok fc with fc .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (out e , _)) , _) , refl , _ = ⊥-elim (e _ ok)
  ... | oi , _ , refl , pr = pr (_ , ok)

  ⊢-after-in : ∀{f g t} → t ∈ dom g → inp f ⊢ out g → f t .force ⊢ g t .force
  ⊢-after-in ok fc with fc .CoInd⟦_⟧.unfold
  ... | client-end , ((_ , (() , _)) , _) , refl , _
  ... | io , _ , refl , pr = pr (_ , ok)