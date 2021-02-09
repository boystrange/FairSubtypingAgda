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

open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Product
open import Data.Sum
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (∷-injectiveʳ)
import Data.Fin as Fin

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable
open import Relation.Unary using (_∈_; _∉_; _⊆_; Satisfiable)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import is-lib.InfSys

module Viability where

open import Common

message : Message 𝔹
message = record{_?=_ = Data.Bool._≟_}

open Message message
open import SessionType message
open import Session message
open import Trace message
open import Transitions message
open import HasTrace message
open import TraceSet message
open import FairCompliance message
open import FairCompliance-IS renaming (U to U-FComp)

U : Set
U = SessionType

data RuleNames : Set where
  inp out out-t out-f out-tf : RuleNames

data CoRuleNames : Set where
  out : CoRuleNames

inp-r : MetaRule U
inp-r .C = Continuation × 𝔹
inp-r .comp (f , x) =
  f x .force ∷ [] ,
  ----------------
  inp f , ⊤

out-r : MetaRule U
out-r .C = Continuation
out-r .comp f =
  [] ,
  ----
  out f , EmptyContinuation f

out-t-r : MetaRule U
out-t-r .C = Continuation
out-t-r .comp f =
  f true .force ∷ [] ,
  ------------------------------------
  out f , (true ∈ dom f × false ∉ dom f)

out-f-r : MetaRule U
out-f-r .C = Continuation
out-f-r .comp f =
  f false .force ∷ [] ,
  ------------------------------------
  out f , (true ∉ dom f × false ∈ dom f)

out-tf-r : MetaRule U
out-tf-r .C = Continuation
out-tf-r .comp f =
  f true .force ∷ f false .force ∷ [] ,
  ------------------------------------
  out f , (true ∈ dom f × false ∈ dom f)

out-co-r : MetaRule U
out-co-r .C = Continuation × 𝔹
out-co-r .comp (f , x) =
  f x .force ∷ [] ,
  --------------------
  out f , (x ∈ dom f)

{- Specification -}

ViabilityS : SessionType -> Set
ViabilityS R = ∃[ T ] ComplianceS (R # T)

FairViabilityS : U -> Set
FairViabilityS R = ∃[ T ] FairComplianceS (R # T)

FairViabilityS⊢ : U → Set
FairViabilityS⊢ R = ∃[ T ] R ⊢ T

specSound : ∀{R} → FairViabilityS⊢ R → FairViabilityS R
specSound (_ , fc) = _ , fc-sound fc

specComplete : ∀{R} → FairViabilityS R → FairViabilityS⊢ R
specComplete (_ , fc) = _ , fc-complete fc

--------------------------------

ViabilityIS : IS U
Names ViabilityIS = RuleNames
rules ViabilityIS inp    = inp-r
rules ViabilityIS out    = out-r
rules ViabilityIS out-t  = out-t-r
rules ViabilityIS out-f  = out-f-r
rules ViabilityIS out-tf = out-tf-r

ViabilityCOIS : IS U
ViabilityCOIS .Names = CoRuleNames
ViabilityCOIS .rules out = out-co-r

FairViability : U -> Set
FairViability = FCoInd⟦ ViabilityIS , ViabilityCOIS ⟧

FairViabilityI : U -> Set
FairViabilityI = Ind⟦ ViabilityIS ∪ ViabilityCOIS ⟧

{- Sample SessionTypes -}

cont cont-true cont-false : SessionType → Continuation
  
cont S false = box S
cont S true = box S

cont-true S false = box nil
cont-true S true = box S

cont-false S false = box S
cont-false S true = box nil

cont-ch : 𝔹 → SessionType → Continuation
cont-ch false S = cont-false S
cont-ch true S = cont-true S

--------------------------------
reductions-preserve-⊢ : ∀{R R' S S'} -> R ⊢ S -> Reductions (R # S) (R' # S') -> R' ⊢ S'
reductions-preserve-⊢ fc red = fc-complete (fair-compliance-red* (fc-sound fc) red)

-- fv-set: FairViability → Trace → Set
-- fv-set→semantics: ∀{R} → (fv : FairViability R) → Semantics (fv-set fv)
-- Semantics → SessionType

get-service : ∀{R} → FairViability R → SessionType
get-service fv with fv .CoInd⟦_⟧.unfold
... | inp , (_ , false) , refl , _ , pr = out λ{true → box nil ; false → λ where .force → get-service (pr Fin.zero)}
... | inp , (_ , true) , refl , _ , pr = out λ{true → (λ where .force → get-service (pr Fin.zero)) ; false → box nil}
... | out , _ , refl , _ = win
... | out-t , _ , refl , _ , pr = inp λ{true → (λ where .force → get-service (pr Fin.zero)) ; false → box nil}
... | out-f , _ , refl , _ , pr = inp λ{true → box nil ; false → λ where .force → get-service (pr Fin.zero)}
... | out-tf , _ , refl , _ , pr = 
  inp λ{true → (λ where .force → get-service (pr Fin.zero)) ; false → λ where .force → get-service (pr (Fin.suc Fin.zero))}

get-service' : ∀{R} → FairViabilityI R → SessionType
get-service' (fold (inj₁ inp , (_ , false) , refl , _ , pr)) = 
  out λ{true → (λ where .force → nil) ; false → λ where .force → get-service' (pr Fin.zero)}
get-service' (fold (inj₁ inp , (_ , true) , refl , _ , pr)) =
  out λ{true → (λ where .force → get-service' (pr Fin.zero)) ; false → λ where .force → nil}
get-service' (fold (inj₁ out , _ , refl , _)) = win
get-service' (fold (inj₁ out-t , _ , refl , _ , pr)) =
  inp λ{true → (λ where .force → get-service' (pr Fin.zero)) ; false → λ where .force → nil}
get-service' (fold (inj₁ out-f , _ , refl , _ , pr)) =
  inp λ{true → (λ where .force → nil) ; false → λ where .force → get-service' (pr Fin.zero)}
get-service' (fold (inj₁ out-tf , _ , refl , _ , pr)) = 
  inp λ{true → box (get-service' (pr Fin.zero)) ; false → box (get-service' (pr (Fin.suc Fin.zero)))}
get-service' (fold (inj₂ out , (_ , false) , refl , _ , pr)) = 
  inp λ{true → (λ where .force → nil); false → λ where .force → get-service' (pr Fin.zero)}
get-service' (fold (inj₂ out , (_ , true) , refl , _ , pr)) = 
  inp λ{true → (λ where .force → get-service' (pr Fin.zero)) ; false → (λ where .force → nil)}

FVI->Defined : ∀{R} → (fv : FairViabilityI R) → Defined (get-service' fv)
FVI->Defined (fold (inj₁ inp , (_ , false) , refl , _)) = out
FVI->Defined (fold (inj₁ inp , (_ , true) , refl , _)) = out
FVI->Defined (fold (inj₁ out , _ , refl , _)) = out
FVI->Defined (fold (inj₁ out-t , _ , refl , _)) = inp
FVI->Defined (fold (inj₁ out-f , _ , refl , _)) = inp
FVI->Defined (fold (inj₁ out-tf , _ , refl , _)) = inp
FVI->Defined (fold (inj₂ out , (_ , false) , refl , _)) = inp
FVI->Defined (fold (inj₂ out , (_ , true) , refl , _)) = inp

FV->Defined : ∀{R} → (fv : FairViability R) → Defined (get-service fv)
FV->Defined fv with fv .CoInd⟦_⟧.unfold
... | inp , (_ , false) , refl , _ = out
... | inp , (_ , true) , refl , _ = out
... | out , _ , refl , _ = out
... | out-t , _ , refl , _ = inp
... | out-f , _ , refl , _ = inp
... | out-tf , _ , refl , _ = inp

FV->MaySucceed : ∀{R} → (fv : FairViabilityI R) → MaySucceed (R # get-service' fv)
FV->MaySucceed (fold (inj₁ inp , (_ , false) , refl , _ , pr)) =
  let S' , red-S' , Succ = FV->MaySucceed (pr Fin.zero) in
  S' , sync inp (out (FVI->Defined (pr Fin.zero))) ◅ red-S' , Succ
FV->MaySucceed (fold (inj₁ inp , (_ , true) , refl , _ , pr)) =
  let S' , red-S' , Succ = FV->MaySucceed (pr Fin.zero) in
  S' , sync inp (out (FVI->Defined (pr Fin.zero))) ◅ red-S' , Succ
FV->MaySucceed (fold (inj₁ out , _ , refl , e , _)) = _ # win , ε , win#def (out e) out
FV->MaySucceed (fold (inj₁ out-t , _ , refl , (ok , _) , pr)) =
  let S' , red-S' , Succ = FV->MaySucceed (pr Fin.zero) in
  S' , sync (out ok) inp ◅ red-S' , Succ 
FV->MaySucceed (fold (inj₁ out-f , _ , refl , (_ , ok) , pr)) =
  let S' , red-S' , Succ = FV->MaySucceed (pr Fin.zero) in
  S' , sync (out ok) inp ◅ red-S' , Succ 
FV->MaySucceed (fold (inj₁ out-tf , _ , refl , (ok , _) , pr)) =
  let S' , red-S' , Succ = FV->MaySucceed (pr Fin.zero) in
  S' , sync (out ok) inp ◅ red-S' , Succ 
FV->MaySucceed (fold (inj₂ out , (_ , false) , refl , ok , pr)) =
  let S' , red-S' , Succ = FV->MaySucceed (pr Fin.zero) in
  S' , sync (out ok) inp ◅ red-S' , Succ
FV->MaySucceed (fold (inj₂ out , (_ , true) , refl , ok , pr)) = 
  let S' , red-S' , Succ = FV->MaySucceed (pr Fin.zero) in
  S' , sync (out ok) inp ◅ red-S' , Succ
  
open import is-lib.InfSys.SCoinduction
open import is-lib.InfSys.FlexSCoinduction
open import is-lib.InfSys.Equivalence
open import Size
open import Codata.Thunk

SFV : U → Size → Set
SFV = SFCoInd⟦ ViabilityIS , ViabilityCOIS ⟧

get-⊢ᵢ : ∀{R} → (fv : FairViability R) → FairViabilityI R → R ⊢ᵢ get-service fv
get-⊢ᵢ fv fvi with fv .CoInd⟦_⟧.unfold

get-⊢ᵢ fv (fold (inj₁ inp , (_ , false) , refl , _ , pr)) | inp , (_ , false) , refl , _ , pr' = 
  apply-ind (inj₁ io-false) ((FV->Defined (pr' Fin.zero)) , (λ ())) λ{Fin.zero → get-⊢ᵢ (pr' Fin.zero) (pr Fin.zero)}
get-⊢ᵢ fv (fold (inj₁ inp , (_ , true) , refl , _ , pr')) | inp , (_ , false) , refl , _ , pr = {!   !}
get-⊢ᵢ fv (fold (inj₂ out , _ , () , _)) | inp , (_ , false) , refl , _

... | inp , (_ , true) , refl , _ , pr = {!   !}

get-⊢ᵢ fv (fold (inj₁ out , _ , refl , _)) | out , _ , refl , (e , _) , _ = apply-ind (inj₁ client-end) (out e , out) λ ()
get-⊢ᵢ fv (fold (inj₁ out-t , c)) | out , _ , refl , (e , _) , _ = {!   !}
get-⊢ᵢ fv (fold (inj₁ out-f , c)) | out , _ , refl , (e , _) , _ = {!   !}
get-⊢ᵢ fv (fold (inj₁ out-tf , c)) | out , _ , refl , (e , _) , _ = {!   !}
get-⊢ᵢ fv (fold (inj₂ y , c)) | out , _ , refl , (e , _) , _ = {!   !}

get-⊢ᵢ fv (fold (inj₁ out , _ , refl , e , _))               | out-t , _ , refl , ((ok-t , _) , _) , _ = ⊥-elim (e _ ok-t)
get-⊢ᵢ fv (fold (inj₁ out-t , _ , refl , _ , pr))            | out-t , _ , refl , ((ok-t , no-f) , _) , pr' = 
  apply-ind (inj₁ oi-true) (ok-t , no-f) λ{Fin.zero → get-⊢ᵢ (pr' Fin.zero) (pr Fin.zero)}
get-⊢ᵢ fv (fold (inj₁ out-f , _ , refl , (_ , ok-f) , _))    | out-t , _ , refl , ((_ , no-f) , _) , _ = ⊥-elim (no-f ok-f)
get-⊢ᵢ fv (fold (inj₁ out-tf , _ , refl , (_ , ok-f) , _))   | out-t , _ , refl , ((_ , no-f) , _) , _ = ⊥-elim (no-f ok-f)
get-⊢ᵢ fv (fold (inj₂ out , (_ , false) , refl , ok-f , pr)) | out-t , _ , refl , ((_ , no-f) , _) , _ = ⊥-elim (no-f ok-f)
get-⊢ᵢ fv (fold (inj₂ out , (_ , true) , refl , ok-t , pr))  | out-t , _ , refl , _ , pr' = 
  apply-ind (inj₂ co-oi) ok-t λ{Fin.zero → get-⊢ᵢ (pr' Fin.zero) (pr Fin.zero)}
... | out-f , c = {!   !}
... | out-tf , c = {!   !}

FV->FC : ∀{R} → (fv : FairViability R) → R ⊢ get-service fv
CoInd⟦_⟧.unfold (FV->FC fv) with fv .CoInd⟦_⟧.unfold 
... | inp , (_ , false) , refl , (_ , ind) , pr = 
  io-false , _ , refl , ((FV->Defined (pr Fin.zero) , λ ()) , {!   !}) , λ{Fin.zero → FV->FC (pr Fin.zero)}
... | inp , (_ , true) , refl , _ , pr = 
  io-true , _ , refl , ((FV->Defined (pr Fin.zero) , λ ()) , {!   !}) , λ{Fin.zero → FV->FC (pr Fin.zero)}
... | out , _ , refl , (e , _) , _ = client-end , _ , refl , ((out e , out) , {!   !}) , λ ()
... | out-t , _ , refl , ((ok-t , no-f) , ind) , pr = 
  let ind' = get-⊢ᵢ (cofold (out-t , _ , refl , ((ok-t , no-f) , ind) , pr)) ind in
  oi-true , _ , refl , ((ok-t , no-f) , ind') , λ{Fin.zero → FV->FC (pr Fin.zero)}
... | out-f , _ , refl , ((no-t , ok-f) , _) , pr = 
  oi-false , _ , refl , ((ok-f , no-t) , {!   !}) , λ{Fin.zero → FV->FC (pr Fin.zero)}
... | out-tf , _ , refl , ((ok-t , ok-f) , _) , pr = 
  oi-both , _ , refl , ((ok-t , ok-f) , {!   !}) , 
  λ{Fin.zero → FV->FC (pr Fin.zero) ; (Fin.suc Fin.zero) → FV->FC (pr (Fin.suc Fin.zero))}

{-
get-⊢ : ∀{R} → (fv : FairViability R) → FairComplianceS (R # get-service' (fcoind-to-ind fv))
get-⊢ fv ε = FV->MaySucceed (fcoind-to-ind fv)
get-⊢ fv (tr ◅ red) with fv .CoInd⟦_⟧.unfold
get-⊢ fv (sync (inp {x = .false}) (out {x = false} !x) ◅ red) | inp , (f , false) , refl , (_ , fold (inj₁ inp , (_ , false) , refl , _ , _)) , pr = {!   !}
get-⊢ fv (sync r t ◅ red) | inp , (f , false) , refl , (_ , fold (inj₁ inp , (_ , true) , refl , _ , _)) , pr = {!   !}
get-⊢ fv (sync r t ◅ red) | inp , (f , false) , refl , (_ , fold (inj₂ out , _ , () , _)) , _
... | inp , (_ , true) , refl , _ , pr = {!   !}
get-⊢ fv (sync r _ ◅ _) | out , _ , refl , (e , _) , _ = ⊥-elim (win-reduces-⊥ (out e) r)
... | out-t , c = {!   !}
... | out-f , c = {!   !}
... | out-tf , c = {!   !}
-}

fv-set : ∀{R} → FairViability R → TraceSet
fv-set fv = ⟦ get-service fv ⟧

fv-set-prclosed : ∀{R} → (fv : FairViability R) → PrefixClosed (fv-set fv)
fv-set-prclosed fv none _ = (get-service fv) , (FV->Defined fv , refl)
fv-set-prclosed fv (some pref) (S , def , step t tr) with fv .CoInd⟦_⟧.unfold
fv-set-prclosed fv (some pref) (S , def , step (out {x = false} !x) tr) | inp , (_ , false) , refl , _ , pr =
  let S' , def' , tr' = fv-set-prclosed (pr Fin.zero) pref (S , def , tr) in 
  S' , def' , step (out !x) tr'
fv-set-prclosed fv (some pref) (S , def , step (out {x = true} !x) tr) | inp , (_ , true) , refl , _ , pr =
  let S' , def' , tr' = fv-set-prclosed (pr Fin.zero) pref (S , def , tr) in 
  S' , def' , step (out !x) tr'
fv-set-prclosed fv (some none) (.nil , () , step (out !x) refl) | out , _ , refl , _
fv-set-prclosed fv (some _) (.nil , () , step (inp {x = false}) refl) | out-t , _ , refl , _
fv-set-prclosed fv (some _) (_ , _ , step (inp {x = false}) (step () _)) | out-t , _ , refl , _
fv-set-prclosed fv (some pref) (S , def , step (inp {x = true}) tr) | out-t , _ , refl , _ , pr =
  let S' , def' , tr' = fv-set-prclosed (pr Fin.zero) pref (S , def , tr) in 
  S' , def' , step inp tr'
fv-set-prclosed fv (some pref) (S , def , step (inp {x = false}) tr) | out-f , _ , refl , _ , pr =
  let S' , def' , tr' = fv-set-prclosed (pr Fin.zero) pref (S , def , tr) in 
  S' , def' , step inp tr'
fv-set-prclosed fv (some _) (.nil , () , step (inp {x = true}) refl) | out-f , _ , refl , _
fv-set-prclosed fv (some _) (_ , _ , step (inp {x = true}) (step () _)) | out-f , _ , refl , _
fv-set-prclosed fv (some pref) (S , def , step (inp {x = false}) tr) | out-tf , _ , refl , _ , pr =
  let S' , def' , tr' = fv-set-prclosed (pr (Fin.suc Fin.zero)) pref (S , def , tr) in 
  S' , def' , step inp tr'
fv-set-prclosed fv (some pref) (S , def , step (inp {x = true}) tr) | out-tf , _ , refl , _ , pr =
  let S' , def' , tr' = fv-set-prclosed (pr Fin.zero) pref (S , def , tr) in 
  S' , def' , step inp tr'

fv-sound : FairViability ⊆ FairViabilityS⊢
fv-sound fv = get-service fv , FV->FC fv


{- Boundedness -}

bounded-lemma : ∀{R φ R'} -> Transitions R φ R' -> Win R' -> FairViabilityI R
bounded-lemma refl (out U) = fold (inj₁ out , _ , refl , U , λ ())
bounded-lemma (step inp rr) w =
  let via = bounded-lemma rr w in
  fold (inj₁ inp , _ , refl , tt , λ { Fin.zero → via })
bounded-lemma (step (out !x) rr) w =
  let via = bounded-lemma rr w in
  fold (inj₂ out , _ , refl , !x , λ { Fin.zero → via })

fv-bounded : FairViabilityS ⊆ FairViabilityI
fv-bounded {R} (T , comp) with comp ε
... | (_ # _) , reds , win#def w def =
  let _ , rr , tr = unzip-red* reds in
  bounded-lemma rr w

----------------------------------

{- Consistency -}

-- Schema: by cases on the client  
-- FairCompliance is preserved by a reduction of the system (i.e. ⊢ premises)
fv⊢-consistent : FairViabilityS⊢ ⊆ ISF[ ViabilityIS ] FairViabilityS⊢
fv⊢-consistent {nil} (_ , fc) = ⊥-elim (¬nil-⊢ fc)
fv⊢-consistent {inp f} (S , fc) with fc .CoInd⟦_⟧.unfold
... | client-end , _ , refl , ((() , _) , _) , _
... | io-true , _ , refl , _ , pr = inp , (f , true) , refl , _ , λ{Fin.zero → _ , pr Fin.zero}
... | io-false , _ , refl , _ , pr = inp , (f , false) , refl , _ , λ{Fin.zero → _ , pr Fin.zero}
... | io-both , _ , refl , _ , pr = inp , (f , true) , refl , _ , λ{Fin.zero → _ , pr Fin.zero}
fv⊢-consistent {out f} (S , fc) with fc .CoInd⟦_⟧.unfold
... | client-end , _ , refl , ((out e , _) , _) , _ = out , _ , refl , e , λ ()
... | oi-true , _ , refl , ((ok-t , no-f) , _) , pr = out-t , _ , refl , (ok-t , no-f) , λ{Fin.zero → _ , pr Fin.zero}
... | oi-false , _ , refl , ((ok-f , no-t) , _) , pr = out-f , _ , refl , (no-t , ok-f) , λ{Fin.zero → _ , pr Fin.zero}
... | oi-both , _ , refl , ((ok-t , ok-f) , _) , pr =
  out-tf , _ , refl , (ok-t , ok-f) , λ{Fin.zero → _ , pr Fin.zero ; (Fin.suc Fin.zero) → _ , pr (Fin.suc Fin.zero)}

fv-consistent : FairViabilityS ⊆ ISF[ ViabilityIS ] FairViabilityS
fv-consistent fv = 
  let rn , c , eq , sd , pr = fv⊢-consistent (specComplete fv) in 
  rn , c , eq , sd , λ i → specSound (pr i)

----------------------------------

fv-complete : FairViabilityS ⊆ FairViability
fv-complete = bounded-coind[ ViabilityIS , ViabilityCOIS ] FairViabilityS fv-bounded fv-consistent
