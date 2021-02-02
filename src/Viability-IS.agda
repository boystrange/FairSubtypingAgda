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
open import Relation.Unary using (_∈_; _∉_; _⊆_; Satisfiable)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import is-lib.InfSys

module Viability-IS where

open import Common

message : Message 𝔹
message = record{_?=_ = Data.Bool._≟_}

open import SessionType message
open import Session message
open import Trace message
open import Transitions message
open import HasTrace message
open import TraceSet message
open import FairCompliance message

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

ViabilityS : SessionType -> Set
ViabilityS R = ∃[ T ] ComplianceS (R # T)

FairViabilityS : SessionType -> Set
FairViabilityS R = ∃[ T ] FairComplianceS (R # T)

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

FairViability : SessionType -> Set
FairViability = FCoInd⟦ ViabilityIS , ViabilityCOIS ⟧

FairViabilityI : SessionType -> Set
FairViabilityI = Ind⟦ ViabilityIS ∪ ViabilityCOIS ⟧

fv-sound : FairViability ⊆ FairViabilityS
fv-sound fv = {!!}

fv-consistent : FairViabilityS ⊆ ISF[ ViabilityIS ] FairViabilityS
fv-consistent {nil} (T , comp) with comp ε
... | _ , reds , win#def w def with unzip-red* reds
... | _ , rr , _ with transitions+defined->defined rr (win->defined w)
... | ()
fv-consistent {inp f} (T , comp) = {!!}
fv-consistent {out f} (T , comp) with true ∈? f | false ∈? f
... | yes ft | yes ff = {!!}
... | yes ft | no nff = {!!}
... | no nft | yes ff =
  let comp' = fc-transitions (step (out ff) refl) (step {!!} refl) comp in
  out-f , {!!} , refl , (nft , ff) , λ { Fin.zero → {!!} , {!!} }
... | no nft | no nff = out , _ , refl , (λ { false fx → ⊥-elim (nff fx)
                                            ; true fx → ⊥-elim (nft fx) }) , λ ()

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

fv-complete : FairViabilityS ⊆ FairViability
fv-complete = bounded-coind[ ViabilityIS , ViabilityCOIS ] FairViabilityS fv-bounded fv-consistent
