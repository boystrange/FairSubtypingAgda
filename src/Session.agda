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

open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.List using ([]; _∷_; _++_)

open import Relation.Nullary
open import Relation.Unary using (_∪_; _∩_; Satisfiable)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)

open import Common

module Session {ℙ : Set} (message : Message ℙ)
  where

open import Trace message
open import SessionType message
open import Transitions message
open import HasTrace message

data Session : Set where
  _#_  : (T : SessionType) (S : SessionType) -> Session

data Reduction : Session -> Session -> Set where
  sync : ∀{α R R' T T'} (r : Transition R (co-action α) R') (t : Transition T α T') -> Reduction (R # T) (R' # T')

Reductions : Session -> Session -> Set
Reductions = Star Reduction

Reduce : Session -> Set
Reduce S = Satisfiable (Reduction S)

data Success : Session -> Set where
  win#def : ∀{T S} (w : Win T) (def : Defined S) -> Success (T # S)

ProgressS : Session -> Set
ProgressS = Success ∪ Reduce

MaySucceed : Session -> Set
MaySucceed S = Satisfiable (Reductions S ∩ Success)

InvariantS : (Session -> Set) -> Session -> Set
InvariantS P S = ∀{S'} -> Reductions S S' -> P S'

ImplyS : (Session -> Set) -> SessionType -> SessionType -> Set
ImplyS P T S = ∀{R} -> P (R # T) -> P (R # S)

ComplianceS : Session -> Set
ComplianceS = InvariantS ProgressS

FairComplianceS : Session -> Set
FairComplianceS = InvariantS MaySucceed

SubtypingS : SessionType -> SessionType -> Set
SubtypingS = ImplyS ComplianceS

FairSubtypingS : SessionType -> SessionType -> Set
FairSubtypingS = ImplyS FairComplianceS

ConvergenceS : SessionType -> SessionType -> Set
ConvergenceS T S = ∀{R} -> FairComplianceS (R # T) -> MaySucceed (R # S)

unzip-red* : ∀{T T' S S'} -> Reductions (T # S) (T' # S') ->
             ∃[ φ ] (Transitions T (co-trace φ) T' × Transitions S φ S')
unzip-red* ε = _ , refl , refl
unzip-red* (sync r t ◅ reds) =
  let _ , tr , sr = unzip-red* reds in
  _ , step r tr , step t sr

zip-red* : ∀{φ T T' S S'} ->
           Transitions T (co-trace φ) T' ->
           Transitions S φ S' ->
           Reductions (T # S) (T' # S')
zip-red* refl refl = ε
zip-red* (step t tr) (step s sr) = sync t s ◅ zip-red* tr sr

zip-traces :
  ∀{R T φ}
  (rφ : R HasTrace (co-trace φ))
  (tφ : T HasTrace φ) ->
  Reductions (R # T) (after rφ # after tφ)
zip-traces (_ , _ , rr) (_ , _ , tr) = zip-red* rr tr

success-not-reduce : ∀{S S'} → Success S → ¬ (Reduction S S')
success-not-reduce (win#def win _) (sync r _) = win-reduces-⊥ win r
