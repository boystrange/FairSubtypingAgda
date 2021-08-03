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

open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤)
open import Data.Product
open import Data.Sum
open import Data.Vec using ([]; _∷_)
open import Data.List as List
import Data.Fin as Fin
open import Data.Nat

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.Definitions
open import Relation.Unary using (_∈_; _∉_; _⊆_; Satisfiable)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; inspect)
open import Common

open import is-lib.InfSys

module WeakTermination-IS {𝕋 : Set} (message : Message 𝕋) where

  open import SessionType message
  open import Trace message
  open import Transitions message
  open import HasTrace message
  open import TraceSet message

  U : Set
  U = SessionType

  data RuleNames : Set where
    nil inp out : RuleNames

  data CoRuleNames : Set where
    inp out : CoRuleNames

  nil-r : FinMetaRule U
  nil-r .Ctx = ⊤
  nil-r .comp _ =
    [] ,
    ----
    nil

  inp-r : MetaRule U
  inp-r .Ctx = Continuation
  inp-r .Pos _ = 𝕋
  inp-r .prems f p = f p .force
  inp-r .conclu f = inp f

  out-r : MetaRule U
  out-r .Ctx = Continuation
  out-r .Pos _ = 𝕋
  out-r .prems f p = f p .force
  out-r .conclu f = out f

  inp-co-r : FinMetaRule U
  inp-co-r .Ctx = Σ[ (f , x) ∈ Continuation × 𝕋 ] x ∈ dom f
  inp-co-r .comp ((f , x) , _) =
    f x .force ∷ [] ,
    --------------------
    inp f

  out-co-r : FinMetaRule U
  out-co-r .Ctx = Σ[ (f , x) ∈ Continuation × 𝕋 ] x ∈ dom f
  out-co-r .comp ((f , x) , _) =
    f x .force ∷ [] ,
    --------------------
    out f

  WeakTerminationS : SessionType → Set
  WeakTerminationS T = ∀{φ} → φ ∈ ⟦ T ⟧ → ∃[ ψ ] (φ ++ ψ ∈ Maximal ⟦ T ⟧)

  WeakTerminationIS : IS U
  Names WeakTerminationIS = RuleNames
  rules WeakTerminationIS nil    = from nil-r
  rules WeakTerminationIS inp    = inp-r
  rules WeakTerminationIS out    = out-r

  WeakTerminationCOIS : IS U
  WeakTerminationCOIS .Names = CoRuleNames
  WeakTerminationCOIS .rules inp = from inp-co-r
  WeakTerminationCOIS .rules out = from out-co-r

  WeakTermination : SessionType → Set
  WeakTermination = FCoInd⟦ WeakTerminationIS , WeakTerminationCOIS ⟧

  WeakTerminationI : SessionType → Set
  WeakTerminationI = Ind⟦ WeakTerminationIS ∪ WeakTerminationCOIS ⟧
  
  {- Soundness -}

  lemma-inp : ∀{f φ x} → φ ∈ Maximal ⟦ f x .force ⟧ → I x ∷ φ ∈ Maximal ⟦ inp f ⟧
  lemma-inp (maximal wit F) =
    maximal (inp-has-trace wit) λ { (some le) (_ , def , step inp tr) → cong (_ ∷_) (F le (_ , def , tr))}

  lemma-out : ∀{f φ x} → φ ∈ Maximal ⟦ f x .force ⟧ → O x ∷ φ ∈ Maximal ⟦ out f ⟧
  lemma-out (maximal wit F) =
    maximal (out-has-trace wit) λ { (some le) (_ , def , step (out _) tr) → cong (_ ∷_) (F le (_ , def , tr))}

  lemma-end : ∀{f} → (∀{x} → x ∉ dom f) → [] ∈ Maximal ⟦ inp f ⟧ 
  lemma-end no-x = maximal (_ , inp , refl)
    λ { {[]} none _ → refl
      ; {O _ ∷ _} none (_ , _ , step () _)
      ; {I _ ∷ _} none (_ , def , step inp tr) → ⊥-elim (no-x (transitions+defined->defined tr def))}

  lemma-win : ∀{f} → (∀{x} → x ∉ dom f) → [] ∈ Maximal ⟦ out f ⟧
  lemma-win no-x = maximal (_ , out , refl)
    λ { {[]} none _ → refl
      ; {I _ ∷ _} none (_ , _ , step () _)
      ; {O _ ∷ _} none (_ , def , step (out ok) _) → ⊥-elim (no-x ok)}

  may-terminate : ∀{T} → Defined T → WeakTerminationI T → Satisfiable (Maximal ⟦ T ⟧)
  may-terminate _ (fold (inj₁ inp , f , refl , pr)) with Empty? f
  ... | inj₁ e = _ , lemma-end λ x → e _ x
  ... | inj₂ (p , def) = 
    let tr , max = may-terminate def (pr p) in
    I p ∷ tr , lemma-inp max
  may-terminate _ (fold (inj₁ out , f , refl , pr)) with Empty? f
  ... | inj₁ e = _ , lemma-win λ x → e _ x
  ... | inj₂ (p , def) = 
    let tr , max = may-terminate def (pr p) in
    O p ∷ tr , lemma-out max
  may-terminate _ (fold (inj₂ inp , ((_ , x) , def) , refl , pr)) = 
    let tr , max = may-terminate def (pr Fin.zero) in
    I x ∷ tr , lemma-inp max
  may-terminate _ (fold (inj₂ out , ((_ , x) , def) , refl , pr)) =
    let tr , max = may-terminate def (pr Fin.zero) in
    O x ∷ tr , lemma-out max


  wt-sound : WeakTermination ⊆ WeakTerminationS
  wt-sound wt (_ , def , refl) = may-terminate def (fcoind-to-ind wt)
  wt-sound wt (_ , def , step t tr) with wt .CoInd⟦_⟧.unfold
  wt-sound wt (_ , def , step (inp {_} {p}) tr) | inp , _ , refl , pr =
    let tr' , max = wt-sound (pr p) (_ , def , tr) in
    tr' , lemma-inp max
  wt-sound wt (_ , def , step (out {_} {p} fx) tr) | out , _ , refl , pr =
    let tr' , max = wt-sound (pr p) (_ , def , tr) in
    tr' , lemma-out max

  {- Boundedness -}

  undefined→terminates : ∀{T} → ¬ Defined T → WeakTerminationI T
  undefined→terminates {nil}   _   = apply-ind (inj₁ nil) _ λ ()
  undefined→terminates {inp f} und = ⊥-elim (und inp)
  undefined→terminates {out f} und = ⊥-elim (und out)

  input-maximal→terminates : ∀{f x} → [] ∈ Maximal ⟦ inp f ⟧ → WeakTerminationI (f x .force)
  input-maximal→terminates {f} {x} (maximal (_ , inp , refl) F) with x ∈? f
  ... | no nfx = undefined→terminates nfx
  ... | yes fx with F none (_ , fx , step inp refl)
  ... | ()

  output-maximal→terminates : ∀{f x} → [] ∈ Maximal ⟦ out f ⟧ → WeakTerminationI (f x .force)
  output-maximal→terminates {f} {x} (maximal (_ , out , refl) F) with x ∈? f
  ... | no nfx = undefined→terminates nfx
  ... | yes fx with F none (_ , fx , step (out fx) refl)
  ... | ()

  bounded-lemma : ∀{T ϕ} → ϕ ∈ Maximal ⟦ T ⟧ → WeakTerminationI T
  bounded-lemma {nil} (maximal _ _) = apply-ind (inj₁ nil) _ λ ()
  bounded-lemma {inp f} c[]@(maximal (_ , def , refl) F) = 
    apply-ind (inj₁ inp) _ λ p → input-maximal→terminates {f} {p} c[]
  bounded-lemma {inp f} cϕ@(maximal (_ , def , step inp tr) F) =
    apply-ind (inj₂ inp) (_ , (transitions+defined->defined tr def)) λ{Fin.zero → bounded-lemma (input-maximal cϕ)}
  bounded-lemma {out f} c[]@(maximal (_ , def , refl) F) = 
    apply-ind (inj₁ out) _ λ p → output-maximal→terminates {f} {p} c[]
  bounded-lemma {out f} cϕ@(maximal (_ , def , step (out x) tr) F) =
    apply-ind (inj₂ out) (_ , x) λ{Fin.zero → bounded-lemma (output-maximal cϕ)}

  wtS-bounded : WeakTerminationS ⊆ WeakTerminationI
  wtS-bounded {nil} _ = apply-ind (inj₁ nil) _ λ ()
  wtS-bounded {inp f} s with s (_ , inp , refl)
  ... | _ , max = bounded-lemma max
  wtS-bounded {out f} s with s (_ , out , refl)
  ... | _ , max = bounded-lemma max

  {- Consistency -}

  lemma-input-maximal : ∀{f x} → WeakTerminationS (inp f) → WeakTerminationS (f x .force)
  lemma-input-maximal {f} {x} spec tφ with x ∈? f
  ... | no nfx = ⊥-elim (nfx (has-trace->defined tφ))
  ... | yes fx with spec (inp-has-trace tφ)
  ... | _ , cψ = _ , input-maximal cψ

  lemma-output-maximal : ∀{f x} → WeakTerminationS (out f) → WeakTerminationS (f x .force)
  lemma-output-maximal {f} {x} spec tφ with x ∈? f
  ... | no nfx = ⊥-elim (nfx (has-trace->defined tφ))
  ... | yes fx with spec (out-has-trace tφ)
  ... | _ , cψ = _ , output-maximal cψ

  wtS-cons : WeakTerminationS ⊆ ISF[ WeakTerminationIS ] WeakTerminationS
  wtS-cons {nil} spec = nil , _ , refl , λ ()
  wtS-cons {inp f} spec =
    inp , f , refl , λ p → lemma-input-maximal {f} {p} spec
  wtS-cons {out f} spec =
    out , f , refl , λ p → lemma-output-maximal {f} {p} spec

  {- Completeness -}

  wt-complete : WeakTerminationS ⊆ WeakTermination
  wt-complete =
    bounded-coind[ WeakTerminationIS , WeakTerminationCOIS ] WeakTerminationS wtS-bounded wtS-cons