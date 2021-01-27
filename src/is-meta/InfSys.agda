open import Agda.Builtin.Equality
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; fromList) renaming (lookup to get)
open import Data.List using (List ; length ; lookup)
open import Data.Unit
open import Level using (Lift) renaming (suc to _++)
open import Size
open import Codata.Thunk

module is-meta.InfSys {l} where
  open import is-meta.InfSys.Base {l} public 
