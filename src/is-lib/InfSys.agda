module is-lib.InfSys {l} where
  open import is-lib.InfSys.Base {l} public 
  open import is-lib.InfSys.Induction {l} public
  open import is-lib.InfSys.Coinduction {l} public
  open import is-lib.InfSys.FlexCoinduction {l} public
  open MetaRule public
  open IS public