-- | Helper functions for TH code
module Database.DSH.Common.TH
    ( nameTyApp
    , equalConstrTy
    ) where

import Language.Haskell.TH

-- | Apply a named type constructor to a type
nameTyApp :: Name -> Type -> Type
nameTyApp className tyVar = AppT (ConT className) tyVar

-- | Construct a type that expresses an equality constraint.
equalConstrTy :: Type -> Type -> Type
equalConstrTy t1 t2 = AppT (AppT EqualityT t1) t2
