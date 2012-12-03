module Database.DSH.Flattening.Optimizer.Common.Aux where

import qualified Data.Map as M

-- | Perform a map lookup and fail with the given error string if the key
-- is not present
lookupUnsafe :: (Ord k, Show k, Show a) => M.Map k a -> String -> k -> a
lookupUnsafe m s u = 
    case M.lookup u m of
        Just p -> p
        Nothing -> error $ s ++ " " ++ (show u) ++ " in " ++ (show m)
