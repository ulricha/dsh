module Database.DSH.Flattening.Optimizer.Common.Aux where

import qualified Data.IntMap as M

-- | Perform a map lookup and fail with the given error string if the key
-- is not present
lookupUnsafe :: Show a => M.IntMap a -> String -> Int -> a
lookupUnsafe m s u =
    case M.lookup u m of
        Just p -> p
        Nothing -> error $ s ++ " " ++ (show u) ++ " in " ++ (show m)
