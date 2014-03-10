{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Rewrite.PruneEmpty(pruneEmpty) where
       
import           Control.Applicative
import           Control.Monad

import           Database.DSH.Optimizer.Common.Rewrite
import           Database.DSH.Optimizer.VL.Properties.Types
import           Database.DSH.Optimizer.VL.Rewrite.Common

import           Database.Algebra.Dag.Common
import           Database.DSH.VL.Lang

pruneEmpty :: VLRewrite Bool
pruneEmpty = postOrder inferBottomUp emptyRules

emptyRules :: VLRuleSet BottomUpProps
emptyRules = [ emptyAppendLeftR1
             -- , emptyAppendLeftR2
             -- , emptyAppendLeftR3
             , emptyAppendRightR1
             -- , emptyAppendRightR2
             -- , emptyAppendRightR3
             ]

isEmpty :: AlgNode -> VLMatch BottomUpProps Bool
isEmpty q = do
  ps <- liftM emptyProp $ properties q
  case ps of
    VProp b -> return b
    x       -> error $ "PruneEmpty.isEmpty: non-vector input " ++ show x

{- If the left input is empty and the other is not, the resulting value vector
is simply the right input. -}
emptyAppendLeftR1 :: VLRule BottomUpProps
emptyAppendLeftR1 q =
  $(pattern 'q "R1 ((q1) Append (q2))"
    [| do
        predicate =<< ((&&) <$> (isEmpty $(v "q1")) <*> (not <$> isEmpty $(v "q2")))

        return $ do
          logRewrite "Empty.Append.Left.R1" q
          replace q $(v "q2") |])

-- FIXME re-add rules when 
{-
-- If the left input is empty, renaming will make the inner vector
-- empty as well.
emptyAppendLeftR2 :: VLRule BottomUpProps
emptyAppendLeftR2 q =
  $(pattern 'q "(R2 ((q1) Append (q2))) PropRename (qv)"
    [| do
        predicate =<< ((&&) <$> (isEmpty $(v "q1")) <*> (not <$> isEmpty $(v "q2")))

        VProp (ValueVector w) <- vectorTypeProp <$> properties $(v "qv")

        return $ do
          logRewrite "Empty.Append.Left.R2" q
          void $ replaceWithNew q (NullaryOp $ Empty w) |])

-- If the left input is empty, the rename vector for the right inner
-- vectors is simply identity
emptyAppendLeftR3 :: VLRule BottomUpProps
emptyAppendLeftR3 q = 
  $(pattern 'q "(R3 ((q1) Append (q2))) PropRename (qv)" 
    [| do 
        predicate =<< ((&&) <$> (isEmpty $(v "q1")) <*> (not <$> isEmpty $(v "q2")))

        return $ do
          logRewrite "Empty.Append.Left.R3" q
          replace q $(v "qv") |])
-}

emptyAppendRightR1 :: VLRule BottomUpProps
emptyAppendRightR1 q =
  $(pattern 'q "R1 ((q1) Append (q2))"
    [| do
        predicate =<< ((&&) <$> (isEmpty $(v "q2")) <*> (not <$> isEmpty $(v "q1")))
        return $ do
          logRewrite "Empty.Append.Right.R1" q
          replace q $(v "q1") |])

{-
-- If the right input is empty, renaming will make the inner vector
-- empty as well.
emptyAppendRightR3 :: VLRule BottomUpProps
emptyAppendRightR3 q =
  $(pattern 'q "(R3 ((q1) Append (q2))) PropRename (qv)"
    [| do
        predicate =<< ((&&) <$> (not <$> isEmpty $(v "q1")) <*> (isEmpty $(v "q2")))
        VProp (ValueVector w) <- vectorTypeProp <$> properties $(v "qv")

        return $ do
          logRewrite "Empty.Append.Right.R3" q
          void $ replaceWithNew q $ NullaryOp $ Empty w |])

-- If the right input is empty, the rename vector for the left inner
-- vectors is simply identity
emptyAppendRightR2 :: VLRule BottomUpProps
emptyAppendRightR2 q =
  $(pattern 'q "(R2 ((q1) Append (q2))) PropRename (qv)"
    [| do
        predicate =<< ((&&) <$> (isEmpty $(v "q2")) <*> (not <$> isEmpty $(v "q1")))
        return $ do
          logRewrite "Empty.Append.Right.R2" q
          void $ replace q $(v "qv") |])
-}
