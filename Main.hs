{-# LANGUAGE GADTs, TypeOperators, DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE RankNTypes #-}
import Data.Char
import Data.Foldable
import Data.Bifunctor (first)
import Control.Applicative
import Debug.Trace
import Control.Monad

data G e a where
  Fail :: G e a
  Done :: a -> G e a
  Or :: G e a -> G e a -> G e a
  Seq :: G e (a -> b) -> G e a -> G e b
  Lift :: (String -> Steps (a, String)) -> G e a
  Mu :: G (a : e) a -> G e a
  VZ :: G (a : e) a
  VS :: G e a -> G (x : e) a

instance Functor (G e) where
  fmap f = Seq (Done f)

instance Applicative (G e) where
  pure = Done
  (<*>) = Seq

instance Alternative (G e) where
  empty = Fail
  (<|>) = Or

-- under :: (forall b. G e b -> G e' b) -> G (x:e) a -> G (x:e') a
-- under _ Fail = Fail
-- under _ (Done x) = Done x
-- under f (Or x y) = Or (under f x) (under f y)
-- under f (Seq x y) = Seq (under f x) (under f y)
-- under _ (Lift s) = Lift s
-- under f (Mu x) = Mu (under (under f) x)
-- under _ VZ = VZ
-- under f (VS x) = VS (f x)
-- 
-- map1 :: (a -> b) -> G (a : e) c -> G (b : e) c
-- map1 _ Fail = Fail
-- map1 _ (Done x) = Done x
-- map1 f (Or x y) = Or (map1 f x) (map1 f y)
-- map1 f (Seq x y) = Seq (map1 f x) (map1 f y)
-- map1 _ (Lift s) = Lift s
-- map1 f (Mu x) = Mu (under (map1 f) x)
-- map1 f VZ = _
-- 
-- mapHead :: (a -> b) -> G (a : e) a -> G (b : e) b
-- mapHead f Fail = Fail
-- mapHead f (Done x) = Done (f x)
-- mapHead f (Or x y) = Or (mapHead f x) (mapHead f y)
-- mapHead f (Seq x y) = Seq _ _
-- 
-- instance Functor (G '[]) where
--   fmap _ Fail = Fail
--   fmap f (Done x) = Done (f x)
--   fmap f (Or x y) = Or (fmap f x) (fmap f y)
--   fmap f (Seq x y) = Seq (fmap (fmap f) x) y
--   fmap f (Lift s) = Lift (fmap (first f) . s)
--   fmap f (Mu x) = Mu (mapHead f x)

fromDigit :: Char -> Maybe Int
fromDigit x 
  | let y = ord x - ord '0'
  , 0 <= y && y <= 9
  = Just y
  | otherwise
  = Nothing

spanMaybe :: (a -> Maybe b) -> [a] -> ([b], [a])
spanMaybe f = go id where
  go s [] = (s [], [])
  go s (x:xs) =
    case f x of
      Nothing -> (s [], x:xs)
      Just y -> go (s . (y:)) xs

nat :: String -> Steps (Int, String)
nat xs = 
  case spanMaybe fromDigit xs of
    ([], _) -> SFail
    (ys, zs) -> foldr (\_ s -> SStep s) (SDone (foldl' (\s x -> s * 10 + x) 0 ys, zs)) ys

plus :: String -> Steps ((), String)
plus ('+':xs) = SStep (SDone ((), xs))
plus _ = SFail

end :: String -> Steps ((), String)
end "" = SDone ((), "")
end _ = SFail

arith :: G e Int
arith = Mu (Lift nat <|> ((+) <$> VZ <* Lift plus <*> VZ))

data Env e where
  ENil :: Env '[]
  ECons :: G (a : e') a -> Env e' -> Env (a : e')

data Steps a where
  SFail :: Steps a
  SDone :: a -> Steps a
--   SApp :: (b -> a) -> Steps b -> Steps a
  SStep :: Steps a -> Steps a
  SRec :: Steps a -> Steps a
  deriving Show

instance Functor Steps where
  fmap = liftM

instance Applicative Steps where
  pure = SDone
  (<*>) = ap

instance Monad Steps where
  SFail >>= _ = SFail
  SDone x >>= k = k x
  SStep x >>= k = SStep (x >>= k)
  SRec x >>= k = SRec (x >>= k)

norm :: Steps a -> Steps a
-- norm x | trace ("norm " ++ showStep x) False = undefined
-- norm SFail = SFail
-- norm (SDone x) = SDone x
-- norm (SApp _ SFail) = SFail
-- norm (SApp f (SDone x)) = SDone (f x)
-- norm (SApp f (SStep x)) = SStep (SApp f x)
-- norm (SApp f (SRec x)) = SRec (SApp f x)
-- norm (SApp f (SApp g x)) = norm (SApp (f . g) x)
-- norm (SStep x) = SStep x
-- norm (SRec (SStep x)) = SStep (SRec x)
-- norm (SRec SFail) = SFail
-- norm (SRec x@SDone{}) = SRec x
norm x = x

showStep :: Steps a -> String
showStep SFail = "SFail"
showStep SDone{} = "SDone"
showStep SStep{} = "SStep"
showStep SRec{} = "SRec"

-- lub/join of a semilattice. 
-- SFail is the bottom element. 
-- SDone are greater than all non-SDone.
-- SStep is greater than SRec
best :: Steps a -> Steps a -> Steps a
best _ _ | trace "best begin" False = undefined
best x0 y0 = norm x0 `best'` norm y0 where
  best' x y | trace ("best " ++ showStep x ++ " " ++ showStep y) False = undefined
  best' SDone{} SDone{} = error "Ambiguous parsers"
  best' x@SDone{} _ = x
  best' _ x@SDone{} = x
  best' SFail x = x
  best' x SFail = x
  best' (SStep x) (SStep y) = SStep (x `best` y)
  best' (SRec x) (SRec y) = SRec (x `best` y)
  -- problem: 
  -- !!!!!!!!
  -- best' (SRec (SStep x)) (SStep y) = SStep (SRec x `best` y)
  -- best' (SStep x) (SRec (SStep y)) = SStep (x `best` SRec y)
  -- !!!!!!!!
  best' (SRec x) y = SRec (x `best` y)
  best' x (SRec y) = SRec (x `best` y)
--  best' _ _ = error "Missing case in best"

eval :: Steps a -> a
eval (SDone x) = x
-- eval (SApp f x) = f (eval x)
eval (SStep x) = eval x
eval (SRec x) = eval x
eval _ = error "failling parse"

steps :: Env e -> G e a -> String -> Steps (a, String)
steps _ _ xs | trace ("steps " ++ show xs) False = undefined
steps _ Fail _ = trace "fail" SFail
steps _ (Done x) xs = trace "done" $ SDone (x, xs)
steps env (Or x y) xs = trace "or" $ trace "left" (steps env x xs) `best` trace "right" (steps env y xs)
steps env (Seq x y) xs = trace "seq" $
  steps env x xs >>= \(x', xs') ->
  steps env y xs' >>= \(y', xs'') -> 
  pure (x' y', xs'')
steps _ (Lift s) xs = trace "lift" $ s xs
steps env (Mu x) xs = trace "mu" $ steps (ECons x env) x xs
steps env@(ECons x _) VZ xs = trace "vz" $ SRec (steps env x xs)
steps (ECons _ env) (VS x) xs = trace "vs" $ steps env x xs

-- step :: Env e -> G e a -> String -> [(G e a, String)]
-- step _ Fail _ = []
-- step _ (Done x) xs = [(Done x, xs)]
-- step env (Or x y) xs = step env x xs ++ step env y xs
-- step env (Seq x y) xs = 
--   step env x xs >>= \(x', xs') ->
--   step env y xs' >>= \(y', xs'') -> 
--   pure (Seq x' y', xs'')
-- step _ (Lift s) xs = first Done <$> s xs
-- step env (Mu x) xs = first Mu <$> step (ECons x env) x xs
-- step env@(ECons x _) VZ xs = step env x xs
-- step (ECons _ env) (VS x) xs = first VS <$> step env x xs

-- parse' :: Show a => Env e -> [(G e a, String)] -> [(a, String)]
-- parse' env gs =
--   gs >>= \(g, xs) ->
--   case g of
--     Done x -> traceShow x [(x, xs)]
--     _ -> parse' env (step env g xs)

char :: Char -> String -> Steps (Char, String)
char x (y:xs) | x == y = SStep (SDone (x, xs))
char _ _ = SFail

parse :: G '[] a -> String -> Steps (a, String)
parse = steps ENil

main :: IO ()
-- main = print $ parse (Mu (VZ *> Lift (char '1') <|> pure '2') <* Lift end) "111"
main = print $ parse ((Lift (char '1') <|> pure '2') <* Lift end) "1"
