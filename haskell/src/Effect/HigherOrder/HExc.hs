{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ExistentialQuantification #-}

module Effect.HigherOrder.HExc where

import           Free
import           Injectable
import           Syntax

data HExc e m a = Throw' e
                | forall x. Catch' (m x) (e -> m x) (x -> m a)

instance (Functor m) => Functor (HExc e m) where
  fmap f (Throw' e) = Throw' e
  fmap f (Catch' p h k) = Catch' p h (fmap f . k)

instance HFunctor (HExc e) where
  hmap t (Throw' e) = Throw' e
  hmap t (Catch' p h k) = Catch' (t p) (t . h) (t . k)

instance Syntax (HExc e) where
  emap f (Throw' e) = Throw' e
  emap f (Catch' p h k) = Catch' p h (f . k)

  weave f hdl (Throw' e) = Throw' e
  weave f hdl (Catch' p h k) =
    Catch' (hdl (p <$ f)) (\e -> hdl (h e <$ f)) (hdl . fmap k)

pattern Throw e <- (project -> Just (Throw' e))

throw :: (HExc e :<: sig) => e -> Free sig a
throw e = inject (Throw' e)

pattern Catch p h k <- (project -> Just (Catch' p h k))

catch :: (HExc e :<: sig) => Free sig a -> (e -> Free sig a) -> Free sig a
catch p h = inject (Catch' p h return)

runExc :: Syntax sig => Free (HExc e :+: sig) a -> Free sig (Either e a)
runExc (Pure x) = return (Right x)
runExc (Throw e) = return (Left e)
runExc (Catch p h k) = runExc p >>= \case
  Left e  -> runExc (h e) >>= \case
    Left e  -> return (Left e)
    Right a -> runExc (k a)
  Right a -> runExc (k a)
runExc (Other op) = Impure (weave (Right ()) hdl op)
  where hdl = either (return . Left) runExc
