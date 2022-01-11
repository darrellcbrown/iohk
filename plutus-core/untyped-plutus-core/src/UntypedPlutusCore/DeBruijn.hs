{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Support for using de Bruijn indices for term names.
module UntypedPlutusCore.DeBruijn
    ( Index (..)
    , DeBruijn (..)
    , NamedDeBruijn (..)
    , FreeVariableError (..)
    , AsFreeVariableError (..)
    , deBruijnTerm
    , deBruijnProgram
    , unDeBruijnTerm
    , unDeBruijnProgram
    , unDeBruijnTermGrace
    , unDeBruijnProgramGrace
    , unNameDeBruijn
    , fakeNameDeBruijn
    ) where

import PlutusCore.DeBruijn.Internal

import PlutusCore.Name
import PlutusCore.Quote
import UntypedPlutusCore.Core

import Control.Lens hiding (Index, Level, index)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Bimap qualified as BM

{- Note [Comparison with typed deBruijn conversion]
This module is just a boring port of the typed version.
-}

-- | Convert a 'Term' with 'Name's into a 'Term' with 'DeBruijn's.
-- Will throw an error if a free variable is encountered.
deBruijnTerm
    :: (AsFreeVariableError e, MonadError e m)
    => Term Name uni fun ann -> m (Term NamedDeBruijn uni fun ann)
deBruijnTerm = flip runReaderT (Levels 0 BM.empty) . deBruijnTermM

-- | Convert a 'Program' with Name's into a 'Program' with 'DeBruijn's.
-- Will throw an error if a free variable is encountered.
deBruijnProgram
    :: (AsFreeVariableError e, MonadError e m)
    => Program Name uni fun ann -> m (Program NamedDeBruijn uni fun ann)
deBruijnProgram (Program ann ver term) = Program ann ver <$> deBruijnTerm term

deBruijnTermM
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => Term Name uni fun ann
    -> m (Term NamedDeBruijn uni fun ann)
deBruijnTermM = \case
    -- variable case
    Var ann n -> Var ann <$> nameToDeBruijn n
    -- binder cases
    LamAbs ann n t -> declareUnique n $ do
        n' <- nameToDeBruijn n
        withScope $ LamAbs ann n' <$> deBruijnTermM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> deBruijnTermM t1 <*> deBruijnTermM t2
    Delay ann t -> Delay ann <$> deBruijnTermM t
    Force ann t -> Force ann <$> deBruijnTermM t
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
    Error ann -> pure $ Error ann

-- | Convert a 'Term' with 'DeBruijn's into a 'Term' with 'Name's.
-- Will throw an error if a free variable is encountered.
unDeBruijnTerm
    :: (MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Term NamedDeBruijn uni fun ann -> m (Term Name uni fun ann)
unDeBruijnTerm = flip runReaderT (Levels 0 BM.empty) . unDeBruijnTermM

-- | Convert a 'Program' with 'DeBruijn's into a 'Program' with 'Name's.
-- Will throw an error if a free variable is encountered.
unDeBruijnProgram
    :: (MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Program NamedDeBruijn uni fun ann -> m (Program Name uni fun ann)
unDeBruijnProgram (Program ann ver term) = Program ann ver <$> unDeBruijnTerm term

-- | Convert a 'Term' with 'NamedDeBruijn's into a 'Term' with 'Name's.
-- A variant that does not throw an error on free variables. See 'freeIndexGrace'.
unDeBruijnTermGrace
    :: MonadQuote m
    => Term NamedDeBruijn uni fun ann -> m (Term Name uni fun ann)
unDeBruijnTermGrace = flip evalStateT BM.empty . flip runReaderT (Levels 0 BM.empty) . unDeBruijnTermGraceM

-- | Convert a 'Program' with 'DeBruijn's into a 'Program' with 'Name's.
-- A variant that does not throw an error on free variables. See 'freeIndexGrace'.
unDeBruijnProgramGrace
    :: MonadQuote m
    => Program NamedDeBruijn uni fun ann -> m (Program Name uni fun ann)
unDeBruijnProgramGrace (Program ann ver term) =  Program ann ver <$> unDeBruijnTermGrace term

unDeBruijnTermM
    :: (MonadReader Levels m, MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Term NamedDeBruijn uni fun ann
    -> m (Term Name uni fun ann)
unDeBruijnTermM = unDeBruijnTermMWith freeIndexThrow

unDeBruijnTermGraceM
    :: (MonadReader Levels m, MonadQuote m, MonadState (BM.Bimap Unique Level) m)
    => Term NamedDeBruijn uni fun ann
    -> m (Term Name uni fun ann)
unDeBruijnTermGraceM = unDeBruijnTermMWith freeIndexGrace

-- | Takes a "handler" function to execute when encountering free variables.
unDeBruijnTermMWith
    :: (MonadReader Levels m, MonadQuote m)
    => (Index -> m Unique)
    -> Term NamedDeBruijn uni fun ann
    -> m (Term Name uni fun ann)
unDeBruijnTermMWith h = \case
    -- variable case
    Var ann n -> Var ann <$> deBruijnToName h n
    -- binder cases
    LamAbs ann n t ->
        -- See NOTE: [DeBruijn indices of Binders]
        declareBinder $ do
            n' <- deBruijnToName h $ set index 0 n
            withScope $ LamAbs ann n' <$> unDeBruijnTermMWith h t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> unDeBruijnTermMWith h t1 <*> unDeBruijnTermMWith h t2
    Delay ann t -> Delay ann <$> unDeBruijnTermMWith h t
    Force ann t -> Force ann <$> unDeBruijnTermMWith h t
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
    Error ann -> pure $ Error ann
