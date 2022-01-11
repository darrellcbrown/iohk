{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Support for using de Bruijn indices for term and type names.
module PlutusCore.DeBruijn
    ( Index (..)
    , DeBruijn (..)
    , NamedDeBruijn (..)
    , TyDeBruijn (..)
    , NamedTyDeBruijn (..)
    , FreeVariableError (..)
    , AsFreeVariableError (..)
    , deBruijnTy
    , deBruijnTerm
    , deBruijnProgram
    , unDeBruijnTy
    , unDeBruijnTerm
    , unDeBruijnProgram
    , unDeBruijnTyGrace
    , unDeBruijnTermGrace
    , unDeBruijnProgramGrace
    , unNameDeBruijn
    , unNameTyDeBruijn
    , fakeNameDeBruijn
    ) where

import PlutusCore.DeBruijn.Internal

import PlutusCore.Core
import PlutusCore.Name
import PlutusCore.Quote

import Control.Lens hiding (Index, Level, index)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Bimap qualified as BM

{- NOTE: [DeBruijn indices of Binders]
In a debruijnijfied Term AST, the Binders have a debruijn index
at their the spefiic AST location.
During *undebruijnification* we ignore such binders' indices because they are meaningless,
and instead use the convention that such introduced binders have
a fixed debruijn index '0' at their introduction.
-}

-- | Convert a 'Type' with 'TyName's into a 'Type' with 'NamedTyDeBruijn's.
-- Will throw an error if a free variable is encountered.
deBruijnTy
    :: (AsFreeVariableError e, MonadError e m)
    => Type TyName uni ann -> m (Type NamedTyDeBruijn uni ann)
deBruijnTy = flip runReaderT (Levels 0 BM.empty) . deBruijnTyM

-- | Convert a 'Term' with 'TyName's and 'Name's into a 'Term' with 'NamedTyDeBruijn's and 'NamedDeBruijn's.
-- Will throw an error if a free variable is encountered.
deBruijnTerm
    :: (AsFreeVariableError e, MonadError e m)
    => Term TyName Name uni fun ann -> m (Term NamedTyDeBruijn NamedDeBruijn uni fun ann)
deBruijnTerm = flip runReaderT (Levels 0 BM.empty) . deBruijnTermM

-- | Convert a 'Program' with 'TyName's and 'Name's into a 'Program' with 'NamedTyDeBruijn's and 'NamedDeBruijn's.
-- Will throw an error if a free variable is encountered.
deBruijnProgram
    :: (AsFreeVariableError e, MonadError e m)
    => Program TyName Name uni fun ann -> m (Program NamedTyDeBruijn NamedDeBruijn uni fun ann)
deBruijnProgram (Program ann ver term) = Program ann ver <$> deBruijnTerm term

{- Note [De Bruijn conversion and recursion schemes]
These are quite repetitive, but we can't use a catamorphism for this, because
we are not only altering the recursive type, but also the name type parameters.
These are normally constant in a catamorphic application.
-}
deBruijnTyM
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => Type TyName uni ann
    -> m (Type NamedTyDeBruijn uni ann)
deBruijnTyM = \case
    -- variable case
    TyVar ann n -> TyVar ann <$> tyNameToDeBruijn n
    -- binder cases
    TyForall ann tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyForall ann tn' k <$> deBruijnTyM ty
    TyLam ann tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyLam ann tn' k <$> deBruijnTyM ty
    -- boring recursive cases
    TyFun ann i o -> TyFun ann <$> deBruijnTyM i <*> deBruijnTyM o
    TyApp ann fun arg -> TyApp ann <$> deBruijnTyM fun <*> deBruijnTyM arg
    TyIFix ann pat arg -> TyIFix ann <$> deBruijnTyM pat <*> deBruijnTyM arg
    -- boring non-recursive cases
    TyBuiltin ann con -> pure $ TyBuiltin ann con

deBruijnTermM
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => Term TyName Name uni fun ann
    -> m (Term NamedTyDeBruijn NamedDeBruijn uni fun ann)
deBruijnTermM = \case
    -- variable case
    Var ann n -> Var ann <$> nameToDeBruijn n
    -- binder cases
    TyAbs ann tn k t -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyAbs ann tn' k <$> deBruijnTermM t
    LamAbs ann n ty t -> declareUnique n $ do
        n' <- nameToDeBruijn n
        withScope $ LamAbs ann n' <$> deBruijnTyM ty <*> deBruijnTermM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> deBruijnTermM t1 <*> deBruijnTermM t2
    TyInst ann t ty -> TyInst ann <$> deBruijnTermM t <*> deBruijnTyM ty
    Unwrap ann t -> Unwrap ann <$> deBruijnTermM t
    IWrap ann pat arg t -> IWrap ann <$> deBruijnTyM pat <*> deBruijnTyM arg <*> deBruijnTermM t
    Error ann ty -> Error ann <$> deBruijnTyM ty
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn

-- | Convert a 'Type' with 'NamedTyDeBruijn's into a 'Type' with 'TyName's.
-- Will throw an error if a free variable is encountered.
unDeBruijnTy
    :: (MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Type NamedTyDeBruijn uni ann -> m (Type TyName uni ann)
unDeBruijnTy = flip runReaderT (Levels 0 BM.empty) . unDeBruijnTyM

-- | Convert a 'Term' with 'NamedTyDeBruijn's and 'NamedDeBruijn's into a 'Term' with 'TyName's and 'Name's.
-- Will throw an error if a free variable is encountered.
unDeBruijnTerm
    :: (MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Term NamedTyDeBruijn NamedDeBruijn uni fun ann -> m (Term TyName Name uni fun ann)
unDeBruijnTerm = flip runReaderT (Levels 0 BM.empty) . unDeBruijnTermM

-- | Convert a 'Program' with 'NamedTyDeBruijn's and 'NamedDeBruijn's into a 'Program' with 'TyName's and 'Name's.
-- Will throw an error if a free variable is encountered.
unDeBruijnProgram
    :: (MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Program NamedTyDeBruijn NamedDeBruijn uni fun ann -> m (Program TyName Name uni fun ann)
unDeBruijnProgram (Program ann ver term) = Program ann ver <$> unDeBruijnTerm term


-- | Convert a 'Type' with 'NamedTyDeBruijn's into a 'Type' with 'TyName's.
-- A variant that does not throw an error on free variables. See 'freeIndexGrace'.
unDeBruijnTyGrace
    :: MonadQuote m
    => Type NamedTyDeBruijn uni ann -> m (Type TyName uni ann)
unDeBruijnTyGrace = flip evalStateT BM.empty . flip runReaderT (Levels 0 BM.empty) . unDeBruijnTyGraceM

-- | Convert a 'Term' with 'NamedTyDeBruijn's and 'NamedDeBruijn's into a 'Term' with 'TyName's and 'Name's.
-- A variant that does not throw an error on free variables. See 'freeIndexGrace'.
unDeBruijnTermGrace
    :: MonadQuote m
    => Term NamedTyDeBruijn NamedDeBruijn uni fun ann -> m (Term TyName Name uni fun ann)
unDeBruijnTermGrace = flip evalStateT BM.empty . flip runReaderT (Levels 0 BM.empty) . unDeBruijnTermGraceM

-- | Convert a 'Program' with 'NamedTyDeBruijn's and 'NamedDeBruijn's into a 'Program' with 'TyName's and 'Name's.
-- A variant that does not throw an error on free variables. See 'freeIndexGrace'.
unDeBruijnProgramGrace
    :: MonadQuote m
    => Program NamedTyDeBruijn NamedDeBruijn uni fun ann -> m (Program TyName Name uni fun ann)
unDeBruijnProgramGrace (Program ann ver term) = Program ann ver <$> unDeBruijnTermGrace term

unDeBruijnTyM
    :: (MonadReader Levels m, MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Type NamedTyDeBruijn uni ann
    -> m (Type TyName uni ann)
unDeBruijnTyM = unDeBruijnTyMWith freeIndexThrow

unDeBruijnTermM
    :: (MonadReader Levels m, MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Term NamedTyDeBruijn NamedDeBruijn uni fun ann
    -> m (Term TyName Name uni fun ann)
unDeBruijnTermM = unDeBruijnTermMWith freeIndexThrow

unDeBruijnTyGraceM
    :: (MonadReader Levels m, MonadQuote m, MonadState (BM.Bimap Unique Level) m)
    => Type NamedTyDeBruijn uni ann
    -> m (Type TyName uni ann)
unDeBruijnTyGraceM = unDeBruijnTyMWith freeIndexGrace

unDeBruijnTermGraceM
    :: (MonadReader Levels m, MonadQuote m, MonadState (BM.Bimap Unique Level) m)
    => Term NamedTyDeBruijn NamedDeBruijn uni fun ann
    -> m (Term TyName Name uni fun ann)
unDeBruijnTermGraceM = unDeBruijnTermMWith freeIndexGrace

-- | Takes a "handler" function to execute when encountering free variables.
unDeBruijnTyMWith
    :: (MonadReader Levels m, MonadQuote m)
    => (Index -> m Unique)
    -> Type NamedTyDeBruijn uni ann
    -> m (Type TyName uni ann)
unDeBruijnTyMWith h = \case
    -- variable case
    TyVar ann n -> TyVar ann <$> deBruijnToTyName h n
    -- binder cases
    TyForall ann tn k ty ->
        -- See NOTE: [DeBruijn indices of Binders]
        declareBinder $ do
            tn' <- deBruijnToTyName h $ set index 0 tn
            withScope $ TyForall ann tn' k <$> unDeBruijnTyMWith h ty
    TyLam ann tn k ty ->
        -- See NOTE: [DeBruijn indices of Binders]
        declareBinder $ do
            tn' <- deBruijnToTyName h $ set index 0 tn
            withScope $ TyLam ann tn' k <$> unDeBruijnTyMWith h ty
    -- boring recursive cases
    TyFun ann i o -> TyFun ann <$> unDeBruijnTyMWith h i <*> unDeBruijnTyMWith h o
    TyApp ann fun arg -> TyApp ann <$> unDeBruijnTyMWith h fun <*> unDeBruijnTyMWith h arg
    TyIFix ann pat arg -> TyIFix ann <$> unDeBruijnTyMWith h pat <*> unDeBruijnTyMWith h arg
    -- boring non-recursive cases
    TyBuiltin ann con -> pure $ TyBuiltin ann con

-- | Takes a "handler" function to execute when encountering free variables.
unDeBruijnTermMWith
    :: (MonadReader Levels m, MonadQuote m)
    => (Index -> m Unique)
    -> Term NamedTyDeBruijn NamedDeBruijn uni fun ann
    -> m (Term TyName Name uni fun ann)
unDeBruijnTermMWith h = \case
    -- variable case
    Var ann n -> Var ann <$> deBruijnToName h n
    -- binder cases
    TyAbs ann tn k t ->
        -- See NOTE: [DeBruijn indices of Binders]
        declareBinder $ do
            tn' <- deBruijnToTyName h $ set index 0 tn
            withScope $ TyAbs ann tn' k <$> unDeBruijnTermMWith h t
    LamAbs ann n ty t ->
        -- See NOTE: [DeBruijn indices of Binders]
        declareBinder $ do
            n' <- deBruijnToName h $ set index 0 n
            withScope $ LamAbs ann n' <$> unDeBruijnTyMWith h ty <*> unDeBruijnTermMWith h t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> unDeBruijnTermMWith h t1 <*> unDeBruijnTermMWith h t2
    TyInst ann t ty -> TyInst ann <$> unDeBruijnTermMWith h t <*> unDeBruijnTyMWith h ty
    Unwrap ann t -> Unwrap ann <$> unDeBruijnTermMWith h t
    IWrap ann pat arg t -> IWrap ann <$> unDeBruijnTyMWith h pat <*> unDeBruijnTyMWith h arg <*> unDeBruijnTermMWith h t
    Error ann ty -> Error ann <$> unDeBruijnTyMWith h ty
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
