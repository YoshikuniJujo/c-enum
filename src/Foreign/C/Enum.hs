{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall -fno-warn-tabs #-}

module Foreign.C.Enum (enum) where

import Language.Haskell.TH (
	Name, mkName, newName, Lit(..), clause, cxt, normalB,
	DecsQ, DecQ, valD, funD, instanceD,
	patSynSigD, patSynD, prefixPatSyn, explBidir,
	newtypeD, normalC, derivClause,
	ExpQ, varE, conE, litE, appE, infixE, listE, lamCaseE,
	conT, appT, varP, conP, litP, MatchQ, match,
	doE, bindS, noBindS,
	bangType, bang, noSourceUnpackedness, noSourceStrictness )
import Control.Arrow (first)
import Data.Bool (bool)
import Data.Maybe (isJust, listToMaybe)
import Data.List (partition)
import Text.Read (Lexeme(..), lexP, step, prec, readPrec, choice, parens)

enum :: String -> Name -> [Name] -> [(String, Integer)] -> DecsQ
enum nt t ds nvs = (\n s r ms -> n : s (r ms))
	<$> mkNewtype nt t ds'
	<*> bool (pure id) ((:) <$> mkShow nt ns) bs
	<*> bool (pure id) ((:) <$> mkRead nt ns) br
	<*> mkMembers nt nvs
	where
	ShowReadClasses bs br ds' = showReadClasses ds
	ns = fst <$> nvs

{- ^

Write like the following.

@
enum Foo ''Int [''Show, ''Read, ''Eq] [
	("FooError", - 1),
	("FooZero", 0),
	("FooOne", 1),
	("FooTwo", 2) ]
@

Then you get like the following.

@
newtype Foo = Foo Int deriving Eq

pattern FooError :: Int -> Foo
pattern FooError <- Foo (- 1) where
	FooError = Foo (- 1)

pattern FooZero :: Int -> Foo
...


instance Show Foo where
	showsPrec = ...

instance Read Foo where
	readPrec = ...
@

And you can read and show like the following.

@
> Foo $ - 1
FooError
> FooTwo
FooTwo
> Foo 3
Foo 3
> read "Foo (- 1)" :: Foo
FooError
> read \"FooOne\" :: Foo
FooOne
@

-}

data ShowReadClasses = ShowReadClasses {
	showReadClassesShow :: Bool,
	showReadClassesRead :: Bool,
	showReadClassesClasses :: [Name] } deriving Show

popIt :: Eq a => a -> [a] -> (Maybe a, [a])
popIt x = (listToMaybe `first`) . partition (== x)

showReadClasses :: [Name] -> ShowReadClasses
showReadClasses ns = ShowReadClasses (isJust s) (isJust r) ns''
	where (s, ns') = popIt ''Show ns; (r, ns'') = popIt ''Read ns'

mkNewtype :: String -> Name -> [Name] -> DecQ
mkNewtype nt t ds = newtypeD (cxt []) (mkName nt) [] Nothing
	(normalC (mkName nt) [bangType (bang noSourceUnpackedness noSourceStrictness) (conT t)])
	$ (derivClause Nothing . (: []) . conT) <$> ds

mkMembers :: String -> [(String, Integer)] -> DecsQ
mkMembers t nvs = concat <$> uncurry (mkMember (mkName t) (mkName t)) `mapM` nvs

mkMember :: Name -> Name -> String -> Integer -> DecsQ
mkMember t c n v = sequence [
	patSynSigD (mkName n) (conT t),
	patSynD (mkName n) (prefixPatSyn [])
		(explBidir [clause [] (normalB (conE c `appE` litE (IntegerL v))) []])
		(conP c [litP (IntegerL v)])
	]

mkShow :: String -> [String] -> DecQ
mkShow t ns = instanceD (cxt []) (conT ''Show `appT` conT (mkName t))
	[defineShowsPrec t ns]

defineShowsPrec :: String -> [String] -> DecQ
defineShowsPrec t ns = do
	d <- newName "d"
	n <- newName "n"
	funD 'showsPrec [
		clause [varP d] (normalB (lamCaseE
			((matchFoo <$> ns) ++
			[match (conP (mkName t) [varP n]) (normalB $ foo d n) []])
			)) []
		]
	where
	foo d n = varE 'showParen `appE` (varE d `gt` litE (IntegerL 10))
		`dl` ((litE (StringL (t ++ " ")) `p` varE '(++))
			`dt` (varE 'showsPrec `appE` litE (IntegerL 11) `appE` varE n))

matchFoo :: String -> MatchQ
matchFoo f = match (conP (mkName f) []) (normalB $ litE (StringL f) `p` (varE '(++))) []

mkRead :: String -> [String] -> DecQ
mkRead t ns = instanceD (cxt []) (conT ''Read `appT` conT (mkName t)) . (: [])
	$ valD (varP 'readPrec) (normalB $ varE 'parens `dl` (varE 'choice `appE` listE (
		(readFoo <$> ns) ++
		[varE 'prec `appE` litE (IntegerL 10) `appE` doE [
			bindS (conP 'Ident [litP $ StringL t]) $ varE 'lexP,
			noBindS $ conE (mkName t) `fdl` (varE 'step `appE` varE 'readPrec) ]]
		))) []

readFoo :: String -> ExpQ
readFoo n = doE [
	bindS (conP 'Ident [litP $ StringL n]) $ varE 'lexP,
	noBindS $ varE 'pure `appE` conE (mkName n) ]

gt :: ExpQ -> ExpQ -> ExpQ
e1 `gt` e2 = infixE (Just e1) (varE '(>)) (Just e2)

dl, fdl :: ExpQ -> ExpQ -> ExpQ
e1 `dl` e2 = infixE (Just e1) (varE '($)) (Just e2)
e1 `fdl` e2 = infixE (Just e1) (varE '(<$>)) (Just e2)

dt :: ExpQ -> ExpQ -> ExpQ
e1 `dt` e2 = infixE (Just e1) (varE '(.)) (Just e2)

p :: ExpQ -> ExpQ -> ExpQ
ex `p` op = infixE (Just ex) op Nothing
