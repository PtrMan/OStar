module Axiom where

import Term

data AxiomData = AxiomData {
	tag :: AxiomTag, -- tau
	t :: TermNode,
	tTick :: TermNode
} deriving (Eq, Ord)

-- NOTE< assumes the tag is equal >
instance Show AxiomData where
  show (AxiomData tag t tTick) = "<AxiomData " ++ show tag ++ " " ++ show t ++ " " ++ show tTick ++ ">"



data AxiomTag =
	Equal |
	Equi |
	Type

instance Eq AxiomTag where
  Equal == Equal  = True
  Equi == Equi    = True
  Type == Type    = True
  _ == _          = False

instance Ord AxiomTag where
	Equal <= Equal = True
	Equal <= Type = True
	Equi <= Type = True
	_ <= _ = False

instance Show AxiomTag where
	show Equal = "Equal"
	show Equi = "Equi"
	show Type = "Type"

stringToAxiomTag :: String -> AxiomTag
stringToAxiomTag "Type" = Type
stringToAxiomTag "Equi" = Equi
stringToAxiomTag "Equal" = Equal
