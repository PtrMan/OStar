module AxiomTag where

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
