module Item where

import Term
import Axiom

-- TODO< left and right can also be terms >
data Item = Item {
	itemTag :: AxiomTag,
	t1 :: TermNode,
	t2 :: TermNode,
	utility :: Int
	}
		deriving (Show)