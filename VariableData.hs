module VariableData where


data VariableData = VariableData {
	delta :: String,
	tau :: String
}

instance Eq VariableData where
  x == y                = areVariablesEqual x y

instance Ord VariableData where
  (VariableData delta1 tau1) <= (VariableData delta2 tau2) = delta1 <= delta2 && tau1 <= tau2

instance Show VariableData where
  show (VariableData delta tau) = "<VariableData " ++ show delta ++ " " ++ show tau ++ ">"

areVariablesEqual :: VariableData -> VariableData -> Bool
areVariablesEqual (VariableData aDelta aTau) (VariableData bDelta bTau) = aDelta == bDelta && aTau == bTau
