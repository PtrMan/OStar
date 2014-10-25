module VariableData where

data VariableData = VariableData { delta :: String
								 , tau :: String
								 } deriving (Ord, Eq)

instance Show VariableData where
  show (VariableData delta tau) = "<VariableData " ++ show delta ++ " " ++ show tau ++ ">"
