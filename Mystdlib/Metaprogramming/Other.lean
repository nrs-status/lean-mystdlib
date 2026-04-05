

def Lean.Name.explicit_repr : Lean.Name -> String
| .anonymous => ".anonymous"
| .num nm nat => ".num " ++ "(" ++ nm.explicit_repr ++ ") " ++ toString nat
| .str nm s => ".str " ++ "(" ++ nm.explicit_repr ++ ") " ++ s


