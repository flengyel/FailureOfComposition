namespace SevenResultNegative

def shared (n : Nat) : Nat := n + 2

theorem selected : shared 0 = shared 0 := rfl

end SevenResultNegative
