namespace FiveResultNegative

def shared (n : Nat) : Nat := n + 1

theorem selected : shared 0 = shared 0 := rfl

end FiveResultNegative
