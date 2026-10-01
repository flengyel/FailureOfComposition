module

/-! Changed-shared-definition Solution fixture for the cumulative Nine checker. -/

@[expose] public section

namespace NineResultNegative

def shared (n : Nat) : Nat := n + 2

theorem selected : shared 0 = shared 0 := rfl

end NineResultNegative
