module

/-! Changed-shared-definition Challenge fixture for the cumulative Nine checker. -/

@[expose] public section

namespace NineResultNegative

def shared (n : Nat) : Nat := n + 1

theorem selected : shared 0 = shared 0 := rfl

end NineResultNegative
